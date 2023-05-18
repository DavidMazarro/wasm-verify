{-# LANGUAGE CPP #-}

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

{- |
 = Symbolic execution and SMT code generation

 TODO: Add description
-}
module WasmVerify.Execution where

import Control.Monad (foldM, forM, forM_, replicateM, replicateM_, unless, void, when)
import Control.Monad.State (get, gets, modify, put)
import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import Data.Containers.ListUtils (nubOrd)
import Data.List (find, isPrefixOf, sort, stripPrefix)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as Lazy
import GHC.Natural
import Helpers.ANSI (bold)
import qualified Language.Wasm as Wasm
import qualified Language.Wasm.Structure as Wasm hiding (Import (desc, name))
import Safe (atMay)
import VerifiWASM.LangTypes
import qualified VerifiWASM.LangTypes as VerifiWASM (FunctionSpec, Program)
import WasmVerify.CFG (functionToCFG, stronglyConnCompCFG)
import WasmVerify.CFG.Types (CFG, Node (Node), NodeLabel, getNodeFromLabel, nodeLabel)
import WasmVerify.Monad
import WasmVerify.Paths (allExecutionPaths, checkAssertsForSCC, getNodesAssertsMap, getTransitionAnnotation)
import WasmVerify.ToSMT (exprToSMT)

#if MIN_VERSION_base(4,15,0)
import Helpers.Numeric
#elif MIN_VERSION_base(4,12,0)
import Helpers.Numeric (i32ToSignedInteger, i64ToSignedInteger)
#else 
import Helpers.Numeric
#endif

{- | Performs the symbolic execution of all functions in a WebAssembly module that
 have a matching specification ('FunctionSpec') in the VerifiWASM 'VerifiWASM.Program' provided,
 by calling 'executeFunction' on each one.
 It returns a map between the names of the functions to be verified, and a list
 of SMT modules that correspond to the possible execution paths (see 'allExecutionPaths')
 of a WebAssembly function.
-}
executeProgram ::
  -- | The VerifiWASM specification to verify against.
  VerifiWASM.Program ->
  -- | The WebAssembly module containing the functions to be verified.
  Wasm.ValidModule ->
  WasmVerify (Map Identifier [Lazy.Text])
executeProgram program wasmModule = do
  modify (\state -> state{wasmFunctionIndicesBimap = wasmFunctionsBimap})
  foldM
    ( \smtMap funcSpec -> do
        let moduleFunctions = (Wasm.functions . Wasm.getModule) wasmModule
        -- 'Map.!' is safe here because we have already validated that there exists
        -- a WASM function for each of the specs in the VerifiWASM program (see 'Validation.validate')
        let wasmFunctionIndex = wasmFunctionsBimap Bimap.! funcName funcSpec
        let mWasmFunction = moduleFunctions `atMay` wasmFunctionIndex

        when (isNothing mWasmFunction) $
          possibleImportErr (funcName funcSpec) wasmFunctionIndex (length moduleFunctions)

        -- The use of 'fromJust' here is safe because we have
        -- just checked whether the value is 'Nothing' or not
        -- (and in that case, we throw a custom failure)
        smtFunction <- executeFunction program (funcName funcSpec, fromJust mWasmFunction)
        return $ Map.insert (funcName funcSpec) smtFunction smtMap
    )
    Map.empty
    $ functions program
  where
    wasmFunctionsBimap = getFunctionIndicesBimap $ Wasm.getModule wasmModule
    possibleImportErr name funcIndex totalFunctions =
      failWithError $
        Failure $
          "Trying to find the WebAssembly function "
            <> (bold . T.pack) name
            <> ", it couldn't be found or the index "
            <> (bold . T.pack . show) funcIndex
            <> "is out of bounds.\n"
            <> "\nOut of "
            <> (bold . T.pack . show) totalFunctions
            <> " functions (indexed from "
            <> (T.pack . show) (0 :: Int)
            <> " to "
            <> (T.pack . show) (totalFunctions - 1)
            <> ") that are exported in the WebAssembly module."
            <> "This most likely happened because you tried to verify"
            <> " a WebAssembly module that imports external functions,"
            <> " which is currently unsupported."

{- | Performs the symbolic execution of a WebAssembly function, verifies it against
 its specification, and returns a list of SMT modules that correspond to the possible
 execution paths (see 'allExecutionPaths') of a WebAssembly function.
-}
executeFunction ::
  -- | The VerifiWASM specification to verify against.
  VerifiWASM.Program ->
  -- | A tuple of the name of the function to be verified
  -- and the function's contents.
  (Identifier, Wasm.Function) ->
  WasmVerify [Lazy.Text]
executeFunction specModule (name, wasmFunction) = do
  cleanSMT
  let mSpec = find ((== name) . funcName) $ functions specModule
  case mSpec of
    (Just spec) -> do
      let cfgInitialFinal@(cfg, _, _) = functionToCFG wasmFunction
      nodesAssertsMap <- getNodesAssertsMap cfg spec
      let sccs = stronglyConnCompCFG cfg

      forM_ sccs (checkAssertsForSCC spec nodesAssertsMap)

      let paths = allExecutionPaths cfgInitialFinal (map nodeLabel $ Map.keys nodesAssertsMap)

      -- Symbolic execution of all execution paths
      forM
        (zip paths [0 ..])
        ( \(path, pathIndex) ->
            executePath specModule spec nodesAssertsMap cfgInitialFinal pathIndex path
        )

    -- When the WebAssembly function doesn't have a specification in the VerifiWASM
    -- module, we simply don't perform verification, so our SMT program is empty.
    Nothing -> return []

{- | Performs the symbolic execution of a given execution path (see 'allExecutionPaths')
 of a WebAssembly function, verifies it against its specification, and returns an
 SMT module. This SMT module, when run through an SMT solver, tells us whether
 the provided execution path adheres to the specification we gave for that function.
 See 'WasmVerify.verifyModule' for more information on how we interpret the
 result of running the SMT solver on an SMT module.
-}
executePath ::
  VerifiWASM.Program ->
  FunctionSpec ->
  Map Node Assert ->
  (CFG, NodeLabel, NodeLabel) ->
  Int ->
  [NodeLabel] ->
  WasmVerify Lazy.Text
executePath specModule spec nodesAssertsMap (cfg, initial, final) pathIndex path = do
  cleanSMT

  addGhostFunctionsToSMT specModule

  appendToSMT $ "\n;;;;; " <> T.pack (funcName spec) <> "\n"

  appendToSMT $ "\n;;; path " <> T.pack (show pathIndex) <> "\n"

  -- If the path starts from the initial node, we need to initialize
  -- the local variables to their default values.
  when (head path == initial) $ initializeIdentifierMap spec

  let numOfArgs = length $ funcArgs spec
  initializeLocalsSMT [numOfArgs .. numOfArgs + length (allLocalsInFunction spec) - 1]

  -- PRECONDITION
  -- Add precondition (requires or assert depending on the first node in the path) to SMT
  varToExprMap <- getVarToExprMap spec
  prePath <- assertionPre varToExprMap $ head path
  appendToSMT "\n; pre\n"
  addAssertSMT $ exprToSMT prePath

  -- SYMBOLIC EXECUTION
  -- Add the SMT code corresponding to the symbolic execution of the nodes in the path
  let lastNodeInPath = last path
  executeNodesInPath specModule cfg $
    map
      (getNodeFromLabel cfg)
      -- If the last node in the path is the final node of the CFG,
      -- we include it for execution. If it is not the final node, then
      -- it means it's a node with an assertion, so that node will be executed
      -- in its respective path and is not executed in the current path.
      (if (== final) lastNodeInPath then path else init path)

  -- POSTCONDITION
  varToExprMapWithReturns <- getVarToExprMapWithReturns spec
  -- Add postcondition (assert or ensures depending on the first node in the path) to SMT
  appendToSMT "\n; post\n"
  -- We negate the postcondition, and we will aim for UNSAT to check our
  -- execution path adheres to the specification
  postPath <- BNot <$> assertionPost varToExprMapWithReturns (last path)
  addAssertSMT $ exprToSMT postPath

  -- Declare SMT variables for all functions.
  varMap <- gets identifierMap
  -- This reverse here is just to make the variables be declared in ascending order.
  forM_ (reverse $ Map.assocs varMap) declareAllVarVersions

  appendToSMT "(check-sat)"
  gets smtText
  where
    initializeLocalsSMT :: [Int] -> WasmVerify ()
    initializeLocalsSMT localIndices = do
      unless (null localIndices) $ do
        appendToSMT $ "\n; initialize local variables" <> "\n"
        -- We are assuming all local variables are integers.
        forM_ localIndices $ \index -> addAssertSMT =<< varEqualsExpr ("var_" <> show index, 0) (IInt 0)

    -- Used later to substitute named arguments in the 'Requires' clauses with
    -- the actual variables that are generated during the symbolic execution.
    getVarToExprMap :: FunctionSpec -> WasmVerify (Map Identifier Expr)
    getVarToExprMap funcSpec = do
      let argsWithIndex = zip (funcArgs funcSpec ++ allLocalsInFunction funcSpec) ([0 ..] :: [Int])
      Map.fromList
        <$> ( forM argsWithIndex $ \(arg, index) -> do
                let var = "var_" <> show index
                varVersion <- lookupVarVersion var
                let identifier = versionedVarToIdentifier (var, varVersion)
                return $ (fst arg, IVar identifier)
            )

    -- Used later to substitute named arguments and the named return variables in the 'Ensures'
    -- clauses with the actual variables that are generated during the symbolic execution.
    getVarToExprMapWithReturns :: FunctionSpec -> WasmVerify (Map Identifier Expr)
    getVarToExprMapWithReturns funcSpec = do
      varToExprMap <- getVarToExprMap funcSpec
      foldM
        ( \varMap ret -> do
            topValue <- popFromStack
            return $ Map.insert (fst ret) (stackValueToExpr topValue) varMap
        )
        varToExprMap
        -- We apply 'reverse' here because when popping values we
        -- are traversing the stack in reverse order.
        $ reverse (funcReturns funcSpec)
    initializeIdentifierMap :: VerifiWASM.FunctionSpec -> WasmVerify ()
    initializeIdentifierMap funcSpec = do
      state <- get
      let numArgs = length $ funcArgs funcSpec
      let numLocals = length $ allLocalsInFunction funcSpec
      let initialMap =
            Map.fromList $
              [ (indexToVar (intToNatural var), 0)
                | var <- [0 .. numArgs + numLocals - 1]
              ]
      put state{identifierMap = initialMap}
    assertionPre :: Map Identifier Expr -> NodeLabel -> WasmVerify Expr
    assertionPre varToExprMap label
      | label == initial =
          (replaceWithVersionedVars varToExprMap . requiresExpr . requires . specBody) spec
      | otherwise =
          (replaceWithVersionedVars varToExprMap . snd . unAssert) (nodesAssertsMap Map.! (getNodeFromLabel cfg label))
    assertionPost :: Map Identifier Expr -> NodeLabel -> WasmVerify Expr
    assertionPost varToExprMap label
      | label == final =
          (replaceWithVersionedVars varToExprMap . ensuresExpr . ensures . specBody) spec
      | otherwise =
          (replaceWithVersionedVars varToExprMap . snd . unAssert) (nodesAssertsMap Map.! (getNodeFromLabel cfg label))
    declareAllVarVersions :: VersionedVar -> WasmVerify ()
    declareAllVarVersions (identifier, varVersion) = do
      addVarDeclsSMT [versionedVarToIdentifier (identifier, version) | version <- [0 .. varVersion]]

executeNodesInPath :: VerifiWASM.Program -> CFG -> [Node] -> WasmVerify ()
executeNodesInPath specModule cfg nodes = do
  appendToSMT "\n; code symbolic execution\n"
  forM_ (zip nodes ([0 ..] :: [Int])) $ \(node, currentNodeIndex) -> do
    -- Before executing the node, we update the state to hold in the 'nodeExecutionContext'
    -- that the node that is about to be executed is the current node,
    -- and the node that follows in the path is the next node.
    modify (\state -> state{nodeExecutionContext = (nodeLabel node, nextNode nodes currentNodeIndex)})

    executeNode specModule node

    (currentNodeLabel, mNextNodeLabel) <- gets nodeExecutionContext
    -- When there's a node to be executed next, we include in the SMT module
    -- an assertion with the contents of the annotation in the transition (edge)
    -- between the current node and the next node.
    when (isJust mNextNodeLabel) $ do
      -- The use of 'fromJust' here is safe because we have
      -- just checked whether the value is 'Nothing' or not
      -- (and in that case, we throw a custom failure)
      let mAnnotation = getTransitionAnnotation cfg currentNodeLabel (fromJust mNextNodeLabel)
      maybe (return ()) addAnnotationToSMT mAnnotation

  void $ gets smtText
  where
    nextNode :: [Node] -> Int -> Maybe NodeLabel
    nextNode path index =
      if index + 1 >= length path then Nothing else Just (nodeLabel $ path !! (index + 1))

executeNode :: VerifiWASM.Program -> Node -> WasmVerify ()
executeNode specModule (Node (_, instructions)) =
  forM_ instructions (executeInstruction specModule . snd)

{- | Performs the symbolic execution of a single 'Wasm.Instruction',
 materializing any changes that need to be applied to the state.
 This includes handling the symbolic execution stack.
-}
executeInstruction :: VerifiWASM.Program -> Wasm.Instruction Natural -> WasmVerify ()
-- For control instructions, the symbolic execution just skips over them
-- since we have taken care of their control flow in the CFG step and the
-- annotations corresponding to the control branching are added in 'executeNodesInPath'.
executeInstruction _ Wasm.Unreachable =
  failWithError $
    Failure $
      "WebAssembly program reached an unreachable instruction"
        <> " during its execution, which results in a runtime error."
executeInstruction _ Wasm.Nop = return ()
executeInstruction _ (Wasm.Block _ _) = return ()
executeInstruction _ (Wasm.Loop _ _) = return ()
executeInstruction _ (Wasm.If _ _ _) = return ()
executeInstruction _ (Wasm.Br _) = return ()
executeInstruction _ (Wasm.BrIf _) = return ()
executeInstruction _ Wasm.Return = return ()
-- When you check the spec of a function, you assume the precondition and
-- check the postcondition. When you call a function it's the opposite:
-- you check the precondition and assume the poscondition holds.
-- That's the gist of the symbolic execution implementation here.
executeInstruction specModule (Wasm.Call index) = do
  functionIndicesBimap <- gets wasmFunctionIndicesBimap
  let name = functionIndicesBimap Bimap.!> naturalToInt index
  let mSpec = find ((== name) . funcName) $ functions specModule
  case mSpec of
    (Just spec) -> do
      appendToSMT $ "\n; verification of " <> T.pack name <> " function call\n(push 1)"

      let args = map fst $ funcArgs spec
      -- Due to validation in WebAssembly, it is safe to pop this many values from the stack
      -- since it is guaranteed as many as the arguments will be at the top of the stack.
      poppedValues <- replicateM (length args) popFromStack
      let argsVarMap = Map.fromList $ zip args (map stackValueToExpr poppedValues)
      precondition <- (replaceWithVersionedVars argsVarMap . requiresExpr . requires . specBody) spec
      -- We must ensure the precondition holds. To do that we negate it and check for UNSAT.
      appendToSMT $ "  \n  ; check that the precondition of " <> T.pack name <> " holds\n  "
      addAssertSMT $ exprToSMT (BNot precondition)
      appendToSMT "  (check-sat)\n(pop 1)"

      -- Adds to SMT as many result variables as return values the called function yields
      let returns = map fst $ funcReturns spec
      replicateM_ (length returns) $ do
        (resultVar, version) <- newResultVar
        void . pushToStack $ ValueVar $ versionedVarToIdentifier (resultVar, version)

      -- It is safe to peek this many values from the stack since we have just
      -- pushed to the top of the stack as many as return variables in the previous step.
      peekedValues <- gets (take (length returns) . symbolicStack)
      let returnsVarMap = Map.fromList $ zip returns (map stackValueToExpr peekedValues)
      -- The map union here is safe (no overlapping variable names) since due to validation
      -- in VerifiWASM, we don't allow any arguments and return variables in a scope to share the same name.
      let argsReturnsVarMap = argsVarMap `Map.union` returnsVarMap
      -- Since the precondition of the called function holds, we can assume the postcondition,
      -- which we will add as an assert to our main SMT frame.
      postcondition <- (replaceWithVersionedVars argsReturnsVarMap . ensuresExpr . ensures . specBody) spec
      appendToSMT $ "  \n; assume the postcondition of " <> T.pack name <> "\n"
      addAssertSMT $ exprToSMT postcondition
      appendToSMT "\n"
    Nothing -> return ()
executeInstruction _ Wasm.Drop = void popFromStack
executeInstruction _ Wasm.Select = do
  topValue3 <- popFromStack
  topValue2 <- popFromStack
  topValue1 <- popFromStack
  (resultVar, version) <- newResultVar
  void . pushToStack $ ValueVar $ versionedVarToIdentifier (resultVar, version)
  addAssertSMT $
    exprToSMT $
      IfThenElse
        (BEq (stackValueToExpr topValue3) (IInt 0))
        (BEq (IVar $ versionedVarToIdentifier (resultVar, version)) (stackValueToExpr topValue2))
        (BEq (IVar $ versionedVarToIdentifier (resultVar, version)) (stackValueToExpr topValue1))
executeInstruction _ (Wasm.GetLocal index) = do
  let identifier = indexToVar index
  varVersion <- lookupVarVersion identifier
  let stackValue = ValueVar $ versionedVarToIdentifier (identifier, varVersion)
  void $ pushToStack stackValue
executeInstruction _ (Wasm.SetLocal index) = do
  topValue <- popFromStack
  let identifier = indexToVar index
  varVersion <- newVarVersion identifier
  addAssertSMT =<< varEqualsExpr (identifier, varVersion) (stackValueToExpr topValue)
executeInstruction specModule (Wasm.TeeLocal index) = do
  topValue <- popFromStack
  void . pushToStack $ topValue
  void . pushToStack $ topValue
  executeInstruction specModule (Wasm.SetLocal index)
executeInstruction _ (Wasm.I32Const n) = do
  let stackValue = ValueConst $ i32ToSignedInteger n
  void . pushToStack $ stackValue
executeInstruction _ (Wasm.I64Const n) = do
  let stackValue = ValueConst $ i64ToSignedInteger n
  void . pushToStack $ stackValue
executeInstruction _ (Wasm.IRelOp _ relOp) = do
  operationResult <- executeIRelOp relOp
  (resultVar, version) <- newResultVar
  addAssertSMT =<< varEqualsExpr (resultVar, version) operationResult
  void . pushToStack $ ValueVar $ versionedVarToIdentifier (resultVar, version)
executeInstruction _ (Wasm.IBinOp _ binOp) = do
  operationResult <- executeIBinOp binOp
  (resultVar, version) <- newResultVar
  addAssertSMT =<< varEqualsExpr (resultVar, version) operationResult
  void . pushToStack $ ValueVar $ versionedVarToIdentifier (resultVar, version)
executeInstruction _ instruction =
  failWithError $
    Failure $
      "Unsupported WebAssembly instruction: "
        <> (T.pack . show)
          instruction

executeIBinOp :: Wasm.IBinOp -> WasmVerify Expr
executeIBinOp binOp = do
  topValue2 <- popFromStack
  topValue1 <- popFromStack
  case binOp of
    Wasm.IAdd -> return $ IPlus (stackValueToExpr topValue1) (stackValueToExpr topValue2)
    Wasm.ISub -> return $ IMinus (stackValueToExpr topValue1) (stackValueToExpr topValue2)
    Wasm.IMul -> return $ IMult (stackValueToExpr topValue1) (stackValueToExpr topValue2)
    Wasm.IRemS -> return $ IMod (stackValueToExpr topValue1) (stackValueToExpr topValue2)
    _ -> unsupportedIBinOpErr >> return BFalse
  where
    unsupportedIBinOpErr =
      failWithError $
        Failure $
          "Unsupported WebAssembly integer arithmetic operation: "
            <> (T.pack . show)
              binOp

executeIRelOp :: Wasm.IRelOp -> WasmVerify Expr
executeIRelOp binOp = do
  topValue2 <- popFromStack
  topValue1 <- popFromStack
  case binOp of
    Wasm.IEq ->
      return $
        IfThenElse
          (BEq (stackValueToExpr topValue1) (stackValueToExpr topValue2))
          (IInt 1)
          (IInt 0)
    Wasm.INe ->
      return $
        IfThenElse
          (BDistinct (stackValueToExpr topValue1) (stackValueToExpr topValue2))
          (IInt 1)
          (IInt 0)
    Wasm.ILtS ->
      return $
        IfThenElse
          (BLess (stackValueToExpr topValue1) (stackValueToExpr topValue2))
          (IInt 1)
          (IInt 0)
    Wasm.IGtS ->
      return $
        IfThenElse
          (BGreater (stackValueToExpr topValue1) (stackValueToExpr topValue2))
          (IInt 1)
          (IInt 0)
    Wasm.ILeS ->
      return $
        IfThenElse
          (BLessOrEq (stackValueToExpr topValue1) (stackValueToExpr topValue2))
          (IInt 1)
          (IInt 0)
    Wasm.IGeS ->
      return $
        IfThenElse
          (BGreaterOrEq (stackValueToExpr topValue1) (stackValueToExpr topValue2))
          (IInt 1)
          (IInt 0)
    _ -> unsupportedIBinOpErr >> return BFalse
  where
    unsupportedIBinOpErr =
      failWithError $
        Failure $
          "Unsupported WebAssembly integer comparison operation: "
            <> (T.pack . show)
              binOp

{- | Returns a 'Bimap' with the names of the functions in the WebAssembly
 module and their corresponding indices in the list of 'Wasm.functions'.
-}
getFunctionIndicesBimap :: Wasm.Module -> Bimap Identifier Int
getFunctionIndicesBimap wasmModule =
  Bimap.fromList (mapMaybe funcWithIndex $ Wasm.exports wasmModule)
  where
    funcWithIndex export = case Wasm.desc export of
      (Wasm.ExportFunc index) -> Just (Lazy.unpack (Wasm.name export), naturalToInt index)
      _ -> Nothing

{- | Returns a fresh result variable to be used in assertions that store
 the result of WebAssembly computations in 'executeInstruction'. It also inserts that
 variable in the 'identifierMap' that is part of the execution context ('ExecState').
 The starting 'IdVersion' for a newly created variable is 0.
-}
newResultVar :: WasmVerify VersionedVar
newResultVar = do
  state <- get
  let varMap = identifierMap state
  let resPrefix = "res_"
  let resultVars = filter (resPrefix `isPrefixOf`) $ Map.keys varMap
  let sortedResultVarsIndices = sort $ map (removePrefix resPrefix) resultVars
  -- Use of 'read' is a bit unsafe here, but it should be fine because
  -- we're stripping the whole prefix until only the index remains, so what
  -- we get should be a number which is what we're trying to read.
  let newResultVarIndex = if null sortedResultVarsIndices then (0 :: Int) else read (last sortedResultVarsIndices) + 1
  let freshResultVar = resPrefix <> show newResultVarIndex

  put state{identifierMap = Map.insert freshResultVar 0 (identifierMap state)}
  return (freshResultVar, 0)
  where
    removePrefix prefix original = fromMaybe original $ stripPrefix prefix original

{- | Given the name of a variable (an identifier), it returns a new
 version of the variable from the latest version used in the symbolic execution,
 and updates 'identifierMap' in the symbolic execution context.
-}
newVarVersion :: Identifier -> WasmVerify IdVersion
newVarVersion identifier = do
  -- The use of 'Map.!' is safe here because we have populated
  -- the map with starting versions for all local variables in
  -- 'executeFunction'.
  oldVer <- gets ((Map.! identifier) . identifierMap)
  let newVer = oldVer + 1
  modify (insertNewVersion identifier newVer)
  return newVer
  where
    insertNewVersion identifier' newVer state =
      state{identifierMap = Map.insert identifier' newVer (identifierMap state)}

{- | Given the name of a variable, it returns its latest version in the
 symbolic execution context at the moment of being called. Taken from 'identifierMap'.
-}
lookupVarVersion :: Identifier -> WasmVerify IdVersion
lookupVarVersion identifier = do
  -- The use of 'Map.!' is safe here because we have populated
  -- the map with starting versions for all local variables in
  -- 'executeFunction'.
  gets ((Map.! identifier) . identifierMap)

{- | Pushes a value to the symbolic execution stack,
 returning the updated stack.
-}
pushToStack :: StackValue -> WasmVerify [StackValue]
pushToStack value = do
  modify (\state -> state{symbolicStack = value : (symbolicStack state)})
  gets symbolicStack

{- | Pops the last value from the top of the symbolic
 execution stack, removing it from the stack and returning
 the value.

 __Note:__ while seemingly unsafe if provided with an empty
 stack, it's not a problem here because when compiling WebAssembly
 modules there's static validation that ensures you don't pop
 a value from the empty stack.
-}
popFromStack :: WasmVerify StackValue
popFromStack = do
  state <- get
  let (topValue : restOfStack) = symbolicStack state
  let newState = state{symbolicStack = restOfStack}
  put newState
  return topValue

{- | Replaces the variables found in an expression with the
 versioned variable version, corresponding to the latest version
 reached in the symbolic execution.
-}
replaceWithVersionedVars :: Map Identifier Expr -> Expr -> WasmVerify Expr
replaceWithVersionedVars varToExprMap (FunCall name args) =
  FunCall name <$> mapM (replaceWithVersionedVars varToExprMap) args
replaceWithVersionedVars varToExprMap (IfThenElse condExpr ifExpr elseExpr) =
  IfThenElse
    <$> replaceWithVersionedVars varToExprMap condExpr
    <*> replaceWithVersionedVars varToExprMap ifExpr
    <*> replaceWithVersionedVars varToExprMap elseExpr
replaceWithVersionedVars _ BFalse = return BFalse
replaceWithVersionedVars _ BTrue = return BTrue
replaceWithVersionedVars varToExprMap (BNot expr) =
  BNot <$> replaceWithVersionedVars varToExprMap expr
replaceWithVersionedVars varToExprMap (BImpl leftExpr rightExpr) =
  BImpl
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BAnd leftExpr rightExpr) =
  BAnd
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BOr leftExpr rightExpr) =
  BOr
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BXor leftExpr rightExpr) =
  BXor
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BEq leftExpr rightExpr) =
  BEq
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BDistinct leftExpr rightExpr) =
  BDistinct
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BLessOrEq leftExpr rightExpr) =
  BLessOrEq
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BLess leftExpr rightExpr) =
  BLess
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BGreaterOrEq leftExpr rightExpr) =
  BGreaterOrEq
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (BGreater leftExpr rightExpr) =
  BGreater
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IVar identifier) =
  return $ varToExprMap Map.! identifier
replaceWithVersionedVars _ (IInt n) = return $ IInt n
replaceWithVersionedVars varToExprMap (INeg expr) =
  INeg <$> replaceWithVersionedVars varToExprMap expr
replaceWithVersionedVars varToExprMap (IMinus leftExpr rightExpr) =
  IMinus
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IPlus leftExpr rightExpr) =
  IPlus
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IMult leftExpr rightExpr) =
  IMult
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IDiv leftExpr rightExpr) =
  IDiv
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IMod leftExpr rightExpr) =
  IMod
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IAbs expr) =
  IAbs <$> replaceWithVersionedVars varToExprMap expr

-- * Helper functions

{- | Returns SMT code for when a versioned variable is equals
 to a VerifiWASM expression (which gets formatted as SMT).
-}
varEqualsExpr :: VersionedVar -> Expr -> WasmVerify Text
varEqualsExpr var stackValue = do
  let identifier = versionedVarToIdentifier var
  let stackValueText = exprToSMT stackValue
  return $ "(= " <> T.pack identifier <> " " <> stackValueText <> ")"

-- | Transforms a WebAssembly index into a variable.
indexToVar :: Natural -> Identifier
indexToVar index = "var_" <> show index

{- | Gets all of the local variables in a function, across the
 different 'Local' declarations found in the 'SpecBody'.
-}
allLocalsInFunction :: FunctionSpec -> [TypedIdentifier]
allLocalsInFunction funcSpec = nubOrd $ concatMap localVars $ (locals . specBody) funcSpec
