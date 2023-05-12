{-# LANGUAGE CPP #-}

module WasmVerify.Execution where

import Control.Monad (foldM, forM, forM_, void)
import Control.Monad.State (get, gets, modify, put)
import Data.Containers.ListUtils (nubOrd)
import Data.List (find, isPrefixOf, sort, stripPrefix)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as Lazy
import Debug.Trace (traceShow)
import GHC.Natural
import qualified Language.Wasm as Wasm
import qualified Language.Wasm.Structure as Wasm hiding (Import (desc, name))
import VerifiWASM.LangTypes
import qualified VerifiWASM.LangTypes as VerifiWASM (Function, Program)
import WasmVerify.CFG (functionToCFG, stronglyConnCompCFG)
import WasmVerify.CFG.Types (CFG, Node (Node), NodeLabel, getNodeFromLabel, nodeLabel)
import WasmVerify.Monad
import WasmVerify.Paths (allExecutionPaths, checkAssertsForSCC, getNodesAssertsMap)
import WasmVerify.ToSMT (exprToSMT)

executeProgram :: VerifiWASM.Program -> Wasm.ValidModule -> WasmVerify (Map Identifier [Lazy.Text])
executeProgram program wasmModule =
  foldM
    ( \smtMap func -> do
        -- '(!!)' from lists is safe here by construction of the map of WASM functions,
        -- and 'Map.!' is safe here because we have already validated that there exists
        -- a WASM function for each of the specs in the VerifiWASM program (see 'ASTValidator.validate')
        let wasmFunction = (Wasm.functions . Wasm.getModule $ wasmModule) !! (wasmFunctions Map.! funcName func)
        smtFunction <- executeFunction program (funcName func, wasmFunction)
        return $ Map.insert (funcName func) smtFunction smtMap
    )
    Map.empty
    $ functions program
  where
    wasmFunctions = getFunctionIndicesFromExports $ Wasm.getModule wasmModule
    getFunctionIndicesFromExports :: Wasm.Module -> Map Identifier Int
    getFunctionIndicesFromExports wasmModule' =
      foldr
        ( \export accMap -> case Wasm.desc export of
            (Wasm.ExportFunc index) -> Map.insert (Lazy.unpack $ Wasm.name export) (naturalToInt index) accMap
            _ -> accMap
        )
        Map.empty
        $ Wasm.exports wasmModule'

-- TODO: Initialise locals to the default values corresponding
-- to their types in the variable version map, and add SMT for
-- those default values. Do the same thing for arguments, but
-- adding SMT matching the precondition in the specification.
executeFunction :: VerifiWASM.Program -> (Identifier, Wasm.Function) -> WasmVerify [Lazy.Text]
executeFunction specModule (name, wasmFunction) = do
  cleanSMT
  let mSpec = find ((== name) . funcName) $ functions specModule
  case mSpec of
    (Just spec) -> do
      let cfgInitialsFinals@(cfg, _, _) = functionToCFG wasmFunction
      nodesAssertsMap <- getNodesAssertsMap cfg spec
      let sccs = stronglyConnCompCFG cfg

      forM_ sccs (checkAssertsForSCC spec nodesAssertsMap)

      let paths = allExecutionPaths cfgInitialsFinals (map nodeLabel $ Map.keys nodesAssertsMap)

      -- Symbolic execution of all execution paths
      forM
        (zip paths [0 ..])
        ( \(path, pathIndex) ->
            executePath specModule spec nodesAssertsMap cfgInitialsFinals pathIndex path
        )

    -- When the WebAssembly function doesn't have a specification in the VerifiWASM
    -- module, we simply don't perform verification, so our SMT program is empty.
    Nothing -> return []

-- TODO: When executing paths, transitions between nodes that have annotations
-- must be added as an assert with whatever is in the annotation.
executePath ::
  VerifiWASM.Program ->
  Function ->
  Map Node Assert ->
  (CFG, NodeLabel, Set NodeLabel) ->
  Int ->
  [NodeLabel] ->
  WasmVerify Lazy.Text
executePath specModule spec nodesAssertsMap (cfg, initial, finals) pathIndex path = do
  cleanSMT
  -- TODO: What do we do with ghost function preconditions?
  addGhostFunctionsToSMT specModule

  appendToSMT $ "\n;;;;; " <> T.pack (funcName spec) <> "\n"

  appendToSMT $ "\n;;; path " <> T.pack (show pathIndex) <> "\n"

  initializeIdentifierMap spec

  -- PRECONDITION
  -- Add precondition (requires or assert depending on the first node in the path) to SMT
  varToExprMap <- getVarToExprMap spec
  prePath <- assertionPre varToExprMap $ head path
  appendToSMT "\n; pre\n"
  addAssertSMT $ exprToSMT prePath

  -- SYMBOLIC EXECUTION
  -- Add the SMT code corresponding to the symbolic execution of the nodes in the path
  let lastNodeInPath = last path
  executeNodesInPath $
    map
      (getNodeFromLabel cfg)
      -- If the last node in the path is a final node in the CFG,
      -- we include it for execution. If it is not a final node, then
      -- it means it's a node with an assertion, so that node will be executed
      -- in its respective path and is not executed in the current path.
      (if isFinalNode lastNodeInPath then path else init path)

  -- POSTCONDITION
  varToExprMapWithReturns <- getVarToExprMapWithReturns spec
  -- Add postcondition (assert or ensures depending on the first node in the path) to SMT
  appendToSMT "\n; post\n"
  -- We negate the postcondition, and we will aim for UNSAT to check our
  -- execution path adheres to the specification
  postPath <- BNot <$> assertionPost varToExprMapWithReturns (last path)
  addAssertSMT $ exprToSMT postPath

  -- Declare SMT variables for all functions
  -- TODO: This reverse here is temporary. It should be unnecessary
  -- to make the variables be declared in ascending order.
  varMap <- gets identifierMap
  forM_ (reverse $ Map.assocs varMap) declareAllVarVersions

  addSetLogicSMT "QF_UFLIA"
  addCheckSatSMT
  gets smtText
  where
    initializeIdentifierMap :: VerifiWASM.Function -> WasmVerify ()
    initializeIdentifierMap func = do
      state <- get
      let numArgs = length $ funcArgs func
      let numLocals = length $ allLocalsInFunction func
      let initialMap =
            Map.fromList $
              [ (indexToVar (intToNatural var), 0)
                | var <- [0 .. numArgs + numLocals - 1]
              ]
      put state{identifierMap = initialMap}
    -- Used later to substitute named arguments in the 'Requires' clauses with
    -- the actual variables that are generated during the symbolic execution.
    getVarToExprMap :: Function -> WasmVerify (Map Identifier Expr)
    getVarToExprMap func = do
      let argsWithIndex = zip (funcArgs func ++ allLocalsInFunction func) ([0 ..] :: [Int])
      Map.fromList
        <$> ( forM argsWithIndex $ \(arg, index) -> do
                let var = "var_" <> show index
                varVersion <- lookupVarVersion var
                let identifier = versionedVarToIdentifier (var, varVersion)
                return $ (fst arg, IVar identifier)
            )
    -- Used later to substitute named arguments and the named return variables in the 'Ensures'
    -- clauses with the actual variables that are generated during the symbolic execution.
    getVarToExprMapWithReturns :: Function -> WasmVerify (Map Identifier Expr)
    getVarToExprMapWithReturns func = do
      varToExprMap <- getVarToExprMap func
      foldM
        ( \varMap ret -> do
            topValue <- popFromStack
            return $ Map.insert (fst ret) (stackValueToExpr topValue) varMap
        )
        varToExprMap
        $ funcReturns func
    isFinalNode :: NodeLabel -> Bool
    isFinalNode label = label `Set.member` finals
    assertionPre :: Map Identifier Expr -> NodeLabel -> WasmVerify Expr
    assertionPre varToExprMap label
      | label == initial =
          (replaceWithVersionedVars varToExprMap . requiresExpr . requires . funcSpec) spec
      | otherwise =
          (replaceWithVersionedVars varToExprMap . snd . unAssert) (nodesAssertsMap Map.! (getNodeFromLabel cfg label))
    assertionPost :: Map Identifier Expr -> NodeLabel -> WasmVerify Expr
    assertionPost varToExprMap label
      | isFinalNode label =
          (replaceWithVersionedVars varToExprMap . ensuresExpr . ensures . funcSpec) spec
      | otherwise =
          (replaceWithVersionedVars varToExprMap . snd . unAssert) (nodesAssertsMap Map.! (getNodeFromLabel cfg label))
    declareAllVarVersions :: VersionedVar -> WasmVerify ()
    declareAllVarVersions (identifier, varVersion) = do
      addVarDeclsSMT [versionedVarToIdentifier (identifier, version) | version <- [0 .. varVersion]]

executeNodesInPath :: [Node] -> WasmVerify ()
executeNodesInPath nodes = do
  appendToSMT "\n; code symbolic execution\n"
  forM_ (zip nodes ([0 ..] :: [Int])) $ \(node, indexInPath) -> do
    executeNode node
  void $ gets smtText >>= (\x -> traceShow x (return x))

executeNode :: Node -> WasmVerify ()
executeNode (Node (_, instructions)) =
  forM_ instructions (executeInstruction . snd)

-- TODO: Add special treatment for function calls. See Manuel's notes.
-- When you check the spec of a function, you assume the precondition and
-- check the postcondition. When you call a function it's the opposite:
-- you check the precondition and assume the poscondition holds (because
-- you already verified the function).
executeInstruction :: Wasm.Instruction Natural -> WasmVerify ()
executeInstruction (Wasm.Block _ _) = return ()
executeInstruction (Wasm.Loop _ _) = return ()
executeInstruction (Wasm.Br _) = return ()
executeInstruction (Wasm.BrIf _) = return ()
executeInstruction Wasm.Return = return ()
executeInstruction (Wasm.GetLocal index) = do
  let identifier = indexToVar index
  varVersion <- lookupVarVersion identifier
  let stackValue = ValueVar $ versionedVarToIdentifier (identifier, varVersion)
  void $ pushToStack stackValue
executeInstruction (Wasm.SetLocal index) = do
  topValue <- popFromStack
  let identifier = indexToVar index
  varVersion <- newVarVersion identifier
  addAssertSMT =<< varEqualsExpr (identifier, varVersion) (stackValueToExpr topValue)
-- TODO: Add support for tee
-- executeInstruction (Wasm.TeeLocal index) = do
--   undefined
executeInstruction (Wasm.I32Const n) = do
  let stackValue = ValueConst $ toInteger n
  void . pushToStack $ stackValue
executeInstruction (Wasm.I64Const n) = do
  let stackValue = ValueConst $ toInteger n
  void . pushToStack $ stackValue
executeInstruction (Wasm.IRelOp _ relOp) = do
  operationResult <- executeIRelOp relOp
  (resultVar, version) <- newResultVar
  addAssertSMT =<< varEqualsExpr (resultVar, version) operationResult
  void . pushToStack $ ValueVar $ versionedVarToIdentifier (resultVar, version)
executeInstruction (Wasm.IBinOp _ binOp) = do
  operationResult <- executeIBinOp binOp
  (resultVar, version) <- newResultVar
  addAssertSMT =<< varEqualsExpr (resultVar, version) operationResult
  void . pushToStack $ ValueVar $ versionedVarToIdentifier (resultVar, version)
-- executeInstruction (Wasm.Call index) = do
--   undefined
executeInstruction instruction =
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

{- | Given the name of a variable (an identifier), generates a new
 version of the variable from the latest version used in the symbolic execution.
-}
newVarVersion :: Identifier -> WasmVerify IdVersion
newVarVersion identifier = do
  -- The use of 'Map.!' is safe here because we have populated
  -- the map with starting versions for all local variables in
  -- 'executeFunction'.
  void $ gets identifierMap >>= (\x -> traceShow x (return x))
  oldVer <- gets ((Map.! (traceShow identifier identifier)) . identifierMap)
  let newVer = oldVer + 1
  modify (insertNewVersion identifier newVer)
  return newVer
  where
    insertNewVersion identifier' newVer state =
      state{identifierMap = Map.insert identifier' newVer (identifierMap state)}

lookupVarVersion :: Identifier -> WasmVerify IdVersion
lookupVarVersion identifier = do
  void $ gets identifierMap >>= (\x -> traceShow x (return x))
  -- The use of 'Map.!' is safe here because we have populated
  -- the map with starting versions for all local variables in
  -- 'executeFunction'.
  gets ((Map.! (traceShow identifier identifier)) . identifierMap)

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

-- Returns SMT code for when a versioned variable is equals
-- to a VerifiWASM expression (which gets formatted as SMT).
varEqualsExpr :: VersionedVar -> Expr -> WasmVerify Text
varEqualsExpr var stackValue = do
  let identifier = versionedVarToIdentifier var
  let stackValueText = exprToSMT stackValue
  return $ "(= " <> T.pack identifier <> " " <> stackValueText <> ")"

-- | Transforms a WebAssembly index into a variable.
indexToVar :: Natural -> Identifier
indexToVar index = "var_" <> show index

{- | Gets all of the local variables in a function, across the
 different 'Local' declarations found in the 'Spec'.
-}
allLocalsInFunction :: Function -> [TypedIdentifier]
allLocalsInFunction func = nubOrd $ concatMap localVars $ (locals . funcSpec) func

-- 'naturalToInt' was only available in the base library
-- from version 4.12.0 up to 4.14.3, for some reason
-- unbeknownst to me. So this piece here defines the function
-- when the system's GHC base version is outside that range.
#if MIN_VERSION_base(4,15,0)
naturalToInt :: Natural -> Int
naturalToInt = fromInteger . naturalToInteger
#elif MIN_VERSION_base(4,12,0)
#else 
naturalToInt :: Natural -> Int
naturalToInt = fromInteger . naturalToInteger
#endif
