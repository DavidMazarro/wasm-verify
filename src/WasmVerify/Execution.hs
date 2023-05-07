{-# LANGUAGE CPP #-}

module WasmVerify.Execution where

import Control.Monad (foldM, forM, forM_, void, when)
import Control.Monad.State (get, gets, modify, put)
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as Map
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
import qualified VerifiWASM.VerifiWASM as VerifiWASM
import WasmVerify.CFG (functionToCFG, stronglyConnCompCFG)
import WasmVerify.CFG.Types (CFG, Node (Node), NodeLabel, getNodeFromLabel, nodeLabel)
import WasmVerify.Monad
import WasmVerify.Paths (allExecutionPaths, checkAssertsForSCC, getNodesAssertsMap)
import WasmVerify.ToSMT (exprToSMT)

executeProgram :: VerifiWASM.Program -> Wasm.ValidModule -> WasmVerify Lazy.Text
executeProgram program wasmModule = do
  varMaps <- forM (functions program) $ \func -> do
    -- '(!!)' from lists is safe here by construction of the map of WASM functions,
    -- and 'Map.!' is safe here because we have already validated that there exists
    -- a WASM function for each of the specs in the VerifiWASM program (see 'ASTValidator.validate')
    let wasmFunction = (Wasm.functions . Wasm.getModule $ wasmModule) !! (wasmFunctions Map.! funcName func)
    executeFunction program (funcName func, wasmFunction)

  -- Declare SMT variables for all functions
  -- TODO: This reverse here is temporary. It should be unnecessary
  -- to make the variables be declared in ascending order.
  forM_ varMaps (\varMap -> forM_ (reverse $ Map.assocs varMap) declareAllVersions)

  addSetLogicSMT "QF_UFLIA"
  addCheckSatSMT
  gets smtText
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
    declareAllVersions :: VersionedVar -> WasmVerify ()
    declareAllVersions (identifier, varVersion) = do
      addVarDeclsSMT [(identifier, version) | version <- [0 .. varVersion]]

-- TODO: Initialise locals to the default values corresponding
-- to their types in the variable version map, and add SMT for
-- those default values. Do the same thing for arguments, but
-- adding SMT matching the precondition in the specification.
executeFunction :: VerifiWASM.Program -> (Identifier, Wasm.Function) -> WasmVerify (Map Identifier IdVersion)
executeFunction specModule (name, wasmFunction) = do
  void $ updateContextFunction name
  let mSpec = find ((== name) . funcName) $ functions specModule
  case mSpec of
    (Just spec) -> do
      let cfgInitialsFinals@(cfg, _, _) = functionToCFG wasmFunction
      nodesAssertsMap <- getNodesAssertsMap cfg spec
      let sccs = stronglyConnCompCFG cfg

      forM_ sccs (checkAssertsForSCC spec nodesAssertsMap)

      initializeIdentifierMap spec

      let paths = allExecutionPaths cfgInitialsFinals (map nodeLabel $ Map.keys nodesAssertsMap)

      forM_ paths (executePath spec nodesAssertsMap cfgInitialsFinals)

      gets identifierMap

    -- When the WebAssembly function doesn't have a specification in the VerifiWASM
    -- module, we simply don't perform verification, so our SMT program is empty.
    Nothing -> return ""
  where
    initializeIdentifierMap :: VerifiWASM.Function -> WasmVerify ()
    initializeIdentifierMap spec = do
      state <- get
      let numArgs = length $ funcArgs spec
      let numLocals = length $ locals $ funcSpec spec
      let initialMap = Map.fromList $ [(indexToVar (intToNatural var), 0) | var <- [0 .. numArgs + numLocals - 1]]
      put state{identifierMap = initialMap}

-- TODO: During execution, for variables named in the specification, n argument
-- variables must be mapped to the first n indices in WebAssembly,
-- m local variables must be mapped to the m indices after n in
-- WebAssembly and the r variables in the return variables must be mapped with
-- r indices in the returned stack (usually, the only returned value
-- is the top of the stack with just one element).

-- TODO: When executing different paths, we have to generate new variables
-- for each path, unused in the other paths. It's like doing different verifications.
-- At the end, we do a check-sat of the whole model with all paths.
executePath ::
  Function ->
  Map Node Assert ->
  (CFG, NodeLabel, Set NodeLabel) ->
  [NodeLabel] ->
  WasmVerify ()
executePath spec nodesAssertsMap (cfg, initial, finals) path = do
  -- Add precondition (requires or assert depending on the first node in the path) to SMT
  varToExprMap <- getVarToExprMap spec
  prePath <- assertionPre varToExprMap $ head path
  appendToSMT "; pre\n"
  addAssertSMT $ exprToSMT prePath

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

  varToExprMapWithReturns <- getVarToExprMapWithReturns spec
  -- Add postcondition (assert or ensures depending on the first node in the path) to SMT
  appendToSMT "\n; post\n"
  postPath <- assertionPost varToExprMapWithReturns $ last path
  addAssertSMT $ exprToSMT postPath
  where
    getVarToExprMap :: Function -> WasmVerify (Map Identifier Expr)
    getVarToExprMap func = do
      let argsWithIndex = zip (funcArgs func) ([0 ..] :: [Int])
      Map.fromList
        <$> ( forM argsWithIndex $ \(arg, index) -> do
                let var = "var_" <> show index
                varVersion <- lookupVarVersion var
                identifier <- versionedVarToIdentifier (var, varVersion)
                return $ (fst arg, IVar identifier)
            )
    getVarToExprMapWithReturns :: Function -> WasmVerify (Map Identifier Expr)
    getVarToExprMapWithReturns func = do
      varToExprMap <- getVarToExprMap func
      foldM
        ( \varMap ret -> do
            topValue <- popFromStack
            return $ Map.insert (fst ret) topValue varMap
        )
        varToExprMap
        $ funcReturns func
    isFinalNode :: NodeLabel -> Bool
    isFinalNode label = label `Set.member` finals
    assertionPre :: Map Identifier Expr -> NodeLabel -> WasmVerify Expr
    assertionPre varToExprMap label
      | label == initial =
          (replaceWithVersionedVars varToExprMap . requiresExpr . requires . funcSpec) spec
      | otherwise = undefined -- TODO: nodesAssertsMap Map.! (getNodeFromLabel nodeLabel)
    assertionPost :: Map Identifier Expr -> NodeLabel -> WasmVerify Expr
    assertionPost varToExprMap label
      | isFinalNode label =
          (replaceWithVersionedVars varToExprMap . ensuresExpr . ensures . funcSpec) spec
      | otherwise = undefined -- TODO: nodesAssertsMap Map.! (getNodeFromLabel nodeLabel)

executeNodesInPath :: [Node] -> WasmVerify ()
executeNodesInPath nodes = do
  appendToSMT "\n; code symbolic execution\n"
  forM_ nodes executeNode
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
executeInstruction (Wasm.GetLocal index) = do
  let identifier = indexToVar index
  varVersion <- lookupVarVersion identifier
  stackValue <- ValueVar <$> versionedVarToIdentifier (indexToVar index, varVersion)
  void $ pushToStack stackValue
-- TODO: Instead of substituting expressions in the stack, we will add new
-- variables to the stack and add an assert that makes the expression equal to that variable.
-- Change the set instruction here.
executeInstruction (Wasm.SetLocal index) = do
  topValue <- popFromStack
  let identifier = indexToVar index
  varVersion <- newVarVersion (indexToVar index)
  addAssertSMT =<< varEqualsStackValueText (identifier, varVersion) topValue
executeInstruction (Wasm.TeeLocal index) = do
  undefined
executeInstruction (Wasm.I32Const n) = do
  let stackValue = ValueConst $ toInteger n
  void . pushToStack $ stackValue
executeInstruction (Wasm.I64Const n) = do
  let stackValue = ValueConst $ toInteger n
  void . pushToStack $ stackValue
executeInstruction (Wasm.IRelOp _ relOp) = do
  undefined
-- TODO: Add new res (result) variable in the operations,
-- make that equal to the result of the operation
executeInstruction (Wasm.IBinOp _ Wasm.IAdd) = do
  topValue2 <- popFromStack
  topValue1 <- popFromStack
  void . pushToStack $ IPlus topValue1 topValue2
executeInstruction (Wasm.IBinOp _ binaryOp) = do
  undefined
executeInstruction (Wasm.Call index) = do
  undefined
executeInstruction instruction =
  failWithError $
    Failure $
      "Unsupported instruction: "
        <> (T.pack . show)
          instruction

{- | Given an the name of a variable (an identifier)
 from WebAssembly, generates a new version of the variable
 from the latest version used in the symbolic execution.
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
  state <- get
  let newState = state{symbolicStack = value : (symbolicStack state)}
  put newState
  return $ symbolicStack newState

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

{- | Update the execution context with the provided name of the
 function that is currently being executed.
-}
updateContextFunction :: Identifier -> WasmVerify (Identifier, Int)
updateContextFunction name = do
  state <- get
  let (_, index) = executionContext state
  let newState = state{executionContext = (name, index)}
  put newState
  return (name, index)

{- | Update the execution context with the provided index of the
 execution path that is currently being executed.
-}
updateContextPathIndex :: Int -> WasmVerify (Identifier, Int)
updateContextPathIndex index = do
  state <- get
  let (name, _) = executionContext state
  let newState = state{executionContext = (name, index)}
  put newState
  return (name, index)

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
  BAnd
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IPlus leftExpr rightExpr) =
  BAnd
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IMult leftExpr rightExpr) =
  BAnd
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IDiv leftExpr rightExpr) =
  BAnd
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IMod leftExpr rightExpr) =
  BAnd
    <$> replaceWithVersionedVars varToExprMap leftExpr
    <*> replaceWithVersionedVars varToExprMap rightExpr
replaceWithVersionedVars varToExprMap (IAbs expr) =
  IAbs <$> replaceWithVersionedVars varToExprMap expr

-- * Helper functions

varEqualsStackValueText :: VersionedVar -> StackValue -> WasmVerify Text
varEqualsStackValueText var stackValue = do
  identifier <- versionedVarToIdentifier var
  stackValueText <- stackValueToText stackValue
  return $ "(= " <> T.pack identifier <> " " <> stackValueText <> ")"

indexToVar :: Natural -> Identifier
indexToVar index = "var_" <> show index

stackValueToText :: StackValue -> WasmVerify Text
stackValueToText (ValueConst n) = (return . T.pack . show) n
stackValueToText (ValueVar var) = undefined -- TODO

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
