{-# LANGUAGE CPP #-}

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

{- |
 = Validation of VerifiWASM specifications #validation#

 To ensure that VerifiWASM specifications are well-formed and sound,
 this module provides some checks after the parsing of the specification
 source file. Currently, these are the validations that are performed on any given
 VerifiWASM specification:

  - __Functions__ (i.e. WebAssembly function specifications) are validated as follows:

      - Functions described in the specification must exist in the
      WebAssembly module that is to be verified, and have the same name.
      - Functions described in the specification must have a matching number
      of arguments and the same types than those of the WebAssembly function
      of the same name.
      - Functions must have different names, and must also have
      different names to any existing ghost functions.
      - The name of the arguments, local variables or return values in a function
      specification must not collide with the name of an existing function or ghost function.
      - There cannot be name duplicates among arguments, local variables or return values
      of a function specification.
      - The instruction index in an 'Assert' must be greater or equal than 1,
      it cannot be 0. It also cannot be a negative number, but that check is performed
      during parsing of the VerifiWASM source code.

  - __Ghost functions__ are validated as follows:

      - Ghost functions must have different names, and must also have
      different names to any existing functions.
      - The name of the arguments in a ghost function must not collide with the name
      of an existing function or ghost function.
      - There cannot be name duplicates among the arguments of a ghost function.
      - Variable identifiers appearing in the 'Termination' condition of a
      ghost function must be arguments of that ghost function.

 In addition, in the 'Requires' \/ 'Ensures' \/ 'Assert's of functions,
 or in the body of 'GhostFunction's, there are expressions ('Expr').
 These are the validations that are performed on expressions:

  - Variable identifiers appearing in an expression must have been declared
  as arguments or as local variables in the local scope of the expression.
  - Expressions must be sound from a type perspective. For instance, arithmetic operations
  require that its operands are integer expressions, @if-then-else@ requires
  that the condition is a boolean expression and the @then@ body and @else@ body
  are of the same type, etc.
  - The expressions in 'Requires' \/ 'Ensures' \/ 'Assert's __must__ be boolean expressions.
  Nested subexpressions can be integer or boolean expressions, but the topmost expression
  must return a boolean value.
  - 'Requires' \/ 'Ensures' \/ 'Assert's each have a scope of variables that can be
  used in their expressions:
      - 'Requires' expressions can make use of arguments, both for function specifications
      and ghost functions. In the case of function specifications, the expression in a 'Requires'
      cannot contain references to local variables or return variables since those are not
      in scope before executing the function.
      - 'Ensures' expressions can make use of arguments and return variables, but not
      local variables since after the function finishes executing those are already out of scope.
      - 'Assert's expressions can make use of arguments and local variables, but not
      return variables since they are not in scope until the function finishes its execution.
  - Ghost function calls appearing in expressions require:
      - That the called ghost function exists in the VerifiWASM module.
      - That the number of arguments received matches with the number of
        arguments that appear in its definition.
      - That the types of all arguments are integers.
  Currently, ghost functions don't support boolean arguments.
  - In an expression, it only makes sense to do a function call on a ghost function.
  Trying to call a function specification in an expression will result in an error.
-}
module VerifiWASM.Validation where

import Control.Monad (unless, void, when)
import Control.Monad.State (get, gets, put)
import Data.Containers.ListUtils (nubOrd)
import Data.List (find, intercalate, intersect)
import qualified Data.Map as M
import Data.Maybe (fromJust, isNothing)
import qualified Data.Set as Set
import Data.Text (Text, pack)
import qualified Data.Text.Lazy as Lazy
import Helpers.ANSI (bold)
import qualified Language.Wasm as Wasm
import qualified Language.Wasm.Structure as Wasm hiding (Import (desc, name))
import Safe (atMay)
import VerifiWASM.LangTypes
import VerifiWASM.VerifiWASM

#if MIN_VERSION_base(4,15,0)
import Helpers.Numeric (naturalToInt)
#elif MIN_VERSION_base(4,12,0)
import GHC.Natural
#else 
import Helpers.Numeric (naturalToInt)
#endif

{- | A function that validates a complete VerifiWASM specification,
 throwing an exception within the 'VerifiWASM' monad when any
 of the checks aren't met. See the [Validation](#validation) section
 above for a list of the current checks that are performed.
-}
validate :: Program -> Wasm.ValidModule -> VerifiWASM ()
validate program wasmModule = do
  wasmFunctions <- getWasmFunctions
  validateFunctionsExist program (map fst wasmFunctions)

  mapM_ (validateSpecArgReturnTypes wasmModule wasmFunctions) (functions program)

  globalTypes <- programTypes program
  put $
    ContextState
      { globalTypes = globalTypes,
        localTypes = ("", M.empty),
        ghostFunReturnTypes = ghostFunReturnTypes
      }
  mapM_ (validateGhostFun program) (ghostFunctions program)
  mapM_ (validateFunction program) (functions program)
  where
    getWasmFunctions :: VerifiWASM [(Lazy.Text, Wasm.Function)]
    getWasmFunctions =
      concat
        <$> mapM
          ( \export -> case Wasm.desc export of
              Wasm.ExportFunc index -> do
                let moduleFunctions = (Wasm.functions . Wasm.getModule) wasmModule
                let mFunction = moduleFunctions `atMay` naturalToInt index
                when (isNothing mFunction) $ possibleImportErr index (length moduleFunctions)
                return [(Wasm.name export, fromJust mFunction)]
              _ -> return []
          )
          ((Wasm.exports . Wasm.getModule) wasmModule)
    ghostFunReturnTypes =
      M.fromList $
        map (\ghostFun -> (ghostName ghostFun, ghostReturnType ghostFun)) $
          ghostFunctions program
    possibleImportErr funcIndex totalFunctions =
      failWithError $
        Failure $
          "Trying to retrieve WebAssembly functions"
            <> ", there was an index that went out of bounds: "
            <> (bold . pack . show . naturalToInt) funcIndex
            <> "\nOut of "
            <> (bold . pack . show) totalFunctions
            <> " functions (indexed from "
            <> (pack . show) (0 :: Int)
            <> " to "
            <> (pack . show) (totalFunctions - 1)
            <> ") that are exported in the WebAssembly module."
            <> "\nThis most likely happened because you tried to verify"
            <> " a WebAssembly module that imports external functions,"
            <> " which is currently unsupported."

{- | Checks that the function specifications described in
 the VerifiWASM module actually exist within the WebAssembly
 module that is to be verified.
-}
validateFunctionsExist :: Program -> [Lazy.Text] -> VerifiWASM ()
validateFunctionsExist program wasmFunctionNames = do
  let specFunctionNames = map (Lazy.pack . funcName) $ functions program
  -- All function names in the spec must be an element of
  -- the list of function names in the WASM module.
  -- Otherwise we throw an error.
  let droppedNames = dropWhile (`elem` wasmFunctionNames) specFunctionNames
  unless (null droppedNames) $
    failWithError $
      Failure $
        "The function "
          <> (bold . Lazy.toStrict . head $ droppedNames)
          <> " was defined in the VerifiWASM specification,"
          <> " but no function with that name exists in the WebAssembly module."

{- | Checks that a function specification described in
 the VerifiWASM module has a matching number of arguments
 and the same types than those of the WebAssembly function
 of the same name.
-}
validateSpecArgReturnTypes :: Wasm.ValidModule -> [(Lazy.Text, Wasm.Function)] -> FunctionSpec -> VerifiWASM ()
validateSpecArgReturnTypes wasmModule wasmFunctions spec = do
  let mWasmFunction = find (\name -> (Lazy.unpack . fst) name == funcName spec) wasmFunctions

  -- Due to the existence validation in 'validateFunctionsExist',
  -- this error shouldn't happen.
  when (isNothing mWasmFunction) $ notFoundWasmFunErr $ funcName spec

  -- The use of 'fromJust' here is safe because we have
  -- just checked whether the value is 'Nothing' or not
  -- (and in that case, we throw a custom failure)
  let (_, wasmFunction) = fromJust mWasmFunction
  let wasmFuncType = wasmFuncTypes !! naturalToInt (Wasm.funcType wasmFunction)
  let wasmArgTypes = Wasm.params wasmFuncType
  let wasmReturnTypes = Wasm.results wasmFuncType
  let wasmLocalTypes = Wasm.localTypes wasmFunction

  unless (listEqualWith idTypeEqWasmType specArgTypes wasmArgTypes) $
    mismatchTypesErr "arguments" specArgTypes wasmArgTypes
  unless (listEqualWith idTypeEqWasmType specReturnTypes wasmReturnTypes) $
    mismatchTypesErr "return values" specReturnTypes wasmReturnTypes
  unless (listEqualWith idTypeEqWasmType specLocalTypes wasmLocalTypes) $
    mismatchTypesErr "local variables" specLocalTypes wasmLocalTypes
  where
    wasmFuncTypes = (Wasm.types . Wasm.getModule) wasmModule
    specArgTypes = map snd $ funcArgs spec
    specReturnTypes = map snd $ funcReturns spec
    specLocalTypes = map snd $ (concatMap localVars . locals . specBody) spec
    notFoundWasmFunErr name =
      failWithError $
        Failure $
          "FunctionSpec "
            <> (bold . pack)
              name
            <> " could not be found in the WebAssembly module "
            <> "(this shouldn't have happened, report as a bug)."
    mismatchTypesErr argReturnOrLocals specTypes wasmTypes =
      failWithError $
        Failure $
          "The "
            <> argReturnOrLocals
            <> "' types in function specification "
            <> (bold . pack . funcName)
              spec
            <> " do not match with those of the corresponding WebAssembly function:\n"
            <> "The function specification has the following types for its "
            <> argReturnOrLocals
            <> ": "
            <> (bold . pack . show)
              specTypes
            <> "\n"
            <> "Whereas the WebAssembly function has the following types for its "
            <> argReturnOrLocals
            <> ": "
            <> (bold . pack . show)
              wasmTypes

validateFunction :: Program -> FunctionSpec -> VerifiWASM ()
validateFunction program funcSpec = do
  -- Sets the local context
  let name = funcName funcSpec
  types <- lookupTypesInFunction name
  ContextState{..} <- get
  put $ ContextState{globalTypes, localTypes = (name, types), ghostFunReturnTypes}

  let identifierCollissions = functionAndGhostNames `intersect` funcArgsIdentifiers
  unless (null identifierCollissions) $
    argsIdentifiersCollissionsErr "function specification" "arguments" name identifierCollissions

  validateLocalIdentifiers functionAndGhostNames (locals . specBody $ funcSpec)
  validateRequires False (funcArgs funcSpec) (requires . specBody $ funcSpec)
  validateEnsures (funcArgs funcSpec ++ funcReturns funcSpec) (ensures . specBody $ funcSpec)
  mapM_
    ( validateAssert
        ( funcArgs funcSpec
            ++ concatMap localVars (locals . specBody $ funcSpec)
            ++ funcReturns funcSpec
        )
    )
    $ (asserts . specBody) funcSpec
  where
    functionAndGhostNames = allFunctionAndGhostNames program
    funcArgsIdentifiers = map fst . funcArgs $ funcSpec

validateGhostFun :: Program -> GhostFunction -> VerifiWASM ()
validateGhostFun program ghostFun = do
  -- Sets the local context
  let name = ghostName ghostFun
  (_, types) <- lookupTypesInGhostFun name
  ContextState{..} <- get
  put $ ContextState{globalTypes, localTypes = (name, types), ghostFunReturnTypes}

  let identifierCollissions = functionAndGhostNames `intersect` ghostArgsIdentifiers
  unless (null identifierCollissions) $
    argsIdentifiersCollissionsErr "ghost function" "arguments" name identifierCollissions

  void . validateExpr . ghostExpr $ ghostFun
  validateTermination ghostFun (ghostTermination ghostFun)
  validateRequires True (ghostArgs ghostFun) (ghostRequires ghostFun)
  where
    functionAndGhostNames = allFunctionAndGhostNames program
    ghostArgsIdentifiers = map fst . ghostArgs $ ghostFun

validateTermination :: GhostFunction -> Termination -> VerifiWASM ()
validateTermination ghostFun (Decreases identifiers) = do
  -- Make sure that all identifiers in the termination condition
  -- are arguments of the ghost function
  mapM_ validateIdentifier identifiers
  where
    validateIdentifier :: Identifier -> VerifiWASM ()
    validateIdentifier identifier =
      unless (identifier `elem` argumentIdentifiers) $ notInArgsErr identifier
    argumentIdentifiers = map fst . ghostArgs $ ghostFun
    notInArgsErr identifier =
      failWithError $
        Failure $
          "In the ghost function "
            <> (bold . pack . ghostName)
              ghostFun
            <> ", the variable "
            <> (bold . pack)
              identifier
            <> " appearing in the termination condition of the ghost function"
            <> " is not one of the arguments of the ghost function:\n"
            <> (bold . pack . intercalate ", ")
              argumentIdentifiers
            <> "\nVariables appearing in a termination condition must"
            <> " refer to the arguments of the ghost function."

validateRequires ::
  -- | 'True' in the case of a 'GhostFunction', 'False' in the case of a 'FunctionSpec'.
  Bool ->
  -- | The scope of valid identifiers for the 'Requires' expression.
  [TypedIdentifier] ->
  Requires ->
  VerifiWASM ()
validateRequires isGhost varScope (Requires expr) = do
  requiresType <- validateExpr expr
  validateBooleanAndScope "requires" expr requiresType varScope requiresScopeErr
  where
    requiresScopeErr =
      Failure $
        "A \"requires\" expression can only contain identifiers declared in the arguments"
          <> ( if isGhost
                then ".\n"
                else
                  ", but not in local variables or in the returns,"
                    <> " since those are not in scope before executing the function.\n"
             )
          <> "This is the failing expression: "
          <> (bold . pack . show) expr

validateEnsures ::
  -- | The scope of valid identifiers for the 'Requires' expression.
  [TypedIdentifier] ->
  Ensures ->
  VerifiWASM ()
validateEnsures varScope (Ensures expr) = do
  ensuresType <- validateExpr expr
  validateBooleanAndScope "ensures" expr ensuresType varScope ensuresScopeErr
  where
    ensuresScopeErr =
      Failure $
        "An \"ensures\" expression can only contain identifiers declared in the arguments"
          <> " or in the returns, but not in local variables, since those are out of scope"
          <> " after execution the function.\nThis is the failing expression: "
          <> (bold . pack . show) expr

validateAssert ::
  -- | The scope of valid identifiers for the 'Requires' expression.
  [TypedIdentifier] ->
  Assert ->
  VerifiWASM ()
validateAssert varScope (Assert (instrIndex, expr)) = do
  when (instrIndex == 0) indexOutOfBoundsErr

  assertType <- validateExpr expr
  validateBooleanAndScope "assert" expr assertType varScope assertScopeErr
  where
    indexOutOfBoundsErr =
      failWithError $
        Failure $
          "Instruction index "
            <> (bold . pack . show)
              instrIndex
            <> " was found in an assert,"
            <> " but instruction indices cannot be 0."
    assertScopeErr =
      Failure $
        "An \"assert\" expression can only contain identifiers declared in the arguments,"
          <> " or in the local variables, but not in the returns, since those are not in"
          <> " scope before the function finishes executing.\n"
          <> "This is the failing expression: "
          <> (bold . pack . show) expr

{- | Ensures that the names of local variables don't clash with
  the names of existing ghost functions and function specifications.
-}
validateLocalIdentifiers :: [Identifier] -> [Local] -> VerifiWASM ()
validateLocalIdentifiers functionAndGhostNames localDecls = do
  currentFuncName <- gets (fst . localTypes)
  let identifierCollissions = functionAndGhostNames `intersect` localIdentifiers
  unless (null identifierCollissions) $
    argsIdentifiersCollissionsErr
      "function specification"
      "local variables"
      currentFuncName
      identifierCollissions
  where
    localIdentifiers = [fst localVar | localDecl <- localDecls, localVar <- localVars localDecl]

{- | Validates an expression and returns its type,
 recursively validating the expressions inside.
-}
validateExpr :: Expr -> VerifiWASM ExprType
validateExpr (FunCall ghostFun args) = do
  (ghostOrFuncSpec, ghostFunTypes) <- lookupTypesInGhostFun ghostFun
  ghostFunReturnTypes <- gets ghostFunReturnTypes
  (scopeName, _) <- gets localTypes

  -- Right now we aren't differentiating between I32 or I64
  -- in the arguments, so it suffices to check that the function
  -- call is made with the same number of arguments and that
  -- the types are all integer.
  argTypes <- mapM validateExpr args
  let numArgs = length args
  let numGhostFunTypes = length ghostFunTypes

  when (ghostOrFuncSpec == FuncSpec) $ callFuncSpecErr scopeName ghostFun

  when (numArgs /= numGhostFunTypes) $ badNumOfArgsErr scopeName numArgs numGhostFunTypes
  when (any (/= ExprInt) argTypes) $ notAllIntegerArgsErr scopeName
  let mReturnType = M.lookup ghostFun ghostFunReturnTypes
  when (isNothing mReturnType) $ notFoundGhostFunErr ghostFun
  -- The use of 'fromJust' here is safe because we have
  -- just checked whether the value is 'Nothing' or not
  -- (and in that case, we throw a custom failure)
  return $ fromJust mReturnType
  where
    badNumOfArgsErr caller receivedArgs actualArgs =
      failWithError $
        Failure $
          "In some expression in the scope of "
            <> (bold . pack)
              caller
            <> ":\nGhost function "
            <> (bold . pack)
              ghostFun
            <> " called with wrong number of arguments:\n"
            <> "it received "
            <> (bold . pack . show)
              receivedArgs
            <> " arguments when it should have received "
            <> (bold . pack . show)
              actualArgs
    notAllIntegerArgsErr caller =
      failWithError $
        Failure $
          "In some expression in the scope of "
            <> (bold . pack)
              caller
            <> ":\nGhost function "
            <> (bold . pack)
              ghostFun
            <> " expects all arguments to be integers,"
            <> " but it received an argument that is not an integer."
    callFuncSpecErr caller callee =
      failWithError $
        Failure $
          "In some expression in the scope of "
            <> (bold . pack)
              caller
            <> ":\nThere's a function call to "
            <> (bold . pack)
              callee
            <> ", which is a function specification."
            <> "\nFunction specifications cannot be called, since they"
            <> " are only meant to specify WebAssembly code. Hence, they"
            <> " are not callable in VerifiWASM."
validateExpr (IfThenElse ifExpr thenExpr elseExpr) = do
  ifType <- validateExpr ifExpr

  when (ifType /= ExprBool) $
    failWithError $
      Failure $
        "The \"if\" condition is not a boolean expression: " <> (bold . pack . show) ifExpr

  thenType <- validateExpr thenExpr
  elseType <- validateExpr elseExpr

  when (thenType /= elseType) $
    failWithError $
      Failure $
        "The \"then\" type and the \"else\" type are not the same:\n"
          <> "    \"then\" expression: "
          <> (bold . pack . show)
            thenExpr
          <> " of "
          <> prettyType thenType
          <> " type.\n"
          <> "    \"else\" expression: "
          <> (bold . pack . show) elseExpr
          <> " of "
          <> prettyType elseType
          <> " type."

  return thenType
validateExpr BFalse =
  return ExprBool
validateExpr BTrue =
  return ExprBool
validateExpr topExpr@(BNot subExpr) =
  validateUnary topExpr subExpr ExprBool ExprBool
validateExpr topExpr@(BImpl leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprBool ExprBool
validateExpr topExpr@(BAnd leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprBool ExprBool
validateExpr topExpr@(BOr leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprBool ExprBool
validateExpr topExpr@(BXor leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprBool ExprBool
validateExpr topExpr@(BEq leftExpr rightExpr) =
  validateSameType topExpr leftExpr rightExpr
validateExpr topExpr@(BDistinct leftExpr rightExpr) =
  validateSameType topExpr leftExpr rightExpr
validateExpr topExpr@(BLessOrEq leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprBool
validateExpr topExpr@(BLess leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprBool
validateExpr topExpr@(BGreaterOrEq leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprBool
validateExpr topExpr@(BGreater leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprBool
validateExpr (IVar identifier) = do
  (scopeName, varTypes) <- gets localTypes

  unless (identifier `M.member` varTypes) $ variableNotInScopeErr scopeName

  -- Variables can currently only be of integer type.
  return ExprInt
  where
    variableNotInScopeErr scopeName =
      failWithError $
        Failure $
          "Variable "
            <> (bold . pack)
              identifier
            <> " was used in "
            <> (bold . pack)
              scopeName
            <> " but it was not declared in the scope.\n"
            <> "Make sure it appears as an argument to "
            <> (bold . pack)
              scopeName
            <> " or that it is declared as a local variable"
            <> " (this only applies to function specifications, not ghost functions)."
validateExpr (IInt _) =
  return ExprInt
validateExpr topExpr@(INeg subExpr) =
  validateUnary topExpr subExpr ExprInt ExprInt
validateExpr topExpr@(IMinus leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprInt
validateExpr topExpr@(IPlus leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprInt
validateExpr topExpr@(IMult leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprInt
validateExpr topExpr@(IDiv leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprInt
validateExpr topExpr@(IMod leftExpr rightExpr) =
  validateBinary topExpr leftExpr rightExpr ExprInt ExprInt
validateExpr topExpr@(IAbs subExpr) =
  validateUnary topExpr subExpr ExprInt ExprInt

validateUnary :: Expr -> Expr -> ExprType -> ExprType -> VerifiWASM ExprType
validateUnary topExpr subExpr expectedType returnType = do
  subType <- validateExpr subExpr

  when (subType /= expectedType) $
    failWithError $
      Failure $
        operation topExpr
          <> " receives a "
          <> prettyType expectedType
          <> " expression but it got: "
          <> (bold . pack . show) subExpr
          <> " of "
          <> prettyType subType
          <> " type instead."

  return returnType
  where
    operation expr = case expr of
      BNot _ -> "not b (boolean negation)"
      INeg _ -> "-n (negative for numbers)"
      IAbs _ -> "|n| (absolute value)"
      _ -> error "This should not happen."

validateBinary :: Expr -> Expr -> Expr -> ExprType -> ExprType -> VerifiWASM ExprType
validateBinary topExpr leftExpr rightExpr expectedType returnType = do
  leftType <- validateExpr leftExpr
  rightType <- validateExpr rightExpr

  when (leftType /= expectedType) $
    failWithError $
      Failure $
        typeErrorWithSide "left" leftExpr leftType

  when (rightType /= expectedType) $
    failWithError $
      Failure $
        typeErrorWithSide "right" rightExpr rightType

  return returnType
  where
    typeErrorWithSide side expr typeExpr =
      side
        <> " side of "
        <> operation topExpr
        <> " receives a "
        <> prettyType expectedType
        <> " expression but it got: "
        <> (bold . pack . show) expr
        <> " of "
        <> prettyType typeExpr
        <> " type instead."
    operation expr = case expr of
      BImpl _ _ -> "=>"
      BAnd _ _ -> "&&"
      BOr _ _ -> "||"
      BXor _ _ -> "^^"
      BLessOrEq _ _ -> "<="
      BLess _ _ -> "<"
      BGreaterOrEq _ _ -> ">="
      BGreater _ _ -> ">"
      IMinus _ _ -> "-"
      IPlus _ _ -> "+"
      IMult _ _ -> "*"
      IDiv _ _ -> "/"
      IMod _ _ -> "%"
      _ -> error "This should not have happened. Report this as a bug."

validateSameType :: Expr -> Expr -> Expr -> VerifiWASM ExprType
validateSameType topExpr leftExpr rightExpr = do
  leftType <- validateExpr leftExpr
  rightType <- validateExpr rightExpr

  when (leftType /= rightType) $
    failWithError $
      Failure $
        "The two sides of the expression "
          <> (bold . pack . show) topExpr
          <> " have mismatching types:\n"
          <> "    left expression: "
          <> (bold . pack . show) leftExpr
          <> " of "
          <> prettyType leftType
          <> " type.\n"
          <> "    right expression: "
          <> (bold . pack . show) rightExpr
          <> " of "
          <> prettyType rightType
          <> " type.\n"

  return $ returnType topExpr
  where
    returnType expr = case expr of
      BEq _ _ -> ExprBool
      BDistinct _ _ -> ExprBool
      _ -> error "This should not have happened. Report this as a bug."

----------- Helper functions -----------

-- * Helper functions

{- | Gets a map with the types of all functions and
 ghost functions that comprise the specification.
 Each value of the map is in turn a map (one for each
 function/ghost function) that associates all of the variables
 within that function/ghost function its corresponding type.
-}
programTypes :: Program -> VerifiWASM FunTypes
programTypes program@Program{functions, ghostFunctions} = do
  let allNames = allFunctionAndGhostNames program
  -- Ensuring that there are no duplicate function/ghost function
  -- names allows us to perform union of the VarTypes safely
  -- since there will be no collisions.
  ensureNoDuplicateNames allNames errMsgDups

  functionVarTypes <-
    mapM
      ( \function -> do
          funTypes <- functionTypes function
          return $ M.singleton (funcName function) (FuncSpec, funTypes)
      )
      functions
  ghostFunctionVarTypes <-
    mapM
      ( \ghostFun -> do
          ghostFunTypes <- ghostFunctionTypes ghostFun
          return $ M.singleton (ghostName ghostFun) (Ghost, ghostFunTypes)
      )
      ghostFunctions
  let allVarTypes = functionVarTypes ++ ghostFunctionVarTypes

  return $ foldr M.union M.empty allVarTypes
  where
    errMsgDups =
      "A duplicate name for a function or ghost function was found. \n"
        <> "Make sure that all functions and ghost functions are named differently."

{- | Returns a map with the types of all variables in
 a function. Those would be: its arguments, its return values,
 and the local variables defined in the specification.
-}
functionTypes :: FunctionSpec -> VerifiWASM VarTypes
functionTypes function = do
  let argNames = map fst (funcArgs function)
  let returnNames = map fst (funcReturns function)
  let localDecls = concatMap localVars $ locals $ specBody function
  let localNames = map fst localDecls
  let allNames = argNames ++ returnNames ++ localNames

  -- Ensuring that there are no duplicate argument/return/local
  -- names to avoid identifier collisions.
  ensureNoDuplicateNames allNames errMsgDups

  return $
    M.fromList (funcArgs function)
      `M.union` M.fromList (funcReturns function)
      `M.union` M.fromList localDecls
  where
    errMsgDups =
      "Some arguments, return variables or local variables"
        <> " with duplicate names were found in function: "
        <> (bold . pack) (funcName function)
        <> "\n"
        <> "Make sure that all arguments, return variables and local variables"
        <> " are named differently within a function declaration."

{- | Returns a map with the types of all variables in a ghost function,
 i.e. the type of its arguments.
-}
ghostFunctionTypes :: GhostFunction -> VerifiWASM VarTypes
ghostFunctionTypes ghostFun = do
  let argNames = map fst (ghostArgs ghostFun)

  -- Ensuring that there are no duplicate argument
  -- names to avoid identifier collisions.
  ensureNoDuplicateNames argNames errMsgDups

  return $ M.fromList $ ghostArgs ghostFun
  where
    errMsgDups =
      "Some arguments with duplicate names were found in ghost function: "
        <> (bold . pack) (ghostName ghostFun)
        <> "\n"
        <> "Make sure that all arguments are named differently"
        <> " within a ghost function declaration."

{- | Checks that an 'IdType' from VerifiWASM and a
 type from WebAssembly are the same.
-}
idTypeEqWasmType :: IdType -> Wasm.ValueType -> Bool
idTypeEqWasmType I32 Wasm.I32 = True
idTypeEqWasmType I64 Wasm.I64 = True
idTypeEqWasmType _ _ = False

{- | Compares two lists of different types for equality
 with a custom predicate.
-}
listEqualWith :: (a -> b -> Bool) -> [a] -> [b] -> Bool
listEqualWith _ [] [] = True
listEqualWith _ [] _ = False
listEqualWith _ _ [] = False
listEqualWith p (x : xs) (y : ys) = p x y && listEqualWith p xs ys

ensureNoDuplicateNames :: [Identifier] -> Text -> VerifiWASM ()
ensureNoDuplicateNames names errMsg = do
  -- If the number of names doesn't match
  -- with the number of names without duplicates,
  -- it means that indeed there are some duplicate names.
  when (length names /= length (nubOrd names)) $
    failWithError $
      Failure errMsg

prettyType :: ExprType -> Text
prettyType ExprBool = "boolean"
prettyType ExprInt = "integer"

lookupTypesInGhostFun :: Identifier -> VerifiWASM (GhostOrFuncSpec, VarTypes)
lookupTypesInGhostFun ghostFun = do
  contextState <- get

  let mVarTypes = M.lookup ghostFun $ globalTypes contextState

  -- If the ghost function isn't found in the program, we throw an error.
  when (isNothing mVarTypes) $ notFoundGhostFunErr ghostFun

  -- The use of 'fromJust' here is safe because we have
  -- just checked whether the value is 'Nothing' or not
  -- (and in that case, we throw a custom failure)
  return $ fromJust mVarTypes

lookupTypesInFunction :: Identifier -> VerifiWASM VarTypes
lookupTypesInFunction function = do
  contextState <- get

  let mVarTypes = M.lookup function $ globalTypes contextState

  -- If the function isn't found in the program, we throw an error.
  when (isNothing mVarTypes) $ notFoundFunErr function

  -- The use of 'fromJust' here is safe because we have
  -- just checked whether the value is 'Nothing' or not
  -- (and in that case, we throw a custom failure)
  return $ (snd . fromJust) mVarTypes
  where
    notFoundFunErr name =
      failWithError $
        Failure $
          "FunctionSpec specification "
            <> (bold . pack)
              name
            <> " could not be found in the VerifiWASM file "
            <> "(this shouldn't have happened, report as a bug)."

allFunctionAndGhostNames :: Program -> [Identifier]
allFunctionAndGhostNames Program{functions, ghostFunctions} = functionNames ++ ghostFunctionNames
  where
    functionNames = map funcName functions
    ghostFunctionNames = map ghostName ghostFunctions

validateBooleanAndScope :: Text -> Expr -> ExprType -> [TypedIdentifier] -> Failure -> VerifiWASM ()
validateBooleanAndScope requiresEnsuresOrAssert expr exprType varScope scopeErr = do
  when (exprType /= ExprBool) $
    failWithError $
      Failure $
        "One of the \""
          <> requiresEnsuresOrAssert
          <> "\" expressions is not a boolean expression: "
          <> (bold . pack . show) expr

  -- When the difference between the list of identifiers in the expression
  -- and the list of identifiers in the scope is not the empty list,
  -- that means there are some identifiers appearing in the expression that
  -- are not in the scope. In that case we throw an error.
  unless (null (setIdentifiersInExpr Set.\\ setVarScope)) $ failWithError scopeErr
  where
    setIdentifiersInExpr = Set.fromList $ identifiersInExpr expr
    setVarScope = Set.fromList $ map fst varScope

-- | Returns all of the identifiers that can be found in a given expression.
identifiersInExpr :: Expr -> [Identifier]
identifiersInExpr (FunCall _ args) =
  concatMap identifiersInExpr args
identifiersInExpr (IfThenElse ifExpr thenExpr elseExpr) =
  identifiersInExpr ifExpr ++ identifiersInExpr thenExpr ++ identifiersInExpr elseExpr
identifiersInExpr BFalse = []
identifiersInExpr BTrue = []
identifiersInExpr (BNot subExpr) =
  identifiersInExpr subExpr
identifiersInExpr (BImpl leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BAnd leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BOr leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BXor leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BEq leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BDistinct leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BLessOrEq leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BLess leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BGreaterOrEq leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (BGreater leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (IVar identifier) = [identifier]
identifiersInExpr (IInt _) = []
identifiersInExpr (INeg subExpr) =
  identifiersInExpr subExpr
identifiersInExpr (IMinus leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (IPlus leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (IMult leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (IDiv leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (IMod leftExpr rightExpr) =
  identifiersInExpr leftExpr ++ identifiersInExpr rightExpr
identifiersInExpr (IAbs subExpr) =
  identifiersInExpr subExpr

notFoundGhostFunErr :: Identifier -> VerifiWASM ()
notFoundGhostFunErr name =
  failWithError $
    Failure $
      "Ghost function "
        <> (bold . pack)
          name
        <> " could not be found in the VerifiWASM file."

argsIdentifiersCollissionsErr :: Text -> Text -> Identifier -> [Identifier] -> VerifiWASM ()
argsIdentifiersCollissionsErr functionOrGhost argsOrLocals name collissions =
  failWithError $
    Failure $
      "In the "
        <> functionOrGhost
        <> " "
        <> (bold . pack)
          name
        <> ", some of the "
        <> argsOrLocals
        <> " were declared with names "
        <> "that overlap with some of the function or ghost function names:\n"
        <> (bold . pack . intercalate ", ")
          collissions
        <> "\nPlease rename either the "
        <> argsOrLocals
        <> " or the functions/ghost functions"
        <> " to avoid name collissions."
