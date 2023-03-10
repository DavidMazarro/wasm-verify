module VerifiWASM.ASTValidator where

import Control.Monad (when)
import Data.Containers.ListUtils (nubOrd)
import qualified Data.Map as M
import Data.Text (Text, pack)
import Helpers.ANSI (bold)
import VerifiWASM.LangTypes
import VerifiWASM.VerifiWASM

programTypes :: Program -> VerifiWASM FuncTypes
programTypes Program{functions, ghostFunctions} = do
  let functionNames = map funcName functions
  let ghostFunctionNames = map ghostName ghostFunctions
  let allNames = functionNames ++ ghostFunctionNames

  -- Ensuring that there are no duplicate function/ghost function
  -- names allows us to perform union of the VarTypes safely
  -- since there will be no collisions.
  ensureNoDuplicateNames allNames errMsgDups

  functionVarTypes <-
    mapM
      ( \function -> do
          funTypes <- functionTypes function
          return $ M.singleton (funcName function) funTypes
      )
      functions
  ghostFunctionVarTypes <-
    mapM
      ( \ghostFun -> do
          ghostFunTypes <- ghostFunctionTypes ghostFun
          return $ M.singleton (ghostName ghostFun) ghostFunTypes
      )
      ghostFunctions
  let allVarTypes = functionVarTypes ++ ghostFunctionVarTypes

  return $ foldl M.union M.empty allVarTypes
  where
    errMsgDups =
      "A duplicate name for a function or ghost function was found. \n"
        <> "Make sure that all functions and ghost functions are named differently."

functionTypes :: Function -> VerifiWASM VarTypes
functionTypes function = do
  let argNames = map fst (funcArgs function)
  let returnNames = map fst (funcReturns function)
  let localDecls = concatMap localVars $ locals $ funcSpec function
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

{- | Validates an expression and returns its type,
 recursively validating the expressions inside.
-}
validateExpr :: Expr -> VerifiWASM ExprType
validateExpr (FunCall _ _) =
  undefined
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
validateExpr (IVar _) =
  return ExprInt
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
      _ -> error "This shouldn't happen."

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
      _ -> error "This shouldn't happen."

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
      _ -> error "This shouldn't happen."

----------- Helper functions -----------

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
