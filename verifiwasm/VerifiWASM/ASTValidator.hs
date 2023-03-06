module VerifiWASM.ASTValidator where

import Control.Monad (when)
import Data.Text (Text, pack)
import Helpers.ANSI (bold)
import VerifiWASM.LangTypes
import VerifiWASM.VerifiWASM

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
  undefined
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

prettyType :: ExprType -> Text
prettyType ExprBool = "boolean"
prettyType ExprInt = "integer"
