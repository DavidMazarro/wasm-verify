{- |
 This module uses version 2.6 of SMTLIB2. The standard is published here:
  <https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf>.
-}
module VerifiWASM.ToSMT where

import Data.Text (Text)
import qualified Data.Text as T
import VerifiWASM.LangTypes

-- TODO: add Haddock
ghostFunToSMT :: GhostFunction -> Text
ghostFunToSMT ghostFun =
  "(define-fun "
    <> (T.pack . ghostName) ghostFun
    <> " ("
    <> (T.unwords . map argWithType . ghostArgs) ghostFun
    <> ") "
    <> (exprTypeToSMT . ghostReturnType) ghostFun
    <> " "
    <> (exprToSMT . ghostExpr) ghostFun
    <> ")"
  where
    argWithType (identifier, _) =
      "(" <> T.pack identifier <> " " <> "Int" <> ")"

-- TODO: add Haddock
exprToSMT :: Expr -> Text
exprToSMT (FunCall name args) =
  "("
    <> foldl (\x y -> x <> " " <> y) (T.pack name) (map exprToSMT args)
    <> ")"
exprToSMT (IfThenElse condExpr ifExpr elseExpr) =
  "(ite "
    <> exprToSMT condExpr
    <> " "
    <> exprToSMT ifExpr
    <> " "
    <> exprToSMT elseExpr
    <> ")"
exprToSMT BFalse = "false"
exprToSMT BTrue = "true"
exprToSMT (BNot expr) = unaryToSMT "not" expr
exprToSMT (BImpl leftExpr rightExpr) = binaryToSMT "=>" leftExpr rightExpr
exprToSMT (BAnd leftExpr rightExpr) = binaryToSMT "and" leftExpr rightExpr
exprToSMT (BOr leftExpr rightExpr) = binaryToSMT "or" leftExpr rightExpr
exprToSMT (BXor leftExpr rightExpr) = binaryToSMT "xor" leftExpr rightExpr
exprToSMT (BEq leftExpr rightExpr) = binaryToSMT "=" leftExpr rightExpr
exprToSMT (BDistinct leftExpr rightExpr) = binaryToSMT "distinct" leftExpr rightExpr
exprToSMT (BLessOrEq leftExpr rightExpr) = binaryToSMT "<=" leftExpr rightExpr
exprToSMT (BLess leftExpr rightExpr) = binaryToSMT "<" leftExpr rightExpr
exprToSMT (BGreaterOrEq leftExpr rightExpr) = binaryToSMT ">=" leftExpr rightExpr
exprToSMT (BGreater leftExpr rightExpr) = binaryToSMT ">" leftExpr rightExpr
exprToSMT (IVar identifier) = T.pack identifier
exprToSMT (IInt n) = T.pack $ show n
exprToSMT (INeg expr) = unaryToSMT "-" expr
exprToSMT (IMinus leftExpr rightExpr) = binaryToSMT "-" leftExpr rightExpr
exprToSMT (IPlus leftExpr rightExpr) = binaryToSMT "+" leftExpr rightExpr
exprToSMT (IMult leftExpr rightExpr) = binaryToSMT "*" leftExpr rightExpr
exprToSMT (IDiv leftExpr rightExpr) = binaryToSMT "div" leftExpr rightExpr
exprToSMT (IMod leftExpr rightExpr) = binaryToSMT "mod" leftExpr rightExpr
exprToSMT (IAbs expr) = unaryToSMT "abs" expr

-- TODO: add Haddock
exprTypeToSMT :: ExprType -> Text
exprTypeToSMT ExprBool = "Bool"
exprTypeToSMT ExprInt = "Int"

----------- Helper functions -----------

-- * Helper functions

-- TODO: add Haddock
unaryToSMT :: Text -> Expr -> Text
unaryToSMT operator expr =
  "(" <> operator <> " " <> exprToSMT expr <> ")"

-- TODO: add Haddock
binaryToSMT :: Text -> Expr -> Expr -> Text
binaryToSMT operator leftExpr rightExpr =
  "(" <> operator <> " " <> exprToSMT leftExpr <> " " <> exprToSMT rightExpr <> ")"
