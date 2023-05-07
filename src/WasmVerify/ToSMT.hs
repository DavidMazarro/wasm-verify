{- |
 This module generates SMT code complying with version 2.6 of SMTLIB2.

 The version 2.6 standard is published here: <https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf>.
-}
module WasmVerify.ToSMT where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text, intercalate)
import qualified Data.Text as T
import Safe (findJust)
import VerifiWASM.LangTypes

-- TODO: add Haddock
ghostFunctionsToSMT :: Program -> Text
ghostFunctionsToSMT program =
  intercalate "\n\n" $ map recursionSetToSMT $ recursionSets program
  where
    recursionSetToSMT :: SCC GhostFunction -> Text
    recursionSetToSMT scc =
      case scc of
        (AcyclicSCC ghostFun) ->
          "(define-fun "
            <> commonDefineFun ghostFun
        (CyclicSCC [ghostFun]) ->
          "(define-fun-rec "
            <> commonDefineFun ghostFun
        (CyclicSCC mutuals) ->
          "(define-funs-rec\n  "
            <> "(\n  "
            <> intercalate "\n  " (map typeMutualToSMT mutuals)
            <> "\n  )\n\n  (\n  "
            <> intercalate "\n  " (map bodyMutualToSMT mutuals)
            <> "\n  )\n)"
    commonDefineFun ghostFun =
      (T.pack . ghostName) ghostFun
        <> "\n  "
        <> typeToSMT ghostFun
        <> "\n  "
        <> bodyToSMT ghostFun
        <> "\n)"
    typeToSMT ghostFun =
      "("
        <> (T.unwords . map argWithType . ghostArgs) ghostFun
        <> ") "
        <> (exprTypeToSMT . ghostReturnType) ghostFun
    typeMutualToSMT ghostFun =
      "  ("
        <> (T.pack . ghostName) ghostFun
        <> " "
        <> typeToSMT ghostFun
        <> ")"
    bodyMutualToSMT ghostFun =
      "  "
        <> bodyToSMT ghostFun
    bodyToSMT ghostFun = (exprToSMT . ghostExpr) ghostFun
    argWithType (identifier, _) =
      "(" <> T.pack identifier <> " " <> "Int" <> ")"

-- TODO: add Haddock
exprToSMT :: Expr -> Text
exprToSMT (FunCall name args) =
  "("
    <> foldr ((\x y -> x <> " " <> y) . exprToSMT) (T.pack name) args
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

{- | Returns the sets of non-recursive ghost functions, recursive ghost functions
 and mutually recursive ghost functions as a list of strongly connected components.

 An 'AcyclicSCC' corresponds to a non-recursive function, a 'CyclicSCC' with just
 one function is a recursive function, and a 'CyclicSCC' with several functions is
 a set of mutually recursive functions.
-}
recursionSets :: Program -> [SCC GhostFunction]
recursionSets = stronglyConnComp . funDepGraph
  where
    -- Gets the dependency graph of function calls as an adjacency list.
    funDepGraph :: Program -> [(GhostFunction, GhostFunction, [GhostFunction])]
    funDepGraph program = map (ghostFunDeps program) $ ghostFunctions program
    -- Gets the dependencies of one ghost function.
    ghostFunDeps :: Program -> GhostFunction -> (GhostFunction, GhostFunction, [GhostFunction])
    ghostFunDeps program ghostFun =
      ( ghostFun,
        ghostFun,
        map (findGhostFunInProgram program) $ functionsCalledInExpr (ghostExpr ghostFun)
      )
    -- Finds the whole ghost function in the program given its name.
    findGhostFunInProgram :: Program -> Identifier -> GhostFunction
    findGhostFunInProgram program ghostFun =
      -- The use of 'findJust' here is safe, because in 'ASTValidator' we have
      -- already checked if the ghost functions called in expressions exist.
      findJust ((== ghostFun) . ghostName) $ ghostFunctions program

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

{- | Returns all the names of the ghost functions
 that are called within an expression.
-}
functionsCalledInExpr :: Expr -> [Identifier]
functionsCalledInExpr (FunCall ghostFun args) =
  ghostFun : (concatMap functionsCalledInExpr args)
-- In this function, there's no default case to gather all of the
-- cases that return [] because that way, if the 'Expr' type
-- grows eventually to support more operations, it will throw an
-- error of non-exhaustive pattern matching, as a reminder to pay
-- attention to those particular cases here. It would be easy to
-- forget about them with a default case, and it could lead to
-- undesired bugs :(
functionsCalledInExpr BFalse = []
functionsCalledInExpr BTrue = []
functionsCalledInExpr (IfThenElse ifExpr thenExpr elseExpr) =
  functionsCalledInExpr ifExpr
    ++ functionsCalledInExpr thenExpr
    ++ functionsCalledInExpr elseExpr
functionsCalledInExpr (BNot subExpr) =
  functionsCalledInExpr subExpr
functionsCalledInExpr (BImpl leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BAnd leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BOr leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BXor leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BEq leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BDistinct leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BLessOrEq leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BLess leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BGreaterOrEq leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (BGreater leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (IVar _) = []
functionsCalledInExpr (IInt _) = []
functionsCalledInExpr (INeg subExpr) =
  functionsCalledInExpr subExpr
functionsCalledInExpr (IMinus leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (IPlus leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (IMult leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (IDiv leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (IMod leftExpr rightExpr) =
  functionsCalledInExpr leftExpr ++ functionsCalledInExpr rightExpr
functionsCalledInExpr (IAbs subExpr) =
  functionsCalledInExpr subExpr
