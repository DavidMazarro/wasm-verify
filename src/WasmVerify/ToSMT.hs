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
    bodyToSMT ghostFun = (exprToSMT Nothing . ghostExpr) ghostFun
    argWithType (identifier, _) =
      "(" <> T.pack identifier <> " " <> "Int" <> ")"

-- TODO: add Haddock
exprToSMT :: Maybe (Map Identifier IdVersion) -> Expr -> Text
exprToSMT varMap (FunCall name args) =
  "("
    <> foldl (\x y -> x <> " " <> y) (T.pack name) (map (exprToSMT varMap) args)
    <> ")"
exprToSMT varMap (IfThenElse condExpr ifExpr elseExpr) =
  "(ite "
    <> exprToSMT varMap condExpr
    <> " "
    <> exprToSMT varMap ifExpr
    <> " "
    <> exprToSMT varMap elseExpr
    <> ")"
exprToSMT _ BFalse = "false"
exprToSMT _ BTrue = "true"
exprToSMT varMap (BNot expr) = unaryToSMT varMap "not" expr
exprToSMT varMap (BImpl leftExpr rightExpr) = binaryToSMT varMap "=>" leftExpr rightExpr
exprToSMT varMap (BAnd leftExpr rightExpr) = binaryToSMT varMap "and" leftExpr rightExpr
exprToSMT varMap (BOr leftExpr rightExpr) = binaryToSMT varMap "or" leftExpr rightExpr
exprToSMT varMap (BXor leftExpr rightExpr) = binaryToSMT varMap "xor" leftExpr rightExpr
exprToSMT varMap (BEq leftExpr rightExpr) = binaryToSMT varMap "=" leftExpr rightExpr
exprToSMT varMap (BDistinct leftExpr rightExpr) = binaryToSMT varMap "distinct" leftExpr rightExpr
exprToSMT varMap (BLessOrEq leftExpr rightExpr) = binaryToSMT varMap "<=" leftExpr rightExpr
exprToSMT varMap (BLess leftExpr rightExpr) = binaryToSMT varMap "<" leftExpr rightExpr
exprToSMT varMap (BGreaterOrEq leftExpr rightExpr) = binaryToSMT varMap ">=" leftExpr rightExpr
exprToSMT varMap (BGreater leftExpr rightExpr) = binaryToSMT varMap ">" leftExpr rightExpr
exprToSMT varMap (IVar identifier) =
  maybe (T.pack identifier) (versionedVarToText . lookupVarVersion identifier) varMap
exprToSMT _ (IInt n) = T.pack $ show n
exprToSMT varMap (INeg expr) = unaryToSMT varMap "-" expr
exprToSMT varMap (IMinus leftExpr rightExpr) = binaryToSMT varMap "-" leftExpr rightExpr
exprToSMT varMap (IPlus leftExpr rightExpr) = binaryToSMT varMap "+" leftExpr rightExpr
exprToSMT varMap (IMult leftExpr rightExpr) = binaryToSMT varMap "*" leftExpr rightExpr
exprToSMT varMap (IDiv leftExpr rightExpr) = binaryToSMT varMap "div" leftExpr rightExpr
exprToSMT varMap (IMod leftExpr rightExpr) = binaryToSMT varMap "mod" leftExpr rightExpr
exprToSMT varMap (IAbs expr) = unaryToSMT varMap "abs" expr

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

{- | We use the dollar sign (\'$\') to keep track
 of the different versions that get created of a variable
 during a symbolic execution of the WebAssembly program.
-}
versionedVarToText :: VersionedVar -> Text
versionedVarToText (var, version) =
  T.pack var <> "$" <> (T.pack . show $ version)

lookupVarVersion :: Identifier -> Map Identifier IdVersion -> VersionedVar
lookupVarVersion identifier varMap =
  -- The use of 'Map.!' is safe here because we have populated
  -- the map with starting versions for all local variables in
  -- 'executeFunction'.
  (identifier, varMap Map.! identifier)

-- TODO: add Haddock
unaryToSMT :: Maybe (Map Identifier IdVersion) -> Text -> Expr -> Text
unaryToSMT varMap operator expr =
  "(" <> operator <> " " <> exprToSMT varMap expr <> ")"

-- TODO: add Haddock
binaryToSMT :: Maybe (Map Identifier IdVersion) -> Text -> Expr -> Expr -> Text
binaryToSMT varMap operator leftExpr rightExpr =
  "(" <> operator <> " " <> exprToSMT varMap leftExpr <> " " <> exprToSMT varMap rightExpr <> ")"

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
