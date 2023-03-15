{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module VerifiWASM.LangTypes where

import Data.Map

{- | Programs are comprised of a list of functions
 as well as a list of ghost functions. Programs
 /can/ be empty, i.e. have no functions of either kind.
-}
data Program = Program
  { functions :: [Function],
    ghostFunctions :: [GhostFunction]
  }
  deriving (Show)

{- | These reflect the behavior of the target
 WASM functions via verification conditions
 that need to hold during the verification process.
-}
data Function = Function
  { funcName :: Identifier,
    funcArgs :: [TypedIdentifier],
    funcReturns :: [TypedIdentifier],
    funcSpec :: Spec
  }
  deriving (Show)

data GhostFunction = GhostFunction
  { ghostName :: Identifier,
    ghostArgs :: [TypedIdentifier],
    ghostTermination :: Termination,
    ghostRequires :: Requires,
    ghostExpr :: Expr,
    ghostReturnType :: ExprType
  }
  deriving (Show)

newtype Termination = Decreases [Identifier]
  deriving (Show)

type TypedIdentifier = (Identifier, IdType)

data Spec = Spec
  { locals :: [Local],
    -- Order between sets of requires, ensures, and asserts doesn't matter
    -- But within a given family, order DOES matter
    requires :: Requires,
    ensures :: Ensures,
    asserts :: [Assert]
  }
  deriving (Show)

newtype Local = Local {localVars :: [TypedIdentifier]}
  deriving (Show)

newtype Requires = Requires Expr
  deriving (Show)

newtype Ensures = Ensures Expr
  deriving (Show)

newtype Assert = Assert (Int, Expr)
  deriving (Show)

data Declaration
  = DeclAssert Assert
  | DeclEnsures Ensures
  | DeclRequires Requires
  | DeclLocals Local
  deriving (Show)

{- | This type encodes all the possible expressions for VerifiWASM.
 essentially, an expression can be:

 * A variable.
 * A ghost function call (arguments must be fully saturated, no support for partial application).
 * An @if \<boolean expr\> then \<expr\> else \<expr\>@.
 * A boolean value, i.e. @true@, @false@.
 * An integer value.
 * An expression using the functions provided by the [Core theory](https://smt  lib.cs.uiowa.edu/theories-Core.shtml) from SMTLIB2.
 * An expression using the functions provided by the [Ints theory](https://smtlib.cs.uiowa.edu/theories-Ints.shtml) from SMTLIB2.

 Expressions are untyped in this ADT, but will be typed
 (just with the boolean and integer types) and checked for soundness
 after the parsing step in the 'ASTValidator' module.

 The data constructors starting with a \'@B@\' encode boolean expressions,
 the ones starting with a \'@I@\' encode integer expressions.
 The two special constructors with regards to their type are:

 * @FunCall@: Its type is the same as the expression that the called ghost function returns,
    can be an boolean or an integer.
 * @IfThenElse@: Its type is the same as its @then@ case, which must also be
    the same as its @else@ case when checked for type soundness.
-}
data Expr
  = FunCall
      Identifier
      -- ^ The name of the function
      [Expr]
      -- ^ The arguments passed to the function
  | -- | The if-then-else is called @ite@ in the [Core theory](https://smtlib.cs.uiowa.edu/theories-Core.shtml) from SMTLIB2
    IfThenElse
      Expr
      -- ^ The boolean condition to check against
      Expr
      -- ^ The @then@ case, if the condition is true
      Expr
      -- ^ The @else@ case, if the condition is false
  | -- | The boolean @false@ value
    BFalse
  | -- | The boolean @true@ value
    BTrue
  | BNot Expr
  | BImpl Expr Expr
  | BAnd Expr Expr
  | BOr Expr Expr
  | BXor Expr Expr
  | BEq Expr Expr
  | BDistinct Expr Expr
  | BLessOrEq Expr Expr
  | BLess Expr Expr
  | BGreaterOrEq Expr Expr
  | BGreater Expr Expr
  | -- | An integer variable, whose type is derived from the arguments
    IVar Identifier
  | -- | A wrapper over Haskell 'Int' values to construct integers
    IInt Int
  | INeg Expr
  | IMinus Expr Expr
  | IPlus Expr Expr
  | IMult Expr Expr
  | IDiv Expr Expr
  | IMod Expr Expr
  | IAbs Expr
  deriving (Show)

data ExprType = ExprBool | ExprInt
  deriving (Eq, Show)

data IdType = I32 | I64
  deriving (Show)

type Identifier = String

{- | A map that stores all of the type scopes (see 'VarTypes')
 associated with the functions and ghost functions in a VerifiWASM file.
 Used in the analysis performed after the parsing for validating the specification.
 Since functions and ghost functions share a global namespace, they can be
 given a unique key which is its 'Identifier' without conflicts.
-}
type FunTypes = Map Identifier VarTypes

{- | A map that stores the returned types of ghost functions
 in a VerifiWASM file. Used in the analysis performed
 after the parsing for validating the specification.
-}
type GhostFunReturnTypes = Map Identifier ExprType

{- | A map that stores the type of the identifiers found
 in the scope of a function or ghost function. Used in the analysis
 performed after the parsing for validating the specification.
-}
type VarTypes = Map Identifier IdType
