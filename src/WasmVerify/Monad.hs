module WasmVerify.Monad where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.State (StateT, evalStateT, gets, modify)
import Control.Monad.Trans.Writer.CPS
import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import Data.ByteString.Builder (Builder, toLazyByteString)
import qualified Data.ByteString.Lazy as BS (putStr)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8Builder)
import qualified Data.Text.Lazy as Lazy
import Helpers.ANSI (colorInRed)
import VerifiWASM.LangTypes (Expr (..), IdVersion, Identifier, Program, VersionedVar)
import WasmVerify.CFG.Types (Annotation (..), NodeLabel)
import WasmVerify.ToSMT (exprToSMT, ghostFunctionsToSMT)

type WasmVerify a = ExceptT Failure (StateT ExecState (Writer Builder)) a

{- | The type that functions as a state when performing the symbolic
 execution of the WebAssembly module.
-}
data ExecState = ExecState
  { -- | A map that stores the last used version of an identifier.
    -- Every time there's an assignment to a variable in WebAssembly,
    -- instead of replacing the variable we already have, we add a constraint
    -- in STM that the old version is equal to the new version, and
    -- use the new version for the rest of the execution afterwards.
    identifierMap :: Map Identifier IdVersion,
    -- | The simulated stack used when performing the symbolic execution
    -- of the WebAssembly instructions.
    symbolicStack :: [StackValue],
    -- | The current node symbolic execution context, i.e. which node is currently
    -- being executed and which is the node that will be executed next (if there's one),
    -- in the execution path that is currently being executed.
    nodeExecutionContext :: (NodeLabel, Maybe NodeLabel),
    -- | A 'Bimap' with the names of the functions in the WebAssembly
    -- module and their corresponding indices in the list of 'Wasm.functions'.
    -- Used during symbolic execution to lookup the index of WebAssembly functions
    -- given their name from the 'VerifiWASM' spec and viceversa.
    wasmFunctionIndicesBimap :: Bimap Identifier Int,
    -- | A text accumulator that keeps adding SMT. After performing
    -- all of the symbolic execution, this value is our SMTLIB2 program
    -- that will be run and output the result of the verification.
    smtText :: Lazy.Text
  }

data StackValue = ValueVar Identifier | ValueConst Const
type Const = Integer

-- | The error type for actions within 'WasmVerify'.
newtype Failure = Failure {unFailure :: T.Text}
  deriving stock (Show)
  deriving anyclass (Exception)

-- | Runner function for the 'WasmVerify' monad.
runWasmVerify :: WasmVerify a -> IO a
runWasmVerify action = do
  let (res, logs) = runWriter $ evalStateT (runExceptT action) emptyContextState
  BS.putStr $ toLazyByteString logs
  case res of
    Right x -> pure x
    Left err -> error $ show $ unFailure err
  where
    emptyContextState = ExecState M.empty [] (0, Nothing) Bimap.empty ""

-- | Provides an easy action for logging within 'WasmVerify' contexts.
logError :: Failure -> WasmVerify ()
logError err =
  lift . lift . tell . encodeUtf8Builder $
    colorInRed "wasm-verify ERROR:" <> " " <> unFailure err <> "\n"

{- | Provides an easy action for throwing a 'Failure' as an 'Exception'
 within 'WasmVerify' contexts, with some extra formatting.
-}
failWithError :: Failure -> WasmVerify ()
failWithError err = logError err >> throwError err

-- * Helper functions

{- | We use the dollar sign (\'$\') to separate the identifier
 from the version. The current format is the following:
 @|identifier|$v|variable version|@.
-}
versionedVarToIdentifier :: VersionedVar -> Identifier
versionedVarToIdentifier (var, version) = var <> "$v" <> show version

{- | Turns a value in the stack of the symbolic execution
 into an expression: if there's a variable, into an 'IVar' expression
 and if there's a constant number, into a  'IInt' expression.
-}
stackValueToExpr :: StackValue -> Expr
stackValueToExpr (ValueVar identifier) = IVar identifier
stackValueToExpr (ValueConst n) = IInt n

{- | Cleans the current SMT accumulator to allow for a new execution
 path or function as a different SMT program.
-}
cleanSMT :: WasmVerify ()
cleanSMT = modify (\state -> state{smtText = ""})

cleanIdentifierMap :: WasmVerify ()
cleanIdentifierMap = modify (\state -> state{identifierMap = Map.empty})

{- | Prepends a piece of SMT code to the SMT accumulator in the
 'WasmVerify' monad. This function assumes that the code provided
 is valid SMT, since arbitrary text can be inserted in the accumulator.
-}
prependToSMT :: Text -> WasmVerify ()
prependToSMT smtCode =
  modify (\state -> state{smtText = Lazy.fromStrict smtCode <> smtText state})

{- | Appends a piece of SMT code to the SMT accumulator in the
 'WasmVerify' monad. This function assumes that the code provided
 is valid SMT, since arbitrary text can be inserted in the accumulator.
-}
appendToSMT :: Text -> WasmVerify ()
appendToSMT smtCode =
  modify (\state -> state{smtText = smtText state <> Lazy.fromStrict smtCode})

{- | Prepends ghost function definitions (in the form of @define-fun@ and/or
 their recursive variants) to the SMT accumulator in the 'WasmVerify' monad.
-}
addGhostFunctionsToSMT :: Program -> WasmVerify ()
addGhostFunctionsToSMT = appendToSMT . ghostFunctionsToSMT

{- | Appends an assertion corresponding to the comparison specified
 by the provided 'Annotation' to the value at the top of the stack
 (it is left in the stack unchanged) to the SMT accumulator in the 'WasmVerify' monad.
-}
addAnnotationToSMT :: Annotation -> WasmVerify ()
addAnnotationToSMT annotation = do
  topValue <- gets (head . symbolicStack)
  case annotation of
    Empty -> return ()
    Eq n -> (addAssertSMT . exprToSMT) $ BEq (stackValueToExpr topValue) (IInt $ toInteger n)
    NotEq n -> (addAssertSMT . exprToSMT) $ BDistinct (stackValueToExpr topValue) (IInt $ toInteger n)
    GreaterEq n ->
      (addAssertSMT . exprToSMT) $
        BOr
          ( BGreaterOrEq
              (stackValueToExpr topValue)
              (IInt $ toInteger n)
          )
          (BLess (stackValueToExpr topValue) (IInt 0))

{- | Prepends constant declarations corresponding to the versioned
 variables provided to the SMT accumulator in the 'WasmVerify' monad.
-}
addVarDeclsSMT :: [Identifier] -> WasmVerify ()
addVarDeclsSMT vars =
  prependToSMT $
    T.concat $
      map
        ( \var ->
            "(declare-const "
              <> T.pack var
              <> " Int)\n"
        )
        vars

-- | Adds an assert command to the SMT accumulator in the 'WasmVerify' monad.
addAssertSMT :: Text -> WasmVerify ()
addAssertSMT assertText =
  appendToSMT $ "(assert " <> assertText <> ")\n"

-- | Adds the command to select SMTLIB2 theory at the beginning of the SMT accumulator.
addSetLogicSMT :: Text -> WasmVerify ()
addSetLogicSMT logic =
  prependToSMT $ "(set-logic " <> logic <> ")\n\n"
