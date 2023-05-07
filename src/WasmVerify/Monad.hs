module WasmVerify.Monad where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.State (StateT, evalStateT, get, gets, put)
import Control.Monad.Trans.Writer.CPS
import Data.ByteString.Builder (Builder, toLazyByteString)
import qualified Data.ByteString.Lazy as BS (putStr)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8Builder)
import qualified Data.Text.Lazy as Lazy
import Helpers.ANSI (colorInRed)
import VerifiWASM.LangTypes (Expr, IdVersion, Identifier, VersionedVar)

-- TODO: add Haddock
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
    -- | The current symbolic execution context, i.e. which WebAssembly
    -- function is being executed and which execution path is being executed
    -- (represented as a position index in the list of all execution paths).
    executionContext :: (Identifier, Int),
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
    emptyContextState = ExecState M.empty [] ("", 0) ""

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

{- | We use the dollar sign (\'$\') to separate the different
 sections of a variable. The current format is the following:
 @|current function|$|current execution path|$|variable name|$v|variable version|$@
-}
versionedVarToIdentifier :: VersionedVar -> WasmVerify Identifier
versionedVarToIdentifier (var, version) = do
  (func, path) <- gets executionContext
  return $ func <> "$" <> "path_" <> show path <> var <> "$v" <> show version

{- | Prepends a piece of SMT code to the SMT accumulator in the
 'WasmVerify' monad. This function assumes that the code provided
 is valid SMT, since arbitrary text can be inserted in the accumulator.
-}
prependToSMT :: Text -> WasmVerify ()
prependToSMT smtCode = do
  state <- get
  let smt = smtText state
  let updatedSmt = Lazy.fromStrict smtCode <> smt
  put state{smtText = updatedSmt}

{- | Appends a piece of SMT code to the SMT accumulator in the
 'WasmVerify' monad. This function assumes that the code provided
 is valid SMT, since arbitrary text can be inserted in the accumulator.
-}
appendToSMT :: Text -> WasmVerify ()
appendToSMT smtCode = do
  state <- get
  let smt = smtText state
  let updatedSmt = smt <> Lazy.fromStrict smtCode
  put state{smtText = updatedSmt}

{- | Adds a constant declaration corresponding to the versioned
 variable provided to the SMT accumulator in the 'WasmVerify' monad.
-}
addVarDeclsSMT :: [VersionedVar] -> WasmVerify ()
addVarDeclsSMT vars =
  prependToSMT $
    T.concat $
      map
        ( \var ->
            "(declare-const "
              <> T.pack (versionedVarToIdentifier var)
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

{- | Adds the final command to the SMT model,
 asking to check for satisfiability of the model.
-}
addCheckSatSMT :: WasmVerify ()
addCheckSatSMT = appendToSMT "\n(check-sat)\n"
