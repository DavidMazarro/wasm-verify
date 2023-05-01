module WasmVerify.Monad where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.State (StateT, evalStateT, get, put)
import Control.Monad.Trans.Writer.CPS
import Data.ByteString.Builder (Builder, toLazyByteString)
import qualified Data.ByteString.Lazy as BS (putStr)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8Builder)
import qualified Data.Text.Lazy as LT
import Helpers.ANSI (colorInRed)
import VerifiWASM.VerifiWASM (Expr)

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
    symbolicStack :: [Expr],
    -- | A text accumulator that keeps adding SMT. After performing
    -- all of the symbolic execution, this value is our SMTLIB2 program
    -- that will be run and output the result of the verification.
    smtText :: LT.Text
  }

type Identifier = String

type VersionedVar = (Identifier, IdVersion)

type IdVersion = Int

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
    emptyContextState = ExecState M.empty [] ""

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

{- | Adds an assert command to the SMT accumulator in the
 'WasmVerify' monad containing the text provided (must be valid SMT).
-}
addAssertSMT :: Text -> WasmVerify ()
addAssertSMT assertText = do
  state <- get
  let smt = smtText state
  let assert = "(assert (" <> assertText <> "))\n"
  let updatedSmt = smt <> LT.fromStrict assert
  put state{smtText = updatedSmt}
