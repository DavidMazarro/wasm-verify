module VerifiWASM.VerifiWASM (
  module VerifiWASM.VerifiWASM,
  module VerifiWASM.LangTypes,
) where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.State (StateT, evalStateT)
import Control.Monad.Trans.Writer.CPS
import Data.ByteString.Builder (Builder, toLazyByteString)
import qualified Data.ByteString.Lazy as BS (putStr)
import qualified Data.Map as M
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8Builder)
import Helpers.ANSI (colorInRed)
import System.Exit (exitFailure)
import VerifiWASM.LangTypes

{- | The base monad used for all actions and checks performed
 over the VerifiWASM AST after the parsing step. Errors
 are logged using the CPS-style 'WriterT' until an unrecoverable
 error is found, in which case a 'Failure' exception is thrown
 and the VerifiWASM program is considered invalid, signaling
 the user to fix the present errors before trying again.
 The 'StateT' is used to store the types of the variables
 (functions, ghost functions and the variables inside them)
 after parsing, during the AST validation step.
-}
type VerifiWASM a = ExceptT Failure (StateT ContextState (Writer Builder)) a

-- | The type that functions as a state in the 'VerifiWASM' monad.
data ContextState = ContextState
  { -- | Contains the types of all variables in functions/ghost functions
    -- in a VerifiWASM file. Once initialised at the
    -- 'VerifiWASM.Validation.validate' step, it doesn't change in the
    -- rest of the execution of the 'VerifiWASM' monad.
    globalTypes :: FunTypes,
    -- | Serves as a local scope, containing the tuple of the name and the types
    -- of the current function/ghost function that is being validated. It's used to
    -- keep track of the parent function/ghost function when performing
    -- the validation of expressions.
    localTypes :: (Identifier, VarTypes),
    -- | Contains the return types of all ghost functions in a VerifiWASM file.
    -- Once initialised at the 'VerifiWASM.Validation.validate' step,
    -- it doesn't change in the rest of the execution of the 'VerifiWASM' monad.
    ghostFunReturnTypes :: GhostFunReturnTypes
  }

{- | The error type for actions within 'VerifiWASM'.
 It's both used for silent logging and also derives 'Exception' for
 being thrown when an unrecoverable error happens.
-}
newtype Failure = Failure {unFailure :: Text}
  deriving stock (Show)
  deriving anyclass (Exception)

-- | Runner function for the 'VerifiWASM' monad.
runVerifiWASM :: VerifiWASM a -> IO a
runVerifiWASM action = do
  let (res, logs) = runWriter $ evalStateT (runExceptT action) emptyContextState
  BS.putStr $ toLazyByteString logs
  case res of
    Right x -> pure x
    Left _ -> exitFailure
  where
    emptyContextState = ContextState M.empty ("", M.empty) M.empty

-- | Provides an easy action for logging within 'VerifiWASM' contexts.
logError :: Failure -> VerifiWASM ()
logError err =
  lift . lift . tell . encodeUtf8Builder $
    colorInRed "VerifiWASM ERROR:" <> " " <> unFailure err <> "\n"

{- | Provides an easy action for throwing a 'Failure' as an 'Exception'
 within 'VerifiWASM' contexts.
-}
failWithError :: Failure -> VerifiWASM ()
failWithError err = logError err >> throwError err
