module VerifiWASM.VerifiWASM (
  module VerifiWASM.VerifiWASM,
  module VerifiWASM.LangTypes,
) where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.Trans.Writer.CPS
import Data.ByteString.Builder (Builder, toLazyByteString)
import qualified Data.ByteString.Lazy as BS (putStr)
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Encoding (encodeUtf8Builder)
import VerifiWASM.LangTypes

{- | The base monad used for all actions and checks performed
 over the VerifiWASM AST after the parsing step. Errors
 are logged using the CPS-style 'WriterT' until an unrecoverable
 error is found, in which case a 'Failure' exception is thrown
 and the VerifiWASM program is considered invalid, signaling
 the user to fix the present errors before trying again.
-}
type VerifiWASM a = ExceptT Failure (Writer Builder) a

{- | The error type for actions within 'VerifiWASM'.
 It's both used for silent logging and also derives 'Exception' for
 being thrown when an unrecoverable error happens.
-}
newtype Failure = Failure {unFailure :: Text}
  deriving stock (Show)
  deriving anyclass (Exception)

runVerifiWASM :: VerifiWASM a -> IO a
runVerifiWASM action = do
  let (res, logs) = runWriter (runExceptT action)
  BS.putStr $ toLazyByteString logs
  case res of
    Right x -> pure x
    Left err -> error $ show $ unFailure err

-- | Provides an easy action for logging within 'VerifiWASM' contexts.
logError :: Failure -> VerifiWASM ()
logError err = lift . tell . encodeUtf8Builder $ colorInRed "ERROR:" <> " " <> unFailure err <> "\n"
  where colorInRed = \s -> "\ESC[31m" <> s <> "\ESC[97m"

{- | Provides an easy action for throwing a 'Failure' as an 'Exception'
 within 'VerifiWASM' contexts.
-}
failWithError :: Failure -> VerifiWASM ()
failWithError err = logError err >> throwError err
