module WasmVerify where

import Control.Exception (ErrorCall (ErrorCall), throwIO)
import Control.Exception.Safe (throwString)
import Control.Monad (forM, when)
import qualified Data.ByteString as BS (readFile)
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as Lazy
import GHC.IO.Exception (ExitCode (ExitSuccess))
import Helpers.ANSI (colorInRed, failureText, successText)
import qualified Language.Wasm as Wasm
import Path
import System.Process (readProcessWithExitCode)
import VerifiWASM.LangTypes (Identifier)
import qualified VerifiWASM.LangTypes as VerifiWASM
import WasmVerify.Execution (executeProgram)
import WasmVerify.Monad (runWasmVerify)

----------------------------------------------------------------------------

{- | Performs the verification of a WebAssembly module against the provided
 VerifiWASM specification, outputting the results of verification in the standard output.
-}
verifyModule ::
  -- | The VerifiWASM specification to verify against.
  VerifiWASM.Program ->
  -- | The WebAssembly module containing the functions to be verified.
  Wasm.ValidModule ->
  IO ()
verifyModule program wasmModule = do
  smtFunctionsMap <- runWasmVerify $ executeProgram program wasmModule
  verificationResults <- forM (Map.assocs smtFunctionsMap) verifyFunction
  T.putStrLn "──────────────────────────────────────"
  if any (== False) verificationResults
    then
      T.putStrLn $
        "Verification failed! Of all "
          <> (T.pack . show) (length verificationResults)
          <> " functions, there were "
          <> (T.pack . show) (length $ filter (== False) verificationResults)
          <> " that didn't match their specification.\n"
          <> "These are some possible causes:\n"
          <> "  - The specification is correct and complete: this means the function"
          <> " is incorrect, and should be fixed.\n"
          <> "  - The specification is complete but incorrect: the function could be"
          <> " correct,\n    but it didn't match the specification because the specification"
          <> " is wrong, and should be fixed.\n"
          <> "  - The specification is incomplete: maybe you are calling a WebAssembly"
          <> " function that doesn't have a spec,\n    or maybe you are using a recursive"
          <> " ghost function that doesn't terminate in some part in the spec."
    else
      T.putStrLn $
        "Verification successful! All "
          <> (T.pack . show) (length verificationResults)
          <> " functions match their specifications."

{- | Performs the verification of the provided WebAssembly function.
 The argument is a pair with the name of the WebAssembly function and the
 SMT modules that check that function against its specification.
 This function calls the Z3 SMT solver to run the SMT modules.
-}
verifyFunction :: (Identifier, [Lazy.Text]) -> IO Bool
verifyFunction (funcName, pathsSMT) = do
  resultsSMT <- forM pathsSMT runZ3
  if any (== "sat") $ concat resultsSMT
    then do
      T.putStrLn . failureText $ T.pack funcName <> " does not match its specification."
      return False
    else do
      T.putStrLn . successText $ T.pack funcName <> " matches its specification."
      return True

{- | Runs the Z3 solver with the SMT module provided and returns the results
 as a list of strings that can be "@sat@" or "@unsat@".
-}
runZ3 :: Lazy.Text -> IO [String]
runZ3 smtCode = do
  (exitCode, stdout, stderr) <-
    readProcessWithExitCode
      "z3"
      ["-smt2", "-in"]
      (Lazy.unpack smtCode)

  -- Throw a Haskell error if the exit code is non-zero
  -- and log the stderr of Z3.
  when (exitCode /= ExitSuccess) $ do
    T.putStrLn . colorInRed $ "Z3 finished with the following logs:"
    putStrLn stdout
    putStrLn stderr
    T.putStrLn "──────────────────────────────────────"
    throwIO $ ErrorCall "command failed"

  return $ words stdout

{- | Loads a binary WebAssembly module provided a file path.
 In case there's an error while reading the file,
 or a 'Wasm.ValidationError' comes up when validating the WASM module,
 a t'Control.Exception.Safe.StringException' is thrown.
-}
loadModuleFromFile :: Path Abs File -> IO Wasm.ValidModule
loadModuleFromFile filepath = do
  fileContents <- BS.readFile $ fromAbsFile filepath
  case Wasm.decode fileContents of
    Left str -> throwString str
    Right wasm -> case Wasm.validate wasm of
      Left validationErr -> throwString $ show validationErr
      Right validWasm -> return validWasm
