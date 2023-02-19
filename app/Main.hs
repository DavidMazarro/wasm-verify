module Main (
  main,
) where

import Control.Exception (
  ErrorCall (ErrorCall),
  throwIO,
 )
import Control.Monad (when)
import Data.Version (showVersion)
import GHC.IO.Exception (ExitCode (ExitSuccess))

-- import           GHC.IO.Exception
import qualified Data.Text.IO as T
import Helpers.ANSI (colorInRed)
import Options.Applicative
import Options.Applicative.Extra (helperWith)
import Path
import Paths_wasm_verify (version)
import System.Process (readProcessWithExitCode)
import Text.Pretty.Simple (pPrint)
import VerifiWASM.Parser (parseVerifiWASMFile)
import WasmVerify.ModuleLoader (loadModuleFromFile)

----------------------------------------------------------------------------

data Options = Options
  { file :: FilePath,
    debugWasmADT :: Bool
  }

parserInfo :: ParserInfo Options
parserInfo =
  info
    (helpParser <*> versionParser <*> optsParser)
    ( fullDesc
        <> progDesc "A proof-of-concept formal verification tool for WASM"
        <> header
          "wasm-verify - A proof-of-concept formal verification tool for WASM"
    )
 where
  helpParser :: Parser (a -> a)
  helpParser =
    helperWith
      ( long "help" <> short 'h' <> help "Displays help for the different commands"
      )
  versionParser :: Parser (a -> a)
  versionParser =
    infoOption
      ("wasm-verify: " <> showVersion version)
      (long "version" <> short 'v' <> help "Show version information")
  optsParser :: Parser Options
  optsParser =
    Options
      <$> strOption
        (long "filepath" <> short 'f' <> help "WASM binary file to print")
      <*> switch
        ( long "debug-wasm-adt"
            <> help
              "Outputs the Haskell ADT representation of the WASM module"
        )

----------------------------------------------------------------------------
-- Main

main :: IO ()
main = do
  Options{..} <- execParser parserInfo
  filepath <- parseAbsFile file
  fileExt <- fileExtension filepath
  case fileExt of
    ".smt2" -> do
      runZ3WithFile filepath
    ".verifiwasm" -> do
      res <- parseVerifiWASMFile filepath
      case res of
        (Just assert) -> pPrint assert
        Nothing -> return ()
    ".wasm" -> do
      wasmModule <- loadModuleFromFile filepath
      when debugWasmADT $ pPrint wasmModule
    _ -> do
      fail "The file extension must be .wasm, .smt2 or .verifiwasm"

{- | Runs the Z3 solver with the contents of the provided SMTLIB2 file
 and outputs the results in the console.
-}
runZ3WithFile :: Path Abs File -> IO ()
runZ3WithFile filepath = do
  (exitCode, stdout, stderr) <-
    readProcessWithExitCode
      "z3"
      ["-smt2", fromAbsFile filepath]
      ""

  when (exitCode /= ExitSuccess) $ T.putStrLn . colorInRed $ "Z3 finished with errors:\n"
  putStrLn stdout

  -- Throw a Haskell error if the exit code is non-zero
  -- and log the stderr of Z3
  when (exitCode /= ExitSuccess) $ do
    T.putStrLn . colorInRed $ "Z3 finished with the following errors (obtained from stderr):"
    putStrLn stderr
    T.putStrLn "──────────────────────────────────────"
    throwIO $ ErrorCall "command failed"
