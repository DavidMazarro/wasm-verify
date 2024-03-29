module Main (
  main,
) where

import Control.Monad (void, when)
import Data.Version (showVersion)
import qualified Language.Wasm as Wasm
import qualified Language.Wasm.Structure as Wasm
import Options.Applicative
import Options.Applicative.Extra (helperWith)
import Path
import Paths_wasm_verify (version)
import System.Directory (makeAbsolute)
import Text.Pretty.Simple (pPrint)
import VerifiWASM.Parser (parseVerifiWASMFile)
import VerifiWASM.Validation (validate)
import VerifiWASM.VerifiWASM (runVerifiWASM)
import WasmVerify
import WasmVerify.CFG (functionToCFG)
import WasmVerify.Execution (executeProgram)
import WasmVerify.Monad (runWasmVerify)
import WasmVerify.ToSMT (ghostFunctionsToSMT)

----------------------------------------------------------------------------

data Options = Options
  { file :: FilePath,
    spec :: FilePath,
    debugWasmADT :: Bool,
    debugSpecADT :: Bool,
    debugSMT :: Bool,
    debugCFG :: Bool
  }

parserInfo :: ParserInfo Options
parserInfo =
  info
    (helpParser <*> versionParser <*> optsParser)
    ( fullDesc
        <> progDesc "A proof-of-concept formal verification tool for WebAssembly."
        <> header
          "wasm-verify - A proof-of-concept formal verification tool for WebAssembly."
    )
  where
    helpParser :: Parser (a -> a)
    helpParser =
      helperWith
        ( long "help" <> short 'h' <> help "Displays help for the different commands."
        )
    versionParser =
      infoOption
        ("wasm-verify: " <> showVersion version)
        (long "version" <> short 'v' <> help "Show version information.")
    optsParser :: Parser Options
    optsParser =
      Options
        <$> strArgument
          (metavar "FILEPATH" <> help "Filepath to the WASM bytecode file.")
        <*> strOption
          (long "spec" <> short 's' <> help "Filepath to the VerifiWASM specification file.")
        <*> switch
          ( long "debug-wasm-adt"
              <> help
                "Outputs the Haskell ADT representation of the WASM module."
          )
        <*> switch
          ( long "debug-spec-adt"
              <> help
                "Outputs the Haskell ADT representation of the VerifiWASM specification."
          )
        <*> switch
          ( long "debug-smt"
              <> help
                "Outputs the SMT modules, resulting from the symbolic execution, that verify the WebAssembly module."
          )
        <*> switch
          ( long "debug-cfg"
              <> help
                "Outputs the CFGs generated from the functions in the WebAssembly module."
          )

----------------------------------------------------------------------------
-- Main

main :: IO ()
main = do
  Options{..} <- execParser parserInfo
  filepath <- parseAbsFile =<< makeAbsolute file
  specFilepath <- parseAbsFile =<< makeAbsolute spec
  fileExt <- fileExtension filepath
  specFileExt <- fileExtension specFilepath

  case fileExt of
    ".wasm" -> do
      case specFileExt of
        ".verifiwasm" -> do
          wasmModule <- loadModuleFromFile filepath
          when debugWasmADT $ pPrint wasmModule

          mProgram <- parseVerifiWASMFile specFilepath
          case mProgram of
            (Just program) -> do
              runVerifiWASM $ validate program wasmModule
              when debugSpecADT $ pPrint program
              when debugSpecADT $ pPrint $ ghostFunctionsToSMT program
              when debugCFG $ mapM_ (pPrint . functionToCFG) (Wasm.functions $ Wasm.getModule wasmModule)
              when debugSMT $ pPrint =<< runWasmVerify (executeProgram program wasmModule)
              void $ verifyModule program wasmModule
            -- No error logging in the 'Nothing' case since 'parseVerifiWASMFile'
            -- runs the VerifiWASM monad which already performs error logging.
            Nothing -> return ()
        _ -> do
          fail "The specification file extension must be .verifiwasm"
    _ -> do
      fail "The WebAssembly module file extension must be .wasm"
