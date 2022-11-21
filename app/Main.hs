module Main
  ( main
  ) where

import           Data.Version                   ( showVersion )
import           Options.Applicative
import           Path
import           Paths_wasm_verify              ( version )
import           Text.Pretty.Simple             ( pPrint )
import           WasmVerify.ModuleLoader        ( loadModuleFromFile )
import Options.Applicative.Extra (helperWith)

----------------------------------------------------------------------------

parserInfo :: ParserInfo String
parserInfo = info
  (helpOption <*> versionOption <*> filepathOption)
  (  fullDesc
  <> progDesc "A proof-of-concept formal verification tool for WASM"
  <> header
       "wasm-verify - A proof-of-concept formal verification tool for WASM"
  )
 where
  helpOption :: Parser (a -> a)
  helpOption = helperWith
    (long "help" <> short 'h' <> help "Displays help for the different commands")
  versionOption :: Parser (a -> a)
  versionOption = infoOption
    ("wasm-verify: " <> showVersion version)
    (long "version" <> short 'v' <> help "Show version information")
  filepathOption :: Parser String
  filepathOption =
    strOption (long "filepath" <> short 'f' <> help "WASM binary file to print")

----------------------------------------------------------------------------
-- Main

main :: IO ()
main = do
  filepath   <- parseAbsFile =<< execParser parserInfo
  wasmModule <- loadModuleFromFile filepath
  pPrint wasmModule
