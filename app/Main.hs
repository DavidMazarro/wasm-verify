module Main
  ( main
  ) where

import           Data.Version                   ( showVersion )
import           Options.Applicative
import           Path
import           Paths_wasm_verify              ( version )
import           WasmVerify.ModuleLoader        ( loadModuleFromFile )

----------------------------------------------------------------------------

parserInfo :: ParserInfo String
parserInfo = info
  (helper <*> versionOption <*> filepathOption)
  (  fullDesc
  <> progDesc "A proof-of-concept formal verification tool for WASM"
  <> header
       "wasm-verify - A proof-of-concept formal verification tool for WASM"
  )
 where
  versionOption :: Parser (a -> a)
  versionOption = infoOption
    ("wasm-verify: " <> showVersion version)
    (long "version" <> short 'v' <> help "Show version information")
  filepathOption :: Parser String
  filepathOption = strOption (long "filepath" <> short 'f')

----------------------------------------------------------------------------
-- Main

main :: IO ()
main = do
  filepath   <- parseAbsFile =<< execParser parserInfo
  wasmModule <- loadModuleFromFile filepath
  print wasmModule
