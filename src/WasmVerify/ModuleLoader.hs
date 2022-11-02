module WasmVerify.ModuleLoader
  ( loadModuleFromFile
  ) where

import           Control.Exception.Safe         ( throwString )
import qualified Data.ByteString               as BS
                                                ( readFile )
import qualified Language.Wasm                 as Wasm
import           Path

loadModuleFromFile :: Path Abs File -> IO Wasm.ValidModule
loadModuleFromFile filepath = do
  fileContents <- BS.readFile $ fromAbsFile filepath
  case Wasm.decode fileContents of
    Left  str  -> throwString str
    Right wasm -> case Wasm.validate wasm of
      Left  validationErr -> throwString $ show validationErr
      Right validWasm     -> return validWasm
