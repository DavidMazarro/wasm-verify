module WasmVerify where

import Control.Exception.Safe (throwString)
import qualified Data.ByteString as BS (readFile)
import qualified Language.Wasm as Wasm
import qualified Language.Wasm.Structure as Wasm
import Path
import WasmVerify.CFGs

----------------------------------------------------------------------------

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

{- | Transforms the functions in a WebAssembly module into
 the Control Flow Graphs that model their execution flow.
-}
wasmModuleToCFG :: Wasm.ValidModule -> [CFG]
wasmModuleToCFG = map functionToCFG . Wasm.functions . Wasm.getModule
