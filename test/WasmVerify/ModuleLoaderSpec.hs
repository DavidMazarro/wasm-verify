{-# LANGUAGE TemplateHaskell #-}

module WasmVerify.ModuleLoaderSpec
  ( spec
  ) where

import qualified Data.ByteString               as BS
import           Data.Either                    ( fromRight )
import qualified Language.Wasm                 as Wasm
import qualified Language.Wasm.Structure       as Wasm
import qualified Language.Wasm.Validate        as Wasm
import           Path
import           System.Directory
import           Test.Hspec
import           WasmVerify.ModuleLoader


spec :: Spec
spec = do
  describe "loadModuleFromFile" $ do
    context "given an existing and valid WASM binary file" $
      it "loads the module" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let examplePath = projectPath </> $(mkRelFile "examples/dup.wasm")
        example <- BS.readFile $ fromAbsFile examplePath
        let decodedModule = fromRight Wasm.emptyModule $ Wasm.decode example
        let wasmModule = Right <$> loadModuleFromFile examplePath
        wasmModule `shouldReturn` Wasm.validate decodedModule
      
    context "given a non-existing file" $
      it "throws an exception" $ do
        pending
