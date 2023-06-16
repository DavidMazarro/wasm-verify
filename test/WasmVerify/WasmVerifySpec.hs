{-# LANGUAGE TemplateHaskell #-}

module WasmVerify.WasmVerifySpec (
  spec,
) where

import qualified Data.ByteString as BS
import Data.Either (fromRight)
import qualified Language.Wasm as Wasm
import qualified Language.Wasm.Structure as Wasm
import Path
import System.Directory
import System.IO.Silently (silence)
import Test.Hspec hiding (example)
import VerifiWASM.Parser (parseVerifiWASMFile)
import WasmVerify

spec :: Spec
spec = do
  describe "verifyModule" $ do
    context "when verifying examples/abs.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/abs.verifiwasm")
        let altSpecPath = projectPath </> $(mkRelFile "examples/abs_alternative.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/abs.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        mSpec <- parseVerifiWASMFile specPath
        mAltSpec <- parseVerifiWASMFile altSpecPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True
        maybe
          (pure Nothing)
          (\altSpec -> Just <$> silence (verifyModule altSpec wasmModule))
          mAltSpec
          `shouldReturn` Just True

    context "when verifying examples/cfg_example.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/cfg_example.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/cfg_example.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        mSpec <- parseVerifiWASMFile specPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True

    context "when verifying examples/dup.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/dup.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/dup.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        mSpec <- parseVerifiWASMFile specPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True

    context "when verifying examples/dup_multivalue.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/dup_multivalue.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/dup_multivalue.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        mSpec <- parseVerifiWASMFile specPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True

    context "when verifying examples/example_br_table.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/example_br_table.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/example_br_table.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        mSpec <- parseVerifiWASMFile specPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True

    context "when verifying examples/fib.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/fib.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/fib.wasm")
        let wasmAltPath = projectPath </> $(mkRelFile "examples/fib_s-exp.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        wasmAltModule <- loadModuleFromFile wasmAltPath
        mSpec <- parseVerifiWASMFile specPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmAltModule))
          mSpec
          `shouldReturn` Just True

    context "when verifying examples/multivalue.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/multivalue.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/multivalue.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        mSpec <- parseVerifiWASMFile specPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True

    context "when verifying examples/no_return_fib.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/no_return_fib.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/no_return_fib.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        mSpec <- parseVerifiWASMFile specPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True

    context "when verifying examples/select.wasm" $ do
      it "the verification is successful" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let specPath = projectPath </> $(mkRelFile "examples/select.verifiwasm")
        let wasmPath = projectPath </> $(mkRelFile "examples/select.wasm")
        wasmModule <- loadModuleFromFile wasmPath
        mSpec <- parseVerifiWASMFile specPath
        maybe
          (pure Nothing)
          (\specification -> Just <$> silence (verifyModule specification wasmModule))
          mSpec
          `shouldReturn` Just True

  describe "loadModuleFromFile" $ do
    context "given an existing and valid WASM binary file" $
      it "loads the module" $ do
        projectPath <- parseAbsDir =<< getCurrentDirectory
        let examplePath = projectPath </> $(mkRelFile "examples/dup.wasm")
        example <- BS.readFile $ fromAbsFile examplePath
        let decodedModule = fromRight Wasm.emptyModule $ Wasm.decode example
        let wasmModule = Right <$> loadModuleFromFile examplePath
        wasmModule `shouldReturn` Wasm.validate decodedModule
