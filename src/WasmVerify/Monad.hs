module WasmVerify.Monad where

import Control.Exception (Exception)
import Control.Monad.Except
import Control.Monad.Identity (runIdentity)
import Control.Monad.State (State, evalStateT)
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.Lazy as LT

-- TODO: add Haddock
type WasmVerify a = ExceptT Failure (State ExecState) a

runWasmVerify :: WasmVerify a -> IO a
runWasmVerify action = do
  let smt = runIdentity $ evalStateT (runExceptT action) emptyExecState
  case smt of
    Right x -> pure x
    Left err -> error $ show $ unFailure err
  where
    emptyExecState = ExecState M.empty [] ""

{- | The type that functions as a state when performing the symbolic
 execution of the WebAssembly module.
-}
data ExecState = ExecState
  { -- | A map that stores the last used version of an identifier.
    -- Every time there's an assignment to a variable in WebAssembly,
    -- instead of replacing the variable we already have, we add a constraint
    -- in STM that the old version is equal to the new version, and
    -- use the new version for the rest of the execution afterwards.
    identifierMap :: Map Identifier IdVersion,
    -- | The simulated stack used when performing the symbolic execution
    -- of the WebAssembly instructions.
    symbolicStack :: [StackValue],
    -- | A text accumulator that keeps adding SMT. After performing
    -- all of the symbolic execution, this value is our SMTLIB2 program
    -- that will be run and output the result of the verification.
    smtText :: LT.Text
  }

type Identifier = String

data StackValue = IntValue Int | VarValue VersionedVar

type VersionedVar = (Identifier, IdVersion)

type IdVersion = Int

-- | The error type for actions within 'WasmVerify'.
newtype Failure = Failure {unFailure :: T.Text}
  deriving stock (Show)
  deriving anyclass (Exception)
