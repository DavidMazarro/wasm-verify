{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingStrategies #-}

module WasmVerify.CFGs where

import Control.Monad.State (State, evalState, gets, modify, void)
import Data.Bifunctor (first, second)
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import GHC.Natural
import qualified Language.Wasm.Structure as Wasm

-- import Data.Graph (stronglyConnComp)

functionToCFG :: Wasm.Function -> CFG
functionToCFG (Wasm.Function _ _ functionBody) = resultingCFG
  where
    (resultingCFG, _, _) = evalState (toCFG (traceShow functionBody functionBody)) (0, [])

{- | __Control Flow Graph__, a graph representation of the
 execution flow of a WebAssembly function.
-}
newtype CFG = CFG {cfg :: (Set Block, Set Edge)}
  deriving stock (Show)
  deriving newtype (Eq, Ord)

{- | The type of blocks, i.e. the nodes of the graph,
 in a 'CFG'. The underlying type is a list of pairs
 with an index (we preserve the index of the instruction
 in the list of instructions of the WebAssembly function)
 and an instruction. We provide 'Natural' as type argument
 to 'Wasm.Instruction' the same way 'Wasm.Expression' does
 (which is the underlying type for the body of expressions).
-}
newtype Block = Block {block :: (BlockLabel, Wasm.Expression)}
  deriving stock (Show)
  deriving newtype (Eq)

-- I'm defining an 'Ord' instance for 'Block' because it's
-- used in the set operations, and it can't be derived
-- because 'Wasm.Instruction' doesn't have an 'Ord' instance.
instance Ord Block where
  Block (label1, _) `compare` Block (label2, _) = label1 `compare` label2

{- | The type of edges for the graph, indicating the
 source 'Block', the destination 'Block' (both indicated
 with their respective 'BlockLabel's) and the annotation
 of the transition, which is the condition under which that
 branch of the CFG takes place.
-}
data Edge = Edge
  { from :: BlockLabel,
    annotation :: Annotation,
    to :: BlockLabel
  }
  deriving (Eq, Ord, Show)

data Annotation
  = Empty
  | Eq Int
  | NotEq Int
  | GreaterEq Int
  deriving (Eq, Ord, Show)

type BlockLabel = Int

{- | Type alias for the state used in the 'toCFG' function.
 The first value of the tuple is the last used 'BlockLabel'
 for a 'Block' and the second value is a list of 'BlockLabel's''
 that serves as a "stack" of nesting level in the function.
-}
type LabelState = (BlockLabel, [BlockLabel])

-- | Turns a WebAssembly function into its associated 'CFG'.
toCFG ::
  -- | A list of instructions ('Wasm.Expression') which is the body
  -- of the WebAssembly function we want to construct the 'CFG' from.
  Wasm.Expression ->
  -- | The first element of the triple is the resulting 'CFG',
  -- the second element is the label of the starting block
  -- when executing the 'CFG', and the third element is a 'Set'
  -- of labels corresponding to the possible final blocks of execution.
  -- The state is used to keep track of fresh 'BlockLabel's to be used,
  -- and are generated with 'freshLabel'.
  State LabelState (CFG, BlockLabel, Set BlockLabel)
toCFG [] = do
  newLabel <- freshLabel
  let blocks = Set.singleton $ Block (newLabel, [])
  let edges = Set.empty
  return (CFG (blocks, edges), newLabel, Set.singleton newLabel)
toCFG [blockInstr@(Wasm.Block _ blockBody)] = do
  newLabel <- freshLabel
  newLabel' <- freshLabel
  void $ pushToLabelStack newLabel'
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG blockBody
  let blocks = blockSet bodyCFG `Set.union` Set.fromList [Block (newLabel, [blockInstr]), Block (newLabel', [])]
  let edges = edgeUnion (edgeSet bodyCFG) bodyInitial newLabel newLabel' bodyFinals
  return (CFG (blocks, edges), newLabel, Set.singleton newLabel')
  where
    edgeUnion set initial l l' finals =
      set
        `Set.union` Set.singleton (Edge l Empty initial)
        `Set.union` Set.fromList
          [Edge final Empty l' | final <- Set.toList finals]
toCFG [loopInstr@(Wasm.Loop _ loopBody)] = do
  newLabel <- freshLabel
  void $ pushToLabelStack newLabel
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG loopBody
  let blocks = blockSet bodyCFG `Set.union` Set.singleton (Block (newLabel, [loopInstr]))
  let edges = edgeSet bodyCFG `Set.union` Set.singleton (Edge newLabel Empty bodyInitial)
  return (CFG (blocks, edges), newLabel, bodyFinals)
toCFG [ifInstr@(Wasm.If _ ifBody elseBody)] = do
  newLabel <- freshLabel
  (ifCFG, ifInitial, ifFinals) <- toCFG ifBody
  (elseCFG, elseInitial, elseFinals) <- toCFG elseBody
  let blocks = blockSet ifCFG `Set.union` blockSet elseCFG `Set.union` Set.singleton (Block (newLabel, [ifInstr]))
  let edges = edgeUnion (edgeSet ifCFG) (edgeSet elseCFG) ifInitial elseInitial newLabel
  return (CFG (blocks, edges), newLabel, ifFinals `Set.union` elseFinals)
  where
    edgeUnion set1 set2 initial1 initial2 label =
      set1
        `Set.union` set2
        `Set.union` Set.fromList
          [Edge label (Eq 0) initial2, Edge label (NotEq 0) initial1]
toCFG [brInstr@(Wasm.Br index)] = do
  newLabel <- freshLabel
  labelStack <- gets snd
  let blocks = Set.singleton $ Block (newLabel, [brInstr])
  let edges = Set.singleton $ Edge newLabel Empty (labelStack !! naturalToInt index)
  return (CFG (blocks, edges), newLabel, Set.empty)
toCFG [brIfInstr@(Wasm.BrIf index)] = do
  newLabel <- freshLabel
  newLabel' <- freshLabel
  labelStack <- gets snd
  let blocks = Set.fromList [Block (newLabel, [brIfInstr]), Block (newLabel', [])]
  let edgeEq0 = Edge newLabel (Eq 0) newLabel'
  let edgeNotEq0 = Edge newLabel (NotEq 0) (labelStack !! naturalToInt index)
  let edges = Set.fromList [edgeEq0, edgeNotEq0]
  return (CFG (blocks, edges), newLabel, Set.singleton newLabel')
toCFG [brTableInstr@(Wasm.BrTable tableCases defaultCase)] = do
  newLabel <- freshLabel
  labelStack <- gets snd
  let blocks = Set.singleton $ Block (newLabel, [brTableInstr])
  let edges = edgesFromTableCases tableCases newLabel labelStack defaultCase
  return (CFG (blocks, edges), newLabel, Set.empty)
  where
    edgesFromTableCases cases label stackLabels caseDefault =
      Set.fromList
        [ Edge label (Eq i) (stackLabels !! naturalToInt (cases !! i))
          | i <- [0 .. length cases - 1]
        ]
        `Set.union` Set.singleton
          (Edge label (GreaterEq (length cases)) (stackLabels !! naturalToInt caseDefault))
toCFG [Wasm.Return] = do
  labelStack <- gets snd
  void . traceShow labelStack $ return ()
  newLabel <- freshLabel
  let blocks = Set.singleton (Block (newLabel, [Wasm.Return]))
  let edges = Set.singleton (Edge newLabel Empty (last labelStack))
  return (CFG (blocks, edges), newLabel, Set.empty)
toCFG [instruction] = do
  newLabel <- freshLabel
  let blocks = Set.singleton $ Block (newLabel, [instruction])
  return (CFG (blocks, Set.empty), newLabel, Set.singleton newLabel)
toCFG (instruction : restOfInstructions) = do
  (instructionCFG, instructionInitial, instructionFinals) <- toCFG [instruction]
  (restCFG, restInitials, restFinals) <- toCFG restOfInstructions
  let blocks = blockSet instructionCFG `Set.union` blockSet restCFG
  let edges = edgeUnion (edgeSet instructionCFG) (edgeSet restCFG) restInitials instructionFinals
  return (CFG (blocks, edges), instructionInitial, restFinals)
  where
    edgeUnion set1 set2 initial finals =
      set1
        `Set.union` set2
        `Set.union` Set.fromList
          [Edge final Empty initial | final <- Set.toList finals]

{- | Generates a fresh 'BlockLabel' to use when
 constructing 'Block's in 'toCFG'.
-}
freshLabel :: State LabelState BlockLabel
freshLabel = modify (first (+ 1)) >> gets fst

pushToLabelStack :: BlockLabel -> State LabelState [BlockLabel]
pushToLabelStack label = modify (second (label :)) >> gets snd

-- * Helper functions

-- 'naturalToInt' was only available in the base library
-- from version 4.12.0 up to 4.14.3, for some reason
-- unbeknownst to me. So this piece here defines the function
-- when the system's GHC base version is outside that range.
#if MIN_VERSION_base(4,15,0)
naturalToInt :: Natural -> Int
naturalToInt = fromInteger . naturalToInteger
#elif MIN_VERSION_base(4,12,0)
#else 
naturalToInt :: Natural -> Int
naturalToInt = fromInteger . naturalToInteger
#endif

blockSet :: CFG -> Set Block
blockSet = fst . cfg

edgeSet :: CFG -> Set Edge
edgeSet = snd . cfg
