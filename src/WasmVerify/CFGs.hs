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

-- | Turns a WebAssembly function into its associated 'CFG'.
functionToCFG :: Wasm.Function -> CFG
functionToCFG function = resultingCFG
  where
    (resultingCFG, _, _) = evalState (toCFGFunction function) (0, [])

{- | __Control Flow Graph__, a graph representation of the
 execution flow of a WebAssembly function.
-}
newtype CFG = CFG {cfg :: (Set Node, Set Edge)}
  deriving stock (Show)
  deriving newtype (Eq, Ord)

{- | Type alias for 'Wasm.Instruction's paired with
 an index (we preserve the index of the instruction
 in the list of instructions of the WebAssembly function).
 We provide 'Natural' as type argument
 to 'Wasm.Instruction' the same way 'Wasm.Expression' does
 (which is the underlying type for the body of expressions)
-}
type IndexedInstruction = (Int, Wasm.Instruction Natural)

{- | The type of blocks, i.e. the nodes of the graph,
 in a 'CFG'.
-}
newtype Node = Node {node :: (NodeLabel, [IndexedInstruction])}
  deriving stock (Show)
  deriving newtype (Eq)

-- I'm defining an 'Ord' instance for 'Node' because it's
-- used in the set operations, and it can't be derived
-- because 'Wasm.Instruction' doesn't have an 'Ord' instance.
instance Ord Node where
  Node (label1, _) `compare` Node (label2, _) = label1 `compare` label2

{- | The type of edges for the graph, indicating the
 source 'Node', the destination 'Node' (both indicated
 with their respective 'NodeLabel's) and the annotation
 of the transition, which is the condition under which that
 branch of the CFG takes place.
-}
data Edge = Edge
  { from :: NodeLabel,
    annotation :: Annotation,
    to :: NodeLabel
  }
  deriving (Eq, Ord, Show)

data Annotation
  = Empty
  | Eq Int
  | NotEq Int
  | GreaterEq Int
  deriving (Eq, Ord, Show)

type NodeLabel = Int

{- | Type alias for the state used in the 'toCFG' function.
 The first value of the tuple is the last used 'NodeLabel'
 for a 'Node' and the second value is a list of 'NodeLabel's''
 that serves as a "stack" of nesting level in the function.
-}
type LabelState = (NodeLabel, [NodeLabel])

{- | This function takes a WebAssembly function,
 calls 'toCFG' and adds a final block to the resulting CFG
 generated from the list of instructions in the body of the function.
 See 'toCFG' for the main logic.
-}
toCFGFunction ::
  Wasm.Function ->
  State LabelState (CFG, NodeLabel, Set NodeLabel)
toCFGFunction (Wasm.Function _ _ functionBody) = do
  newLabel <- freshLabel
  void $ pushToLabelStack newLabel
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG $ indexInstructions 1 functionBody
  let blocks = blockSet bodyCFG `Set.union` Set.singleton (Node (newLabel, []))
  let edges = edgesFromFinals (edgeSet bodyCFG) newLabel bodyFinals
  return (CFG (blocks, edges), bodyInitial, Set.singleton newLabel)
  where
    edgesFromFinals edges label finals =
      edges
        `Set.union` Set.fromList
          [Edge finalLabel Empty label | finalLabel <- Set.toList finals]

{- | Recursive function used by 'functionToCFG' to translate
 the body of a function into the corresponding CFG.
-}
toCFG ::
  -- | A list of indexed 'Wasm.Instruction' coming from the body
  -- of the WebAssembly function we want to construct the 'CFG' from.
  [IndexedInstruction] ->
  -- | The first element of the triple is the resulting 'CFG',
  -- the second element is the label of the starting block
  -- when executing the 'CFG', and the third element is a 'Set'
  -- of labels corresponding to the possible final blocks of execution.
  -- The state is used to keep track of fresh 'NodeLabel's to be used,
  -- and are generated with 'freshLabel'.
  State LabelState (CFG, NodeLabel, Set NodeLabel)
toCFG [] = do
  newLabel <- freshLabel
  let blocks = Set.singleton $ Node (newLabel, [])
  let edges = Set.empty
  return (CFG (blocks, edges), newLabel, Set.singleton newLabel)
toCFG [blockInstr@(indexInstr, Wasm.Block _ blockBody)] = do
  newLabel <- freshLabel
  newLabel' <- freshLabel
  void $ pushToLabelStack newLabel'
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG $ indexInstructions (indexInstr + 1) blockBody
  let blocks = blockSet bodyCFG `Set.union` Set.fromList [Node (newLabel, [blockInstr]), Node (newLabel', [])]
  let edges = edgeUnion (edgeSet bodyCFG) bodyInitial newLabel newLabel' bodyFinals
  return (CFG (blocks, edges), newLabel, Set.singleton newLabel')
  where
    edgeUnion set initial l l' finals =
      set
        `Set.union` Set.singleton (Edge l Empty initial)
        `Set.union` Set.fromList
          [Edge final Empty l' | final <- Set.toList finals]
toCFG [loopInstr@(indexInstr, Wasm.Loop _ loopBody)] = do
  newLabel <- freshLabel
  void $ pushToLabelStack newLabel
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG $ indexInstructions (indexInstr + 1) loopBody
  let blocks = blockSet bodyCFG `Set.union` Set.singleton (Node (newLabel, [loopInstr]))
  let edges = edgeSet bodyCFG `Set.union` Set.singleton (Edge newLabel Empty bodyInitial)
  return (CFG (blocks, edges), newLabel, bodyFinals)
toCFG [ifInstr@(indexInstr, Wasm.If _ ifBody elseBody)] = do
  newLabel <- freshLabel
  (ifCFG, ifInitial, ifFinals) <- toCFG $ indexInstructions (indexInstr + 1) ifBody
  (elseCFG, elseInitial, elseFinals) <- toCFG $ indexInstructions (indexInstr + 1) elseBody
  let blocks = blockSet ifCFG `Set.union` blockSet elseCFG `Set.union` Set.singleton (Node (newLabel, [ifInstr]))
  let edges = edgeUnion (edgeSet ifCFG) (edgeSet elseCFG) ifInitial elseInitial newLabel
  return (CFG (blocks, edges), newLabel, ifFinals `Set.union` elseFinals)
  where
    edgeUnion set1 set2 initial1 initial2 label =
      set1
        `Set.union` set2
        `Set.union` Set.fromList
          [Edge label (Eq 0) initial2, Edge label (NotEq 0) initial1]
toCFG [brInstr@(_, Wasm.Br index)] = do
  newLabel <- freshLabel
  labelStack <- gets snd
  let blocks = Set.singleton $ Node (newLabel, [brInstr])
  let edges = Set.singleton $ Edge newLabel Empty (labelStack !! naturalToInt index)
  return (CFG (blocks, edges), newLabel, Set.empty)
toCFG [brIfInstr@(_, Wasm.BrIf index)] = do
  newLabel <- freshLabel
  newLabel' <- freshLabel
  labelStack <- gets snd
  let blocks = Set.fromList [Node (newLabel, [brIfInstr]), Node (newLabel', [])]
  let edgeEq0 = Edge newLabel (Eq 0) newLabel'
  let edgeNotEq0 = Edge newLabel (NotEq 0) (labelStack !! naturalToInt index)
  let edges = Set.fromList [edgeEq0, edgeNotEq0]
  return (CFG (blocks, edges), newLabel, Set.singleton newLabel')
toCFG [brTableInstr@(_, Wasm.BrTable tableCases defaultCase)] = do
  newLabel <- freshLabel
  labelStack <- gets snd
  let blocks = Set.singleton $ Node (newLabel, [brTableInstr])
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
toCFG [returnInstr@(_, Wasm.Return)] = do
  labelStack <- gets snd
  void . traceShow labelStack $ return ()
  newLabel <- freshLabel
  let blocks = Set.singleton (Node (newLabel, [returnInstr]))
  let edges = Set.singleton (Edge newLabel Empty (last labelStack))
  return (CFG (blocks, edges), newLabel, Set.empty)
toCFG [instruction] = do
  newLabel <- freshLabel
  let blocks = Set.singleton $ Node (newLabel, [instruction])
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

{- | Generates a fresh 'NodeLabel' to use when
 constructing 'Node's in 'toCFG'.
-}
freshLabel :: State LabelState NodeLabel
freshLabel = modify (first (+ 1)) >> gets fst

pushToLabelStack :: NodeLabel -> State LabelState [NodeLabel]
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

{- | Adds an index to each instruction of
 a list coming from a 'Wasm.Function' body.
 Used to keep track of the index of an instruction to check
 the asserts provided by the VerifiWASM specification.
 It has an index accumulator to help with indexing nested
 instructions within bodies of 'Wasm.Block', 'Wasm.Loop' and 'Wasm.If'.
-}
indexInstructions :: Int -> Wasm.Expression -> [IndexedInstruction]
indexInstructions _ [] = []
indexInstructions startIndex (instruction : restOfInstructions) =
  let (nextIndex, indexedInstr) = addInstructionIndex instruction startIndex
   in indexedInstr : (indexInstructions nextIndex restOfInstructions)

addInstructionIndex :: Wasm.Instruction Natural -> Int -> (Int, IndexedInstruction)
addInstructionIndex blockInstr@(Wasm.Block _ blockBody) index =
  (index + 1 + length blockBody, (index, blockInstr))
addInstructionIndex loopInstr@(Wasm.Loop _ loopBody) index =
  (index + 1 + length loopBody, (index, loopInstr))
addInstructionIndex blockInstr@(Wasm.If _ ifBody elseBody) index =
  (index + 1 + length ifBody + length elseBody, (index, blockInstr))
addInstructionIndex instruction index = (index + 1, (index, instruction))

blockSet :: CFG -> Set Node
blockSet = fst . cfg

edgeSet :: CFG -> Set Edge
edgeSet = snd . cfg
