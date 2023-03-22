{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingStrategies #-}

module WasmVerify.CFG where

import Control.Monad.State (State, evalState, gets, modify, void)
import Data.Bifunctor (first, second)
import Data.Graph (SCC, stronglyConnComp)
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace (traceShow)
import GHC.Natural
import qualified Language.Wasm.Structure as Wasm
import WasmVerify.CFG.Fusion (simplifyCFG)
import WasmVerify.CFG.Types

{- | Turns a WebAssembly function into its associated 'CFG',
 along with the initial node (starting point of the execution)
 and the set of final nodes (possible ending points of execution).
-}
functionToCFG :: Wasm.Function -> (CFG, NodeLabel, Set NodeLabel)
functionToCFG function = evalState (simplifyCFG <$> toCFGFunction function) (0, [])

{- | Returns the list of strongly connected components in a
 function's 'CFG'. Used for generating verification conditions.
-}
stronglyConnCompCFG :: CFG -> [SCC Node]
stronglyConnCompCFG cfg =
  stronglyConnComp $
    map
      ( \node ->
          ( node,
            nodeLabel node,
            traceShow ((map nodeLabel . Set.toList) $ adjacents cfg node) ((map nodeLabel . Set.toList) $ adjacents cfg node)
          )
      )
      (Set.toList $ nodeSet cfg)

{- | This function takes a WebAssembly function,
 calls 'toCFG' and adds a final node to the resulting CFG
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
  let nodes = Node (newLabel, []) `Set.insert` nodeSet bodyCFG
  let edges = edgesFromFinals (edgeSet bodyCFG) newLabel bodyFinals
  return (CFG (nodes, edges), bodyInitial, Set.singleton newLabel)
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
  -- the second element is the label of the starting node
  -- when executing the 'CFG', and the third element is a 'Set'
  -- of labels corresponding to the possible final nodes of execution.
  -- The state is used to keep track of fresh 'NodeLabel's to be used,
  -- and are generated with 'freshLabel'.
  State LabelState (CFG, NodeLabel, Set NodeLabel)
toCFG [] = do
  newLabel <- freshLabel
  let nodes = Set.singleton $ Node (newLabel, [])
  let edges = Set.empty
  return (CFG (nodes, edges), newLabel, Set.singleton newLabel)
toCFG [blockInstr@(indexInstr, Wasm.Block _ blockBody)] = do
  newLabel <- freshLabel
  newLabel' <- freshLabel
  void $ pushToLabelStack newLabel'
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG $ indexInstructions (indexInstr + 1) blockBody
  let nodes = nodeSet bodyCFG `Set.union` Set.fromList [Node (newLabel, [blockInstr]), Node (newLabel', [])]
  let edges = edgeUnion (edgeSet bodyCFG) bodyInitial newLabel newLabel' bodyFinals
  return (CFG (nodes, edges), newLabel, Set.singleton newLabel')
  where
    edgeUnion set initial l l' finals =
      Edge l Empty initial
        `Set.insert` set
        `Set.union` Set.fromList
          [Edge final Empty l' | final <- Set.toList finals]
toCFG [loopInstr@(indexInstr, Wasm.Loop _ loopBody)] = do
  newLabel <- freshLabel
  void $ pushToLabelStack newLabel
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG $ indexInstructions (indexInstr + 1) loopBody
  let nodes = Node (newLabel, [loopInstr]) `Set.insert` nodeSet bodyCFG
  let edges = Edge newLabel Empty bodyInitial `Set.insert` edgeSet bodyCFG
  return (CFG (nodes, edges), newLabel, bodyFinals)
toCFG [ifInstr@(indexInstr, Wasm.If _ ifBody elseBody)] = do
  newLabel <- freshLabel
  (ifCFG, ifInitial, ifFinals) <- toCFG $ indexInstructions (indexInstr + 1) ifBody
  (elseCFG, elseInitial, elseFinals) <- toCFG $ indexInstructions (indexInstr + 1) elseBody
  let nodes = Node (newLabel, [ifInstr]) `Set.insert` nodeSet elseCFG `Set.union` nodeSet ifCFG
  let edges = edgeUnion (edgeSet ifCFG) (edgeSet elseCFG) ifInitial elseInitial newLabel
  return (CFG (nodes, edges), newLabel, ifFinals `Set.union` elseFinals)
  where
    edgeUnion set1 set2 initial1 initial2 label =
      set1
        `Set.union` set2
        `Set.union` Set.fromList
          [Edge label (Eq 0) initial2, Edge label (NotEq 0) initial1]
toCFG [brInstr@(_, Wasm.Br index)] = do
  newLabel <- freshLabel
  labelStack <- gets snd
  let nodes = Set.singleton $ Node (newLabel, [brInstr])
  let edges = Set.singleton $ Edge newLabel Empty (labelStack !! naturalToInt index)
  return (CFG (nodes, edges), newLabel, Set.empty)
toCFG [brIfInstr@(_, Wasm.BrIf index)] = do
  newLabel <- freshLabel
  newLabel' <- freshLabel
  labelStack <- gets snd
  let nodes = Set.fromList [Node (newLabel, [brIfInstr]), Node (newLabel', [])]
  let edgeEq0 = Edge newLabel (Eq 0) newLabel'
  let edgeNotEq0 = Edge newLabel (NotEq 0) (labelStack !! naturalToInt index)
  let edges = Set.fromList [edgeEq0, edgeNotEq0]
  return (CFG (nodes, edges), newLabel, Set.singleton newLabel')
toCFG [brTableInstr@(_, Wasm.BrTable tableCases defaultCase)] = do
  newLabel <- freshLabel
  labelStack <- gets snd
  let nodes = Set.singleton $ Node (newLabel, [brTableInstr])
  let edges = edgesFromTableCases tableCases newLabel labelStack defaultCase
  return (CFG (nodes, edges), newLabel, Set.empty)
  where
    edgesFromTableCases cases label stackLabels caseDefault =
      Edge label (GreaterEq (length cases)) (stackLabels !! naturalToInt caseDefault)
        `Set.insert` Set.fromList
          [ Edge label (Eq i) (stackLabels !! naturalToInt (cases !! i))
            | i <- [0 .. length cases - 1]
          ]
toCFG [returnInstr@(_, Wasm.Return)] = do
  labelStack <- gets snd
  newLabel <- freshLabel
  let nodes = Set.singleton (Node (newLabel, [returnInstr]))
  let edges = Set.singleton (Edge newLabel Empty (last labelStack))
  return (CFG (nodes, edges), newLabel, Set.empty)
toCFG [instruction] = do
  newLabel <- freshLabel
  let nodes = Set.singleton $ Node (newLabel, [instruction])
  return (CFG (nodes, Set.empty), newLabel, Set.singleton newLabel)
toCFG (instruction : restOfInstructions) = do
  (instructionCFG, instructionInitial, instructionFinals) <- toCFG [instruction]
  (restCFG, restInitials, restFinals) <- toCFG restOfInstructions
  let nodes = nodeSet instructionCFG `Set.union` nodeSet restCFG
  let edges = edgeUnion (edgeSet instructionCFG) (edgeSet restCFG) restInitials instructionFinals
  return (CFG (nodes, edges), instructionInitial, restFinals)
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

{- | Pushes a 'NodeLabel' to the "top" of the node label stack
 (the beginning of the list). It represents the deepest
 nesting level reached so far during the conversion to a 'CFG'.
-}
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

{- | It returns the set of nodes adjacent to a given one,
 taking the following definition of adjacency:
 "a node Y in a CFG is adjacent to a node X if there
 is an edge that goes from X to Y".
-}
adjacents :: CFG -> Node -> Set Node
adjacents cfg (Node (label, _)) =
  nodesFromNodeLabels adjacentNodeLabels
  where
    nodesFromNodeLabels nodeLabels =
      Set.filter ((`Set.member` nodeLabels) . fst . node) $ nodeSet cfg
    adjacentNodeLabels =
      Set.map to . Set.filter ((== label) . from) $ edgeSet cfg

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

{- | Adds an index to a given instruction, returning
 the indexed instruction and the next index that should
 be used. For control instructions with a body
 ('Wasm.Block', 'Wasm.Loop', 'Wasm.If') it increases
 the index by the number of instructions that appear
 in the body.
-}
addInstructionIndex :: Wasm.Instruction Natural -> Int -> (Int, IndexedInstruction)
addInstructionIndex blockInstr@(Wasm.Block _ blockBody) index =
  (index + 1 + length blockBody, (index, blockInstr))
addInstructionIndex loopInstr@(Wasm.Loop _ loopBody) index =
  (index + 1 + length loopBody, (index, loopInstr))
addInstructionIndex blockInstr@(Wasm.If _ ifBody elseBody) index =
  (index + 1 + length ifBody + length elseBody, (index, blockInstr))
addInstructionIndex instruction index = (index + 1, (index, instruction))
