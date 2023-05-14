-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

{- |
 = Execution path search and related functionality

 TODO: Describe module
-}
module WasmVerify.Paths where

import Control.Monad (forM_, unless, when)
import Control.Monad.State (MonadState (get), State, evalState, modify)
import Data.Containers.ListUtils (nubOrd)
import Data.Graph (SCC (..))
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (intercalate, pack)
import Helpers.ANSI (bold)
import VerifiWASM.LangTypes as VerifiWASM
import WasmVerify.CFG.Types
import WasmVerify.Monad (Failure (Failure), WasmVerify, failWithError)

{- | Given a 'CFG' and a function specification ('VerifiWASM.FunctionSpec'),
 this function returns a map that associates each node in the 'CFG' with
 an 'Assert'. This function makes a couple of checks and assumptions:

  - Assertions can only be __at the entry point__ of 'Node's.
  This means that the instruction index to which an assertion points
  must be the first instruction in that 'Node''s block of code.
  This also implies that assertions cannot be in the middle of a block
  of code.

  - As a corollary from the previous point, a 'Node' is not allowed to have
  multiple assertions __unless__ all of them are indexed on the first
  instruction in that 'Node''s block of code. In that case, they will
  get transformed into a single assertion by applying a logical AND
  operation to all of them.

  - The index of an assertion must be inbounds with regards to the
  number of instructions in the function. Falling out of bounds of the
  indexed instructions range will result in an out of bounds exception.

  If any of these criteria are not met by the specification, this function
  will throw a 'Failure'.
-}
getNodesAssertsMap :: CFG -> VerifiWASM.FunctionSpec -> WasmVerify (Map Node Assert)
getNodesAssertsMap specCFG spec = do
  nodeLabelsAndAsserts <- mapM (nodeLabelAndAssert specCFG) $ (asserts . specBody) spec

  -- We check that all of the asserts have their index pointing
  -- to the first instruction in the list of instructions in the node,
  -- i.e. asserts appear in the entry point of nodes.
  forM_ nodeLabelsAndAsserts (checkAssertAtStart specCFG)

  return $ Map.fromListWith logicAndAsserts nodeLabelsAndAsserts
  where
    nodeLabelAndAssert :: CFG -> Assert -> WasmVerify (Node, Assert)
    nodeLabelAndAssert cfg assert@(Assert (index, _)) = do
      let mNode = find (isIndexInNode index) $ nodeSet cfg
      when (isNothing mNode) $ indexOutOfBoundsErr assert cfg

      -- The use of 'fromJust' here is safe because we have
      -- just checked whether the value is 'Nothing' or not
      -- (and in that case, we throw a custom failure)
      return (fromJust mNode, assert)
    isIndexInNode :: Int -> Node -> Bool
    isIndexInNode index node =
      isJust $ find (\instr -> fst instr == index) $ nodeInstructions node
    checkAssertAtStart :: CFG -> (Node, Assert) -> WasmVerify ()
    checkAssertAtStart cfg (Node (_, instructions), assert@(Assert (index, _))) =
      case instructions of
        -- When the list of instructions is empty, it's the empty exit node
        -- so we don't have to throw an error.
        [] -> return ()
        (firstInstr : _) ->
          unless (index == fst firstInstr) $ badIndexInvariantErr assert cfg
    logicAndAsserts :: Assert -> Assert -> Assert
    -- Used to combine asserts with a logical and.
    logicAndAsserts (Assert (index, expr1)) (Assert (_, expr2)) =
      Assert (index, BAnd expr1 expr2)
    indexOutOfBoundsErr assert cfg =
      let (index, instr) = lastInstruction cfg
       in failWithError $
            Failure $
              "In function specification "
                <> (bold . pack . funcName)
                  spec
                <> ", the following assertion has an instruction index"
                <> " that is out of bounds of the instruction range:\n\n"
                <> (bold . pack . show)
                  assert
                <> "\n\nBut the last instruction of the WebAssembly function is:\n\n"
                <> (bold . pack)
                  ( show index
                      <> ": "
                      <> show instr
                  )
    badIndexInvariantErr assert cfg =
      let instructions = firstInstrEveryNode cfg
       in failWithError $
            Failure $
              "In function specification "
                <> (bold . pack . funcName)
                  spec
                <> ", the following assertion has an instruction index"
                <> " that points to an instruction in the middle of a block:\n\n"
                <> (bold . pack . show)
                  assert
                <> "\n\nBut assertions can only point to the entry points of blocks.\n"
                <> "More specifically, these are all the indexed instructions which correspond to"
                <> " entry points in the control flow of the WebAssembly function:\n\n"
                <> intercalate
                  "\n"
                  [ (bold . pack)
                      ( show index
                          <> ": "
                          <> show instr
                      )
                    | (index, instr) <- instructions
                  ]

{- | Returns the 'Annotation' corresponding to the transition
 from the first 'NodeLabel' argument to the second one.
 If there's no edge between those nodes, it returns 'Nothing'.
-}
getTransitionAnnotation :: CFG -> NodeLabel -> NodeLabel -> Maybe Annotation
getTransitionAnnotation cfg from to =
  annotation <$> find (\(Edge from' _ to') -> from == from' && to == to') (edgeSet cfg)

{- | Since there must be an invariant (represented with the assert) for
 every looping part of the WebAssembly program, this check is used to ensure
 that there's an assert in the specification for the provided strongly connected
 component of the 'CFG' in the case that it is a 'CyclicSCC' (representing a loop).
-} -- TODO: Use this function after calling getNodesAssertsMap in the main to check for asserts in SCCs
checkAssertsForSCC :: VerifiWASM.FunctionSpec -> Map Node Assert -> SCC Node -> WasmVerify ()
checkAssertsForSCC spec nodesAssertsMap scc =
  case scc of
    AcyclicSCC _ -> return ()
    CyclicSCC nodes -> do
      unless (any (isJust . (`Map.lookup` nodesAssertsMap)) nodes) $
        missingInvariantErr nodes
  where
    missingInvariantErr nodes =
      failWithError $
        Failure $
          "In function specification "
            <> (bold . pack . funcName)
              spec
            <> ", there is a loop that has no assertions.\n"
            <> "Loops should have at least one assertion at the beginning of one of its nodes, "
            <> "for invariant checking purposes during analysis.\n"
            <> "These are the blocks of instructions in the loop without assertion:\n----------\n"
            <> intercalate
              "\n----------\n"
              (map (instructionsToText . snd . node) nodes)
            <> "\n----------\nPlease, add an assertion indexed at the entry point"
            <> " instruction of one of those code blocks."
    instructionsToText instructions =
      intercalate
        "\n"
        [ (bold . pack)
            ( show index
                <> ": "
                <> show instr
            )
          | (index, instr) <- instructions
        ]

{- | The list of all execution paths in a 'CFG'. A path is a sequence
 of nodes that are executed. Every path returned by this function
 falls into one of the following types of paths:

    - An execution from the initial node (precondition) to 
    the final node (postcondition). No asserts found in-between.

        - In the case of simple WebAssembly functions, it could happen that
        the 'CFG' consists only of one node, which would be both the initial
        and the final node.

    - An execution from the initial node (precondition) to a node
    with an assert.
    - An execution from a node with an assert to another node with
    an assert. If the start and end nodes are the same, it represents
    the execution of a loop.
    - An execution from a node with an assert to one the final node (postcondition).
-}
allExecutionPaths ::
  -- | (The 'CFG', the initial node, the final node)
  (CFG, NodeLabel, NodeLabel) ->
  -- | List of nodes with an assert. These are the nodes that
  -- serve as a stopping point in the search process: execution
  -- paths going through an assert are split into the path before
  -- the assert and the path after the assert. It also serves as
  -- a loop breaker in cyclic SCCs (those asserts are invariants).
  [NodeLabel] ->
  [[NodeLabel]]
allExecutionPaths (cfg, initial, final) nodesWithAssert =
  let adjacencyMap = cfgToAdjacencyMap cfg
   in evalState
        (searchPathsFromNode (adjacencyMap, initial, final) nodesWithAssert [] [initial])
        Set.empty

{- | Recursive function used in 'allExecutionPaths' to do the search
 of all possible execution paths in a CFG. The state encodes the
 set of all nodes that have been visited, i.e. nodes from which
  execution paths have already been searched over in the 'CFG'.
-}
searchPathsFromNode ::
  -- | (The 'CFG' as an adjacency map, the initial node, the final node)
  (Map NodeLabel (Set NodeLabel), NodeLabel, NodeLabel) ->
  -- | List of nodes with an assert. See 'allExecutionPaths' for more details.
  [NodeLabel] ->
  -- | Accumulator of paths. It should be set to the empty list
  -- when calling this function.
  [[NodeLabel]] ->
  -- | Queue of nodes to calculate paths from. It should be set
  -- to a list only containing the initial node when calling this function.
  [NodeLabel] ->
  -- | In the recursion, this returns the list of paths found so far.
  State (Set NodeLabel) [[NodeLabel]]
searchPathsFromNode (adjacencyMap, initial, final) nodesWithAssert paths queue =
  case queue of
    [] -> return paths
    (x : xs) -> do
      let newPaths = allPathsWithCondition (`elem` nodesWithAssert) adjacencyMap x
      modify (Set.insert x)
      used <- get
      let beacons = (nubOrd . filter (not . flip Set.member (Set.union used $ Set.singleton final)) . map last) newPaths
      restOfPaths <- searchPathsFromNode (adjacencyMap, initial, final) nodesWithAssert paths (xs ++ beacons)
      return $ newPaths ++ restOfPaths

{- | A list of execution paths from the provided node to nodes that
 satisfy the provided condition, or until the final node is reached.
-}
allPathsWithCondition ::
  -- | The condition in which the search algorithm stops
  -- the search and breaks a path.
  (NodeLabel -> Bool) ->
  -- | The 'CFG' as an adjacency map.
  Map NodeLabel (Set NodeLabel) ->
  -- | The node to search paths from.
  NodeLabel ->
  [[NodeLabel]]
allPathsWithCondition condition adjacencyMap initial
  | adjs == Set.empty = [[initial]]
  | otherwise = map (initial :) $ concatMap (pathsWithCondition condition adjacencyMap) adjs
  where
    adjs = adjacencyMap Map.! initial
    pathsWithCondition check aMap n =
      if check n
        then [[n]]
        else allPathsWithCondition check aMap n
