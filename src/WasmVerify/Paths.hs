module WasmVerify.Paths where

import Control.Monad.State (MonadState (get), State, evalState, modify)
import Data.Containers.ListUtils (nubOrd)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import WasmVerify.CFG.Types

{- | The list of all execution paths in a 'CFG'. A path is a sequence
 of nodes that are executed. Every path returned by this function
 falls into one of the following types of paths:

    - An execution from the precondition (initial node) to one of
    the final nodes (postconditions). No asserts found in-between.  

        - In the case of simple WebAssembly functions, it could happen that
        the 'CFG' consists only of one node, which would be both the initial
        and the final node.

    - An execution from the precondition (initial node) to a node
    with an assert.
    - An execution from a node with an assert to another node with
    an assert. If the start and end nodes are the same, it represents
    the execution of a loop.
    - An execution from a node with an assert to one of the final
    nodes (postconditions).
-}
allExecutionPaths ::
  -- | (The 'CFG', the initial node, the set of final nodes)
  (CFG, NodeLabel, Set NodeLabel) ->
  -- | List of nodes with an assert. These are the nodes that
  -- serve as a stopping point in the search process: execution
  -- paths going through an assert are split into the path before
  -- the assert and the path after the assert. It also serves as
  -- a loop breaker in cyclic SCCs (those asserts are invariants).
  [NodeLabel] ->
  [[NodeLabel]]
allExecutionPaths (cfg, initial, finals) nodesWithAssert =
  let adjacencyMap = cfgToAdjacencyMap cfg
   in evalState
        (searchPathsFromNode (adjacencyMap, initial, finals) nodesWithAssert [] [initial])
        Set.empty

{- | Recursive function used in 'allExecutionPaths' to do the search
 of all possible execution paths in a CFG. The state encodes the
 set of all nodes that have been visited, i.e. nodes from which
  execution paths have already been searched over in the 'CFG'.
-}
searchPathsFromNode ::
  -- | (The 'CFG' as an adjacency map, the initial node, the set of final nodes)
  (Map NodeLabel (Set NodeLabel), NodeLabel, Set NodeLabel) ->
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
searchPathsFromNode (adjacencyMap, initial, finals) nodesWithAssert paths queue =
  case queue of
    [] -> return paths
    (x : xs) -> do
      -- TODO: Change condition to check for node in the beginning
      -- of a cyclic SCC. Use getNodesAssertsMap to check if a node has an assert.
      let newPaths = allPathsWithCondition (`elem` nodesWithAssert) adjacencyMap x
      modify (Set.insert x)
      used <- get
      let beacons = (nubOrd . filter (not . flip Set.member (Set.union used finals)) . map last) newPaths
      restOfPaths <- searchPathsFromNode (adjacencyMap, initial, finals) nodesWithAssert paths (xs ++ beacons)
      return $ newPaths ++ restOfPaths

allPathsWithCondition ::
  -- | The condition in which the search algorithm stops
  -- the search and breaks a path.
  (NodeLabel -> Bool) ->
  -- | The 'CFG' as an adjacency map.
  Map NodeLabel (Set NodeLabel) ->
  -- | The node to search paths from.
  NodeLabel ->
  -- | A list of execution paths from the provided node
  -- to nodes that satisfy the provided condition or are final nodes.
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
