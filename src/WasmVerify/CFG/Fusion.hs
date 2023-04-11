module WasmVerify.CFG.Fusion where

import Data.Foldable (find)
import Data.Set (Set)
import qualified Data.Set as Set
import WasmVerify.CFG.Types

{- | Given any 'CFG', it returns the most simplified possible
 version of that CFG. It performs simplification (i.e. node fusion)
 steps until the simplified 'CFG' is the same as the provided 'CFG',
 which means that it has already reached the most simplified representation.
-}
simplifyCFG ::
  (CFG, NodeLabel, Set NodeLabel) ->
  (CFG, NodeLabel, Set NodeLabel)
simplifyCFG cfg =
  let simplifiedCFG = simplifyStepCFG cfg
   in if simplifiedCFG == cfg
        then cfg
        else simplifyCFG simplifiedCFG

{- | Performs a simplification step for the provided 'CFG',
 i.e. if there's a pair of nodes that can be fusioned,
 it returns the resulting 'CFG' of applying that fusion step.
-}
simplifyStepCFG ::
  (CFG, NodeLabel, Set NodeLabel) ->
  (CFG, NodeLabel, Set NodeLabel)
simplifyStepCFG cfgInitialsFinals =
  maybe cfgInitialsFinals (fusionNodesInCFG cfgInitialsFinals) $
    fusionableNodes cfgInitialsFinals

-- | Performs the fusion of a pair of fusionable nodes in a 'CFG'.
fusionNodesInCFG ::
  (CFG, NodeLabel, Set NodeLabel) ->
  (Node, Node) ->
  (CFG, NodeLabel, Set NodeLabel)
fusionNodesInCFG cfgInitialsFinals (node1, node2) =
  (CFG (nodes, edges), initialLabel, finals)
  where
    (cfg@(CFG (prevNodes, prevEdges)), initialLabel, prevFinals) = cfgInitialsFinals
    nodeLabel1 = nodeLabel node1
    nodeLabel2 = nodeLabel node2
    nodes =
      Set.insert
        (Node (nodeLabel1, nodeInstructions node1 ++ nodeInstructions node2))
        (Set.delete node2 . Set.delete node1 $ prevNodes)
    edges =
      let edgesFromNode2 = edgesFromNode node2 cfg
       in Set.delete
            (Edge nodeLabel1 Empty nodeLabel2)
            (prevEdges Set.\\ edgesFromNode2)
            `Set.union` Set.fromList
              [ Edge nodeLabel1 annotation label
                | Edge _ annotation label <- Set.toList edgesFromNode2
              ]
    finals =
      if nodeLabel2 `Set.member` prevFinals
        then Set.insert nodeLabel1 . Set.delete nodeLabel2 $ prevFinals
        else prevFinals

{- | Tries to find a pair of fusionable nodes in the provided 'CFG'.
 If there are no two fusionable nodes in the 'CFG',
 the function returns 'Nothing'.
-}
fusionableNodes ::
  (CFG, NodeLabel, Set NodeLabel) ->
  Maybe (Node, Node)
fusionableNodes (cfg@(CFG (nodes, _)), initialLabel, _) =
  (find . uncurry) (areFusionableInCFG cfg initialLabel) $
    nodes `Set.cartesianProduct` nodes

{- | Returns 'True' if a pair of nodes can be fusioned
 in a 'CFG' (with an initial label), and 'False' otherwise.
-}
areFusionableInCFG :: CFG -> NodeLabel -> Node -> Node -> Bool
areFusionableInCFG cfg initialLabel node1 node2 =
  nodeLabel node2 /= initialLabel
    && edgesFromNode node1 cfg == edgeBetweenNodes
    && edgesToNode node2 cfg == edgeBetweenNodes
  where
    nodeLabel1 = nodeLabel node1
    nodeLabel2 = nodeLabel node2
    edgeBetweenNodes = Set.singleton (Edge nodeLabel1 Empty nodeLabel2)
