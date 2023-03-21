module WasmVerify.CFG.Types where

import Data.Set (Set)
import GHC.Natural
import qualified Language.Wasm.Structure as Wasm

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

{- | The type of nodes in a 'CFG', consisting of a 'NodeLabel'
 that identifies the node in the graph and a list of 'IndexedInstruction'
 which are the WebAssembly instructions contained in that node.
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

-- * Helper functions

nodeLabel :: Node -> NodeLabel
nodeLabel (Node (label, _)) = label

nodeInstructions :: Node -> [IndexedInstruction]
nodeInstructions (Node (_, instructions)) = instructions

nodeSet :: CFG -> Set Node
nodeSet = fst . cfg

edgeSet :: CFG -> Set Edge
edgeSet = snd . cfg
