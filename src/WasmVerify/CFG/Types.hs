module WasmVerify.CFG.Types where

import Data.Set (Set)
import qualified Data.Set as Set
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

{- | A datatype used in 'Edge's for encoding the condition that
must hold for the execution to go from one 'Node' to another 'Node'.
 It can be understood similarly to a labeled transition
 in a [finite-state machine](https://en.wikipedia.org/wiki/Finite-state_machine).
-}
data Annotation
  = -- | The edge is __always__ traversed.
    Empty
  | -- | The edge is traversed when the value at the top
    -- of the WebAssembly program stack is __equal__ to the given 'Int'.
    Eq Int
  | -- | The edge is traversed when the value at the top
    -- of the WebAssembly program stack is __different__ to the given 'Int'.
    NotEq Int
  | -- | The edge is traversed when the value at the top
    -- of the WebAssembly program stack is __greater or equal__ to the given 'Int'.
    GreaterEq Int
  deriving (Eq, Ord, Show)

{- | A type alias for 'Int's, used to tag nodes in a 'CFG'
 and serve as the identifier for a given node.
-}
type NodeLabel = Int

{- | Type alias for the state used in the 'WasmVerify.CFG.toCFG' function.
 The first value of the tuple is the last used 'NodeLabel'
 for a 'Node' and the second value is a list of 'NodeLabel's
 that serves as a "stack" of nesting level in the function.
-}
type LabelState = (NodeLabel, [NodeLabel])

-- * Helper functions

-- | Returns the 'NodeLabel' for the provided 'Node'.
nodeLabel :: Node -> NodeLabel
nodeLabel (Node (label, _)) = label

-- | Returns the WebAssembly instructions contained in the provided 'Node'.
nodeInstructions :: Node -> [IndexedInstruction]
nodeInstructions (Node (_, instructions)) = instructions

-- | Returns the 'Set' of 'Node's in a 'CFG'.
nodeSet :: CFG -> Set Node
nodeSet = fst . cfg

-- | Returns the 'Set' of 'Edge's in a 'CFG'.
edgeSet :: CFG -> Set Edge
edgeSet = snd . cfg

{- | Gets the set of edges that go __from__ the specified
 'Node' to other 'Node's in the 'CFG'.
-}
edgesFromNode :: Node -> CFG -> Set Edge
edgesFromNode (Node (label, _)) cfg =
  Set.filter ((== label) . from) $ edgeSet cfg

{- | Gets the set of edges that go __to__ the specified
 'Node' from other 'Node's in the 'CFG'.
-}
edgesToNode :: Node -> CFG -> Set Edge
edgesToNode (Node (label, _)) cfg =
  Set.filter ((== label) . to) $ edgeSet cfg
