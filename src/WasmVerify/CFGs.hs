{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingStrategies #-}

module WasmVerify.CFGs where

import Control.Monad.State
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Language.Wasm.Structure as Wasm
import GHC.Natural

-- import Data.Graph (stronglyConnComp)

{- | __Control Flow Graph__, a graph representation of the
 execution flow of a WebAssembly function.
-}
newtype CFG = CFG {cfg :: (Set Block, Set Edge)}
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
  deriving (Eq, Ord)

data Annotation
  = Empty
  | Eq Natural
  | NotEq Natural
  | GreaterEq Natural
  deriving (Eq, Ord)

type BlockLabel = Int

labels :: Set Block -> Set BlockLabel
labels = Set.map (fst . block)

-- | Turns a WebAssembly function into its associated 'CFG'.
toCFG ::
  -- | A list of instructions ('Wasm.Expression') which is the body
  -- of the WebAssembly function we want to construct the 'CFG' from.
  Wasm.Expression ->
  -- | A list of block labels that serves as a "stack"
  -- of nesting level in the function.
  [BlockLabel] ->
  -- | The first element of the triple is the resulting 'CFG',
  -- the second element is the label of the starting block
  -- when executing the 'CFG', and the third element is a 'Set'
  -- of labels corresponding to the possible final blocks of execution.
  -- The state is used to keep track of fresh 'BlockLabel's to be used,
  -- and are generated with 'freshLabel'.
  State BlockLabel (CFG, BlockLabel, Set BlockLabel)
toCFG [] _ = do
  newLabel <- freshLabel
  let blocks = Set.singleton $ Block (newLabel, [])
  let edges = Set.empty
  return (CFG (blocks, edges), newLabel, Set.singleton newLabel)
toCFG [blockInstr@(Wasm.Block _ blockBody)] labelStack = do
  newLabel <- freshLabel
  newLabel' <- freshLabel
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG blockBody (newLabel' : labelStack)
  let blocks = blockSet bodyCFG `Set.union` Set.fromList [Block (newLabel, [blockInstr]), Block (newLabel', [])]
  let edges = edgeUnion (edgeSet bodyCFG) bodyInitial newLabel newLabel' bodyFinals
  return (CFG (blocks, edges), newLabel, Set.singleton newLabel')
  where
    edgeUnion set initial l l' finals =
      set
        `Set.union` Set.singleton (Edge l Empty initial)
        `Set.union` Set.fromList
          [Edge final Empty l' | final <- Set.toList finals]
toCFG [loopInstr@(Wasm.Loop _ loopBody)] labelStack = do
  newLabel <- freshLabel
  (bodyCFG, bodyInitial, bodyFinals) <- toCFG loopBody (newLabel : labelStack)
  let blocks = blockSet bodyCFG `Set.union` Set.singleton (Block (newLabel, [loopInstr]))
  let edges = edgeSet bodyCFG `Set.union` Set.singleton (Edge newLabel Empty bodyInitial)
  return (CFG (blocks, edges), newLabel, bodyFinals)
toCFG [ifInstr@(Wasm.If _ ifBody elseBody)] labelStack = do
  newLabel <- freshLabel
  (ifCFG, ifInitial, ifFinals) <- toCFG ifBody labelStack
  (elseCFG, elseInitial, elseFinals) <- toCFG elseBody labelStack
  let blocks = blockSet ifCFG `Set.union` blockSet elseCFG `Set.union` Set.singleton (Block (newLabel, [ifInstr]))
  let edges = edgeUnion (edgeSet ifCFG) (edgeSet elseCFG) ifInitial elseInitial newLabel
  return (CFG (blocks, edges), newLabel, ifFinals `Set.union` elseFinals)
  where
    edgeUnion set1 set2 initial1 initial2 label =
      set1
        `Set.union` set2
        `Set.union` Set.fromList
          [Edge label (Eq 0) initial2, Edge label (NotEq 0) initial1]
toCFG [brInstr@(Wasm.Br index)] labelStack = do
  newLabel <- freshLabel
  let blocks = Set.singleton $ Block (newLabel, [brInstr])
  let edges = Set.singleton $ Edge newLabel Empty (labelStack !! naturalToInt index)
  return (CFG (blocks, edges), newLabel, Set.empty)
-- toCFG [Wasm.BrIf index] labelStack = do
--   let blocks =
--   let edges =
-- toCFG [Wasm.BrTable cases defaultCase] labelStack = do
--   let blocks =
--   let edges =
toCFG [Wasm.Return] labelStack = do
  newLabel <- freshLabel
  let blocks = Set.singleton (Block (newLabel, [Wasm.Return]))
  let edges = Set.singleton (Edge newLabel Empty (last labelStack))
  return (CFG (blocks, edges), newLabel, Set.empty)
toCFG (instruction : restOfInstructions) labelStack = do
  (instructionCFG, instructionInitial, instructionFinals) <- toCFG [instruction] labelStack
  (restCFG, restInitials, restFinals) <- toCFG restOfInstructions labelStack
  let blocks = blockSet instructionCFG `Set.union` blockSet restCFG
  let edges = edgeUnion (edgeSet instructionCFG) (edgeSet restCFG) restInitials instructionFinals
  return (CFG (blocks, edges), instructionInitial, restFinals)
  where
    edgeUnion set1 set2 initial finals =
      set1
        `Set.union` set2
        `Set.union` Set.fromList
          [Edge final Empty initial | final <- Set.toList finals]

freshLabel :: State BlockLabel BlockLabel
freshLabel = modify (+ 1) >> get

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

-- Vamos acumulando las etiquetas en las llamadas
-- recursivas (se construyen al revés los niveles de anidación,
-- e.g. [l_2, l_1, l_0]). La lista de etiquetas tiene
-- un elemento inicialmente, y es el bloque que me marca
-- el final de esa función. Tenemos que devolver aquí el bloque inicial
-- y los posibles bloques finales.
-- toCFG :: (WASM, [BlockLabel]) -> CFG

-- Esta es la función que usaremos en toCFG para construirlo
-- translateCFG :: ([ListaInstrucciones], [BlockLabel]) -> CFG

-- Generador de etiquietas que no se hayan usado antes
-- fresh = undefined

-- Con todo eso vamos a tener bloques con solo una instrucción
-- y bloques vacíos. Queremos simplificar el CFG después.
