module WasmVerify.CFGs where

import Control.Monad.State
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Language.Wasm.Structure as Wasm
import Numeric.Natural (Natural)

-- | __Control Flow Graph__, a graph representation of the
-- execution flow of a WebAssembly function.
newtype CFG = CFG (Set Block, Set Edge)

{- | The type of blocks, i.e. the nodes of the graph,
 in a 'CFG'. The underlying type is a list of pairs
 with an index (we preserve the index of the instruction
 in the list of instructions of the WebAssembly function)
 and an instruction. We provide 'Natural' as type argument
 to 'Wasm.Instruction' the same way 'Wasm.Expression' does
 (which is the underlying type for the body of expressions).
-}
data Block = Block
  { label :: BlockLabel,
    instructions :: [(Natural, Wasm.Instruction Natural)]
  }

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

data Annotation
  = Empty
  | Eq Natural
  | NotEq Natural
  | GreaterEq Natural
  deriving (Eq)

type BlockLabel = Int

labels :: Set Block -> Set BlockLabel
labels = Set.map label

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
  State Int (CFG, BlockLabel, Set BlockLabel)
toCFG = undefined

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
