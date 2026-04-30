/-
  Pollux.InterParse.Theorems — Correctness theorems for the intermediate format.

  Corresponds to src/InterParse.v (Section Theorems) in the Rocq development.

  This file is an umbrella that re-exports the theorems split across the
  `Theorems/` subdirectory. Layers (each builds independently for fast
  incremental rebuilds):

  - Primitives    : roundtrip lemmas for byte/unsigned/nat/z32/bool
  - SortedHelpers : map-on-sorted-list facts about sortedInsert/sortedErase
  - Validity      : `valid'` decomposition + encoding-length unfold
  - SchemaCorrect : `SchemaCorrect`/`SchemaCorrectOrdered` + structural lemmas
  - Compatible    : `Compatible` relation + `compatibleEqual`
  - Serialization : willEncode + weakening + serializer inversion + length
  - ValList       : `valList` filtering + listToValue roundtrip
  - InterParseOk  : `parseOk_wf` + top-level `interParseOk`
-/
import Pollux.InterParse.Theorems.Primitives
import Pollux.InterParse.Theorems.SortedHelpers
import Pollux.InterParse.Theorems.Validity
import Pollux.InterParse.Theorems.SchemaCorrect
import Pollux.InterParse.Theorems.Compatible
import Pollux.InterParse.Theorems.Serialization
import Pollux.InterParse.Theorems.ValList
import Pollux.InterParse.Theorems.InterParseOk
