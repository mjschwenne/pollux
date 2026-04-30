/-
  Pollux.InterParse.Theorems.InterParseOk — `parseOk_wf` and the top-level
  `interParseOk` correctness theorem for the intermediate format.
-/
import Pollux.Parse.Theorems
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer
import Pollux.InterParse.Theorems.SchemaCorrect
import Pollux.InterParse.Theorems.Compatible
import Pollux.InterParse.Theorems.Serialization
import Pollux.InterParse.Theorems.ValList

namespace Pollux.InterParse

open Pollux.Parse
open Pollux.Parse.Theorems

theorem parseOk_wf (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ → valueWf d v →
    Serializer.repWf (willEncode d) (valList d v) := by sorry

/-! ## Top-level correctness theorem

This is the main result: for any schema-correct value, serializing with
`serialValue` and then parsing with `parseValue` recovers a compatible value. -/

theorem interParseOk (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ →
    LimitParseOkCompat'' Compatible parseValue serialValue d d v := by sorry

end Pollux.InterParse
