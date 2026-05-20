/-
  Pollux.InterParse.Theorems.IdCompatible - The `IdCompatible` relation between
  descriptor/value pairs (used for schema-evolution correctness).
-/
import Pollux.InterParse.Theorems.SortedHelpers
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer

namespace Pollux.InterParse

/-! ## IdCompatible relation

  The `IdCompatible` relation captures when two values are compatible under the same descriptor.
  Unlike the `SchemaCorrectCompatible` relation, there is no requirement that these values are schema
  correct. The input value can have fields not in the descriptor, which are dropped in the parsed
  message. Or it could be missing fields (or have `V_MISSING` for these fields) and the output message
  will have `V_MISSING` automatically injected.

-/

inductive IdCompatible : Desc → Value → Value → Prop where
  | emp :
    IdCompatible (∅ : Desc) (∅ : Value) (∅ : Value)
  | insertInt (d : Desc) (v1 v2 : Value) (k : Int) (z : Int) :
    IdCompatible d v1 v2 →
    d.get? k = none →
    v1.get? k = none →
    v2.get? k = none →
    IdCompatible (d.insert k .int) (v1.insert k (.int z)) (v2.insert k (.int z))
  | insertBool (d : Desc) (v1 v2 : Value) (k : Int) (b : Bool) :
    IdCompatible d v1 v2 →
    d.get? k = none →
    v1.get? k = none →
    v2.get? k = none →
    IdCompatible (d.insert k .bool) (v1.insert k (.bool b)) (v2.insert k (.bool b))
  | insertMsg (d d' : Desc) (v1 v2 v1' v2' : Value) (k : Int) :
    IdCompatible d v1 v2 →
    IdCompatible d' v1' v2' →
    d.get? k = none →
    v1.get? k = none →
    v2.get? k = none →
    IdCompatible (d.insert k (.msg d'))
      (v1.insert k (.msg v1')) (v2.insert k (.msg v2'))
  | drop (d : Desc) (v1 v2 : Value) (k : Int) (val : Val) :
    IdCompatible d v1 v2 →
    d.get? k = none →
    v1.get? k = none →
    IdCompatible d (v1.insert k val) v2
  | addMissing (d : Desc) (v1 v2 : Value) (k : Int) (f : Field) :
    IdCompatible d v1 v2 →
    d.get? k = none →
    v1.get? k = none →
    v2.get? k = none →
    IdCompatible (d.insert k f) v1 (v2.insert k .missing)
  | inputMissing (d : Desc) (v1 v2 : Value) (k : Int) (f : Field) :
    IdCompatible d v1 v2 →
    d.get? k = none →
    v1.get? k = none →
    v2.get? k = none →
    IdCompatible (d.insert k f) (v1.insert k .missing) (v2.insert k .missing)

notation "⟨ " v1 " ≼ " v2 " ⟩∷ " d => IdCompatible d v1 v2

/-! ## Round-trip transformation

The transformation `idCompatTransform d v` produces the value that an
`IdCompatible`-respecting round trip yields from `v` under descriptor `d`:
- fields of `v` whose key is not in `d` are dropped,
- fields in `d` with no matching entry in `v` (or with `.missing`) become `.missing`,
- type-matched entries are preserved unchanged.

It reuses `listToValue` and `valList` from `InterParse.Descriptor`. -/

def idCompatTransform (d : Desc) (v : Value) : Value :=
  listToValue d (valList d v)

theorem idCompatRoundTrip (v : Value) (d : Desc) :
    d.WF → v.WF → ⟨ v ≼ idCompatTransform d v ⟩∷ d := by
  sorry

end Pollux.InterParse
