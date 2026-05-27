/-
  Pollux.InterParse.Theorems.IdCompatible - The `IdCompatible` relation between
  descriptor/value pairs (used for schema-evolution correctness).

  This file contains only the relation, the round-trip transform, and the
  basic properties of the transform. Helper lemmas live in
  `IdCompatibleHelpers.lean`; the main round-trip theorem lives in
  `IdCompatibleRoundTrip.lean`.
-/
import Pollux.InterParse.Theorems.SortedHelpers
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer
import Mathlib

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

def IdCompatibleWrapper (d _d' : Desc) (v₁ v₂ : Value) : Prop :=
  IdCompatible d v₁ v₂

/-! ## Round-trip transformation

The transformation `idCompatTransform d v` produces the value that an
`IdCompatible`-respecting round trip yields from `v` under descriptor `d`:
- fields of `v` whose key is not in `d` are dropped,
- fields in `d` with no matching entry in `v` (or with `.missing`) become `.missing`,
- type-matched entries are preserved unchanged,
- nested message fields are recursively transformed. -/

mutual
/-- Build the output value for each field in the descriptor. -/
def idCompatTransformAux : List (Int × Field) → Value → List (Int × Val)
  | [], _ => []
  | (k, f) :: rest, v =>
    let resultVal := match f, v.get? k with
      | Field.bool, some (Val.bool b) => Val.bool b
      | Field.int, some (Val.int z) => Val.int z
      | Field.msg d', some (Val.msg v') => Val.msg (idCompatTransform d' v')
      | _, _ => Val.missing
    (k, resultVal) :: idCompatTransformAux rest v
/-- Recursively transform a value according to a descriptor. -/
def idCompatTransform : Desc → Value → Value
  | .mk fs, v => .mk (idCompatTransformAux fs v)
end

/-! ## Basic properties of the transform -/

/-- The keys of the transform output are exactly the keys of the descriptor. -/
theorem idCompatTransformAux_keys (fs : List (Int × Field)) (v : Value) :
    (idCompatTransformAux fs v).map Prod.fst = fs.map Prod.fst := by
  induction' fs with f fs ih generalizing v <;> simp +decide [*, idCompatTransformAux]

/-- The recursive transform preserves the sorted invariant of the descriptor's keys. -/
theorem idCompatTransformAux_sorted (fs : List (Int × Field)) (v : Value) :
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) fs →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) (idCompatTransformAux fs v) := by
  intro h
  induction fs with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    unfold idCompatTransformAux; simp only []
    rw [List.pairwise_cons]
    exact ⟨fun b hb => by
      have : b.1 ∈ tl.map Prod.fst := by
        have := List.mem_map_of_mem (f := Prod.fst) hb
        rwa [idCompatTransformAux_keys] at this
      obtain ⟨c, hc, hc_eq⟩ := List.mem_map.mp this
      rw [← hc_eq]; exact List.rel_of_pairwise_cons h hc, ih h.tail⟩

/-- The recursive transform preserves the no-dup invariant. -/
theorem idCompatTransformAux_nodup (fs : List (Int × Field)) (v : Value) :
    (fs.map Prod.fst).Nodup →
    ((idCompatTransformAux fs v).map Prod.fst).Nodup := by
  rw [idCompatTransformAux_keys]; exact id

/-- The transformed value is well-formed. -/
theorem idCompatTransform_wf (d : Desc) (v : Value) :
    d.WF → (idCompatTransform d v).WF := by
  intro ⟨hSorted, hNodup⟩
  cases d with | mk fs =>
  simp only [idCompatTransform]
  exact ⟨idCompatTransformAux_sorted fs v hSorted, idCompatTransformAux_nodup fs v hNodup⟩

/-- Lookup in the transformed value at a key NOT in the descriptor. -/
theorem idCompatTransformAux_lookup_none (fs : List (Int × Field)) (v : Value)
    (k : Int) :
    List.lookup k fs = none →
    List.lookup k (idCompatTransformAux fs v) = none := by
  induction' fs with hd tl ih generalizing v
  · intro; rfl
  · intro hk
    have hne : k ≠ hd.1 := by
      intro heq
      have : List.lookup hd.1 (hd :: tl) = some hd.2 := by
        show (match hd.1 == hd.1 with | true => some hd.2 | false => _) = _; simp
      rw [← heq] at this; rw [this] at hk; exact absurd hk (by simp)
    have htl : List.lookup k tl = none := by
      have h1 : List.lookup k (hd :: tl) =
        (match k == hd.1 with | true => some hd.2 | false => List.lookup k tl) := rfl
      rw [h1, show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hne]] at hk
      simpa using hk
    unfold idCompatTransformAux
    change (match k == hd.1 with | true => _ | false => _) = none
    rw [show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hne]]
    exact ih v htl

/-- Lookup in the transformed value at a key in the descriptor. -/
theorem idCompatTransformAux_lookup (fs : List (Int × Field)) (v : Value)
    (k : Int) (f : Field) :
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) fs →
    List.lookup k fs = some f →
    List.lookup k (idCompatTransformAux fs v) =
      some (match f, v.get? k with
        | Field.bool, some (Val.bool b) => Val.bool b
        | Field.int, some (Val.int z) => Val.int z
        | Field.msg d', some (Val.msg v') => Val.msg (idCompatTransform d' v')
        | _, _ => Val.missing) := by
  induction' fs with hd tl ih generalizing v k f
  · intro _ h; cases h
  · intro hSorted hLookup
    by_cases hk : k = hd.1
    · subst hk
      have hf : hd.2 = f := by
        have : List.lookup hd.1 (hd :: tl) = some hd.2 := by
          show (match hd.1 == hd.1 with | true => some hd.2 | false => _) = _; simp
        rw [this] at hLookup; exact Option.some.inj hLookup
      subst hf
      unfold idCompatTransformAux
      show (match hd.1 == hd.1 with | true => _ | false => _) = _
      simp
    · have htl : List.lookup k tl = some f := by
        have h1 : List.lookup k (hd :: tl) =
          (match k == hd.1 with | true => some hd.2 | false => List.lookup k tl) := rfl
        rw [h1, show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hk]] at hLookup
        simpa using hLookup
      unfold idCompatTransformAux
      show (match k == hd.1 with | true => _ | false => _) = _
      rw [show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hk]]
      exact ih v k f hSorted.tail htl

/-- `idCompatTransform` lookup at a key in the descriptor. -/
theorem idCompatTransform_get?_some (d : Desc) (v : Value) (k : Int) (f : Field) :
    d.WF → d.get? k = some f →
    (idCompatTransform d v).get? k =
      some (match f, v.get? k with
        | Field.bool, some (Val.bool b) => Val.bool b
        | Field.int, some (Val.int z) => Val.int z
        | Field.msg d', some (Val.msg v') => Val.msg (idCompatTransform d' v')
        | _, _ => Val.missing) := by
  intro ⟨hSorted, _⟩ hd
  cases d with | mk fs =>
  simp [idCompatTransform, Value.get?, Value.vals, Desc.get?, Desc.fields] at *
  exact idCompatTransformAux_lookup fs v k f hSorted hd

/-- `idCompatTransform` lookup at a key NOT in the descriptor. -/
theorem idCompatTransform_get?_none (d : Desc) (v : Value) (k : Int) :
    d.get? k = none → (idCompatTransform d v).get? k = none := by
  intro hdk
  cases d with | mk fs =>
  simp only [idCompatTransform, Value.get?, Value.vals, Desc.get?, Desc.fields] at *
  exact idCompatTransformAux_lookup_none fs v k hdk

/-- Transform an entry according to the descriptor: recursively apply
    `idCompatTransform` to nested messages, leave other entries unchanged. -/
def entryTransform (d : Desc) : (Int × Val) → (Int × Val)
  | (k, .msg v') =>
    match d.fields.lookup k with
    | some (.msg d') => (k, .msg (idCompatTransform d' v'))
    | _ => (k, .msg v')
  | kv => kv

end Pollux.InterParse
