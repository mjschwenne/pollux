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

/-- `valWfFold` is monotone in `acc`: it can be split into a closed-form
    "per-entry" predicate (`valWfFold _ _ _ True`) and `acc`. -/
private theorem valWfFold_split (fs : List (Int × Field)) (k : Int) (v : Val)
    (acc : Prop) :
    valWfFold fs k v acc ↔ valWfFold fs k v True ∧ acc := by
  unfold valWfFold
  cases fs.lookup k with
  | none =>
    simp only []
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | some f =>
    cases f <;> cases v <;>
      first
        | exact ⟨fun h => ⟨h, trivial⟩, fun h => h.elim⟩
        | (simp only [and_assoc]; tauto)

/-- `valWfFoldList fs vs acc` decomposes into per-entry constraints AND `acc`. -/
private theorem valWfFoldList_decomp (fs : List (Int × Field)) :
    ∀ (vs : List (Int × Val)) (acc : Prop),
    valWfFoldList fs vs acc ↔
      (∀ kv : Int × Val, kv ∈ vs → valWfFold fs kv.1 kv.2 True) ∧ acc := by
  intro vs
  induction vs with
  | nil =>
    intro acc
    show acc ↔
      (∀ kv : Int × Val, kv ∈ ([] : List (Int × Val)) → valWfFold fs kv.1 kv.2 True) ∧ acc
    simp
  | cons hd tl ih =>
    intro acc
    obtain ⟨k, v⟩ := hd
    show valWfFoldList fs tl (valWfFold fs k v acc) ↔
      (∀ kv : Int × Val, kv ∈ ((k, v) :: tl) → valWfFold fs kv.1 kv.2 True) ∧ acc
    rw [ih (valWfFold fs k v acc), valWfFold_split fs k v acc]
    constructor
    · rintro ⟨htl, hhd, hacc⟩
      refine ⟨?_, hacc⟩
      intro kv hkv
      cases List.mem_cons.mp hkv with
      | inl heq => subst heq; exact hhd
      | inr htl' => exact htl _ htl'
    · rintro ⟨hall, hacc⟩
      refine ⟨?_, hall (k, v) List.mem_cons_self, hacc⟩
      intro kv hkv
      exact hall kv (List.mem_cons_of_mem _ hkv)

/-- Helper: extract `valWfFold` for a specific entry from `valueWf`. -/
private theorem valueWf_mem (d : Desc) (v : Value) :
    valueWf d v →
    ∀ (k : Int) (val : Val), (k, val) ∈ v.vals →
    valWfFold d.fields k val True := by
  intro hwf k val hmem
  rcases d with ⟨fs⟩
  rcases v with ⟨vs⟩
  have hwf' : valWfFoldList fs vs True := hwf
  exact ((valWfFoldList_decomp fs vs True).mp hwf').1 (k, val) hmem

/-- Convert `repWf` to a universal quantifier. -/
private theorem repWf_of_forall {α : Type} (wf : α → Prop) :
    ∀ (l : List α),
    (∀ x ∈ l, wf x) → Serializer.repWf wf l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons hd tl ih =>
    intro h
    refine ⟨h hd List.mem_cons_self, ih ?_⟩
    intro x hx; exact h x (List.mem_cons_of_mem _ hx)

theorem parseOk_wf (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ → valueWf d v →
    Serializer.repWf (willEncode d) (valList d v) := by
  intro hsc hwf
  obtain ⟨_hd_wf, hv_wf⟩ := sc_implies_wf d v hsc
  apply repWf_of_forall
  intro kv hkv
  obtain ⟨k, val⟩ := kv
  -- (k, val) ∈ valList d v ⊆ v.vals
  have hmem : (k, val) ∈ v.vals := (List.mem_filter.mp hkv).1
  -- v.get? k = some val (from membership and `v.WF`).
  have hget : v.get? k = some val := valList_elem_of v d k val hv_wf hkv
  -- Field exists and is type-matched (from `SchemaCorrect`).
  obtain ⟨f, hf, _hmatch⟩ := sc_implies_val_in_desc_typed d v hsc k val hget
  refine ⟨f, hf, ?_⟩
  -- valWf d (k, val) — extract from valueWf via `valueWf_mem`.
  show valWfFold d.fields k val True
  exact valueWf_mem d v hwf k val hmem

/-! ## Top-level correctness theorem

This is the main result: for any schema-correct value, serializing with
`serialValue` and then parsing with `parseValue` recovers a compatible value. -/

theorem interParseOk (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ →
    LimitParseOkCompat'' Compatible parseValue serialValue d d v := by sorry

end Pollux.InterParse
