/-
  Pollux.InterParse.Theorems.Serialization — Serialization helper lemmas:
  `willEncode` non-emptiness, weakening under `erase`, the `serialValue`
  inversion lemma for insert, and the encoding-length theorem.
-/
import Pollux.Parse.Input
import Pollux.Parse.Theorems
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer
import Pollux.InterParse.Theorems.Primitives
import Pollux.InterParse.Theorems.Validity

namespace Pollux.InterParse

open Pollux.Parse
open Pollux.Parse.Theorems

/-! ## Serialization correctness helper lemmas -/

theorem willEncode_nonEmpty (d : Desc) (k : Int) (v : Val) (enc : List UInt8) :
    willEncode d (k, v) →
    serialVal serialValue d (k, v) = .success () enc →
    Input.length enc > 0 := by
  rintro ⟨f, hf, hwfd⟩ hser
  -- `valWf d (k, v)` reduces to `valWfFold d.fields k v True`.
  have hwfd : valWfFold d.fields k v True := hwfd
  unfold valWfFold at hwfd
  rw [hf] at hwfd
  -- Unfold the serializer; the body matches on `d.fields.lookup k`.
  unfold serialVal at hser
  rw [hf] at hser
  -- Helper: given `serialVal` reduces to `concat serialUnsigned _`, the encoding
  -- contributed by `serialUnsigned k` is one byte, so the total is at least 1.
  have aux : ∀ (β : Type) (wfβ : β → Prop) (b : β) (right : Serializer (List UInt8) β wfβ),
      Serializer.concat serialUnsigned right (k, b) = .success () enc →
      Input.length enc > 0 := by
    intro β wfβ b right h
    rw [serialConcat_inversion] at h
    obtain ⟨encL, encR, hL, _hR, henc⟩ := h
    have hLlen : encL.length = 1 := unsignedLength k encL hL
    subst henc
    show (encL ++ encR).length > 0
    rw [List.length_append, hLlen]; omega
  -- Case split on f and v.
  cases f <;> cases v <;>
    first
      | exact hwfd.elim
      | (simp only [Serializer.map, Serializer.opt] at hser
         exact aux _ _ _ _ hser)

/-- `field_val_type_match` for serializer error data. -/
def fieldValTypeMatch (f : Field) (v : Val) : Prop :=
  match f, v with
  | .bool, .bool _ | .int, .int _ | .msg _, .msg _ => True
  | _, _ => False

/-! ## Well-formedness -/

theorem valueWf_weaken (v : Value) (d : Desc) (k : Int) :
    d.WF → v.get? k = none → (valueWf d v ↔ valueWf (d.erase k) v) := by
  intro hwf hno
  -- All keys in `v.vals` differ from `k`.
  have h_keys_ne : ∀ kv ∈ v.vals, kv.1 ≠ k := by
    intro kv hkv hk
    unfold Value.get? at hno
    rw [List.lookup_eq_none_iff] at hno
    have := hno kv hkv
    -- this : k != kv.1 (as Prop, i.e. (k != kv.1) = true)
    simp_all
  -- For any key `k' ≠ k`, lookup in `d.fields` and `(d.erase k).fields` agree.
  have h_lookup_eq : ∀ k', k' ≠ k → (d.erase k).fields.lookup k' = d.fields.lookup k' := by
    intro k' hne
    have := Desc.get?_erase_ne d k k' hwf (Ne.symm hne)
    unfold Desc.get? at this
    exact this
  -- Destructure to expose underlying lists, then induct.
  rcases v with ⟨vs⟩
  rcases d with ⟨fs⟩
  simp only [Value.vals] at h_keys_ne
  -- Specialize the lookup-equality helper to the destructured form.
  have h_lookup_eq' : ∀ k', k' ≠ k → (Desc.sortedErase k fs).lookup k' = fs.lookup k' := by
    intro k' hne
    have := h_lookup_eq k' hne
    simpa [Desc.fields, Desc.erase] using this
  -- Generalize the accumulator and prove by induction.
  suffices h : ∀ (vs : List (Int × Val)) (acc : Prop),
      (∀ kv ∈ vs, kv.1 ≠ k) →
      (valWfFoldList fs vs acc ↔ valWfFoldList (Desc.sortedErase k fs) vs acc) by
    -- Both sides reduce to `valWfFoldList _ vs True` since both `Desc` and `Value` are now in
    -- constructor form.
    show valWfFoldList fs vs True ↔ valWfFoldList (Desc.sortedErase k fs) vs True
    exact h vs True h_keys_ne
  intro vs acc hkeys
  induction' vs with hd tl ih generalizing acc
  · exact Iff.rfl
  · obtain ⟨k', val⟩ := hd
    have hne : k' ≠ k := hkeys (k', val) (List.mem_cons_self)
    have hne_keys_tl : ∀ kv ∈ tl, kv.1 ≠ k :=
      fun kv hkv => hkeys kv (List.mem_cons_of_mem _ hkv)
    -- The two folds will agree if `valWfFold` agrees on the head.
    have hfold_eq : valWfFold fs k' val acc
                   = valWfFold (Desc.sortedErase k fs) k' val acc := by
      unfold valWfFold
      rw [h_lookup_eq' k' hne]
    show valWfFoldList fs tl (valWfFold fs k' val acc)
       ↔ valWfFoldList (Desc.sortedErase k fs) tl (valWfFold (Desc.sortedErase k fs) k' val acc)
    rw [hfold_eq]
    exact ih _ hne_keys_tl

theorem willEncode_weaken (kv : Int × Val) (d : Desc) (k : Int) (v : Value) :
    d.WF →
    kv ∈ valList (d.erase k) v →
    (willEncode d kv ↔ willEncode (d.erase k) kv) := by
  intro hwf hin
  -- Membership in `valList (d.erase k) v` implies the filter holds.
  have hfilt : valListFilterP (d.erase k) kv = true := by
    unfold valList at hin
    exact (List.mem_filter.mp hin).2
  -- The filter requires the lookup to be `some _` and val ≠ missing.
  have hlk_erase : ∃ f, (d.erase k).fields.lookup kv.1 = some f := by
    unfold valListFilterP at hfilt
    -- Make the lookup non-`none` from the filter, then extract a witness.
    have h_ne_none : (d.erase k).fields.lookup kv.1 ≠ none := by
      intro hnone
      rw [hnone] at hfilt
      simp at hfilt
    exact Option.ne_none_iff_exists'.mp h_ne_none
  -- Show kv.1 ≠ k.
  have hne : kv.1 ≠ k := by
    intro heq
    obtain ⟨f, hf⟩ := hlk_erase
    rw [heq] at hf
    have := Desc.get?_erase_same d k hwf
    unfold Desc.get? at this
    rw [this] at hf
    cases hf
  -- Now, lookup in `d.fields` and `(d.erase k).fields` agree at `kv.1`.
  have hlk_eq : (d.erase k).fields.lookup kv.1 = d.fields.lookup kv.1 := by
    have := Desc.get?_erase_ne d k kv.1 hwf (Ne.symm hne)
    unfold Desc.get? at this
    exact this
  -- And `valWf d kv ↔ valWf (d.erase k) kv`.
  have hvwf_eq : valWf d kv = valWf (d.erase k) kv := by
    unfold valWf valWfFold
    rw [hlk_eq]
  -- Conclude.
  unfold willEncode
  constructor
  · rintro ⟨f, hf, hwfd⟩
    refine ⟨f, ?_, ?_⟩
    · rw [hlk_eq, hf]
    · rw [← hvwf_eq]; exact hwfd
  · rintro ⟨f, hf, hwfd⟩
    refine ⟨f, ?_, ?_⟩
    · rw [← hlk_eq, hf]
    · rw [hvwf_eq]; exact hwfd

/-! ## Serializer inversion lemmas -/

/-- Inversion for `serialValue` of an inserted key.  Requires `k` to be the
    smallest key in `m` (in the Lean sorted-list representation, this means
    `(m.insert k v).vals = (k, v) :: m.vals`).  This mirrors Rocq's
    `SerialValueInversion`, which has the analogous `map_first_key` precondition.

    Without this hypothesis the encoding factors as
    `encPrefix ++ encV ++ encSuffix`, not `encV ++ encRest`. -/
theorem serialValueInversion (d : Desc) (k : Int) (v : Val) (m : Value)
    (enc : List UInt8) :
    m.get? k = none →
    (∀ kv ∈ m.vals, k < kv.1) →
    (serialValue d (m.insert k v) = .success () enc ↔
    ∃ encV encRest,
      serialValue d m = .success () encRest ∧
      serialVal serialValue d (k, v) = .success () encV ∧
      enc = Input.app encV encRest) := by sorry

/-- Encoding length matches the predicted length. -/
theorem valueEncLength_length (v : Value) (d : Desc) (enc : List UInt8) :
    valid' d v →
    serialValue d v = .success () enc →
    Input.length enc = valueEncLen' d v := by sorry

end Pollux.InterParse
