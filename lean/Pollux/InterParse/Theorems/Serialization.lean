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

/-- Substitution principle for `Serializer.rep`: serializers that agree
    pointwise on a list produce the same encoding. -/
theorem serialRep_pointwise_eq {α : Type} {wfα : α → Prop}
    (ser1 ser2 : Serializer (List UInt8) α wfα) (xs : List α) :
    (∀ x ∈ xs, ser1 x = ser2 x) →
    Serializer.rep ser1 xs = Serializer.rep ser2 xs := by
  intro h
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : ser1 hd = ser2 hd := h hd List.mem_cons_self
    have htl : ∀ x ∈ tl, ser1 x = ser2 x := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ih' := ih htl
    show Serializer.rep' ser1 (hd :: tl) = Serializer.rep' ser2 (hd :: tl)
    unfold Serializer.rep'
    rw [hhd]
    show (match ser2 hd, Serializer.rep' ser1 tl with | _, _ => _) =
         (match ser2 hd, Serializer.rep' ser2 tl with | _, _ => _)
    have ih'' : Serializer.rep' ser1 tl = Serializer.rep' ser2 tl := ih'
    rw [ih'']

/-- `valList d ((k, v) :: m.vals)`-style decomposition: when `k` is smaller
    than all keys in `m.vals`, inserting `k` at the head and then filtering
    is the same as filtering and (conditionally) prepending `(k, v)`. -/
private theorem valList_insert_first (d : Desc) (k : Int) (v : Val) (m : Value) :
    (∀ kv ∈ m.vals, k < kv.1) →
    valList d (m.insert k v) =
      (if valListFilterP d (k, v) then (k, v) :: valList d m else valList d m) := by
  intro hfst
  have hins : (m.insert k v).vals = (k, v) :: m.vals := by
    rcases m with ⟨vs⟩
    show Value.sortedInsert k v vs = (k, v) :: vs
    cases vs with
    | nil => rfl
    | cons hd tl =>
      have h1 : k < hd.1 := hfst hd List.mem_cons_self
      simp [Value.sortedInsert, h1]
  unfold valList
  rw [hins]
  rw [List.filter_cons]

/-- `serialVal` is invariant under changing the recursive serializer if the
    two serializers agree on the inner `Value` for nested-message entries. -/
private theorem serialVal_self_eq_pointwise
    (self1 self2 : ∀ d : Desc, Serializer (List UInt8) Value (valueWf d))
    (d : Desc) (k : Int) (val : Val)
    (h : ∀ d' v', val = Val.msg v' → self1 d' v' = self2 d' v') :
    serialVal self1 d (k, val) = serialVal self2 d (k, val) := by
  unfold serialVal
  cases hf : d.fields.lookup k with
  | none => rfl
  | some f =>
    cases f with
    | bool => rfl
    | int  => rfl
    | msg d' =>
      cases val with
      | bool _ => rfl
      | int _  => rfl
      | missing => rfl
      | msg v' =>
        have hself : self1 d' v' = self2 d' v' := h d' v' rfl
        unfold Serializer.map Serializer.opt Serializer.concat Serializer.partMap
               Serializer.len'
        simp only [hself]

/-- Key unfolding: the recursive serializer `serialValue d v` reduces to one
    step of `Serializer.rep` where the inner serializer recurses via
    `serialValue` itself.  This works because every recursive call inside
    `serialVal` operates on a sub-value of `v`, hence has strictly smaller
    `valueDepth`. -/
private theorem serialValue_eq_rep (d : Desc) (v : Value) :
    serialValue d v =
    Serializer.rep (serialVal serialValue d) (valList d v) := by
  unfold serialValue Serializer.recursiveState
  rw [serializer_recurSt_unfold serialValue' valueDepth d v]
  show Serializer.rep (serialVal _ d) (valList d v) =
       Serializer.rep (serialVal serialValue d) (valList d v)
  apply serialRep_pointwise_eq
  intro kv hkv
  obtain ⟨k', val⟩ := kv
  apply serialVal_self_eq_pointwise
  intro d' v' heq
  subst heq
  -- `(k', .msg v') ∈ valList d v ⊆ v.vals`, so `valueDepth v' < valueDepth v`.
  have hin : (k', Val.msg v') ∈ v.vals := by
    have := List.mem_filter.mp hkv
    exact this.1
  -- Depth bound directly from `mem`, sidestepping `Value.get?`.
  have hdep : valueDepth v' < valueDepth v := by
    rcases v with ⟨vs⟩
    show valueDepth v' < valueDepthList vs 0
    have h_depth : ∀ (l : List (Int × Val)) (acc : Nat),
        (k', Val.msg v') ∈ l →
        valueDepthList l acc ≥ Nat.max acc (valueDepth v' + 1) := by
      intro l acc hmem
      induction l generalizing acc with
      | nil => exact (List.not_mem_nil hmem).elim
      | cons hd tl ih =>
        cases hmem with
        | head =>
          show valueDepthList ((k', Val.msg v') :: tl) acc ≥ _
          unfold valueDepthList valueDepthFold
          have h_mono : ∀ (l : List (Int × Val)) (acc : Nat),
              valueDepthList l acc ≥ acc := by
            intro l acc
            induction l generalizing acc with
            | nil => exact Nat.le_refl _
            | cons hd tl ih =>
              show valueDepthList (hd :: tl) acc ≥ acc
              unfold valueDepthList
              calc acc ≤ valueDepthFold hd.2 acc := by
                      cases hd.2 <;> simp [valueDepthFold]
                _ ≤ valueDepthList tl (valueDepthFold hd.2 acc) := ih _
          refine Nat.max_le.mpr ⟨?_, ?_⟩
          · exact le_trans (Nat.le_max_left _ _) (h_mono tl _)
          · exact lt_of_lt_of_le (Nat.lt_succ_self _)
              (le_trans (Nat.le_max_right _ _) (h_mono tl _))
        | tail _ htl =>
          show valueDepthList (hd :: tl) acc ≥ _
          unfold valueDepthList
          exact le_trans (Nat.max_le.mpr
            ⟨by cases hd.2 <;> simp [valueDepthFold], by
              cases hd.2 <;> simp [valueDepthFold]⟩)
            (ih (valueDepthFold hd.2 acc) htl)
    have := h_depth vs 0 hin
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (Nat.le_max_right _ _) this)
  -- Now show `(if valueDepth v' < valueDepth v then ... else error) = serialValue d' v'`.
  show (if valueDepth v' < valueDepth v then
         Serializer.recurSt serialValue' valueDepth d' v'
        else _) = serialValue d' v'
  rw [if_pos hdep]
  rfl

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
      enc = Input.app encV encRest) := by
  intro _hnone hfst
  rw [serialValue_eq_rep d (m.insert k v), serialValue_eq_rep d m]
  rw [valList_insert_first d k v m hfst]
  by_cases hf : valListFilterP d (k, v) = true
  · -- Filter passes: cons case
    rw [if_pos hf, serialRep_first_inversion]
    constructor
    · rintro ⟨ev, er, hv, hr, hen⟩; exact ⟨ev, er, hr, hv, hen⟩
    · rintro ⟨ev, er, hr, hv, hen⟩; exact ⟨ev, er, hv, hr, hen⟩
  · -- Filter fails: no cons; serialVal serialValue d (k, v) = .success () []
    rw [if_neg hf]
    have hempty : serialVal serialValue d (k, v) = .success () [] := by
      simp only [Bool.not_eq_true] at hf
      unfold valListFilterP at hf
      unfold serialVal
      cases hkf : d.fields.lookup k with
      | none => rfl
      | some f =>
        rw [hkf] at hf
        -- In the .missing case for v, serialVal reduces to .success () [].
        -- In the other cases, the filter would have been true → contradiction.
        cases f <;> cases v <;>
          first
            | (unfold Serializer.map Serializer.opt; rfl)
            | (exfalso; simp_all)
    constructor
    · intro h
      refine ⟨[], enc, h, hempty, ?_⟩
      show enc = [] ++ enc
      rfl
    · rintro ⟨ev, er, hr, hv, hen⟩
      rw [hempty] at hv
      -- hv : .success () [] = .success () ev, so ev = [].
      have hev : ev = [] := by
        injection hv with _ heq
        exact heq.symm
      subst hev
      show (serialVal serialValue d).rep (valList d m) = .success () enc
      rw [hr]
      show Result.success () er = Result.success () enc
      rw [show enc = er from by rw [hen]; rfl]

/-! ## Encoding length lemmas -/

/-- A boolean's serialized length is always 4 bytes. -/
private theorem boolLength (b : Bool) (enc : List UInt8) :
    serialBool b = .success () enc → Input.length enc = 4 := by
  intro h
  unfold serialBool at h
  cases b <;> exact z32Length _ enc h

/-- `Serializer.rep` length is the sum of per-element lengths, when each
    succeeds with a length given by `lenFn`. -/
private theorem rep_length_eq {α : Type} {wfα : α → Prop}
    (ser : Serializer (List UInt8) α wfα) (lenFn : α → Nat) :
    ∀ (xs : List α) (enc : List UInt8),
    (∀ x ∈ xs, ∀ encX, ser x = .success () encX → Input.length encX = lenFn x) →
    Serializer.rep ser xs = .success () enc →
    Input.length enc = (xs.map lenFn).sum := by
  intro xs
  induction xs with
  | nil =>
    intro enc _ hser
    have : enc = [] := by
      show enc = (Input.default : List UInt8)
      injection hser with _ heq
      exact heq.symm
    subst this
    rfl
  | cons hd tl ih =>
    intro enc hper hser
    rw [serialRep_first_inversion] at hser
    obtain ⟨encH, encT, hH, hT, henc⟩ := hser
    have hlenH : Input.length encH = lenFn hd :=
      hper hd List.mem_cons_self _ hH
    have hper' : ∀ x ∈ tl, ∀ encX, ser x = .success () encX → Input.length encX = lenFn x :=
      fun x hx => hper x (List.mem_cons_of_mem _ hx)
    have hlenT := ih encT hper' hT
    subst henc
    show Input.length (Input.app encH encT) = ((hd :: tl).map lenFn).sum
    rw [Input.app_length]
    show Input.length encH + Input.length encT = lenFn hd + (tl.map lenFn).sum
    rw [hlenH, hlenT]

/-- `valueEncLen'List` accumulator linearity. -/
private theorem valueEncLen'List_linear (ds : List (Int × Field)) :
    ∀ (vs : List (Int × Val)) (acc : Nat),
    valueEncLen'List ds vs acc = valueEncLen'List ds vs 0 + acc := by
  intro vs
  induction vs with
  | nil => intro acc; show acc = 0 + acc; omega
  | cons hd tl ih =>
    intro acc
    obtain ⟨k, val⟩ := hd
    show valueEncLen'List ds tl (valueEncLen'Fold ds k val acc) =
         valueEncLen'List ds tl (valueEncLen'Fold ds k val 0) + acc
    rw [ih (valueEncLen'Fold ds k val acc), ih (valueEncLen'Fold ds k val 0)]
    have h := valueEncLen'Fold_linear ⟨ds⟩ k val acc
    simp only [Desc.fields] at h
    omega

/-- `valueEncLen'Fold` is zero on entries that fail the filter. -/
private theorem valueEncLen'Fold_zero_of_filterP_false
    (d : Desc) (k : Int) (val : Val) :
    valListFilterP d (k, val) = false →
    valueEncLen'Fold d.fields k val 0 = 0 := by
  intro hf
  unfold valListFilterP at hf
  unfold valueEncLen'Fold
  cases hkf : d.fields.lookup k with
  | none => rfl
  | some f =>
    rw [hkf] at hf
    cases f <;> cases val <;> simp_all

/-- Predicted-encoding length on a value's entries equals the sum over
    the *filtered* entries. -/
private theorem valueEncLen'List_eq_sum_filter (d : Desc) :
    ∀ (vs : List (Int × Val)),
    valueEncLen'List d.fields vs 0 =
      ((vs.filter (valListFilterP d)).map
        (fun kv => valueEncLen'Fold d.fields kv.1 kv.2 0)).sum := by
  intro vs
  induction vs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, val⟩ := hd
    show valueEncLen'List d.fields tl (valueEncLen'Fold d.fields k val 0) = _
    rw [valueEncLen'List_linear d.fields tl (valueEncLen'Fold d.fields k val 0)]
    rw [List.filter_cons]
    by_cases hf : valListFilterP d (k, val) = true
    · rw [if_pos hf]
      show valueEncLen'List d.fields tl 0 + valueEncLen'Fold d.fields k val 0 =
           ((((k, val) :: tl.filter (valListFilterP d)).map _).sum)
      simp [List.map_cons, List.sum_cons]
      rw [ih]
      omega
    · rw [if_neg hf]
      show valueEncLen'List d.fields tl 0 + valueEncLen'Fold d.fields k val 0 = _
      simp only [Bool.not_eq_true] at hf
      rw [valueEncLen'Fold_zero_of_filterP_false d k val hf]
      rw [Nat.add_zero]
      exact ih

/-- Depth bound for nested values: `(z, .msg v') ∈ vs` implies
    `valueDepth v' < valueDepthList vs 0`. -/
private theorem valueDepth_msg_in_list (z : Int) (v' : Value) (vs : List (Int × Val)) :
    (z, Val.msg v') ∈ vs → valueDepth v' < valueDepthList vs 0 := by
  intro hin
  have h_mono : ∀ (l : List (Int × Val)) (acc : Nat),
      valueDepthList l acc ≥ acc := by
    intro l acc
    induction l generalizing acc with
    | nil => exact Nat.le_refl _
    | cons hd tl ih =>
      show valueDepthList (hd :: tl) acc ≥ acc
      unfold valueDepthList
      calc acc ≤ valueDepthFold hd.2 acc := by
              cases hd.2 <;> simp [valueDepthFold]
        _ ≤ valueDepthList tl (valueDepthFold hd.2 acc) := ih _
  have h_depth : ∀ (l : List (Int × Val)) (acc : Nat),
      (z, Val.msg v') ∈ l →
      valueDepthList l acc ≥ Nat.max acc (valueDepth v' + 1) := by
    intro l acc hmem
    induction l generalizing acc with
    | nil => exact (List.not_mem_nil hmem).elim
    | cons hd tl ih =>
      cases hmem with
      | head =>
        show valueDepthList ((z, Val.msg v') :: tl) acc ≥ _
        unfold valueDepthList valueDepthFold
        refine Nat.max_le.mpr ⟨?_, ?_⟩
        · exact le_trans (Nat.le_max_left _ _) (h_mono tl _)
        · exact lt_of_lt_of_le (Nat.lt_succ_self _)
            (le_trans (Nat.le_max_right _ _) (h_mono tl _))
      | tail _ htl =>
        show valueDepthList (hd :: tl) acc ≥ _
        unfold valueDepthList
        exact le_trans (Nat.max_le.mpr
          ⟨by cases hd.2 <;> simp [valueDepthFold], by
            cases hd.2 <;> simp [valueDepthFold]⟩)
          (ih (valueDepthFold hd.2 acc) htl)
  have := h_depth vs 0 hin
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_trans (Nat.le_max_right _ _) this)

/-- Encoding length matches the predicted length. -/
theorem valueEncLength_length (v : Value) (d : Desc) (enc : List UInt8) :
    valid' d v →
    serialValue d v = .success () enc →
    Input.length enc = valueEncLen' d v := by
  -- Strong induction on `valueDepth v` via an auxiliary form.
  suffices h : ∀ (n : Nat) (v : Value) (d : Desc) (enc : List UInt8),
      valueDepth v < n →
      valid' d v →
      serialValue d v = .success () enc →
      Input.length enc = valueEncLen' d v from
    h (valueDepth v + 1) v d enc (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero =>
    intro _v _d _enc hdep
    exact absurd hdep (Nat.not_lt_zero _)
  | succ k ih =>
    intro v d enc hdep hvalid hser
    -- Reduce both sides to forms over `valList d v`.
    have hencLenEq : valueEncLen' d v = valueEncLen'List d.fields v.vals 0 := by
      rcases d with ⟨fs⟩; rcases v with ⟨vs⟩; rfl
    rw [serialValue_eq_rep d v] at hser
    rw [hencLenEq, valueEncLen'List_eq_sum_filter d v.vals]
    apply rep_length_eq (serialVal serialValue d)
      (fun kv => valueEncLen'Fold d.fields kv.1 kv.2 0)
      (valList d v) enc _ hser
    -- Per-entry: each filtered entry's encoding has the predicted length.
    intro x hx encX hencX
    obtain ⟨z, val⟩ := x
    have hmem : (z, val) ∈ v.vals := (List.mem_filter.mp hx).1
    have hfilt : valListFilterP d (z, val) = true := (List.mem_filter.mp hx).2
    have hvalEntry : valid'Fold d.fields z val True := by
      rcases d with ⟨fs⟩
      rcases v with ⟨vs⟩
      exact valid'FoldList_mem fs vs z val hvalid hmem
    -- Beta-reduce the goal.
    change Input.length encX = valueEncLen'Fold d.fields z val 0
    -- Case split on `val`.
    cases val with
    | missing =>
      exfalso
      unfold valListFilterP at hfilt
      cases hf' : d.fields.lookup z with
      | none => rw [hf'] at hfilt; simp at hfilt
      | some _ => rw [hf'] at hfilt; simp at hfilt
    | bool b =>
      have hlk : d.fields.lookup z = some .bool := by
        unfold valid'Fold at hvalEntry
        exact hvalEntry.1
      have hencX' : Serializer.concat serialUnsigned
          (Serializer.partMap serialBool
            (fun v => match v with | .bool b => some b | _ => none)
            "Expected Boolean") (z, Val.bool b) = .success () encX := by
        unfold serialVal at hencX
        rw [hlk] at hencX
        unfold Serializer.map Serializer.opt at hencX
        exact hencX
      rw [serialConcat_inversion] at hencX'
      obtain ⟨encT, encR, hT, hR, henc⟩ := hencX'
      have hlenT : encT.length = 1 := unsignedLength _ _ hT
      have hlenR : encR.length = 4 := by
        unfold Serializer.partMap at hR
        simp only at hR
        exact boolLength _ _ hR
      subst henc
      show (encT ++ encR).length = valueEncLen'Fold d.fields z (Val.bool b) 0
      rw [List.length_append, hlenT, hlenR]
      unfold valueEncLen'Fold
      rw [hlk]
    | int n' =>
      have hlk : d.fields.lookup z = some .int := by
        unfold valid'Fold at hvalEntry
        exact hvalEntry.1
      have hencX' : Serializer.concat serialUnsigned
          (Serializer.partMap serialZ32
            (fun v => match v with | .int z => some z | _ => none)
            "Expected Integer") (z, Val.int n') = .success () encX := by
        unfold serialVal at hencX
        rw [hlk] at hencX
        unfold Serializer.map Serializer.opt at hencX
        exact hencX
      rw [serialConcat_inversion] at hencX'
      obtain ⟨encT, encR, hT, hR, henc⟩ := hencX'
      have hlenT : encT.length = 1 := unsignedLength _ _ hT
      have hlenR : encR.length = 4 := by
        unfold Serializer.partMap at hR
        simp only at hR
        exact z32Length _ _ hR
      subst henc
      show (encT ++ encR).length = valueEncLen'Fold d.fields z (Val.int n') 0
      rw [List.length_append, hlenT, hlenR]
      unfold valueEncLen'Fold
      rw [hlk]
    | msg v' =>
      have hex : ∃ d', d.fields.lookup z = some (.msg d') ∧ valid' d' v' := by
        unfold valid'Fold at hvalEntry
        exact hvalEntry.1
      obtain ⟨d', hlk, hvalid'⟩ := hex
      -- `v'` has strictly smaller depth than `v`, so IH applies.
      have hdepLt : valueDepth v' < valueDepth v := by
        rcases v with ⟨vs⟩
        exact valueDepth_msg_in_list z v' vs hmem
      have hdepLt' : valueDepth v' < k :=
        lt_of_lt_of_le hdepLt (Nat.le_of_lt_succ hdep)
      have hencX' : Serializer.concat serialUnsigned
          (Serializer.partMap (Serializer.len' serialNatStrict (serialValue d'))
            (fun v => match v with | .msg x => some x | _ => none)
            "Expected nested message") (z, Val.msg v') = .success () encX := by
        unfold serialVal at hencX
        rw [hlk] at hencX
        unfold Serializer.map Serializer.opt at hencX
        exact hencX
      rw [serialConcat_inversion] at hencX'
      obtain ⟨encT, encR, hT, hR, henc⟩ := hencX'
      have hlenT : encT.length = 1 := unsignedLength _ _ hT
      have hR' : Serializer.len' serialNatStrict (serialValue d') v' =
          .success () encR := by
        unfold Serializer.partMap at hR
        simp only at hR
        exact hR
      rw [serialLen'_inversion] at hR'
      obtain ⟨encL, encP, hL, hP, hR_eq⟩ := hR'
      have hlenL : encL.length = 1 := natStrictLength _ _ hL
      have hlenP : encP.length = valueEncLen' d' v' :=
        ih v' d' encP hdepLt' hvalid' hP
      subst hR_eq
      subst henc
      have hRHS : valueEncLen'Fold d.fields z (Val.msg v') 0 =
          2 + valueEncLen' d' v' := by
        unfold valueEncLen'Fold; rw [hlk]
      show (encT ++ (encL ++ encP)).length =
        valueEncLen'Fold d.fields z (Val.msg v') 0
      rw [List.length_append, List.length_append, hlenT, hlenL, hlenP, hRHS]
      omega

end Pollux.InterParse
