/-
  Pollux.InterParse.Theorems.CompatTransform — the cross-descriptor round-trip
  transform `compatTransform d₁ d₂ v`: the value obtained by serializing `v`
  under the writer's descriptor `d₁` and parsing the result under the reader's
  descriptor `d₂`.

  This is the two-descriptor analogue of `idCompatTransform`, and it is defined
  the same way: a structural recursion over the *reader's* field list, reading
  the writer's descriptor and the writer's value by key lookup.  The four
  scalar combinations reflect the shared four-byte little-endian encoding of
  `bool` and `int`; a nested message recurses with both descriptors.
-/
import Pollux.InterParse.Theorems.IdCompatible
import Pollux.InterParse.Theorems.IdCompatibleHelpers
import Pollux.InterParse.Theorems.ValList
import Pollux.InterParse.Theorems.Compatible
import Mathlib

namespace Pollux.InterParse

/-! ## The transform -/

mutual
/-- Build the reader's entry list, one entry per field of the reader's
    descriptor. -/
def compatTransformAux : List (Int × Field) → Desc → Value → List (Int × Val)
  | [], _, _ => []
  | (k, f₂) :: rest, d₁, v =>
    let resultVal := match f₂, d₁.get? k, v.get? k with
      | Field.bool, some Field.bool, some (Val.bool b) => Val.bool b
      | Field.int, some Field.bool, some (Val.bool b) => Val.int (if b then 1 else 0)
      | Field.bool, some Field.int, some (Val.int z) => Val.bool (decide (0 < z))
      | Field.int, some Field.int, some (Val.int z) => Val.int z
      | Field.msg d₂', some (Field.msg d₁'), some (Val.msg v') =>
        Val.msg (compatTransform d₁' d₂' v')
      | _, _, _ => Val.missing
    (k, resultVal) :: compatTransformAux rest d₁ v
/-- The value a round trip from the writer's descriptor `d₁` to the reader's
    descriptor `d₂` produces. -/
def compatTransform : Desc → Desc → Value → Value
  | d₁, .mk fs₂, v => .mk (compatTransformAux fs₂ d₁ v)
end

/-- Reinterpretation of a single serialized value: the writer's field type is
    `of₁`, the reader's is `of₂`. -/
def compatVal (of₂ of₁ : Option Field) (val : Val) : Val :=
  match of₂, of₁, val with
  | some Field.bool, some Field.bool, Val.bool b => Val.bool b
  | some Field.int, some Field.bool, Val.bool b => Val.int (if b then 1 else 0)
  | some Field.bool, some Field.int, Val.int z => Val.bool (decide (0 < z))
  | some Field.int, some Field.int, Val.int z => Val.int z
  | some (Field.msg d₂'), some (Field.msg d₁'), Val.msg v' =>
    Val.msg (compatTransform d₁' d₂' v')
  | _, _, _ => Val.missing

/-- The cross-descriptor analogue of `entryTransform`: the parsed entry the
    reader obtains from a serialized entry of the writer. -/
def compatEntryTransform (d₁ d₂ : Desc) (kv : Int × Val) : Int × Val :=
  (kv.1, compatVal (d₂.get? kv.1) (d₁.get? kv.1) kv.2)

@[simp] theorem compatEntryTransform_fst (d₁ d₂ : Desc) (kv : Int × Val) :
    (compatEntryTransform d₁ d₂ kv).1 = kv.1 := rfl

/-- The head entry of `compatTransformAux`, expressed with `compatVal`. -/
theorem compatTransformAux_cons (k : Int) (f₂ : Field)
    (rest : List (Int × Field)) (d₁ : Desc) (v : Value) :
    compatTransformAux ((k, f₂) :: rest) d₁ v =
      (k, (match v.get? k with
            | some val => compatVal (some f₂) (d₁.get? k) val
            | none => Val.missing)) :: compatTransformAux rest d₁ v := by
  conv_lhs => unfold compatTransformAux
  simp only []
  cases hv : v.get? k with
  | none => cases f₂ <;> cases hd : d₁.get? k <;> simp
  | some val =>
    cases f₂ <;> cases val <;> cases hd : d₁.get? k <;>
      simp [compatVal] <;>
      rename_i f <;> cases f <;> simp

/-- `compatTransformAux_cons` when the writer's value has an entry at the key. -/
theorem compatTransformAux_cons_some (k : Int) (f₂ : Field)
    (rest : List (Int × Field)) (d₁ : Desc) (v : Value) (val : Val)
    (h : v.get? k = some val) :
    compatTransformAux ((k, f₂) :: rest) d₁ v =
      (k, compatVal (some f₂) (d₁.get? k) val) :: compatTransformAux rest d₁ v := by
  rw [compatTransformAux_cons, h]

/-- `compatTransformAux_cons` when the writer's value has no entry at the key. -/
theorem compatTransformAux_cons_none (k : Int) (f₂ : Field)
    (rest : List (Int × Field)) (d₁ : Desc) (v : Value)
    (h : v.get? k = none) :
    compatTransformAux ((k, f₂) :: rest) d₁ v =
      (k, Val.missing) :: compatTransformAux rest d₁ v := by
  rw [compatTransformAux_cons, h]

/-! ## Basic properties -/

/-- The keys of the transform output are exactly the reader's keys. -/
theorem compatTransformAux_keys (fs : List (Int × Field)) (d₁ : Desc) (v : Value) :
    (compatTransformAux fs d₁ v).map Prod.fst = fs.map Prod.fst := by
  induction fs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, f⟩ := hd
    rw [compatTransformAux_cons]
    simp [ih]

/-- The transform preserves sortedness of the reader's key list. -/
theorem compatTransformAux_sorted (fs : List (Int × Field)) (d₁ : Desc) (v : Value) :
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) fs →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) (compatTransformAux fs d₁ v) := by
  intro h
  induction fs with
  | nil => exact List.Pairwise.nil
  | cons hd tl ih =>
    obtain ⟨k, f⟩ := hd
    rw [compatTransformAux_cons, List.pairwise_cons]
    refine ⟨fun b hb => ?_, ih h.tail⟩
    have hmem : b.1 ∈ tl.map Prod.fst := by
      have := List.mem_map_of_mem (f := Prod.fst) hb
      rwa [compatTransformAux_keys] at this
    obtain ⟨c, hc, hc_eq⟩ := List.mem_map.mp hmem
    rw [← hc_eq]
    exact List.rel_of_pairwise_cons h hc

/-- The transformed value is well-formed whenever the reader's descriptor is. -/
theorem compatTransform_wf (d₁ d₂ : Desc) (v : Value) :
    d₂.WF → (compatTransform d₁ d₂ v).WF := by
  intro ⟨hSorted, hNodup⟩
  cases d₂ with | mk fs =>
  refine ⟨compatTransformAux_sorted fs d₁ v hSorted, ?_⟩
  show ((compatTransformAux fs d₁ v).map Prod.fst).Nodup
  rw [compatTransformAux_keys]
  exact hNodup

/-- Lookup in the transform at a key the reader's descriptor does not declare. -/
theorem compatTransformAux_lookup_none (fs : List (Int × Field)) (d₁ : Desc)
    (v : Value) (k : Int) :
    List.lookup k fs = none → List.lookup k (compatTransformAux fs d₁ v) = none := by
  induction fs with
  | nil => intro _; rfl
  | cons hd tl ih =>
    obtain ⟨k', f⟩ := hd
    intro hk
    rw [List.lookup_cons] at hk
    cases hbeq : (k == k') with
    | true => rw [hbeq] at hk; exact absurd hk (by simp)
    | false =>
      rw [hbeq] at hk
      rw [compatTransformAux_cons, List.lookup_cons, hbeq]
      exact ih hk

/-- Lookup in the transform at a key the reader's descriptor declares. -/
theorem compatTransformAux_lookup (fs : List (Int × Field)) (d₁ : Desc) (v : Value)
    (k : Int) (f : Field) :
    List.lookup k fs = some f →
    List.lookup k (compatTransformAux fs d₁ v) =
      some (match v.get? k with
            | some val => compatVal (some f) (d₁.get? k) val
            | none => Val.missing) := by
  induction fs with
  | nil => intro h; cases h
  | cons hd tl ih =>
    obtain ⟨k', f'⟩ := hd
    intro hk
    rw [List.lookup_cons] at hk
    cases hbeq : (k == k') with
    | true =>
      rw [hbeq] at hk
      have hkk : k = k' := by simpa using hbeq
      subst hkk
      have : f' = f := by simpa using hk
      subst this
      rw [compatTransformAux_cons, List.lookup_cons, hbeq]
    | false =>
      rw [hbeq] at hk
      rw [compatTransformAux_cons, List.lookup_cons, hbeq]
      exact ih hk

/-- `compatTransform` lookup at a key the reader declares. -/
theorem compatTransform_get?_some (d₁ d₂ : Desc) (v : Value) (k : Int) (f : Field) :
    d₂.get? k = some f →
    (compatTransform d₁ d₂ v).get? k =
      some (match v.get? k with
            | some val => compatVal (some f) (d₁.get? k) val
            | none => Val.missing) := by
  intro hd
  cases d₂ with | mk fs =>
  exact compatTransformAux_lookup fs d₁ v k f hd

/-- `compatTransform` lookup at a key the reader does not declare. -/
theorem compatTransform_get?_none (d₁ d₂ : Desc) (v : Value) (k : Int) :
    d₂.get? k = none → (compatTransform d₁ d₂ v).get? k = none := by
  intro hd
  cases d₂ with | mk fs =>
  exact compatTransformAux_lookup_none fs d₁ v k hd

/-! ## Recursive well-formedness at a key -/

/-- `fieldListAllWF` is inherited by the field found at any key. -/
theorem fieldListAllWF_lookup (fs : List (Int × Field)) (k : Int) (f : Field) :
    fieldListAllWF fs → fs.lookup k = some f → fieldAllWF f := by
  induction fs with
  | nil => intro _ h; cases h
  | cons hd tl ih =>
    obtain ⟨k', f'⟩ := hd
    intro hall hlk
    rw [List.lookup_cons] at hlk
    cases hbeq : (k == k') with
    | true =>
      rw [hbeq] at hlk
      have : f' = f := by simpa using hlk
      subst this
      exact fieldListAllWF_head hall
    | false =>
      rw [hbeq] at hlk
      exact ih (fieldListAllWF_tail hall) hlk

/-- `valListAllWF` is inherited by the value found at any key. -/
theorem valListAllWF_lookup (vs : List (Int × Val)) (k : Int) (val : Val) :
    valListAllWF vs → vs.lookup k = some val → valAllWF val := by
  induction vs with
  | nil => intro _ h; cases h
  | cons hd tl ih =>
    obtain ⟨k', val'⟩ := hd
    intro hall hlk
    rw [List.lookup_cons] at hlk
    cases hbeq : (k == k') with
    | true =>
      rw [hbeq] at hlk
      have : val' = val := by simpa using hlk
      subst this
      exact valListAllWF_head hall
    | false =>
      rw [hbeq] at hlk
      exact ih (valListAllWF_tail hall) hlk

/-- A nested descriptor of a recursively well-formed descriptor is itself
    recursively well-formed. -/
theorem descAllWF_nested (d : Desc) (k : Int) (d' : Desc) :
    d.AllWF → d.get? k = some (.msg d') → d'.AllWF := by
  intro hd hk
  have h := fieldListAllWF_lookup d.fields k (.msg d') hd.2 hk
  cases d' with | mk fs => exact ⟨h.1, h.2⟩

/-- A nested value of a recursively well-formed value is itself recursively
    well-formed. -/
theorem valueAllWF_nested (v : Value) (k : Int) (v' : Value) :
    v.AllWF → v.get? k = some (.msg v') → v'.AllWF := by
  intro hv hk
  have h := valListAllWF_lookup v.vals k (.msg v') hv.2 hk
  cases v' with | mk vs => exact ⟨h.1, h.2⟩

/-! ## The bridge between parsing and the transform

  The parser produces `(valList d₁ v).map (compatEntryTransform d₁ d₂)`, which
  `listToValue d₂` then merges.  This section shows the result is exactly
  `compatTransform d₁ d₂ v`. -/

/-- Lookup in the reinterpreted entry list. -/
theorem lookup_map_compatEntryTransform (d₁ d₂ : Desc) (vs : List (Int × Val))
    (k : Int) :
    (vs.map (compatEntryTransform d₁ d₂)).lookup k =
      (vs.lookup k).map (compatVal (d₂.get? k) (d₁.get? k)) := by
  induction vs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k', val⟩ := hd
    rw [List.map_cons, List.lookup_cons, List.lookup_cons,
      compatEntryTransform_fst]
    cases hbeq : (k == k') with
    | true =>
      have hkk : k = k' := by simpa using hbeq
      subst hkk
      simp [compatEntryTransform]
    | false => simpa using ih

/-- The merged lookup of the reinterpreted entry list agrees with
    `compatTransform` at every key. -/
theorem listToValue_compatEntryTransform_lookup (d₁ d₂ : Desc) (v : Value)
    (k : Int) (hd₂ : d₂.WF) (hv : v.WF) (hwf : valueWf d₁ v) (hc : d₁ ⋘ d₂) :
    (listToValue d₂ ((valList d₁ v).map (compatEntryTransform d₁ d₂))).get? k =
      (compatTransform d₁ d₂ v).get? k := by
  have hnodup : (d₂.fields.map Prod.fst).Nodup := by
    cases d₂ with | mk fs => exact hd₂.2
  have hlhs : (listToValue d₂ ((valList d₁ v).map (compatEntryTransform d₁ d₂))).get? k =
      mergeFieldVal (d₂.fields.lookup k)
        (((valList d₁ v).map (compatEntryTransform d₁ d₂)).lookup k) := by
    cases d₂ with | mk fs =>
    show (listMerge mergeFieldVal fs _).lookup k = _
    exact listMerge_mergeFieldVal_lookup fs _ k hnodup
  rw [hlhs, lookup_map_compatEntryTransform,
    valList_lookup_characterize d₁ v k hv]
  cases hd2k : d₂.get? k with
  | none =>
    rw [compatTransform_get?_none d₁ d₂ v k hd2k]
    have : d₂.fields.lookup k = none := hd2k
    rw [this]
    cases d₁.fields.lookup k <;> cases v.get? k <;> rfl
  | some f₂ =>
    rw [compatTransform_get?_some d₁ d₂ v k f₂ hd2k]
    have hf₂ : d₂.fields.lookup k = some f₂ := hd2k
    rw [hf₂]
    cases hd1k : d₁.get? k with
    | none =>
      have hd1k' : d₁.fields.lookup k = none := hd1k
      rw [hd1k']
      cases hvk : v.get? k with
      | none => rfl
      | some val => cases f₂ <;> cases val <;> rfl
    | some f₁ =>
      have hd1k' : d₁.fields.lookup k = some f₁ := hd1k
      have hcompat : f₁ ∝ f₂ := by
        obtain ⟨f₂', hf₂', hc'⟩ := descCompat_field d₁ d₂ k hc f₁ hd1k
        rw [hd2k] at hf₂'
        cases hf₂'
        exact hc'
      rw [hd1k']
      cases hvk : v.get? k with
      | none => rfl
      | some val =>
        have hentry : valWfFold d₁.fields k val True :=
          valueWf_at_key d₁ v k val hwf hvk
        cases val with
        | missing => exact absurd hentry (fun h =>
            valWfFold_missing_elim d₁.fields k f₁ True hd1k' h)
        | bool b =>
          have hf : f₁ = .bool := valWfFold_bool_field d₁.fields k b f₁ True hd1k' hentry
          subst hf
          cases f₂ with
          | bool => rfl
          | int => rfl
          | msg d₂' =>
            exact absurd rfl (fieldCompat_scalar_inv _ _ hcompat (by rintro d ⟨⟩) d₂')
        | int z =>
          have hf : f₁ = .int := valWfFold_int_field d₁.fields k z f₁ True hd1k' hentry
          subst hf
          cases f₂ with
          | bool => rfl
          | int => rfl
          | msg d₂' =>
            exact absurd rfl (fieldCompat_scalar_inv _ _ hcompat (by rintro d ⟨⟩) d₂')
        | msg v' =>
          obtain ⟨d₁', hf, _⟩ := valWfFold_msg_field d₁.fields k v' f₁ True hd1k' hentry
          subst hf
          obtain ⟨d₂', hd₂', _⟩ := fieldCompat_msg_inv d₁' f₂ hcompat
          subst hd₂'
          rfl

/-- The reader's round-trip value: parsing the writer's bytes under `d₂` and
    merging with `listToValue d₂` yields exactly `compatTransform d₁ d₂ v`. -/
theorem listToValue_map_eq_compatTransform (d₁ d₂ : Desc) (v : Value) :
    d₂.WF → v.WF → valueWf d₁ v → d₁ ⋘ d₂ →
    listToValue d₂ ((valList d₁ v).map (compatEntryTransform d₁ d₂)) =
      compatTransform d₁ d₂ v := by
  intro hd₂ hv hwf hc
  refine Value.ext_lookup _ _ ?_ (compatTransform_wf d₁ d₂ v hd₂) ?_
  · cases d₂ with | mk fs =>
    show Value.WF (Value.mk (listMerge mergeFieldVal fs _))
    exact listMerge_mergeFieldVal_wf fs _ hd₂.1 hd₂.2
  · intro k
    exact listToValue_compatEntryTransform_lookup d₁ d₂ v k hd₂ hv hwf hc

end Pollux.InterParse
