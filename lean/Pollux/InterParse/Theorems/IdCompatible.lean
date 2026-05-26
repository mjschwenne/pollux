/-
  Pollux.InterParse.Theorems.IdCompatible - The `IdCompatible` relation between
  descriptor/value pairs (used for schema-evolution correctness).
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

/-! ## Round-trip transformation

The transformation `idCompatTransform d v` produces the value that an
`IdCompatible`-respecting round trip yields from `v` under descriptor `d`:
- fields of `v` whose key is not in `d` are dropped,
- fields in `d` with no matching entry in `v` (or with `.missing`) become `.missing`,
- type-matched entries are preserved unchanged,
- nested message fields are recursively transformed.

The original non-recursive definition `listToValue d (valList d v)` does not
handle nested messages correctly (inner values are passed through without
recursive transformation) and drops type-mismatched entries entirely instead
of producing `.missing`. The corrected version below is mutually recursive. -/

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

/-
  The original (non-recursive) definition is incorrect for nested messages
  and type-mismatched entries. It has been replaced by the recursive version above.

  def idCompatTransform (d : Desc) (v : Value) : Value :=
    listToValue d (valList d v)
-/

/-! ## Auxiliary lemmas for the round-trip proof -/

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

/-! ## Main round-trip theorem -/

/-
If the descriptor is empty and all entries in the value are `.missing`,
    dropping each entry gives `IdCompatible ∅ v ∅`.
-/
theorem idcompat_drop_all_missing (vs : List (Int × Val)) :
    (∀ kv ∈ vs, kv.2 = Val.missing) →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs →
    (List.map Prod.fst vs).Nodup →
    IdCompatible (∅ : Desc) (.mk vs) (∅ : Value) := by
  induction' vs with kv vs ih;
  · exact fun _ _ _ => IdCompatible.emp;
  · intro h1 h2 h3;
    -- Apply the induction hypothesis to the rest of the list.
    have h_ind : IdCompatible ∅ (Value.mk vs) ∅ := by
      aesop;
    convert IdCompatible.drop ∅ ( Value.mk vs ) ∅ kv.1 kv.2 h_ind _ _ using 1;
    · unfold Value.insert;
      unfold Value.sortedInsert; aesop;
    · -- The empty list's lookup function returns none for any key.
      simp [Desc.get?];
      simp +decide [ Desc.fields ];
    · simp_all +decide [ Value.get? ];
      exact fun a b hab => ne_of_lt ( h2.1 a b hab )

/-- Extract the accumulated predicate from `valid'Fold`. -/
theorem valid'Fold_extract (ds : List (Int × Field)) (k : Int) (v : Val) (P : Prop) :
    valid'Fold ds k v P → P := by
  unfold valid'Fold; cases v <;> simp

/-- Extract the accumulated predicate from `valid'FoldList`. -/
theorem valid'FoldList_extract (ds : List (Int × Field)) (vs : List (Int × Val)) (P : Prop) :
    valid'FoldList ds vs P → P := by
  induction vs generalizing P with
  | nil => exact id
  | cons hd tl ih =>
    intro h; exact valid'Fold_extract ds hd.1 hd.2 _ (ih _ h)

/-- Weaken the accumulator in `valid'Fold`. -/
theorem valid'Fold_weaken (ds : List (Int × Field)) (k : Int) (v : Val) (P Q : Prop) :
    (P → Q) → valid'Fold ds k v P → valid'Fold ds k v Q := by
  intro hPQ; unfold valid'Fold; cases v <;> simp <;> tauto

/-- Weaken the accumulator in `valid'FoldList`. -/
theorem valid'FoldList_weaken (ds : List (Int × Field)) (vs : List (Int × Val))
    (P Q : Prop) :
    (P → Q) → valid'FoldList ds vs P → valid'FoldList ds vs Q := by
  induction vs generalizing P Q with
  | nil => exact id
  | cons hd tl ih =>
    intro hPQ h
    show valid'FoldList ds tl (valid'Fold ds hd.1 hd.2 Q)
    exact ih _ _ (valid'Fold_weaken ds hd.1 hd.2 P Q hPQ) h

/-- Dropping the head preserves `valid'`. -/
theorem valid'_cons (ds : List (Int × Field)) (kv : Int × Val) (vs : List (Int × Val)) :
    valid'FoldList ds (kv :: vs) True → valid'FoldList ds vs True := by
  intro h; unfold valid'FoldList at h
  exact valid'FoldList_weaken ds vs _ _ (fun _ => trivial) h

/-- Extract info about the head entry from `valid'`. -/
theorem valid'_entry_head (ds : List (Int × Field)) (kv : Int × Val) (vs : List (Int × Val)) :
    valid'FoldList ds (kv :: vs) True → valid'Fold ds kv.1 kv.2 True := by
  intro h; unfold valid'FoldList at h
  exact valid'FoldList_extract ds vs _ h

/-- `idCompatTransformAux` is independent of entries at keys not in `ds`. -/
theorem idCompatTransformAux_erase_irrelevant
    (ds : List (Int × Field)) (v : Value) (k : Int) :
    List.lookup k ds = none →
    idCompatTransformAux ds (v.erase k) = idCompatTransformAux ds v := by
  intro hk
  induction' ds with hd tl ih generalizing v k
  · rfl
  · have hne : k ≠ hd.1 := by
      intro heq; subst heq; simp [List.lookup] at hk
    have htl : List.lookup k tl = none := by
      have : List.lookup k (hd :: tl) =
        (match k == hd.1 with | true => some hd.2 | false => List.lookup k tl) := rfl
      rw [this, show (k == hd.1) = false from by rw [beq_eq_decide]; simp [hne]] at hk
      simpa using hk
    unfold idCompatTransformAux
    have hlookup_eq : (v.erase k).get? hd.1 = v.get? hd.1 := by
      cases v with | mk vs =>
      simp [Value.erase, Value.get?, Value.vals]
      exact value_lookup_sortedErase_ne k hd.1 vs (Ne.symm hne)
    simp only [hlookup_eq]
    congr 1
    exact ih v k htl


/-! ## Recursive well-formedness predicates

The `IdCompatible.insertMsg` constructor requires a recursive derivation
on a sub-descriptor `d'` and sub-value `v'`.  To carry out the inner
induction we need to know that **all** nested descriptors and values are
well-formed (sorted, no-dup), not just the top-level ones.  The predicates
below make this requirement explicit. -/

mutual
/-- Every nested `Desc` inside a field list is well-formed. -/
def fieldListAllWF : List (Int × Field) → Prop
  | [] => True
  | (_, f) :: rest => fieldAllWF f ∧ fieldListAllWF rest
/-- Every nested `Desc` inside a field is well-formed. -/
def fieldAllWF : Field → Prop
  | .msg (Desc.mk fs) => (Desc.mk fs).WF ∧ fieldListAllWF fs
  | .bool | .int => True
end

mutual
/-- Every nested `Value` inside a val list is well-formed. -/
def valListAllWF : List (Int × Val) → Prop
  | [] => True
  | (_, v) :: rest => valAllWF v ∧ valListAllWF rest
/-- Every nested `Value` inside a val is well-formed. -/
def valAllWF : Val → Prop
  | .msg (Value.mk vs) => (Value.mk vs).WF ∧ valListAllWF vs
  | .bool _ | .int _ | .missing => True
end

theorem fieldListAllWF_tail {f : Int × Field} {rest : List (Int × Field)} :
    fieldListAllWF (f :: rest) → fieldListAllWF rest := by
  exact fun h => h.2

theorem fieldListAllWF_head {k : Int} {f : Field} {rest : List (Int × Field)} :
    fieldListAllWF ((k, f) :: rest) → fieldAllWF f := by
  exact fun h => h.1

theorem valListAllWF_tail {v : Int × Val} {rest : List (Int × Val)} :
    valListAllWF (v :: rest) → valListAllWF rest := by
  exact fun h => h.2

theorem valListAllWF_head {k : Int} {v : Val} {rest : List (Int × Val)} :
    valListAllWF ((k, v) :: rest) → valAllWF v := by
  exact fun h => h.1

/-! ## IdCompatible constructors for sorted-cons form -/

/-- addMissing when the insert acts as a cons (key below all others). -/
theorem IdCompatible.addMissing_cons (k : Int) (f : Field)
    (rest_ds : List (Int × Field)) (vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk vs) (.mk v2))
    (h1 : rest_ds.lookup k = none)
    (h2 : vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, f) :: rest_ds)) (.mk vs) (.mk ((k, Val.missing) :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k f = Desc.mk ((k, f) :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk v2).insert k Val.missing = Value.mk ((k, Val.missing) :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2]
  exact IdCompatible.addMissing _ _ _ k f ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-- drop when the insert acts as a cons. -/
theorem IdCompatible.drop_cons (k : Int) (val : Val)
    (ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (ih : IdCompatible (.mk ds) (.mk rest_vs) (.mk v2))
    (h1 : ds.lookup k = none)
    (h2 : rest_vs.lookup k = none) :
    IdCompatible (.mk ds) (.mk ((k, val) :: rest_vs)) (.mk v2) := by
  have h_eq : (Value.mk rest_vs).insert k val = Value.mk ((k, val) :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  rw [← h_eq]
  exact IdCompatible.drop _ _ _ k val ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2])

/-- insertInt when the insert acts as a cons. -/
theorem IdCompatible.insertInt_cons (k : Int) (z : Int)
    (rest_ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk rest_vs) (.mk v2))
    (h1 : rest_ds.lookup k = none)
    (h2 : rest_vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, .int) :: rest_ds)) (.mk ((k, .int z) :: rest_vs))
      (.mk ((k, .int z) :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k .int = Desc.mk ((k, .int) :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk rest_vs).insert k (.int z) = Value.mk ((k, .int z) :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  have h_eq3 : (Value.mk v2).insert k (.int z) = Value.mk ((k, .int z) :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2, ← h_eq3]
  exact IdCompatible.insertInt _ _ _ k z ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-- insertBool when the insert acts as a cons. -/
theorem IdCompatible.insertBool_cons (k : Int) (b : Bool)
    (rest_ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk rest_vs) (.mk v2))
    (h1 : rest_ds.lookup k = none)
    (h2 : rest_vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, .bool) :: rest_ds)) (.mk ((k, .bool b) :: rest_vs))
      (.mk ((k, .bool b) :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k .bool = Desc.mk ((k, .bool) :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk rest_vs).insert k (.bool b) = Value.mk ((k, .bool b) :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  have h_eq3 : (Value.mk v2).insert k (.bool b) = Value.mk ((k, .bool b) :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2, ← h_eq3]
  exact IdCompatible.insertBool _ _ _ k b ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-- insertMsg when the insert acts as a cons. -/
theorem IdCompatible.insertMsg_cons (k : Int) (d' : Desc) (v1' v2' : Value)
    (rest_ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk rest_vs) (.mk v2))
    (ih_inner : IdCompatible d' v1' v2')
    (h1 : rest_ds.lookup k = none)
    (h2 : rest_vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, .msg d') :: rest_ds)) (.mk ((k, .msg v1') :: rest_vs))
      (.mk ((k, .msg v2') :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k (.msg d') = Desc.mk ((k, .msg d') :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk rest_vs).insert k (.msg v1') = Value.mk ((k, .msg v1') :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  have h_eq3 : (Value.mk v2).insert k (.msg v2') = Value.mk ((k, .msg v2') :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2, ← h_eq3]
  exact IdCompatible.insertMsg _ _ _ _ _ _ k ih ih_inner
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-- inputMissing when the insert acts as a cons. -/
theorem IdCompatible.inputMissing_cons (k : Int) (f : Field)
    (rest_ds : List (Int × Field)) (rest_vs : List (Int × Val)) (v2 : List (Int × Val))
    (hlt_ds : ∀ p ∈ rest_ds, k < p.1)
    (hlt_vs : ∀ p ∈ rest_vs, k < p.1)
    (hlt_v2 : ∀ p ∈ v2, k < p.1)
    (ih : IdCompatible (.mk rest_ds) (.mk rest_vs) (.mk v2))
    (h1 : rest_ds.lookup k = none)
    (h2 : rest_vs.lookup k = none)
    (h3 : v2.lookup k = none) :
    IdCompatible (.mk ((k, f) :: rest_ds)) (.mk ((k, .missing) :: rest_vs))
      (.mk ((k, .missing) :: v2)) := by
  have h_eq1 : (Desc.mk rest_ds).insert k f = Desc.mk ((k, f) :: rest_ds) := by
    unfold Desc.insert Desc.fields; congr 1
    cases rest_ds with | nil => simp [Desc.sortedInsert] | cons hd _ => simp [Desc.sortedInsert, show k < hd.1 from hlt_ds hd (by simp)]
  have h_eq2 : (Value.mk rest_vs).insert k .missing = Value.mk ((k, .missing) :: rest_vs) := by
    unfold Value.insert Value.vals; congr 1
    cases rest_vs with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_vs hd (by simp)]
  have h_eq3 : (Value.mk v2).insert k .missing = Value.mk ((k, .missing) :: v2) := by
    unfold Value.insert Value.vals; congr 1
    cases v2 with | nil => simp [Value.sortedInsert] | cons hd _ => simp [Value.sortedInsert, show k < hd.1 from hlt_v2 hd (by simp)]
  rw [← h_eq1, ← h_eq2, ← h_eq3]
  exact IdCompatible.inputMissing _ _ _ k f ih
    (by simp [Desc.get?, Desc.fields, h1]) (by simp [Value.get?, Value.vals, h2]) (by simp [Value.get?, Value.vals, h3])

/-! ## Case lemmas for the round-trip proof -/

/-
Case ds=[], vs nonempty.
-/
private theorem roundTrip_case2
    (vs : List (Int × Val))
    (hvs_sorted : List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs)
    (hvs_nodup : (List.map Prod.fst vs).Nodup)
    (hvalid : valid' (.mk []) (.mk vs)) :
    IdCompatible (.mk []) (.mk vs) (.mk (idCompatTransformAux [] (.mk vs))) := by
  -- Apply the induction hypothesis to the tail of the list.
  have h_ind : ∀ (vs' : List (Int × Val)), valid'FoldList [] vs' True → (∀ kv ∈ vs', kv.2 = Val.missing) := by
    intros vs' hvs' kv hk; induction vs' <;> simp_all +decide [ valid'FoldList ] ;
    nontriviality;
    rename_i h₁ h₂ h₃;
    rename_i h₄op;
    cases h₄op ; simp_all +decide;
    cases ‹Val› <;> simp_all +decide [ valid'Fold ];
    · exact absurd ( valid'FoldList_extract _ _ _ hvs' ) ( by decide );
    · exact absurd ( valid'FoldList_extract _ _ _ hvs' ) ( by tauto );
    · exact absurd ( valid'FoldList_extract _ _ _ hvs' ) ( by simp +decide );
    · grind;
  exact idcompat_drop_all_missing vs ( h_ind vs hvalid ) hvs_sorted hvs_nodup

/-! ## Additional helpers needed for case lemmas -/

/-- If `k` is less than every key in a sorted field list, lookup returns `none`. -/
private theorem lookup_none_of_lt_all_field (k : Int) (l : List (Int × Field)) :
    (∀ p ∈ l, k < p.1) → l.lookup k = none := by
  intro h
  rw [List.lookup_eq_none_iff]
  intro ⟨a, b⟩ hab
  simp [bne_iff_ne]; exact ne_of_lt (h _ hab)

/-- If `k` is less than every key in a sorted val list, lookup returns `none`. -/
private theorem lookup_none_of_lt_all_val (k : Int) (l : List (Int × Val)) :
    (∀ p ∈ l, k < p.1) → l.lookup k = none := by
  intro h
  rw [List.lookup_eq_none_iff]
  intro ⟨a, b⟩ hab
  simp [bne_iff_ne]; exact ne_of_lt (h _ hab)

/-- The keys of `idCompatTransformAux rest_ds v` are all `> k` when all keys in `rest_ds` are `> k`. -/
private theorem idCompatTransformAux_keys_gt (rest_ds : List (Int × Field)) (v : Value) (k : Int) :
    (∀ p ∈ rest_ds, k < p.1) →
    ∀ p ∈ idCompatTransformAux rest_ds v, k < p.1 := by
  intro h p hp
  have h_keys_eq := idCompatTransformAux_keys rest_ds v
  have hmem : p.1 ∈ rest_ds.map Prod.fst := by
    have : p.1 ∈ (idCompatTransformAux rest_ds v).map Prod.fst :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    rwa [h_keys_eq] at this
  obtain ⟨q, hq, hq_eq⟩ := List.mem_map.mp hmem
  rw [← hq_eq]; exact h q hq

/-- If `k` is less than all keys in `ds`, the transform ignores the extra entry at `k`. -/
private theorem idCompatTransformAux_prepend_lt
    (ds : List (Int × Field)) (k : Int) (val : Val) (rest : List (Int × Val)) :
    (∀ p ∈ ds, k < p.1) →
    idCompatTransformAux ds (Value.mk ((k, val) :: rest)) =
    idCompatTransformAux ds (Value.mk rest) := by
  intro hds
  have h_erase : idCompatTransformAux ds ((Value.mk ((k, val) :: rest)).erase k) =
      idCompatTransformAux ds (Value.mk ((k, val) :: rest)) :=
    idCompatTransformAux_erase_irrelevant ds _ k (lookup_none_of_lt_all_field k ds hds)
  convert h_erase.symm using 2
  show Value.mk rest = Value.mk (Value.sortedErase k ((k, val) :: rest))
  simp [Value.sortedErase]

/-- `valid'Fold` can switch between field lists with the same lookup at `k`. -/
private theorem valid'Fold_lookup_congr (fs gs : List (Int × Field)) (k : Int) (v : Val) (P : Prop) :
    fs.lookup k = gs.lookup k →
    valid'Fold fs k v P → valid'Fold gs k v P := by
  unfold valid'Fold
  cases v <;> aesop (simp_config := { singlePass := true })

/-- `valid'FoldList` can switch between field lists with the same lookup at all keys. -/
private theorem valid'FoldList_lookup_congr (fs gs : List (Int × Field)) (vs : List (Int × Val)) (P : Prop) :
    (∀ kv ∈ vs, fs.lookup kv.1 = gs.lookup kv.1) →
    valid'FoldList fs vs P → valid'FoldList gs vs P := by
  intro h_lookup h_valid; simp_all +decide [valid'FoldList]
  induction' vs with kv vs ih generalizing P <;> simp_all +decide [valid'FoldList]
  convert ih _ _ h_valid using 1
  · exact ⟨fun h => valid'Fold_lookup_congr _ _ _ _ _ (h_lookup _ _ (Or.inl rfl) |> Eq.symm) h,
          fun h => valid'Fold_lookup_congr _ _ _ _ _ (h_lookup _ _ (Or.inl rfl)) h⟩
  · exact fun a b hab => h_lookup a b <| Or.inr hab

/-- When all keys in `vs` are `> k₀`, dropping the head `(k₀, f₀)` from `ds` preserves `valid'`. -/
private theorem valid'_drop_head_ds (k₀ : Int) (f₀ : Field)
    (rest_ds : List (Int × Field)) (vs : List (Int × Val)) :
    (∀ kv ∈ vs, k₀ < kv.1) →
    valid'FoldList ((k₀, f₀) :: rest_ds) vs True →
    valid'FoldList rest_ds vs True := by
  intro h_all_gt_k₀ h_valid'FoldList
  apply valid'FoldList_lookup_congr
  any_goals assumption
  intro kv hkv
  have hne : kv.1 ≠ k₀ := ne_of_gt (h_all_gt_k₀ kv hkv)
  simp [List.lookup, show (kv.1 == k₀) = false from by rw [beq_eq_decide]; simp [hne]]

/-- Helper: unfold the transform for matching keys. -/
private theorem transform_head_eq (k : Int) (f_d : Field) (rest_ds : List (Int × Field))
    (val : Val) (rest_vs : List (Int × Val)) :
    idCompatTransformAux ((k, f_d) :: rest_ds) (.mk ((k, val) :: rest_vs)) =
    (k, match f_d, val with
      | .bool, .bool b => .bool b
      | .int, .int z => .int z
      | .msg d', .msg v' => .msg (idCompatTransform d' v')
      | _, _ => .missing) :: idCompatTransformAux rest_ds (.mk ((k, val) :: rest_vs)) := by
  conv_lhs => unfold idCompatTransformAux
  simp only [Value.get?, Value.vals, List.lookup_cons_self]
  cases f_d <;> cases val <;> rfl

/-- Case vs=[], ds nonempty. -/
private theorem roundTrip_case3
    (ds : List (Int × Field))
    (hds_sorted : List.Pairwise (fun a b : Int × Field => a.1 < b.1) ds)
    (hds_nodup : (List.map Prod.fst ds).Nodup)
    (hvalid : valid' (.mk ds) (.mk [])) :
    IdCompatible (.mk ds) (.mk []) (.mk (idCompatTransformAux ds (.mk []))) := by
  induction ds with
  | nil => exact IdCompatible.emp
  | cons hd rest ih =>
    obtain ⟨k, f⟩ := hd
    have hunfold : idCompatTransformAux ((k, f) :: rest) (.mk []) =
        (k, .missing) :: idCompatTransformAux rest (.mk []) := by
      conv_lhs => unfold idCompatTransformAux
      simp only [Value.get?, Value.vals, List.lookup_nil]
    rw [hunfold]
    have ih_rest := ih hds_sorted.tail hds_nodup.of_cons (by simp [valid', valid'FoldList])
    have hlt_ds : ∀ (p : Int × Field), p ∈ rest → k < p.1 :=
      fun p hp => List.rel_of_pairwise_cons hds_sorted hp
    exact IdCompatible.addMissing_cons k f rest [] (idCompatTransformAux rest (.mk [])) hlt_ds
      (idCompatTransformAux_keys_gt rest (.mk []) k hlt_ds) ih_rest
      (lookup_none_of_lt_all_field k rest hlt_ds) rfl
      (lookup_none_of_lt_all_val k _ (idCompatTransformAux_keys_gt rest (.mk []) k hlt_ds))

/-- Case k_v < k_d: drop the value entry. -/
private theorem roundTrip_case4a
    (k_d : Int) (f_d : Field) (rest_ds : List (Int × Field))
    (k_v : Int) (val : Val) (rest_vs : List (Int × Val))
    (h_lt : k_v < k_d)
    (hds_sorted : List.Pairwise (fun a b : Int × Field => a.1 < b.1) ((k_d, f_d) :: rest_ds))
    (hds_nodup : (List.map Prod.fst ((k_d, f_d) :: rest_ds)).Nodup)
    (hvs_sorted : List.Pairwise (fun a b : Int × Val => a.1 < b.1) ((k_v, val) :: rest_vs))
    (hvs_nodup : (List.map Prod.fst ((k_v, val) :: rest_vs)).Nodup)
    (hds_allwf : fieldListAllWF ((k_d, f_d) :: rest_ds))
    (hvs_allwf : valListAllWF ((k_v, val) :: rest_vs))
    (hvalid : valid' (.mk ((k_d, f_d) :: rest_ds)) (.mk ((k_v, val) :: rest_vs)))
    (ih_vs : IdCompatible (.mk ((k_d, f_d) :: rest_ds)) (.mk rest_vs)
      (.mk (idCompatTransformAux ((k_d, f_d) :: rest_ds) (.mk rest_vs)))) :
    IdCompatible (.mk ((k_d, f_d) :: rest_ds)) (.mk ((k_v, val) :: rest_vs))
      (.mk (idCompatTransformAux ((k_d, f_d) :: rest_ds) (.mk ((k_v, val) :: rest_vs)))) := by
  have hlt_all : ∀ (p : Int × Field), p ∈ (k_d, f_d) :: rest_ds → k_v < p.1 := by
    intro p hp
    cases hp with
    | head => exact h_lt
    | tail _ h => exact lt_trans h_lt (List.rel_of_pairwise_cons hds_sorted h)
  rw [idCompatTransformAux_prepend_lt _ k_v val rest_vs hlt_all]
  exact IdCompatible.drop_cons k_v val _ rest_vs _
    (fun p hp => List.rel_of_pairwise_cons hvs_sorted hp) ih_vs
    (lookup_none_of_lt_all_field k_v _ hlt_all)
    (lookup_none_of_lt_all_val k_v rest_vs (fun p hp => List.rel_of_pairwise_cons hvs_sorted hp))

/-- Case k_d < k_v: add missing for the descriptor field. -/
private theorem roundTrip_case4c
    (k_d : Int) (f_d : Field) (rest_ds : List (Int × Field))
    (k_v : Int) (val : Val) (rest_vs : List (Int × Val))
    (h_lt : k_d < k_v)
    (hds_sorted : List.Pairwise (fun a b : Int × Field => a.1 < b.1) ((k_d, f_d) :: rest_ds))
    (hds_nodup : (List.map Prod.fst ((k_d, f_d) :: rest_ds)).Nodup)
    (hvs_sorted : List.Pairwise (fun a b : Int × Val => a.1 < b.1) ((k_v, val) :: rest_vs))
    (hvs_nodup : (List.map Prod.fst ((k_v, val) :: rest_vs)).Nodup)
    (hds_allwf : fieldListAllWF ((k_d, f_d) :: rest_ds))
    (hvs_allwf : valListAllWF ((k_v, val) :: rest_vs))
    (hvalid : valid' (.mk ((k_d, f_d) :: rest_ds)) (.mk ((k_v, val) :: rest_vs)))
    (ih_outer : IdCompatible (.mk rest_ds) (.mk ((k_v, val) :: rest_vs))
      (.mk (idCompatTransformAux rest_ds (.mk ((k_v, val) :: rest_vs))))) :
    IdCompatible (.mk ((k_d, f_d) :: rest_ds)) (.mk ((k_v, val) :: rest_vs))
      (.mk (idCompatTransformAux ((k_d, f_d) :: rest_ds) (.mk ((k_v, val) :: rest_vs)))) := by
  have hne : k_d ≠ k_v := ne_of_lt h_lt
  have hlookup_rest : List.lookup k_d rest_vs = none :=
    lookup_none_of_lt_all_val k_d rest_vs (fun p hp => lt_trans h_lt (List.rel_of_pairwise_cons hvs_sorted hp))
  have hunfold : idCompatTransformAux ((k_d, f_d) :: rest_ds) (.mk ((k_v, val) :: rest_vs)) =
      (k_d, .missing) :: idCompatTransformAux rest_ds (.mk ((k_v, val) :: rest_vs)) := by
    conv_lhs => unfold idCompatTransformAux
    simp only [Value.get?, Value.vals, List.lookup_cons, beq_eq_decide, hne]
    simp only [hlookup_rest]
    cases f_d <;> rfl
  rw [hunfold]
  have hlt_ds : ∀ (p : Int × Field), p ∈ rest_ds → k_d < p.1 :=
    fun p hp => List.rel_of_pairwise_cons hds_sorted hp
  have hlt_v2 := idCompatTransformAux_keys_gt rest_ds (.mk ((k_v, val) :: rest_vs)) k_d hlt_ds
  have h2 : ((k_v, val) :: rest_vs).lookup k_d = none := by
    simp [List.lookup, show (k_d == k_v) = false from by rw [beq_eq_decide]; simp [hne], hlookup_rest]
  exact IdCompatible.addMissing_cons k_d f_d rest_ds ((k_v, val) :: rest_vs)
    (idCompatTransformAux rest_ds (.mk ((k_v, val) :: rest_vs))) hlt_ds hlt_v2 ih_outer
    (lookup_none_of_lt_all_field k_d rest_ds hlt_ds) h2
    (lookup_none_of_lt_all_val k_d _ hlt_v2)

/-- Case k_v = k_d: matching keys. -/
private theorem roundTrip_case4b
    (k : Int) (f_d : Field) (rest_ds : List (Int × Field))
    (val : Val) (rest_vs : List (Int × Val))
    (hds_sorted : List.Pairwise (fun a b : Int × Field => a.1 < b.1) ((k, f_d) :: rest_ds))
    (hds_nodup : (List.map Prod.fst ((k, f_d) :: rest_ds)).Nodup)
    (hvs_sorted : List.Pairwise (fun a b : Int × Val => a.1 < b.1) ((k, val) :: rest_vs))
    (hvs_nodup : (List.map Prod.fst ((k, val) :: rest_vs)).Nodup)
    (hds_allwf : fieldListAllWF ((k, f_d) :: rest_ds))
    (hvs_allwf : valListAllWF ((k, val) :: rest_vs))
    (hvalid : valid' (.mk ((k, f_d) :: rest_ds)) (.mk ((k, val) :: rest_vs)))
    (ih_tails : IdCompatible (.mk rest_ds) (.mk rest_vs)
      (.mk (idCompatTransformAux rest_ds (.mk rest_vs))))
    (ih_msg : ∀ (d' : Desc) (v' : Value),
      fieldListSize d'.fields < fieldListSize ((k, f_d) :: rest_ds) →
      d'.WF → v'.WF → fieldListAllWF d'.fields → valListAllWF v'.vals →
      valid' d' v' →
      IdCompatible d' v' (idCompatTransform d' v')) :
    IdCompatible (.mk ((k, f_d) :: rest_ds)) (.mk ((k, val) :: rest_vs))
      (.mk (idCompatTransformAux ((k, f_d) :: rest_ds) (.mk ((k, val) :: rest_vs)))) := by
  have hlt_ds : ∀ (p : Int × Field), p ∈ rest_ds → k < p.1 :=
    fun p hp => List.rel_of_pairwise_cons hds_sorted hp
  have hlt_vs : ∀ (p : Int × Val), p ∈ rest_vs → k < p.1 :=
    fun p hp => List.rel_of_pairwise_cons hvs_sorted hp
  have htail_eq := idCompatTransformAux_prepend_lt rest_ds k val rest_vs hlt_ds
  have hlt_v2 := idCompatTransformAux_keys_gt rest_ds (.mk rest_vs) k hlt_ds
  have h_ds_lookup := lookup_none_of_lt_all_field k rest_ds hlt_ds
  have h_vs_lookup := lookup_none_of_lt_all_val k rest_vs hlt_vs
  have h_v2_lookup := lookup_none_of_lt_all_val k _ hlt_v2
  have hentry := valid'_entry_head ((k, f_d) :: rest_ds) (k, val) rest_vs hvalid
  rw [transform_head_eq, htail_eq]
  cases val with
  | missing =>
    simp only
    exact IdCompatible.inputMissing_cons k f_d rest_ds rest_vs _ hlt_ds hlt_vs hlt_v2
      ih_tails h_ds_lookup h_vs_lookup h_v2_lookup
  | bool b =>
    simp only [valid'Fold, List.lookup_cons_self] at hentry
    have hf : f_d = .bool := Option.some_injective _ hentry.1; subst hf; simp only
    exact IdCompatible.insertBool_cons k b rest_ds rest_vs _ hlt_ds hlt_vs hlt_v2
      ih_tails h_ds_lookup h_vs_lookup h_v2_lookup
  | int z =>
    simp only [valid'Fold, List.lookup_cons_self] at hentry
    have hf : f_d = .int := Option.some_injective _ hentry.1; subst hf; simp only
    exact IdCompatible.insertInt_cons k z rest_ds rest_vs _ hlt_ds hlt_vs hlt_v2
      ih_tails h_ds_lookup h_vs_lookup h_v2_lookup
  | msg v' =>
    simp only [valid'Fold, List.lookup_cons_self] at hentry
    obtain ⟨⟨d', hd', hvalid'⟩, _⟩ := hentry
    have hf : f_d = .msg d' := Option.some_injective _ hd'; subst hf; simp only
    have hsize : fieldListSize d'.fields < fieldListSize ((k, .msg d') :: rest_ds) := by
      show fieldListSize d'.fields < fieldSize (.msg d') + fieldListSize rest_ds
      show fieldListSize d'.fields < 1 + descSize d' + fieldListSize rest_ds
      cases d' with | mk fs =>
      show fieldListSize fs < 1 + (1 + fieldListSize fs) + fieldListSize rest_ds
      omega
    have hd'_data := fieldListAllWF_head (k := k) (rest := rest_ds) hds_allwf
    have hv'_data := valListAllWF_head (k := k) (rest := rest_vs) hvs_allwf
    have hd'_wf : d'.WF := by cases d' with | mk fs => exact hd'_data.1
    have hd'_allwf : fieldListAllWF d'.fields := by cases d' with | mk fs => exact hd'_data.2
    have hv'_wf : v'.WF := by cases v' with | mk vs => exact hv'_data.1
    have hv'_allwf : valListAllWF v'.vals := by cases v' with | mk vs => exact hv'_data.2
    exact IdCompatible.insertMsg_cons k d' v' (idCompatTransform d' v') rest_ds rest_vs _
      hlt_ds hlt_vs hlt_v2 ih_tails (ih_msg d' v' hsize hd'_wf hv'_wf hd'_allwf hv'_allwf hvalid')
      h_ds_lookup h_vs_lookup h_v2_lookup

/-- Well-founded induction helper: assembles the case lemmas. -/
private theorem idCompatRoundTrip_aux_wf :
    ∀ (n : Nat) (ds : List (Int × Field)) (vs : List (Int × Val)),
    fieldListSize ds ≤ n →
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) ds →
    (List.map Prod.fst ds).Nodup →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs →
    (List.map Prod.fst vs).Nodup →
    fieldListAllWF ds →
    valListAllWF vs →
    valid' (.mk ds) (.mk vs) →
    IdCompatible (.mk ds) (.mk vs) (.mk (idCompatTransformAux ds (.mk vs))) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_n =>
  intro ds vs; revert ds
  induction vs with
  | nil =>
    intro ds hn hds_sorted hds_nodup _ _ hds_allwf _ hvalid
    cases ds with
    | nil => exact IdCompatible.emp
    | cons _ _ => exact roundTrip_case3 _ hds_sorted hds_nodup hvalid
  | cons kv rest_vs ih_vs =>
    obtain ⟨k_v, val⟩ := kv
    intro ds hn hds_sorted hds_nodup hvs_sorted hvs_nodup hds_allwf hvs_allwf hvalid
    cases ds with
    | nil => exact roundTrip_case2 _ hvs_sorted hvs_nodup hvalid
    | cons hd rest_ds =>
      obtain ⟨k_d, f_d⟩ := hd
      have hfls : fieldListSize rest_ds < fieldListSize ((k_d, f_d) :: rest_ds) := by
        show fieldListSize rest_ds < fieldSize f_d + fieldListSize rest_ds
        have := fieldSize_positive f_d; omega
      rcases lt_trichotomy k_v k_d with h_lt | h_eq | h_gt
      · -- case 4a: k_v < k_d, drop value entry
        apply roundTrip_case4a k_d f_d rest_ds k_v val rest_vs h_lt
          hds_sorted hds_nodup hvs_sorted hvs_nodup hds_allwf hvs_allwf hvalid
        exact ih_vs ((k_d, f_d) :: rest_ds) hn hds_sorted hds_nodup
          hvs_sorted.tail hvs_nodup.of_cons hds_allwf (valListAllWF_tail hvs_allwf)
          (valid'_cons _ (k_v, val) rest_vs hvalid)
      · -- case 4b: k_v = k_d, matching keys
        subst h_eq
        apply roundTrip_case4b k_v f_d rest_ds val rest_vs
          hds_sorted hds_nodup hvs_sorted hvs_nodup hds_allwf hvs_allwf hvalid
        · -- IH on tails (rest_ds, rest_vs): use ih_n with smaller n
          exact ih_n (fieldListSize rest_ds) (by omega) rest_ds rest_vs le_rfl
            hds_sorted.tail hds_nodup.of_cons hvs_sorted.tail hvs_nodup.of_cons
            (fieldListAllWF_tail hds_allwf) (valListAllWF_tail hvs_allwf)
            (valid'_drop_head_ds k_v f_d rest_ds rest_vs
              (fun kv hkv => List.rel_of_pairwise_cons hvs_sorted hkv)
              (valid'_cons _ (k_v, val) rest_vs hvalid))
        · -- ih_msg for nested messages: use ih_n with smaller n
          intro d' v' hsize hd'_wf hv'_wf hd'_allwf hv'_allwf hvalid'
          cases d' with | mk fs =>
          cases v' with | mk vs' =>
          simp only [idCompatTransform]
          have : fieldListSize (Desc.mk fs).fields = fieldListSize fs := rfl
          exact ih_n (fieldListSize fs) (by omega) fs vs' le_rfl hd'_wf.1 hd'_wf.2
            hv'_wf.1 hv'_wf.2 hd'_allwf hv'_allwf hvalid'
      · -- case 4c: k_d < k_v, add missing
        apply roundTrip_case4c k_d f_d rest_ds k_v val rest_vs h_gt
          hds_sorted hds_nodup hvs_sorted hvs_nodup hds_allwf hvs_allwf hvalid
        exact ih_n (fieldListSize rest_ds) (by omega) rest_ds ((k_v, val) :: rest_vs) le_rfl
          hds_sorted.tail hds_nodup.of_cons hvs_sorted hvs_nodup
          (fieldListAllWF_tail hds_allwf) hvs_allwf
          (valid'_drop_head_ds k_d f_d rest_ds _
            (fun kv hkv => by cases hkv with
              | head => exact h_gt
              | tail _ h => exact lt_trans h_gt (List.rel_of_pairwise_cons hvs_sorted h))
            hvalid)

/-- Core induction lemma: processes both descriptor fields and value entries
    simultaneously to build the `IdCompatible` derivation.
    Works on raw lists to enable structural induction.

    The `fieldListAllWF` / `valListAllWF` hypotheses ensure that all
    nested descriptors and values are well-formed, which is needed for
    the `insertMsg` case where we recurse into sub-descriptors. -/
theorem idCompatRoundTrip_aux
    (ds : List (Int × Field)) (vs : List (Int × Val)) :
    List.Pairwise (fun a b : Int × Field => a.1 < b.1) ds →
    (List.map Prod.fst ds).Nodup →
    List.Pairwise (fun a b : Int × Val => a.1 < b.1) vs →
    (List.map Prod.fst vs).Nodup →
    fieldListAllWF ds →
    valListAllWF vs →
    valid' (.mk ds) (.mk vs) →
    IdCompatible (.mk ds) (.mk vs) (.mk (idCompatTransformAux ds (.mk vs))) :=
  idCompatRoundTrip_aux_wf (fieldListSize ds) ds _ le_rfl
/- Proof sketch (for future formalization).

We argue by well-founded recursion on `ds.length + vs.length`, processing the
sorted lists in lockstep and applying one `IdCompatible` constructor per step.
Throughout, "the transform" means `idCompatTransformAux ds (.mk vs)`.

Case 1: `ds = []` and `vs = []`.
  The transform is `[]`. Apply `IdCompatible.emp`.

Case 2: `ds = []` and `vs = (k_v, val) :: rest_vs`.
  Since `ds` is empty, `valid'` forces `val = .missing`. Apply `IdCompatible.drop`.

Case 3: `ds = (k_d, f_d) :: rest_ds` and `vs = []`.
  The transform pads every key in `ds` with `.missing`. Apply `IdCompatible.addMissing`.

Case 4: Compare `k_v` and `k_d`:
  4a. `k_v < k_d`: drop the value entry.
  4b. `k_v = k_d`: match on field/value type.
  4c. `k_d < k_v`: add missing for the descriptor field.
-/

/-- Recursive well-formedness for a `Desc`: the top-level is well-formed
    and every nested descriptor inside its fields is also recursively WF. -/
def Desc.AllWF (d : Desc) : Prop := d.WF ∧ fieldListAllWF d.fields

/-- Recursive well-formedness for a `Value`: the top-level is well-formed
    and every nested value inside its vals is also recursively WF. -/
def Value.AllWF' (v : Value) : Prop := v.WF ∧ valListAllWF v.vals

/-- The round-trip theorem with recursive well-formedness.

    The `insertMsg` case of `IdCompatible` recurses into nested
    descriptors/values that must also be sorted and duplicate-free,
    hence the need for `AllWF` / `AllWF'` instead of plain `WF`. -/
theorem idCompatRoundTrip (v : Value) (d : Desc) :
    d.AllWF → v.AllWF' → valid' d v → ⟨ v ≼ idCompatTransform d v ⟩∷ d := by
  intro ⟨hd, hd_all⟩ ⟨hv, hv_all⟩ hvalid
  cases d with | mk ds =>
  cases v with | mk vs =>
  simp only [idCompatTransform]
  exact idCompatRoundTrip_aux ds vs hd.1 hd.2 hv.1 hv.2 hd_all hv_all hvalid

end Pollux.InterParse
