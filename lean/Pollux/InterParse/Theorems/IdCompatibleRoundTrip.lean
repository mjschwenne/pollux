/-
  Pollux.InterParse.Theorems.IdCompatibleRoundTrip — The round-trip theorem
  for `IdCompatible`: `idCompatTransform` always produces an output that is
  `IdCompatible` with the input under the same descriptor.

  The proof is by well-founded induction on a list-size measure, processing
  the sorted descriptor and value in lockstep. The case lemmas below handle
  each combination of empty/nonempty heads and the three orderings between
  the descriptor and value keys.
-/
import Pollux.InterParse.Theorems.IdCompatible
import Pollux.InterParse.Theorems.IdCompatibleHelpers
import Pollux.InterParse.Theorems.Validity

namespace Pollux.InterParse

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
    (hvs_sorted : List.Pairwise (fun a b : Int × Val => a.1 < b.1) ((k_v, val) :: rest_vs))
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
    (hvs_sorted : List.Pairwise (fun a b : Int × Val => a.1 < b.1) ((k_v, val) :: rest_vs))
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

/-! ## Well-founded assembly -/

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
          hds_sorted hvs_sorted
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
          hds_sorted hvs_sorted
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

/-! ## Main round-trip theorem -/

/-- The round-trip theorem with recursive well-formedness.

    The `insertMsg` case of `IdCompatible` recurses into nested
    descriptors/values that must also be sorted and duplicate-free,
    hence the need for `AllWF` instead of plain `WF`. -/
theorem idCompatRoundTrip (v : Value) (d : Desc) :
    d.AllWF → v.AllWF → valid' d v → ⟨ v ≼ idCompatTransform d v ⟩∷ d := by
  intro ⟨hd, hd_all⟩ ⟨hv, hv_all⟩ hvalid
  cases d with | mk ds =>
  cases v with | mk vs =>
  simp only [idCompatTransform]
  exact idCompatRoundTrip_aux ds vs hd.1 hd.2 hv.1 hv.2 hd_all hv_all hvalid

end Pollux.InterParse
