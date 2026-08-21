/-
  Pollux.InterParse.Theorems.InterParseOk — the top-level
  `schemaCorrectInterParseOk` and `idInterParseOk` theorems for the
  intermediate format, plus the cross-descriptor `compatInterParseOk`. The per-element correctness lemmas
  `parseVal_serialVal_correct` and `parseVal_serialVal_transform` are the
  bulk of the work; the rest is plumbing onto the generic
  `repCorrectWeakFull` / `repCorrectWeakFullMap` combinators.
-/
import Pollux.Parse.Theorems
import Pollux.InterParse.Parser
import Pollux.InterParse.Serializer
import Pollux.InterParse.Theorems.SchemaCorrect
import Pollux.InterParse.Theorems.SchemaCorrectCompatible
import Pollux.InterParse.Theorems.IdCompatible
import Pollux.InterParse.Theorems.IdCompatibleHelpers
import Pollux.InterParse.Theorems.IdCompatibleRoundTrip
import Pollux.InterParse.Theorems.Serialization
import Pollux.InterParse.Theorems.ValList
import Pollux.InterParse.Theorems.Compatible
import Pollux.InterParse.Theorems.CompatTransform
import Pollux.InterParse.Theorems.CompatRoundTrip

namespace Pollux.InterParse

open Pollux.Parse
open Pollux.Parse.Theorems

/-! ## Top-level correctness theorems

For any schema-correct value, serializing with `serialValue` and then parsing
with `parseValue` recovers a compatible value. -/

/-- Per-element correctness: for an element of `valList d v` satisfying willEncode,
    given depth-bounded IH for nested messages, the parser inverts the serializer. -/
private theorem parseVal_serialVal_correct
    (d : Desc) (v : Value) (enc : List UInt8) (hsc : ⟨ v ∷ d ⟩)
    (IH : ∀ (d' : Desc) (v' : Value) (encInner : List UInt8),
        Input.length encInner < Input.length enc →
        valueDepth v' < valueDepth v →
        valueWf d' v' → ⟨ v' ∷ d' ⟩ →
        Serializer.recurSt serialValue' valueDepth d' v' = .success () encInner →
        Parser.recurSt parseValue' d' encInner = .success v' Input.default) :
    ∀ kv encElem, kv ∈ valList d v →
        serialVal serialValue d kv = .success () encElem →
        Input.length encElem ≤ Input.length enc →
        ∀ rest, willEncode d kv → serialVal serialValue d kv = .success () encElem →
        (parseVal (fun d' rem =>
          if Input.length rem < Input.length enc then
            Parser.recurSt parseValue' d' rem
          else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) d)
        (Input.app encElem rest) = .success kv rest := by
  intro kv encElem hin hser hbound rest hwf _hser2
  obtain ⟨z, val⟩ := kv
  -- From membership in valList: lookup is some f.
  have hmem : (z, val) ∈ v.vals := (List.mem_filter.mp hin).1
  -- From willEncode: lookup is some f, valWf holds.
  obtain ⟨f, hf, hwfd⟩ := hwf
  -- Normalize `(z, val).1 = z` in hf and hwfd via simp.
  simp only at hf
  -- Now hf : d.fields.lookup z = some f
  -- The serializer succeeded; combined with valWf, this constrains f and val.
  unfold parseVal
  unfold serialVal at hser
  rw [hf] at hser
  -- valWf forces type matching.
  have hwfd' : valWfFold d.fields z val True := hwfd
  unfold valWfFold at hwfd'
  rw [hf] at hwfd'
  cases f with
  | bool =>
    -- val must be .bool b (otherwise valWfFold = False).
    cases val with
    | bool b =>
      -- valWfFold: 0 ≤ z ∧ z < 256 ∧ True
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.1, hwfd'.2.1⟩
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hBP : parseBool (Input.app encB rest) = .success b rest := by
        unfold Serializer.partMap at hB
        simp only at hB
        exact boolParseOk b encB rest trivial hB
      subst hencEq
      show Parser.depConcat _ _
        (Input.app (Input.app encT encB) rest) = _
      unfold Parser.depConcat
      rw [Input.app_assoc, hUnsignedParse]
      simp only [hf]
      show (match Parser.map parseBool (fun b => Val.bool b) (Input.app encB rest) with | _ => _) = _
      unfold Parser.map
      rw [hBP]
    | int _ => exact hwfd'.elim
    | msg _ => exact hwfd'.elim
    | missing => exact hwfd'.elim
  | int =>
    cases val with
    | int z' =>
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.2.1, hwfd'.2.2.1⟩
      have hwfZ' : 0 ≤ z' ∧ z' < 2 ^ 32 := ⟨hwfd'.2.2.2.1, hwfd'.2.2.2.2⟩
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hZP : parseZ32 (Input.app encB rest) = .success z' rest := by
        unfold Serializer.partMap at hB
        simp only at hB
        exact z32ParseOk z' encB rest hwfZ' hB
      subst hencEq
      show Parser.depConcat _ _
        (Input.app (Input.app encT encB) rest) = _
      unfold Parser.depConcat
      rw [Input.app_assoc, hUnsignedParse]
      simp only [hf]
      show (match Parser.map parseZ32 (fun z'' => Val.int z'') (Input.app encB rest) with | _ => _) = _
      unfold Parser.map
      rw [hZP]
    | bool _ => exact hwfd'.elim
    | msg _ => exact hwfd'.elim
    | missing => exact hwfd'.elim
  | msg d' =>
    cases val with
    | msg v' =>
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.2.1, hwfd'.2.2.1⟩
      have hv'_wf : valueWf d' v' := hwfd'.2.2.2
      have hsc_v' : ⟨ v' ∷ d' ⟩ := by
        have hnc := sc_implies_nested_correct d v hsc (z, Val.msg v') hmem
        unfold nestedCorrect at hnc
        rw [hf] at hnc
        exact hnc
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hB' : Serializer.len' serialNatStrict (serialValue d') v' =
          .success () encB := by
        unfold Serializer.partMap at hB
        simp only at hB
        exact hB
      rw [serialLen'_inversion] at hB'
      obtain ⟨encL, encP, hL, hP, hBeq⟩ := hB'
      have hencT_len : Input.length encT = 1 := unsignedLength _ _ hT
      have hencL_len : Input.length encL = 1 := natStrictLength _ _ hL
      have hwfNL : 0 ≤ Input.length encP ∧ Input.length encP < 256 :=
        natStrictStrict _ _ hL
      have hencP_lt_enc : Input.length encP < Input.length enc := by
        have hencElem : Input.length encElem =
            Input.length encT + (Input.length encL + Input.length encP) := by
          subst hBeq; subst hencEq
          rw [Input.app_length, Input.app_length]
        rw [hencT_len, hencL_len] at hencElem
        omega
      have hdepth_lt : valueDepth v' < valueDepth v := by
        rcases v with ⟨vs⟩
        exact valueDepth_msg_in_list z v' vs hmem
      have hPP : Parser.recurSt parseValue' d' encP =
          .success v' Input.default :=
        IH d' v' encP hencP_lt_enc hdepth_lt hv'_wf hsc_v' hP
      subst hBeq; subst hencEq
      show Parser.depConcat _ _ _ = _
      unfold Parser.depConcat
      rw [show Input.app (Input.app encT (Input.app encL encP)) rest =
              Input.app encT (Input.app (Input.app encL encP) rest) by
            rw [Input.app_assoc]]
      rw [hUnsignedParse]
      simp only [hf]
      show (match Parser.map (Parser.len parseNat (fun rem =>
              if Input.length rem < Input.length enc then
                Parser.recurSt parseValue' d' rem
              else Parser.recursiveProgressError "Parser.RecursiveState" enc rem))
              (fun v => Val.msg v)
              (Input.app (Input.app encL encP) rest) with | _ => _) = _
      unfold Parser.map Parser.len Parser.bind
      have hNatParse : parseNat (Input.app (Input.app encL encP) rest) =
          .success (Input.length encP) (Input.app encP rest) := by
        rw [Input.app_assoc]
        exact natStrictParseOk (Input.length encP) encL (Input.app encP rest) hwfNL hL
      rw [hNatParse]
      show (match (Parser.limit (fun rem => if Input.length rem < Input.length enc then
                Parser.recurSt parseValue' d' rem
              else Parser.recursiveProgressError "Parser.RecursiveState" enc rem)
                  (Input.length encP)) (Input.app encP rest) with | _ => _) = _
      unfold Parser.limit
      have hslice : Input.slice (Input.app encP rest) 0 (Input.length encP) = encP :=
        Input.slice_app encP rest
      have hdrop : Input.drop (Input.app encP rest) (Input.length encP) = rest :=
        Input.drop_app encP rest
      have hgated_lt : Input.length encP < Input.length enc := hencP_lt_enc
      simp only [hslice, hdrop, if_pos hgated_lt, hPP, Input.app_default_left]
    | bool _ => exact hwfd'.elim
    | int _ => exact hwfd'.elim
    | missing => exact hwfd'.elim

/-- Per-element correctness for `parseVal` when the IH gives
    `idCompatTransform` for nested messages. -/
private theorem parseVal_serialVal_transform
    (d : Desc) (v : Value) (enc : List UInt8)
    (hdwf : d.AllWF) (hvwf : v.AllWF) (hwf : valueWf d v)
    (IH : ∀ (d' : Desc) (v' : Value) (encInner : List UInt8),
        Input.length encInner < Input.length enc →
        valueDepth v' < valueDepth v →
        valueWf d' v' → d'.AllWF → v'.AllWF →
        Serializer.recurSt serialValue' valueDepth d' v' = .success () encInner →
        Parser.recurSt parseValue' d' encInner =
          .success (idCompatTransform d' v') Input.default) :
    ∀ kv encElem, kv ∈ valList d v →
        serialVal serialValue d kv = .success () encElem →
        Input.length encElem ≤ Input.length enc →
        ∀ rest, willEncode d kv → serialVal serialValue d kv = .success () encElem →
        (parseVal (fun d' rem =>
          if Input.length rem < Input.length enc then
            Parser.recurSt parseValue' d' rem
          else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) d)
        (Input.app encElem rest) = .success (entryTransform d kv) rest := by
  intro kv encElem hin hser hbound rest hwfe _hser2
  obtain ⟨z, val⟩ := kv
  have hmem : (z, val) ∈ v.vals := (List.mem_filter.mp hin).1
  obtain ⟨f, hf, hwfd⟩ := hwfe
  simp only at hf
  unfold parseVal
  unfold serialVal at hser
  rw [hf] at hser
  have hwfd' : valWfFold d.fields z val True := hwfd
  unfold valWfFold at hwfd'
  rw [hf] at hwfd'
  cases f with
  | bool =>
    cases val with
    | bool b =>
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.1, hwfd'.2.1⟩
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hBP : parseBool (Input.app encB rest) = .success b rest := by
        unfold Serializer.partMap at hB; simp only at hB
        exact boolParseOk b encB rest trivial hB
      subst hencEq
      show Parser.depConcat _ _ (Input.app (Input.app encT encB) rest) = _
      unfold Parser.depConcat
      rw [Input.app_assoc, hUnsignedParse]
      simp only [hf]
      show (match Parser.map parseBool (fun b => Val.bool b) (Input.app encB rest) with | _ => _) = _
      unfold Parser.map
      rw [hBP]
      show Result.success (z, Val.bool b) rest = Result.success (entryTransform d (z, Val.bool b)) rest
      unfold entryTransform; rfl
    | int _ => exact hwfd'.elim
    | msg _ => exact hwfd'.elim
    | missing => exact hwfd'.elim
  | int =>
    cases val with
    | int z' =>
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.2.1, hwfd'.2.2.1⟩
      have hwfZ' : 0 ≤ z' ∧ z' < 2 ^ 32 := ⟨hwfd'.2.2.2.1, hwfd'.2.2.2.2⟩
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hZP : parseZ32 (Input.app encB rest) = .success z' rest := by
        unfold Serializer.partMap at hB; simp only at hB
        exact z32ParseOk z' encB rest hwfZ' hB
      subst hencEq
      show Parser.depConcat _ _ (Input.app (Input.app encT encB) rest) = _
      unfold Parser.depConcat
      rw [Input.app_assoc, hUnsignedParse]
      simp only [hf]
      show (match Parser.map parseZ32 (fun z'' => Val.int z'') (Input.app encB rest) with | _ => _) = _
      unfold Parser.map
      rw [hZP]
      show Result.success (z, Val.int z') rest = Result.success (entryTransform d (z, Val.int z')) rest
      unfold entryTransform; rfl
    | bool _ => exact hwfd'.elim
    | msg _ => exact hwfd'.elim
    | missing => exact hwfd'.elim
  | msg d' =>
    cases val with
    | msg v' =>
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.2.1, hwfd'.2.2.1⟩
      have hv'_wf : valueWf d' v' := hwfd'.2.2.2
      have hd'_allwf : d'.AllWF := by
        obtain ⟨_, hfall⟩ := hdwf
        suffices h : fieldAllWF (Field.msg d') by
          cases d' with | mk fs' => exact ⟨h.1, h.2⟩
        have hfall' : ∀ (fs : List (Int × Field)), fieldListAllWF fs → ∀ (k : Int) (f : Field), List.lookup k fs = some f → fieldAllWF f := by
          intros fs hfs k f hf; exact (by
          induction' fs with fs ih generalizing k f <;> simp +decide [ List.lookup ] at hf ⊢;
          cases h : k == fs.1 <;> simp +decide [ h ] at hf ⊢;
          · exact ‹fieldListAllWF ih → ∀ k f, List.lookup k ih = some f → fieldAllWF f› ( by cases hfs ; tauto ) k f hf;
          · cases hfs ; aesop ( simp_config := { singlePass := true } ));
        exact hfall' _ hfall _ _ hf
      have hv'_allwf : v'.AllWF := by
        obtain ⟨_, hvall⟩ := hvwf
        suffices h : valAllWF (Val.msg v') by
          cases v' with | mk vs' => exact ⟨h.1, h.2⟩
        have hvall' : ∀ {l : List (Int × Val)}, (z, Val.msg v') ∈ l → valListAllWF l → valAllWF (Val.msg v') := by
          intros l hmem hvall; induction' l with l ih <;> simp +decide [ valListAllWF ] at hvall hmem ⊢;
          rcases hmem with ( rfl | hmem ) <;> tauto;
        exact hvall' hmem hvall
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hB' : Serializer.len' serialNatStrict (serialValue d') v' =
          .success () encB := by
        unfold Serializer.partMap at hB; simp only at hB; exact hB
      rw [serialLen'_inversion] at hB'
      obtain ⟨encL, encP, hL, hP, hBeq⟩ := hB'
      have hencT_len : Input.length encT = 1 := unsignedLength _ _ hT
      have hencL_len : Input.length encL = 1 := natStrictLength _ _ hL
      have hwfNL : 0 ≤ Input.length encP ∧ Input.length encP < 256 :=
        natStrictStrict _ _ hL
      have hencP_lt_enc : Input.length encP < Input.length enc := by
        have hencElem : Input.length encElem =
            Input.length encT + (Input.length encL + Input.length encP) := by
          subst hBeq; subst hencEq; rw [Input.app_length, Input.app_length]
        rw [hencT_len, hencL_len] at hencElem; omega
      have hdepth_lt : valueDepth v' < valueDepth v := by
        rcases v with ⟨vs⟩; exact valueDepth_msg_in_list z v' vs hmem
      -- KEY DIFFERENCE: IH gives idCompatTransform instead of exact roundtrip.
      have hPP : Parser.recurSt parseValue' d' encP =
          .success (idCompatTransform d' v') Input.default :=
        IH d' v' encP hencP_lt_enc hdepth_lt hv'_wf hd'_allwf hv'_allwf hP
      subst hBeq; subst hencEq
      show Parser.depConcat _ _ _ = _
      unfold Parser.depConcat
      rw [show Input.app (Input.app encT (Input.app encL encP)) rest =
              Input.app encT (Input.app (Input.app encL encP) rest) by
            rw [Input.app_assoc]]
      rw [hUnsignedParse]
      simp only [hf]
      show (match Parser.map (Parser.len parseNat (fun rem =>
              if Input.length rem < Input.length enc then
                Parser.recurSt parseValue' d' rem
              else Parser.recursiveProgressError "Parser.RecursiveState" enc rem))
              (fun v => Val.msg v)
              (Input.app (Input.app encL encP) rest) with | _ => _) = _
      unfold Parser.map Parser.len Parser.bind
      have hNatParse : parseNat (Input.app (Input.app encL encP) rest) =
          .success (Input.length encP) (Input.app encP rest) := by
        rw [Input.app_assoc]
        exact natStrictParseOk (Input.length encP) encL (Input.app encP rest) hwfNL hL
      rw [hNatParse]
      show (match (Parser.limit (fun rem => if Input.length rem < Input.length enc then
                Parser.recurSt parseValue' d' rem
              else Parser.recursiveProgressError "Parser.RecursiveState" enc rem)
                  (Input.length encP)) (Input.app encP rest) with | _ => _) = _
      unfold Parser.limit
      have hslice : Input.slice (Input.app encP rest) 0 (Input.length encP) = encP :=
        Input.slice_app encP rest
      have hdrop : Input.drop (Input.app encP rest) (Input.length encP) = rest :=
        Input.drop_app encP rest
      have hgated_lt : Input.length encP < Input.length enc := hencP_lt_enc
      simp only [hslice, hdrop, if_pos hgated_lt, hPP, Input.app_default_left]
      show Result.success (z, Val.msg (idCompatTransform d' v')) rest =
        Result.success (entryTransform d (z, Val.msg v')) rest
      unfold entryTransform
      simp only [hf]
    | bool _ => exact hwfd'.elim
    | int _ => exact hwfd'.elim
    | missing => exact hwfd'.elim

theorem idInterParseOk (v : Value) (d : Desc) :
    d.AllWF → v.AllWF →
    LimitParseOkCompat'' IdCompatibleWrapper parseValue serialValue d d v := by
  intro hd hv
  -- Use the transform-equality approach: prove parsing produces idCompatTransform d v,
  -- then derive IdCompatible via idCompatRoundTrip.
  -- First, prove the stronger LimitParseOkCompat'' with R = "result equals idCompatTransform".
  suffices hstrong : LimitParseOkCompat'' (fun d₁ _ v v' => v' = idCompatTransform d₁ v)
      parseValue serialValue d d v by
    unfold LimitParseOkCompat'' at hstrong ⊢
    intro enc hwf hser
    obtain ⟨x', hparse, heq⟩ := hstrong enc hwf hser
    exact ⟨x', hparse, heq ▸ idCompatRoundTrip v d hd hv hwf⟩
  -- Apply the recursive-state correctness combinator.
  apply limitRecursiveStateCompat_correct
    (fun d₁ _ v v' => v' = idCompatTransform d₁ v)
    parseValue' serialValue'
    (fun d v => d.AllWF ∧ v.AllWF) (· = ·)
    valueDepth d d v _ ⟨hd, hv⟩ rfl
  -- Per-step proof.
  intro st1 st2 x enc hwf_x ⟨hdwf, hvwf⟩ hlinked IH hser
  subst hlinked
  -- Extract IH in usable form.
  have IH' : ∀ (d' : Desc) (v' : Value) (encInner : List UInt8),
      Input.length encInner < Input.length enc →
      valueDepth v' < valueDepth x →
      valueWf d' v' → d'.AllWF → v'.AllWF →
      Serializer.recurSt serialValue' valueDepth d' v' = .success () encInner →
      Parser.recurSt parseValue' d' encInner =
        .success (idCompatTransform d' v') Input.default := by
    intro d' v' encInner hlen hdep hwfv' hd' hv' hserv'
    obtain ⟨x'', hpar, heq⟩ :=
      IH encInner d' d' v' hlen hdep hwfv' ⟨hd', hv'⟩ rfl hserv'
    subst heq; exact hpar
  -- The witness is idCompatTransform st1 x.
  refine ⟨idCompatTransform st1 x, ?_, rfl⟩
  -- Show parsing produces idCompatTransform st1 x.
  -- Step 1: Unfold serializer.
  have hser_unfold : Serializer.rep
      (serialVal (fun d' v' =>
        if valueDepth v' < valueDepth x then
          Serializer.recurSt serialValue' valueDepth d' v'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          valueDepth x v') st1) (valList st1 x) = .success () enc := by
    have : serialValue' (fun st' x' =>
        if valueDepth x' < valueDepth x then
          Serializer.recurSt serialValue' valueDepth st' x'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          valueDepth x x') st1 x = .success () enc := hser
    unfold serialValue' at this
    show Serializer.rep _ _ = _
    exact this
  -- Step 2: Swap gated/ungated serializer on valList entries.
  have hpointwise : ∀ kv ∈ valList st1 x,
      serialVal (fun d' v' =>
        if valueDepth v' < valueDepth x then
          Serializer.recurSt serialValue' valueDepth d' v'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          valueDepth x v') st1 kv =
      serialVal serialValue st1 kv := by
    intro kv hkv
    obtain ⟨k', val⟩ := kv
    apply serialVal_self_eq_pointwise
    intro d' v' heq
    subst heq
    have hin : (k', Val.msg v') ∈ x.vals := (List.mem_filter.mp hkv).1
    have hdep : valueDepth v' < valueDepth x := by
      rcases x with ⟨vs⟩; exact valueDepth_msg_in_list k' v' vs hin
    show (if valueDepth v' < valueDepth x then
           Serializer.recurSt serialValue' valueDepth d' v'
          else _) = serialValue d' v'
    rw [if_pos hdep]; rfl
  have hser_swap :
      @Serializer.rep' (List UInt8) _ (Int × Val) (willEncode st1)
        (serialVal serialValue st1) (valList st1 x) =
      .success () enc := by
    have heq := serialRep_pointwise_eq
      (serialVal (fun d' v' =>
        if valueDepth v' < valueDepth x then
          Serializer.recurSt serialValue' valueDepth d' v'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          valueDepth x v') st1)
      (serialVal serialValue st1) (valList st1 x) hpointwise
    have h1 : @Serializer.rep' (List UInt8) _ (Int × Val) (valWf st1)
        (serialVal serialValue st1) (valList st1 x) =
        .success () enc := heq.symm.trans hser_unfold
    have hbridge : ∀ (l : List (Int × Val)),
        @Serializer.rep' (List UInt8) _ (Int × Val) (valWf st1)
          (serialVal serialValue st1) l =
        @Serializer.rep' (List UInt8) _ (Int × Val) (willEncode st1)
          (serialVal serialValue st1) l := by
      intro l; induction l with
      | nil => rfl
      | cons hd tl ih => unfold Serializer.rep'; rw [ih]
    rw [← hbridge]; exact h1
  -- Step 3: Well-formedness.
  have hpwf : Serializer.repWf (willEncode st1) (valList st1 x) :=
    parseOk_wf_valid' x st1 hvwf.1 hwf_x
  -- Step 4: Apply repCorrectWeakFullMap.
  have hrep : Parser.rep
      (parseVal (fun d' rem =>
        if Input.length rem < Input.length enc then
          Parser.recurSt parseValue' d' rem
        else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st1)
        enc = .success ((valList st1 x).map (entryTransform st1)) Input.default := by
    apply repCorrectWeakFullMap (willEncode st1) (serialVal serialValue st1)
    · -- Parser at empty input fails recoverably.
      have hpar_def : (parseVal (fun d' rem =>
        if Input.length rem < Input.length enc then
          Parser.recurSt parseValue' d' rem
        else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st1)
          (Input.default : List UInt8) =
        .failure .recoverable ⟨"DepConcat left failed", Input.default,
          .some ⟨"Map underlying failed", Input.default,
            .some ⟨"No more data to parse", Input.default, .none⟩⟩⟩ := by
        unfold parseVal Parser.depConcat parseUnsigned Parser.map parseByte; rfl
      exact ⟨_, _, hpar_def⟩
    · -- Positive encoding length.
      intro kv encE hwfE hserE
      exact willEncode_nonEmpty st1 kv.1 kv.2 encE hwfE hserE
    · -- Per-element correctness.
      intro kv encElem hin hser_e hbound rest hwfE hserE
      exact parseVal_serialVal_transform st1 x enc hdwf hvwf hwf_x IH'
        kv encElem hin hser_e hbound rest hwfE hserE
    · exact hpwf
    · exact hser_swap
    · exact le_refl _
  -- Step 5: Wrap with Parser.map and listToValue.
  show parseValue' (fun st' rem =>
    if Input.length rem < Input.length enc then
      Parser.recurSt parseValue' st' rem
    else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st1 enc =
    .success (idCompatTransform st1 x) Input.default
  show Parser.map (Parser.rep _) _ enc = _
  unfold Parser.map
  rw [hrep]
  -- Step 6: Simplify the match and use the key equality.
  simp only []
  rw [listToValue_map_eq_idCompatTransform st1 x hdwf hvwf hwf_x]

theorem schemaCorrectInterParseOk (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ →
    LimitParseOkCompat'' SchemaCorrectCompatible parseValue serialValue d d v := by
  intro hsc
  apply limitRecursiveStateCompat_correct SchemaCorrectCompatible parseValue' serialValue'
    (fun d v => ⟨ v ∷ d ⟩) (· = ·) valueDepth d d v _ hsc rfl
  -- Per-step correctness with `linkedState = (· = ·)`, so st1 = st2.
  intro st1 st2 x enc hwf_x hsc_x hlinked IH hser
  subst hlinked
  -- The witness is the result of round-tripping through `valList`/`listToValue`.
  refine ⟨listToValue st1 (valList st1 x), ?_, ?_⟩
  · -- Strategy: rewrite the gated serializer to `serialValue` on `valList`
    --   entries (since each entry has strictly smaller depth), then apply
    --   `repCorrectWeakFull` to lift per-element correctness through `Parser.rep`.
    have hser_unfold : Serializer.rep
        (serialVal (fun d' v' =>
          if valueDepth v' < valueDepth x then
            Serializer.recurSt serialValue' valueDepth d' v'
          else Serializer.recursiveProgressError "Serial.RecursiveState"
            valueDepth x v') st1) (valList st1 x) = .success () enc := by
      have : serialValue' (fun st' x' =>
          if valueDepth x' < valueDepth x then
            Serializer.recurSt serialValue' valueDepth st' x'
          else Serializer.recursiveProgressError "Serial.RecursiveState"
            valueDepth x x') st1 x = .success () enc := hser
      unfold serialValue' at this
      show Serializer.rep _ _ = _
      exact this
    -- Swap the gated rec for the ungated `serialValue` on `valList` entries:
    -- nested messages have strictly smaller depth, so the gate is always taken.
    have hpointwise : ∀ kv ∈ valList st1 x,
        serialVal (fun d' v' =>
          if valueDepth v' < valueDepth x then
            Serializer.recurSt serialValue' valueDepth d' v'
          else Serializer.recursiveProgressError "Serial.RecursiveState"
            valueDepth x v') st1 kv =
        serialVal serialValue st1 kv := by
      intro kv hkv
      obtain ⟨k', val⟩ := kv
      apply serialVal_self_eq_pointwise
      intro d' v' heq
      subst heq
      have hin : (k', Val.msg v') ∈ x.vals := (List.mem_filter.mp hkv).1
      have hdep : valueDepth v' < valueDepth x := by
        rcases x with ⟨vs⟩
        exact valueDepth_msg_in_list k' v' vs hin
      show (if valueDepth v' < valueDepth x then
             Serializer.recurSt serialValue' valueDepth d' v'
            else _) = serialValue d' v'
      rw [if_pos hdep]
      rfl
    -- `Serializer.rep'` ignores the phantom `wfα`; bridge between `valWf st1`
    -- and `willEncode st1`.
    have hser_swap :
        @Serializer.rep' (List UInt8) _ (Int × Val) (willEncode st1)
          (serialVal serialValue st1) (valList st1 x) =
        .success () enc := by
      have heq := serialRep_pointwise_eq
        (serialVal (fun d' v' =>
          if valueDepth v' < valueDepth x then
            Serializer.recurSt serialValue' valueDepth d' v'
          else Serializer.recursiveProgressError "Serial.RecursiveState"
            valueDepth x v') st1)
        (serialVal serialValue st1) (valList st1 x) hpointwise
      have h1 : @Serializer.rep' (List UInt8) _ (Int × Val) (valWf st1)
          (serialVal serialValue st1) (valList st1 x) =
          .success () enc := heq.symm.trans hser_unfold
      have hbridge : ∀ (l : List (Int × Val)),
          @Serializer.rep' (List UInt8) _ (Int × Val) (valWf st1)
            (serialVal serialValue st1) l =
          @Serializer.rep' (List UInt8) _ (Int × Val) (willEncode st1)
            (serialVal serialValue st1) l := by
        intro l
        induction l with
        | nil => rfl
        | cons hd tl ih =>
          unfold Serializer.rep'
          rw [ih]
      rw [← hbridge]
      exact h1
    have hbound_le : Input.length enc ≤ Input.length enc := le_refl _
    have hpwf : Serializer.repWf (willEncode st1) (valList st1 x) :=
      parseOk_wf x st1 hsc_x hwf_x
    have hrep : Parser.rep
        (parseVal (fun d' rem =>
          if Input.length rem < Input.length enc then
            Parser.recurSt parseValue' d' rem
          else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st1)
          enc = .success (valList st1 x) Input.default := by
      apply repCorrectWeakFull (willEncode st1) (serialVal serialValue st1)
      · -- (a) `parseVal` at `Input.default` fails recoverably (parseUnsigned
        --     fails on empty input), as required by `repCorrectWeakFull`.
        have hpar_def : (parseVal (fun d' rem =>
          if Input.length rem < Input.length enc then
            Parser.recurSt parseValue' d' rem
          else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st1)
            (Input.default : List UInt8) =
          .failure .recoverable ⟨"DepConcat left failed", Input.default,
            .some ⟨"Map underlying failed", Input.default,
              .some ⟨"No more data to parse", Input.default, .none⟩⟩⟩ := by
          unfold parseVal Parser.depConcat parseUnsigned Parser.map parseByte
          rfl
        exact ⟨_, _, hpar_def⟩
      · -- (b) willEncode-satisfying entries produce > 0 bytes.
        intro kv encE hwfE hserE
        exact willEncode_nonEmpty st1 kv.1 kv.2 encE hwfE hserE
      · -- (c) per-element correctness via `parseVal_serialVal_correct`.
        intro kv encElem hin hser hbound rest hwfE hserE
        -- Project the outer IH (provided by `limitRecursiveStateCompat_correct`)
        -- to depth-bounded inner correctness, using `compatibleEqual` to recover
        -- equality from the `Compatible` relation.
        have IH' : ∀ (d' : Desc) (v' : Value) (encInner : List UInt8),
            Input.length encInner < Input.length enc →
            valueDepth v' < valueDepth x →
            valueWf d' v' → ⟨ v' ∷ d' ⟩ →
            Serializer.recurSt serialValue' valueDepth d' v' = .success () encInner →
            Parser.recurSt parseValue' d' encInner = .success v' Input.default := by
          intro d' v' encInner hlen hdep hwfv' hscv' hserv'
          obtain ⟨v'', hpar, hcompat⟩ :=
            IH encInner d' d' v' hlen hdep hwfv' hscv' rfl hserv'
          have hv_eq : v' = v'' := schemaCorrectCompatibleEqual d' v' d' v'' hcompat rfl
          rw [← hv_eq] at hpar
          exact hpar
        exact parseVal_serialVal_correct st1 x enc hsc_x IH'
          kv encElem hin hser hbound rest hwfE hserE
      · exact hpwf
      · exact hser_swap
      · exact hbound_le
    -- Apply `listToValue` to the parsed list via the outer `Parser.map`.
    show parseValue' (fun st' rem =>
      if Input.length rem < Input.length enc then
        Parser.recurSt parseValue' st' rem
      else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st1 enc =
      .success (listToValue st1 (valList st1 x)) Input.default
    show Parser.map (Parser.rep _) _ enc = _
    unfold Parser.map
    rw [hrep]
  · -- Compatibility: full-descriptor roundtrip yields `SchemaCorrectCompatible`.
    exact fullDescriptor_roundTrip x st1 hsc_x

/-! ## The cross-descriptor round-trip theorem

  `schemaCorrectInterParseOk` and `idInterParseOk` both fix `d₁ = d₂`.  This is
  the general statement: serialize with the writer's descriptor, parse with a
  reader's descriptor that the writer's evolves into, and recover a value
  related by the full compatibility relation `≼` of `Theorems.Compatible`.

  ### Why `d₂.AllWF` is a hypothesis

  `limitRecursiveStateCompat_correct`'s `validState` is threaded on the
  writer's descriptor alone, so the reader's recursive well-formedness has to
  ride in the `linkedState` slot alongside `≪`.  It cannot be recovered from
  `d₁.AllWF` and `d₁ ≪ d₂`: `D-Add` inserts a completely unconstrained field,
  which `not_descCompat_allWF` turns into a counterexample.  (The alternative
  is to put a `fieldAllWF` premise on `D-Add`/`D-Chg`, at the cost of a
  relation that is no longer the report's.)

  ### Proof outline

  1. Reduce with

     ```
     apply limitRecursiveStateCompat_correct MsgCompatWrapper
       parseValue' serialValue'
       (fun d v => d.AllWF ∧ v.AllWF)     -- validState
       (fun a b => a ⋘ b ∧ b.AllWF)       -- linkedState
       valueDepth d₁ d₂ v _ ⟨hd₁, hv⟩ ⟨hcompat, hd₂⟩
     ```

     This elaborates as written; what remains is the per-step goal, with
     `valueWf st₁ x`, `st₁ ⋘ st₂`, `st₂.AllWF` and an IH demanding
     `st₁' ⋘ st₂' ∧ st₂'.AllWF` at nested messages.

  2. Per entry of `valList st₁ x` — the generalization of
     `parseVal_serialVal_correct`, and the bulk of the work.  The writer's key
     `k` has `st₁.get? k = some f₁`, and `descCompat_field` supplies
     `st₂.get? k = some f₂` with `f₁ ∝ f₂`.  Case on `f₁`:

     * `f₁ = .msg d₁'`.  `descCompat_msg` gives `f₂ = .msg d₂'` with
       `d₁' ⋘ d₂'`, and `d₂'.AllWF` follows from `st₂.AllWF`; recurse through
       the IH and close with `V-Msg`.  `fieldCompat_msg_inv` is what rules out
       a scalar `f₂`, which would desynchronize the length-delimited payload.
     * `f₁` scalar.  `fieldCompat_scalar_inv` rules out `f₂ = .msg _`, so the
       payload is four little-endian bytes on both sides: `serialBool b` is
       `serialZ32 (if b then 1 else 0)` and `parseBool` is `parseZ32`
       thresholded.  Four sub-cases, closed by `V-Refl`, `V-Bool-Int` or
       `V-Int-Bool`.  `V-Int-Bool` needs `parseBool`'s `0 < z` test to agree
       with the rule's `z ≠ 0`; it does, because `valWfFold` pins
       `0 ≤ z < 2 ^ 32` on the writer's integers.

  3. Assemble the `≼` derivation over `listToValue st₂ vs`, the way
     `idCompatRoundTrip` assembles `IdCompatible` over `idCompatTransform`:

     | key `k` | rule |
     | --- | --- |
     | in `dom(m₁) ∩ dom(d₁)` | `M-Update`, with step 2's `≺` and `∝` |
     | in `dom(d₁) \ dom(m₁)` | `M-Declare`, at the `f₁ ∝ f₂` from step 2 |
     | in `dom(d₂) \ dom(d₁)` | `M-Missing` |
     | in `dom(m₁) \ dom(d₁)` | `M-Missing`, then `M-Drop-Unknown` — the latter
       constrains only the writer's side, so the two compose |
     | in `dom(d₁) \ dom(d₂)` | unreachable: `descCompat_isSome` |

     `M-Drop` is unreachable from a round trip under `≪`; it is in the relation
     for its own generality, not for this theorem.

  The likely shape of the work is a `compatTransform d₁ d₂ v` mirroring
  `idCompatTransform`, a "parsing yields exactly the transform" lemma, and a
  `compatRoundTrip` mirroring `idCompatRoundTrip`.  `idInterParseOk` above is
  the template throughout.

  This is exactly how the proof below is organized: `compatTransform` lives in
  `Theorems.CompatTransform`, `compatRoundTrip` in
  `Theorems.CompatRoundTrip`, and `parseVal_serialVal_compat` just below is
  step 2. -/

/-- `serialBool b` is the four-byte encoding of the indicator integer. -/
private theorem serialBool_eq_serialZ32 (b : Bool) (encB : List UInt8) :
    serialBool b = .success () encB →
    serialZ32 (if b then 1 else 0) = .success () encB := by
  cases b <;> simp [serialBool]

/-- Reading a four-byte integer payload as a boolean thresholds it at zero. -/
private theorem parseBool_of_serialZ32 (z : Int) (encB rest : List UInt8) :
    0 ≤ z → z < 2 ^ 32 → serialZ32 z = .success () encB →
    parseBool (Input.app encB rest) = .success (decide (0 < z)) rest := by
  intro h1 h2 hser
  have hZP : parseZ32 (Input.app encB rest) = .success z rest :=
    z32ParseOk z encB rest ⟨h1, h2⟩ hser
  unfold parseBool Parser.map
  rw [hZP]

/-- Per-element correctness across descriptors: an entry serialized under the
    writer's descriptor `d₁` parses, under the reader's descriptor `d₂`, to the
    reinterpreted entry `compatEntryTransform d₁ d₂`. -/
private theorem parseVal_serialVal_compat
    (d₁ d₂ : Desc) (v : Value) (enc : List UInt8)
    (hd₁ : d₁.AllWF) (hd₂ : d₂.AllWF) (hvwf : v.AllWF) (hwf : valueWf d₁ v)
    (hc : d₁ ⋘ d₂)
    (IH : ∀ (d₁' d₂' : Desc) (v' : Value) (encInner : List UInt8),
        Input.length encInner < Input.length enc →
        valueDepth v' < valueDepth v →
        valueWf d₁' v' → d₁'.AllWF → v'.AllWF → d₂'.AllWF → d₁' ⋘ d₂' →
        Serializer.recurSt serialValue' valueDepth d₁' v' = .success () encInner →
        Parser.recurSt parseValue' d₂' encInner =
          .success (compatTransform d₁' d₂' v') Input.default) :
    ∀ kv encElem, kv ∈ valList d₁ v →
        serialVal serialValue d₁ kv = .success () encElem →
        Input.length encElem ≤ Input.length enc →
        ∀ rest, willEncode d₁ kv → serialVal serialValue d₁ kv = .success () encElem →
        (parseVal (fun d' rem =>
          if Input.length rem < Input.length enc then
            Parser.recurSt parseValue' d' rem
          else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) d₂)
        (Input.app encElem rest) = .success (compatEntryTransform d₁ d₂ kv) rest := by
  intro kv encElem hin hser hbound rest hwfe _hser2
  obtain ⟨z, val⟩ := kv
  have hmem : (z, val) ∈ v.vals := (List.mem_filter.mp hin).1
  obtain ⟨f, hf, hwfd⟩ := hwfe
  simp only at hf
  -- The reader's field at the same key.
  obtain ⟨f₂, hf₂, hfc⟩ := descCompat_field d₁ d₂ z hc f hf
  have hf₂' : d₂.fields.lookup z = some f₂ := hf₂
  unfold parseVal
  unfold serialVal at hser
  rw [hf] at hser
  have hwfd' : valWfFold d₁.fields z val True := hwfd
  unfold valWfFold at hwfd'
  rw [hf] at hwfd'
  cases f with
  | bool =>
    cases val with
    | bool b =>
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.1, hwfd'.2.1⟩
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hB' : serialBool b = .success () encB := by
        unfold Serializer.partMap at hB; simp only at hB; exact hB
      subst hencEq
      show Parser.depConcat _ _ (Input.app (Input.app encT encB) rest) = _
      unfold Parser.depConcat
      rw [Input.app_assoc, hUnsignedParse]
      cases f₂ with
      | bool =>
        simp only [hf₂']
        have hBP : parseBool (Input.app encB rest) = .success b rest :=
          boolParseOk b encB rest trivial hB'
        show (match Parser.map parseBool (fun b => Val.bool b) (Input.app encB rest)
          with | _ => _) = _
        unfold Parser.map
        rw [hBP]
        show Result.success (z, Val.bool b) rest =
          Result.success (compatEntryTransform d₁ d₂ (z, Val.bool b)) rest
        unfold compatEntryTransform
        rw [show d₂.get? z = some Field.bool from hf₂',
          show d₁.get? z = some Field.bool from hf]
        rfl
      | int =>
        simp only [hf₂']
        have hZ : serialZ32 (if b then 1 else 0) = .success () encB :=
          serialBool_eq_serialZ32 b encB hB'
        have hwf32 : 0 ≤ (if b then (1 : Int) else 0) ∧
            (if b then (1 : Int) else 0) < 2 ^ 32 := by
          cases b <;> norm_num
        have hZP : parseZ32 (Input.app encB rest) =
            .success (if b then 1 else 0) rest :=
          z32ParseOk _ encB rest hwf32 hZ
        show (match Parser.map parseZ32 (fun z' => Val.int z') (Input.app encB rest)
          with | _ => _) = _
        unfold Parser.map
        rw [hZP]
        show Result.success (z, Val.int (if b then 1 else 0)) rest =
          Result.success (compatEntryTransform d₁ d₂ (z, Val.bool b)) rest
        unfold compatEntryTransform
        rw [show d₂.get? z = some Field.int from hf₂',
          show d₁.get? z = some Field.bool from hf]
        rfl
      | msg d₂' =>
        exact absurd rfl (fieldCompat_scalar_inv _ _ hfc (by rintro d ⟨⟩) d₂')
    | int _ => exact hwfd'.elim
    | msg _ => exact hwfd'.elim
    | missing => exact hwfd'.elim
  | int =>
    cases val with
    | int z' =>
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.2.1, hwfd'.2.2.1⟩
      have hwfZ' : 0 ≤ z' ∧ z' < 2 ^ 32 := ⟨hwfd'.2.2.2.1, hwfd'.2.2.2.2⟩
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hB' : serialZ32 z' = .success () encB := by
        unfold Serializer.partMap at hB; simp only at hB; exact hB
      subst hencEq
      show Parser.depConcat _ _ (Input.app (Input.app encT encB) rest) = _
      unfold Parser.depConcat
      rw [Input.app_assoc, hUnsignedParse]
      cases f₂ with
      | bool =>
        simp only [hf₂']
        have hBP : parseBool (Input.app encB rest) =
            .success (decide (0 < z')) rest :=
          parseBool_of_serialZ32 z' encB rest hwfZ'.1 hwfZ'.2 hB'
        show (match Parser.map parseBool (fun b => Val.bool b) (Input.app encB rest)
          with | _ => _) = _
        unfold Parser.map
        rw [hBP]
        show Result.success (z, Val.bool (decide (0 < z'))) rest =
          Result.success (compatEntryTransform d₁ d₂ (z, Val.int z')) rest
        unfold compatEntryTransform
        rw [show d₂.get? z = some Field.bool from hf₂',
          show d₁.get? z = some Field.int from hf]
        rfl
      | int =>
        simp only [hf₂']
        have hZP : parseZ32 (Input.app encB rest) = .success z' rest :=
          z32ParseOk z' encB rest hwfZ' hB'
        show (match Parser.map parseZ32 (fun z'' => Val.int z'') (Input.app encB rest)
          with | _ => _) = _
        unfold Parser.map
        rw [hZP]
        show Result.success (z, Val.int z') rest =
          Result.success (compatEntryTransform d₁ d₂ (z, Val.int z')) rest
        unfold compatEntryTransform
        rw [show d₂.get? z = some Field.int from hf₂',
          show d₁.get? z = some Field.int from hf]
        rfl
      | msg d₂' =>
        exact absurd rfl (fieldCompat_scalar_inv _ _ hfc (by rintro d ⟨⟩) d₂')
    | bool _ => exact hwfd'.elim
    | msg _ => exact hwfd'.elim
    | missing => exact hwfd'.elim
  | msg d₁' =>
    cases val with
    | msg v' =>
      -- The reader's field must be a nested message too.
      obtain ⟨d₂', hd₂'eq, hcompat'⟩ := fieldCompat_msg_inv d₁' f₂ hfc
      subst hd₂'eq
      have hwfZ : 0 ≤ z ∧ z < 256 := ⟨hwfd'.2.1, hwfd'.2.2.1⟩
      have hv'_wf : valueWf d₁' v' := hwfd'.2.2.2
      have hd₁'_allwf : d₁'.AllWF := descAllWF_nested d₁ z d₁' hd₁ hf
      have hd₂'_allwf : d₂'.AllWF := descAllWF_nested d₂ z d₂' hd₂ hf₂
      have hget : v.get? z = some (Val.msg v') :=
        valList_elem_of v d₁ z (Val.msg v') hvwf.1 hin
      have hv'_allwf : v'.AllWF := valueAllWF_nested v z v' hvwf hget
      simp only [Serializer.map, Serializer.opt] at hser
      rw [serialConcat_inversion] at hser
      obtain ⟨encT, encB, hT, hB, hencEq⟩ := hser
      have hUnsignedParse :
          parseUnsigned (Input.app encT (Input.app encB rest)) =
            .success z (Input.app encB rest) :=
        unsignedParseOk z encT (Input.app encB rest) hwfZ hT
      have hB' : Serializer.len' serialNatStrict (serialValue d₁') v' =
          .success () encB := by
        unfold Serializer.partMap at hB; simp only at hB; exact hB
      rw [serialLen'_inversion] at hB'
      obtain ⟨encL, encP, hL, hP, hBeq⟩ := hB'
      have hencT_len : Input.length encT = 1 := unsignedLength _ _ hT
      have hencL_len : Input.length encL = 1 := natStrictLength _ _ hL
      have hwfNL : 0 ≤ Input.length encP ∧ Input.length encP < 256 :=
        natStrictStrict _ _ hL
      have hencP_lt_enc : Input.length encP < Input.length enc := by
        have hencElem : Input.length encElem =
            Input.length encT + (Input.length encL + Input.length encP) := by
          subst hBeq; subst hencEq; rw [Input.app_length, Input.app_length]
        rw [hencT_len, hencL_len] at hencElem; omega
      have hdepth_lt : valueDepth v' < valueDepth v := by
        rcases v with ⟨vs⟩; exact valueDepth_msg_in_list z v' vs hmem
      have hPP : Parser.recurSt parseValue' d₂' encP =
          .success (compatTransform d₁' d₂' v') Input.default :=
        IH d₁' d₂' v' encP hencP_lt_enc hdepth_lt hv'_wf hd₁'_allwf hv'_allwf
          hd₂'_allwf hcompat' hP
      subst hBeq; subst hencEq
      show Parser.depConcat _ _ _ = _
      unfold Parser.depConcat
      rw [show Input.app (Input.app encT (Input.app encL encP)) rest =
              Input.app encT (Input.app (Input.app encL encP) rest) by
            rw [Input.app_assoc]]
      rw [hUnsignedParse]
      simp only [hf₂']
      show (match Parser.map (Parser.len parseNat (fun rem =>
              if Input.length rem < Input.length enc then
                Parser.recurSt parseValue' d₂' rem
              else Parser.recursiveProgressError "Parser.RecursiveState" enc rem))
              (fun v => Val.msg v)
              (Input.app (Input.app encL encP) rest) with | _ => _) = _
      unfold Parser.map Parser.len Parser.bind
      have hNatParse : parseNat (Input.app (Input.app encL encP) rest) =
          .success (Input.length encP) (Input.app encP rest) := by
        rw [Input.app_assoc]
        exact natStrictParseOk (Input.length encP) encL (Input.app encP rest) hwfNL hL
      rw [hNatParse]
      show (match (Parser.limit (fun rem => if Input.length rem < Input.length enc then
                Parser.recurSt parseValue' d₂' rem
              else Parser.recursiveProgressError "Parser.RecursiveState" enc rem)
                  (Input.length encP)) (Input.app encP rest) with | _ => _) = _
      unfold Parser.limit
      have hslice : Input.slice (Input.app encP rest) 0 (Input.length encP) = encP :=
        Input.slice_app encP rest
      have hdrop : Input.drop (Input.app encP rest) (Input.length encP) = rest :=
        Input.drop_app encP rest
      simp only [hslice, hdrop, if_pos hencP_lt_enc, hPP, Input.app_default_left]
      show Result.success (z, Val.msg (compatTransform d₁' d₂' v')) rest =
        Result.success (compatEntryTransform d₁ d₂ (z, Val.msg v')) rest
      unfold compatEntryTransform
      rw [show d₂.get? z = some (Field.msg d₂') from hf₂',
        show d₁.get? z = some (Field.msg d₁') from hf]
      rfl
    | bool _ => exact hwfd'.elim
    | int _ => exact hwfd'.elim
    | missing => exact hwfd'.elim

/-- Cross-descriptor round-trip correctness: a value serialized under `d₁` and
    parsed under any `d₂` the writer's schema evolves into (`d₁ ⋘ d₂`) is
    recovered up to the full compatibility relation `≼`.

    Generalizes `idInterParseOk`, which is the `d₁ = d₂` case at `D-Refl` —
    `msgCompat_of_idCompatible` records that `≼` really does subsume
    `IdCompatible` there.

    See the outline above. -/
theorem compatInterParseOk (v : Value) (d₁ d₂ : Desc) :
    d₁.AllWF → v.AllWF → d₂.AllWF → d₁ ⋘ d₂ →
    LimitParseOkCompat'' MsgCompatWrapper parseValue serialValue d₁ d₂ v := by
  intro hd₁ hv hd₂ hc
  -- As for `idInterParseOk`: first prove the stronger statement that parsing
  -- produces exactly `compatTransform`, then hand it to `compatRoundTrip`.
  suffices hstrong : LimitParseOkCompat'' (fun a b v v' => v' = compatTransform a b v)
      parseValue serialValue d₁ d₂ v by
    unfold LimitParseOkCompat'' at hstrong ⊢
    intro enc hwf hser
    obtain ⟨x', hparse, heq⟩ := hstrong enc hwf hser
    exact ⟨x', hparse, heq ▸ compatRoundTrip v d₁ d₂ hd₁ hv hd₂ hc hwf⟩
  apply limitRecursiveStateCompat_correct
    (fun a b v v' => v' = compatTransform a b v)
    parseValue' serialValue'
    (fun d v => d.AllWF ∧ v.AllWF) (fun a b => a ⋘ b ∧ b.AllWF)
    valueDepth d₁ d₂ v _ ⟨hd₁, hv⟩ ⟨hc, hd₂⟩
  -- Per-step proof.
  intro st1 st2 x enc hwf_x ⟨hdwf, hvwf⟩ ⟨hlink, hd2wf⟩ IH hser
  -- Extract the induction hypothesis in usable form.
  have IH' : ∀ (d₁' d₂' : Desc) (v' : Value) (encInner : List UInt8),
      Input.length encInner < Input.length enc →
      valueDepth v' < valueDepth x →
      valueWf d₁' v' → d₁'.AllWF → v'.AllWF → d₂'.AllWF → d₁' ⋘ d₂' →
      Serializer.recurSt serialValue' valueDepth d₁' v' = .success () encInner →
      Parser.recurSt parseValue' d₂' encInner =
        .success (compatTransform d₁' d₂' v') Input.default := by
    intro d₁' d₂' v' encInner hlen hdep hwfv' hd₁' hv' hd₂' hc' hserv'
    obtain ⟨x'', hpar, heq⟩ :=
      IH encInner d₁' d₂' v' hlen hdep hwfv' ⟨hd₁', hv'⟩ ⟨hc', hd₂'⟩ hserv'
    subst heq; exact hpar
  refine ⟨compatTransform st1 st2 x, ?_, rfl⟩
  -- Step 1: unfold the serializer.
  have hser_unfold : Serializer.rep
      (serialVal (fun d' v' =>
        if valueDepth v' < valueDepth x then
          Serializer.recurSt serialValue' valueDepth d' v'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          valueDepth x v') st1) (valList st1 x) = .success () enc := by
    have : serialValue' (fun st' x' =>
        if valueDepth x' < valueDepth x then
          Serializer.recurSt serialValue' valueDepth st' x'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          valueDepth x x') st1 x = .success () enc := hser
    unfold serialValue' at this
    show Serializer.rep _ _ = _
    exact this
  -- Step 2: swap the gated serializer for the ungated one on `valList` entries.
  have hpointwise : ∀ kv ∈ valList st1 x,
      serialVal (fun d' v' =>
        if valueDepth v' < valueDepth x then
          Serializer.recurSt serialValue' valueDepth d' v'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          valueDepth x v') st1 kv =
      serialVal serialValue st1 kv := by
    intro kv hkv
    obtain ⟨k', val⟩ := kv
    apply serialVal_self_eq_pointwise
    intro d' v' heq
    subst heq
    have hin : (k', Val.msg v') ∈ x.vals := (List.mem_filter.mp hkv).1
    have hdep : valueDepth v' < valueDepth x := by
      rcases x with ⟨vs⟩; exact valueDepth_msg_in_list k' v' vs hin
    show (if valueDepth v' < valueDepth x then
           Serializer.recurSt serialValue' valueDepth d' v'
          else _) = serialValue d' v'
    rw [if_pos hdep]; rfl
  have hser_swap :
      @Serializer.rep' (List UInt8) _ (Int × Val) (willEncode st1)
        (serialVal serialValue st1) (valList st1 x) =
      .success () enc := by
    have heq := serialRep_pointwise_eq
      (serialVal (fun d' v' =>
        if valueDepth v' < valueDepth x then
          Serializer.recurSt serialValue' valueDepth d' v'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          valueDepth x v') st1)
      (serialVal serialValue st1) (valList st1 x) hpointwise
    have h1 : @Serializer.rep' (List UInt8) _ (Int × Val) (valWf st1)
        (serialVal serialValue st1) (valList st1 x) =
        .success () enc := heq.symm.trans hser_unfold
    have hbridge : ∀ (l : List (Int × Val)),
        @Serializer.rep' (List UInt8) _ (Int × Val) (valWf st1)
          (serialVal serialValue st1) l =
        @Serializer.rep' (List UInt8) _ (Int × Val) (willEncode st1)
          (serialVal serialValue st1) l := by
      intro l; induction l with
      | nil => rfl
      | cons hd tl ih => unfold Serializer.rep'; rw [ih]
    rw [← hbridge]; exact h1
  -- Step 3: well-formedness of the entry list.
  have hpwf : Serializer.repWf (willEncode st1) (valList st1 x) :=
    parseOk_wf_valid' x st1 hvwf.1 hwf_x
  -- Step 4: lift per-element correctness through `Parser.rep`.
  have hrep : Parser.rep
      (parseVal (fun d' rem =>
        if Input.length rem < Input.length enc then
          Parser.recurSt parseValue' d' rem
        else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st2)
        enc = .success ((valList st1 x).map (compatEntryTransform st1 st2))
          Input.default := by
    apply repCorrectWeakFullMap (willEncode st1) (serialVal serialValue st1)
    · -- Parser at empty input fails recoverably.
      have hpar_def : (parseVal (fun d' rem =>
        if Input.length rem < Input.length enc then
          Parser.recurSt parseValue' d' rem
        else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st2)
          (Input.default : List UInt8) =
        .failure .recoverable ⟨"DepConcat left failed", Input.default,
          .some ⟨"Map underlying failed", Input.default,
            .some ⟨"No more data to parse", Input.default, .none⟩⟩⟩ := by
        unfold parseVal Parser.depConcat parseUnsigned Parser.map parseByte; rfl
      exact ⟨_, _, hpar_def⟩
    · -- Positive encoding length.
      intro kv encE hwfE hserE
      exact willEncode_nonEmpty st1 kv.1 kv.2 encE hwfE hserE
    · -- Per-element correctness.
      intro kv encElem hin hser_e hbound rest hwfE hserE
      exact parseVal_serialVal_compat st1 st2 x enc hdwf hd2wf hvwf hwf_x hlink IH'
        kv encElem hin hser_e hbound rest hwfE hserE
    · exact hpwf
    · exact hser_swap
    · exact le_refl _
  -- Step 5: wrap with `Parser.map` and `listToValue`.
  show parseValue' (fun st' rem =>
    if Input.length rem < Input.length enc then
      Parser.recurSt parseValue' st' rem
    else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st2 enc =
    .success (compatTransform st1 st2 x) Input.default
  show Parser.map (Parser.rep _) _ enc = _
  unfold Parser.map
  rw [hrep]
  simp only []
  rw [listToValue_map_eq_compatTransform st1 st2 x hd2wf.1 hvwf.1 hwf_x hlink]

end Pollux.InterParse
