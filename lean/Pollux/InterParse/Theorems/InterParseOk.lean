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

/-- The "weak full" version of `repCorrect`: only requires per-element correctness
    on elements actually in the list, with bounded encoding length. Adapted from
    Rocq's `RepCorrectWeakFull`.  The well-formedness predicate `wfα` is taken
    explicitly so it can differ from the serializer's intrinsic phantom wf.  The
    serializer is taken as a raw function to avoid the phantom wfα mismatch. -/
private theorem repCorrectWeakFull {α : Type} (wfα : α → Prop)
    (ser : α → Result (List UInt8) Unit) (par : Parser (List UInt8) α)
    (l : List α) (bound : Nat) :
    (∃ msg data, par (Input.default : List UInt8) =
      .failure .recoverable ⟨msg, Input.default, data⟩) →
    (∀ x enc, wfα x → ser x = .success () enc → Input.length enc > 0) →
    (∀ x encElem, x ∈ l → ser x = .success () encElem →
        Input.length encElem ≤ bound →
        ∀ rest, wfα x → ser x = .success () encElem →
        par (Input.app encElem rest) = .success x rest) →
    ∀ enc, Serializer.repWf wfα l →
        @Serializer.rep' (List UInt8) _ α wfα ser l = .success () enc →
        Input.length enc ≤ bound →
        Parser.rep par enc = .success l Input.default := by
  intro hparEmp hpro
  induction l with
  | nil =>
    intro hpOk enc _hwf hser _hbound
    have henc : enc = Input.default := by
      show enc = (Input.default : List UInt8)
      have : @Serializer.rep' (List UInt8) _ α wfα ser [] = .success () Input.default := rfl
      rw [this] at hser
      injection hser with _ h; exact h.symm
    subst henc
    obtain ⟨msg, data, hpar⟩ := hparEmp
    show Parser.rep par Input.default = _
    unfold Parser.rep
    rw [parser_rep'_unfold]
    rw [hpar]
  | cons hd tl ih =>
    intro hpOk enc ⟨hwfH, hwfT⟩ hser hbound
    -- Inversion of Serializer.rep' on cons.
    -- Key observation: serialRep_first_inversion proves it for Serializer.rep,
    -- and Serializer.rep ser xs = Serializer.rep' ser xs by definition. We can
    -- get the right form by bridging.
    have hser2 : @Serializer.rep (List UInt8) _ α wfα ser (hd :: tl) =
        .success () enc := hser
    rw [serialRep_first_inversion] at hser2
    obtain ⟨encH, encT, hH, hT, henc⟩ := hser2
    have hT : @Serializer.rep' (List UInt8) _ α wfα ser tl = .success () encT := hT
    have hHlen_pos : Input.length encH > 0 := hpro hd encH hwfH hH
    have hHlen : Input.length encH ≤ bound := by
      subst henc; rw [Input.app_length] at hbound; omega
    have hTlen : Input.length encT ≤ bound := by
      subst henc; rw [Input.app_length] at hbound; omega
    have hpOk_tl : ∀ x encElem, x ∈ tl → ser x = .success () encElem →
        Input.length encElem ≤ bound → ∀ rest, wfα x → ser x = .success () encElem →
        par (Input.app encElem rest) = .success x rest :=
      fun x encElem hx => hpOk x encElem (List.mem_cons_of_mem _ hx)
    have hH_par : par (Input.app encH encT) = .success hd encT :=
      hpOk hd encH List.mem_cons_self hH hHlen encT hwfH hH
    have hT_par : Parser.rep par encT = .success tl Input.default :=
      ih hpOk_tl encT hwfT hT hTlen
    subst henc
    show Parser.rep par (Input.app encH encT) = _
    unfold Parser.rep
    rw [parser_rep'_unfold, hH_par]
    have hlen : Input.length encT < Input.length (Input.app encH encT) := by
      rw [Input.app_length]; omega
    have : Parser.rep' par encT = .success tl Input.default := hT_par
    show (if Input.length encT < Input.length (Input.app encH encT) then
            match Parser.rep' par encT with | _ => _ else _) = _
    rw [if_pos hlen]
    show (match Parser.rep' par encT with | _ => _) = _
    rw [this]

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

theorem interParseOk (v : Value) (d : Desc) :
    ⟨ v ∷ d ⟩ →
    LimitParseOkCompat'' Compatible parseValue serialValue d d v := by
  intro hsc
  apply limitRecursiveStateCompat_correct Compatible parseValue' serialValue'
    (fun d v => ⟨ v ∷ d ⟩) (· = ·) valueDepth d d v _ hsc rfl
  -- The remaining goal: per-step correctness.
  intro st1 st2 x enc hwf_x hsc_x hlinked IH hser
  -- Subst st1 = st2.
  subst hlinked
  -- The witness is `listToValue st1 (valList st1 x)`.
  refine ⟨listToValue st1 (valList st1 x), ?_, ?_⟩
  · -- Parser side. The serializer step result is `serialValue' (rec_fun) st1 x`,
    -- which by definition equals `Serializer.map (Serializer.rep (serialVal (rec_fun) st1)) (valList st1) x`
    -- = `Serializer.rep (serialVal (rec_fun) st1) (valList st1 x)`.
    -- And the recurSt-bound version equals serialValue st1 x at the top, so we need to bridge.
    -- First show that the gated rec_fun produces the same encoding as the ungated serialValue
    -- on entries of valList. This is the same trick as `serialValue_eq_rep`.
    -- Since `hser` already gives us success () enc for the gated form, we need to show
    -- the parser gated form succeeds.
    -- Approach: Apply repCorrectWeakFull. We need:
    --   1. par (default) = recoverable failure
    --   2. ser produces > 0 bytes
    --   3. per-element ParseOk''
    -- Then we get Parser.rep par enc = .success (valList st1 x) Input.default.
    -- And the parser step is Parser.map (Parser.rep par) (listToValue st1) on enc,
    -- giving us .success (listToValue st1 (valList st1 x)) Input.default.
    --
    -- Decompose hser: serialValue' (rec_ser) st1 x = success () enc means
    -- Serializer.rep (serialVal (rec_ser) st1) (valList st1 x) = success () enc.
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
    -- We need to swap the gated serializer with `serialValue` (ungated) on entries
    -- of valList st1 x, to apply our existing primitive parse correctness.
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
      have hin : (k', Val.msg v') ∈ x.vals :=
        (List.mem_filter.mp hkv).1
      have hdep : valueDepth v' < valueDepth x := by
        rcases x with ⟨vs⟩
        exact valueDepth_msg_in_list k' v' vs hin
      show (if valueDepth v' < valueDepth x then
             Serializer.recurSt serialValue' valueDepth d' v'
            else _) = serialValue d' v'
      rw [if_pos hdep]
      rfl
    -- `Serializer.rep ser xs` doesn't depend on the phantom wfα.
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
      -- Bridge phantom wfα: induct on the list to get a true equality.
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
    -- Now use repCorrectWeakFull. First establish a few preliminaries:
    -- (a) parseUnsigned default = recoverable failure
    -- (b) willEncode-elements produce > 0 bytes
    -- (c) per-element correctness
    have hbound_le : Input.length enc ≤ Input.length enc := le_refl _
    have hpwf : Serializer.repWf (willEncode st1) (valList st1 x) :=
      parseOk_wf x st1 hsc_x hwf_x
    -- The parser side: we need to evaluate `parseValue' (rec_par) st2 enc` where
    -- rec_par is the gated form. parseValue' = Parser.map (Parser.rep (parseVal _ st1)) listToValue.
    -- After Parser.rep computes the list, Parser.map applies listToValue.
    -- So the goal reduces to showing Parser.rep _ enc = .success (valList st1 x) Input.default.
    -- Need: Parser.rep (parseVal (rec_par) st1) enc = .success (valList st1 x) Input.default.
    have hrep : Parser.rep
        (parseVal (fun d' rem =>
          if Input.length rem < Input.length enc then
            Parser.recurSt parseValue' d' rem
          else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st1)
          enc = .success (valList st1 x) Input.default := by
      apply repCorrectWeakFull (willEncode st1) (serialVal serialValue st1)
      -- (a) par default = recoverable failure
      · -- parseVal at default: starts with parseUnsigned which fails recoverably on empty input
        -- Compute parseVal Input.default explicitly.
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
      -- (b) willEncode produces > 0 bytes
      · intro kv encE hwfE hserE
        exact willEncode_nonEmpty st1 kv.1 kv.2 encE hwfE hserE
      -- (c) per-element correctness
      · intro kv encElem hin hser hbound
        -- Need: ParseOk'' (parser with ungated rec_par for nested) (serialVal serialValue) kv encElem.
        -- But we have ParseOk'' relative to the gated serializer-form. Wait — the elements
        -- of valList come with serialVal _ st1 ... (the swapped one).
        -- We use parseVal_serialVal_correct. Note: hser : serialVal serialValue st1 kv = .success () encElem.
        intro rest hwfE hserE
        -- Establish the IH for parseVal_serialVal_correct: depth-bounded inner correctness.
        have IH' : ∀ (d' : Desc) (v' : Value) (encInner : List UInt8),
            Input.length encInner < Input.length enc →
            valueDepth v' < valueDepth x →
            valueWf d' v' → ⟨ v' ∷ d' ⟩ →
            Serializer.recurSt serialValue' valueDepth d' v' = .success () encInner →
            Parser.recurSt parseValue' d' encInner = .success v' Input.default := by
          intro d' v' encInner hlen hdep hwfv' hscv' hserv'
          -- Apply the original IH from limitRecursiveStateCompat_correct with linked_state = eq.
          obtain ⟨v'', hpar, hcompat⟩ := IH encInner d' d' v' hlen hdep hwfv' hscv' rfl hserv'
          -- v'' = v' by compatibleEqual.
          have hv_eq : v' = v'' := compatibleEqual d' v' d' v'' hcompat rfl
          rw [← hv_eq] at hpar
          exact hpar
        exact parseVal_serialVal_correct st1 x enc hsc_x IH' kv encElem hin hser hbound
          rest hwfE hserE
      · exact hpwf
      · exact hser_swap
      · exact hbound_le
    -- Now use hrep to evaluate the goal.
    show parseValue' (fun st' rem =>
      if Input.length rem < Input.length enc then
        Parser.recurSt parseValue' st' rem
      else Parser.recursiveProgressError "Parser.RecursiveState" enc rem) st1 enc =
      .success (listToValue st1 (valList st1 x)) Input.default
    show Parser.map (Parser.rep _) _ enc = _
    unfold Parser.map
    rw [hrep]
  · -- Compatibility: Compatible st1 st1 x (listToValue st1 (valList st1 x)).
    exact fullDescriptor_roundTrip x st1 hsc_x

end Pollux.InterParse
