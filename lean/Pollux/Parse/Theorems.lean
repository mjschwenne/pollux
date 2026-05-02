/-
  Pollux.Parse.Theorems — Correctness definitions and theorem statements.

  Corresponds to src/parse/Theorems.v and src/parse/TheoremsRel.v in the Rocq
  development.

  The central notion is **ParseOk**: a parser/serializer pair is correct when
  serializing a well-formed value and then parsing the result recovers the
  original value (with arbitrary trailing data preserved).
-/
import Pollux.Parse.Parser
import Pollux.Parse.Serializer
import Mathlib

namespace Pollux.Parse.Theorems

variable {ι : Type} [Input ι]
variable {α β σ : Type}

/-! ## Core correctness definitions -/

/-- Most specific: fixed `x`, `enc`, `rest`. -/
def ParseOk''' {wf : α → Prop}
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) (enc rest : ι) : Prop :=
  wf x → ser x = .success () enc → par (Input.app enc rest) = .success x rest

/-- Fixed `x`, `enc`; universally quantified over `rest`. -/
def ParseOk'' {wf : α → Prop}
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) (enc : ι) : Prop :=
  ∀ rest, ParseOk''' par ser x enc rest

/-- Fixed `x`; universally quantified over `enc` and `rest`. -/
def ParseOk' {wf : α → Prop}
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) : Prop :=
  ∀ enc, ParseOk'' par ser x enc

/-- Full correctness: for all well-formed values, serializing then parsing
    recovers the value with arbitrary trailing data. -/
def ParseOk {wf : α → Prop} (par : Parser ι α) (ser : Serializer ι α wf) : Prop :=
  ∀ x, ParseOk' par ser x

/-! ## Limit correctness (no trailing data) -/

/-- Correctness without trailing data: parser consumes exactly the encoding. -/
def LimitParseOkFull {wf : α → Prop}
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) (enc : ι) : Prop :=
  wf x → ser x = .success () enc → par enc = .success x Input.default

def LimitParseOkWeak {wf : α → Prop}
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) : Prop :=
  ∀ enc, LimitParseOkFull par ser x enc

def LimitParseOk {wf : α → Prop}
    (par : Parser ι α) (ser : Serializer ι α wf) : Prop :=
  ∀ x, LimitParseOkWeak par ser x

/-! ## Length correctness -/

/-- The declared length function agrees with the actual encoding length. -/
def LenOk {wf : α → Prop}
    (ser : Serializer ι α wf) (lenFn : α → Nat) (x : α) : Prop :=
  ∀ enc, ser x = .success () enc → lenFn x = Input.length enc

/-! ## Basic combinator correctness -/

theorem succeedWith_correct (x : α) :
    @ParseOk' ι _ α _ (Parser.succeedWith x) Serializer.succeedWith x := by
  intro enc rest
  -- `succeedWith` serializes to `Input.default`, so the parser sees `rest`.
  have : ∀ (s : ι), Input.app Input.default s = s := Input.app_default_left
  unfold ParseOk''' Serializer.succeedWith; aesop

theorem epsilon_correct :
    @ParseOk ι _ Unit _ Parser.epsilon Serializer.epsilon := by
  intro x enc rest _ h
  injection h
  unfold Parser.epsilon Parser.succeedWith
  rw [← ‹Input.default = enc›, Input.app_default_left]

/-! ## Bind correctness -/

theorem bind_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (rp : α → Parser ι β) (rs : Serializer ι β wfβ)
    (tag : β → α) (ls : (r : β) → Serializer ι α (fun l => l = tag r ∧ wfα l))
    (r : β) :
    ParseOk lp (ls r) → ParseOk (rp (tag r)) rs →
    ParseOk' (Parser.bind lp rp) (Serializer.bind tag ls rs) r := by
  intro hlp hrp x enc
  generalize_proofs at *
  intro h1 h2
  obtain ⟨lEnc, rEnc, hl, hr, henc⟩ : ∃ lEnc rEnc,
      ls r (tag r) = .success () lEnc ∧ rs r = .success () rEnc ∧
      x = Input.app lEnc rEnc := by
    unfold Serializer.bind at h2; aesop
  have := hlp (tag r); have := hrp r
  simp_all +decide [ParseOk, ParseOk', ParseOk'', ParseOk''']
  unfold Parser.bind; simp +decide [*, Input.app_assoc]
  rw [hlp _ _ _ rfl h1.1 rfl]; simp +decide [this _ _ h1.2 rfl]

theorem bind'_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (ls : Serializer ι α wfα)
    (rp : α → Parser ι β) (rs : Serializer ι β wfβ) (tag : β → α) (r : β) :
    ParseOk lp ls → ParseOk' (rp (tag r)) rs r →
    ParseOk' (Parser.bind lp rp) (Serializer.bind' tag ls rs) r := by
  intro hlp hrs enc hser hpar
  unfold Serializer.bind'Wf at hpar; unfold Serializer.bind' at *
  simp_all +decide [ParseOk]
  intro h
  obtain ⟨lEnc, rEnc, hlEnc, hrEnc, henc⟩ : ∃ lEnc rEnc,
      ls (tag r) = .success () lEnc ∧ rs r = .success () rEnc ∧
      enc = Input.app lEnc rEnc := by
    unfold Serializer.concat at h; aesop
  have := hlp (tag r) lEnc
  have := hrs rEnc hser
  simp_all +decide [ParseOk''', ParseOk'']
  unfold Parser.bind; simp_all +decide [Input.app_assoc]

/-! ## BindSucceeds correctness -/

def BindSucceedsRightOk {wfβ : β → Prop}
    (rp : α → ι → Parser ι β) (rs : Serializer ι β wfβ) (tag : β → α) : Prop :=
  ∀ r rEnc rest, ParseOk''' (rp (tag r) (Input.app rEnc rest)) rs r rEnc rest

def BindSucceedsLeftOk {wfα : α → Prop}
    (lp : Parser ι α) (ls : β → ι → Serializer ι α wfα) (tag : β → α) : Prop :=
  ∀ r lEnc rEnc rest,
    ParseOk''' lp (ls r rEnc) (tag r) lEnc (Input.app rEnc rest)

theorem bindSucceeds_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (ls : β → ι → Serializer ι α wfα)
    (rp : α → ι → Parser ι β) (rs : Serializer ι β wfβ) (tag : β → α) :
    BindSucceedsRightOk rp rs tag → BindSucceedsLeftOk lp ls tag →
    ParseOk (Parser.bindSucceeds lp rp) (Serializer.bindSucceeds tag ls rs) := by
  unfold ParseOk BindSucceedsRightOk BindSucceedsLeftOk ParseOk'
    Parser.bindSucceeds Serializer.bindSucceeds ParseOk'' ParseOk'''
    Serializer.bindSucceedsWf
  grind +suggestions

/-! ## Concat correctness -/

theorem serialConcat_inversion {wfα : α → Prop} {wfβ : β → Prop}
    (serα : Serializer ι α wfα) (serβ : Serializer ι β wfβ)
    (a : α) (b : β) (enc : ι) :
    Serializer.concat serα serβ (a, b) = .success () enc ↔
    ∃ encα encβ, serα a = .success () encα ∧
                 serβ b = .success () encβ ∧
                 enc = Input.app encα encβ := by
  unfold Serializer.concat; aesop

theorem concat_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (ls : Serializer ι α wfα)
    (rp : Parser ι β) (rs : Serializer ι β wfβ) :
    ParseOk lp ls → ParseOk rp rs →
    ParseOk (Parser.concat lp rp) (Serializer.concat ls rs) := by
  intro hlp hrp x enc rest hαβ hser
  obtain ⟨encα, encβ, hserα, hserβ, henc⟩ : ∃ encα encβ,
      ls x.1 = .success () encα ∧ rs x.2 = .success () encβ ∧
      enc = Input.app encα encβ := by
    exact (serialConcat_inversion ls rs x.1 x.2 enc).mp hser
  have := hlp x.1 encα
  have := hrp x.2 encβ
  unfold ParseOk'' ParseOk''' at *
  simp_all +decide [Serializer.concatWf]
  simp_all +decide [Parser.concat, Input.app_assoc]

theorem depConcat_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (ls : Serializer ι α wfα)
    (rp : α → Parser ι β) (rs : Serializer ι β wfβ) (l : α) (r : β) :
    ParseOk lp ls → ParseOk' (rp l) rs r →
    ParseOk' (Parser.depConcat lp rp) (Serializer.concat ls rs) (l, r) := by
  intro h1 h2 enc rest h3 h4
  obtain ⟨encα, encβ, h5, h6, h7⟩ : ∃ encα encβ,
      ls l = .success () encα ∧ rs r = .success () encβ ∧
      enc = Input.app encα encβ := by
    exact (serialConcat_inversion ls rs l r enc).mp h4
  have := h1 l encα
  unfold Parser.depConcat
  rw [h7, Input.app_assoc]
  rw [this _ h3.1 h5]
  simp +decide [h2 encβ rest h3.2 h6]

/-! ## Limit / Len correctness -/

theorem limit_correct {wf : α → Prop} (lenFn : α → Nat)
    (ser : Serializer ι α wf) (par : Parser ι α) (x : α) :
    LimitParseOk par ser → LenOk ser lenFn x →
    ParseOk' (Parser.limit par (lenFn x)) (Serializer.limit ser lenFn) x := by
  intro h1 h2 enc
  unfold ParseOk''
  intro rest
  simp [ParseOk''', Parser.limit, Serializer.limit]
  intro hx hser
  have hslice : Input.slice (Input.app enc rest) 0 (lenFn x) = enc := by
    have := h2 enc hser
    have := h1 x enc; simp_all +decide [LimitParseOkFull]
    exact Input.slice_app enc rest
  have hdrop : Input.drop (Input.app enc rest) (lenFn x) = rest := by
    have := h2 enc hser
    rw [this]
    exact Input.drop_app enc rest
  have := h1 x
  have := this enc; simp_all +decide [LimitParseOkFull]
  exact Input.app_default_left rest

theorem len_correct {wfα : α → Prop} {wfn : Nat → Prop}
    (serLen : Serializer ι Nat wfn) (parLen : Parser ι Nat) (lenFn : α → Nat)
    (serX : Serializer ι α wfα) (parX : Parser ι α) (x : α) :
    ParseOk parLen serLen → LimitParseOk parX serX → LenOk serX lenFn x →
    ParseOk' (Parser.len parLen parX) (Serializer.len lenFn serLen serX) x := by
  intro h1 h2 h3
  apply bind'_correct
  · assumption
  · exact limit_correct lenFn serX parX x h2 h3

theorem len'_correct {wfα : α → Prop} {wfn : Nat → Prop}
    (serLen : Serializer ι Nat wfn) (parLen : Parser ι Nat)
    (serX : Serializer ι α wfα) (parX : Parser ι α) :
    ParseOk parLen serLen → LimitParseOk parX serX →
    ParseOk (Parser.len parLen parX) (Serializer.len' serLen serX) := by
  intro h1 h2 x enc rest hx hser
  -- `Serializer.len'` produces a length-prefixed encoding.
  obtain ⟨encLen, encBody, henc⟩ : ∃ encLen encBody,
      enc = Input.app encLen encBody ∧
      serLen (Input.length encBody) = .success () encLen ∧
      serX x = .success () encBody := by
    unfold Serializer.len' at hser
    grind +qlia
  -- Reduce to `len_correct` with the actual encoding length.
  have := len_correct serLen parLen
    (fun x => Input.length (Serializer.out (serX x))) serX parX x
  simp_all +decide [Parser.len]
  have := this (by
    intro enc' hser'; unfold Serializer.out at *; aesop)
  convert this (Input.app encLen encBody) rest _ _ using 1
  · unfold Serializer.lenWf
    unfold Serializer.len'Wf at hx; aesop
  · unfold Serializer.len Serializer.bind' Serializer.concat Serializer.limit
    simp +decide [henc]
    rw [show Serializer.out (Result.success () encBody) = encBody from rfl]
    aesop

theorem serialLen'_inversion {wfn : Nat → Prop} {wfα : α → Prop}
    (serN : Serializer ι Nat wfn) (serX : Serializer ι α wfα)
    (x : α) (enc : ι) :
    Serializer.len' serN serX x = .success () enc ↔
    ∃ encN encX, serN (Input.length encX) = .success () encN ∧
                 serX x = .success () encX ∧
                 enc = Input.app encN encX := by
  unfold Serializer.len'; aesop

/-! ## Map correctness -/

theorem map_correct {wfβ : β → Prop}
    (par : Parser ι β) (ser : Serializer ι β wfβ)
    (to_ : α → β) (from_ : β → α)
    (inv : ∀ x, from_ (to_ x) = x) :
    ParseOk par ser →
    ParseOk (Parser.map par from_) (Serializer.map ser to_) := by
  unfold ParseOk Parser.map ParseOk' ParseOk'' ParseOk'''
    Serializer.map Serializer.mapWf
  grind

/-! ## Repetition correctness -/

theorem serialRep_first_inversion {wfα : α → Prop}
    (ser : Serializer ι α wfα) (x : α) (xs : List α) (enc : ι) :
    Serializer.rep ser (x :: xs) = .success () enc ↔
    ∃ encX encRest, ser x = .success () encX ∧
                    Serializer.rep ser xs = .success () encRest ∧
                    enc = Input.app encX encRest := by
  refine ⟨?_, ?_⟩
  · intro h
    unfold Serializer.rep Serializer.rep' at h
    cases h' : ser x <;> cases h'' : ser.rep' xs <;> aesop
  · rintro ⟨encX, encRest, hx, hxs, rfl⟩
    unfold Serializer.rep Serializer.rep'
    unfold Serializer.rep at hxs; aesop

theorem rep_correct {wfα : α → Prop}
    (ser : Serializer ι α wfα) (par : Parser ι α) :
    (∃ msg data, par (Input.default : ι) =
      Result.failure .recoverable (.mk msg Input.default data)) →
    (∀ x enc, wfα x → ser x = .success () enc → Input.length enc > 0) →
    ParseOk par ser →
    LimitParseOk (Parser.rep par) (Serializer.rep ser) := by
  intros h1 h2 h3
  intro x enc h
  induction x generalizing enc <;> simp_all +decide [Serializer.rep]
  · -- nil: empty list; encoding must be `Input.default`, parser yields `[]`.
    intro h4
    have h_empty : enc = Input.default := by cases h4; aesop
    unfold Parser.rep Parser.rep'; aesop
  · -- cons: split encoding by `serialRep_first_inversion`, parse head with
    --       `h3`, recurse on tail.
    intro h_enc
    obtain ⟨encX, encRest, hencX, hencRest, henc⟩ : ∃ encX encRest,
        ser ‹_› = .success () encX ∧
        Serializer.rep ser ‹_› = .success () encRest ∧
        enc = Input.app encX encRest := by
      exact (serialRep_first_inversion ser _ _ enc).mp h_enc
    have h_head : par (Input.app encX encRest) = .success ‹_› encRest := by
      cases h; tauto
    have h_tail : par.rep encRest = .success ‹_› Input.default := by
      cases h; aesop
    rw [henc, Parser.rep, Parser.rep']
    -- Strict progress is needed to take the recursive branch.
    have h_len : Input.length encRest < Input.length (Input.app encX encRest) := by
      have := h2 _ _ (by cases h; tauto) hencX
      rw [Input.app_length encX encRest]; omega
    unfold Parser.rep at h_tail; aesop

/-! ## Unfold lemmas -/

theorem parser_rep'_unfold (underlying : Parser ι α) (inp : ι) :
    Parser.rep' underlying inp =
    match underlying inp with
    | .success x rem =>
      if Input.length rem < Input.length inp then
        match Parser.rep' underlying rem with
        | .success xs rest        => .success (x :: xs) rest
        | .failure .recoverable _ => .success [x] rem
        | .failure .fatal data    => .failure .fatal data
      else .failure .fatal
        ⟨"Parser.Rep underlying increased input length", rem, .none⟩
    | .failure .recoverable ⟨_, rem, _⟩ => .success [] rem
    | .failure .fatal data => .failure .fatal data := by
  rw [Parser.rep']
  congr! 2

theorem parser_repFold'_unfold (underlying : Parser ι β) (combine : α → β → α)
    (acc : α) (inp : ι) :
    Parser.repFold' underlying combine acc inp =
    match underlying inp with
    | .success ret rem =>
      if Input.length rem < Input.length inp then
        Parser.repFold' underlying combine (combine acc ret) rem
      else .success acc inp
    | .failure lvl data =>
      let r : Result ι β := .failure lvl data
      if r.needsAlternative inp then .success acc inp
      else .failure lvl data := by
  rw [Parser.repFold'];
  cases h : underlying inp <;> aesop

theorem parser_recur_unfold (underlying : Parser ι α → Parser ι α) (inp : ι) :
    Parser.recur underlying inp =
    underlying (fun rem =>
      if Input.length rem < Input.length inp then Parser.recur underlying rem
      else Parser.recursiveProgressError "Parser.Recursive" inp rem) inp := by
  rw [Parser.recur]

theorem serializer_recur_unfold {wf : α → Prop}
    (underlying : Serializer ι α wf → Serializer ι α wf)
    (depth : α → Nat) (x : α) :
    Serializer.recur underlying depth x =
    underlying (fun x' =>
      if depth x' < depth x then Serializer.recur underlying depth x'
      else Serializer.recursiveProgressError "Serial.Recursive" depth x x') x :=
  Serializer.recur.eq_def underlying depth x

theorem parser_recurSt_unfold
    (underlying : (σ → Parser ι α) → σ → Parser ι α) (st : σ) (inp : ι) :
    Parser.recurSt underlying st inp =
    underlying (fun st' rem =>
      if Input.length rem < Input.length inp then
        Parser.recurSt underlying st' rem
      else Parser.recursiveProgressError "Parser.RecursiveState" inp rem
    ) st inp := by
  rw [Parser.recurSt]

theorem serializer_recurSt_unfold {wf : σ → α → Prop}
    (underlying : (∀ s : σ, Serializer ι α (wf s)) →
      ∀ s : σ, Serializer ι α (wf s))
    (depth : α → Nat) (st : σ) (x : α) :
    Serializer.recurSt underlying depth st x =
    underlying (fun st' x' =>
      if depth x' < depth x then Serializer.recurSt underlying depth st' x'
      else Serializer.recursiveProgressError "Serial.RecursiveState" depth x x'
    ) st x := by
  rw [ Serializer.recurSt]

/-! ## Recursive combinator correctness -/

theorem recursive_correct {wf : α → Prop}
    (parU : Parser ι α → Parser ι α)
    (serU : Serializer ι α wf → Serializer ι α wf) (depth : α → Nat) :
    (∀ x enc rest,
      wf x →
      (∀ inp' x', Input.length inp' < Input.length (Input.app enc rest) →
        depth x' < depth x → wf x' → ∀ rest',
        Serializer.recur serU depth x' = .success () inp' →
        Parser.recur parU (Input.app inp' rest') = .success x' rest') →
      serU (fun x' =>
        if depth x' < depth x then Serializer.recur serU depth x'
        else Serializer.recursiveProgressError "Serial.Recursive" depth x x') x =
        .success () enc →
      parU (fun rem =>
        if Input.length rem < Input.length (Input.app enc rest) then
          Parser.recur parU rem
        else Parser.recursiveProgressError "Parser.Recursive"
          (Input.app enc rest) rem) (Input.app enc rest) =
        .success x rest) →
    ParseOk (Parser.recursive parU) (Serializer.recursive serU depth) := by
  intro h x enc rest wf_x
  -- Strong induction on `depth x'` proves correctness for all values of
  -- smaller depth, which we then feed to the user-supplied step `h`.
  have h_ind : ∀ x' (enc' : ι) (rest' : ι),
      depth x' < depth x → wf x' →
      Serializer.recur serU depth x' = .success () enc' →
      Parser.recur parU (Input.app enc' rest') = .success x' rest' := by
    intros x' enc' rest' hx'_lt hx'_wf hx'_ser
    induction' n : depth x' using Nat.strong_induction_on with n ih
      generalizing x' enc' rest'
    grind +suggestions
  convert h x enc rest wf_x _ using 1
  · rw [Serializer.recursive, Serializer.recur]
  · rw [Parser.recursive, parser_recur_unfold]
  · exact fun inp' x' _ h₂ h₃ rest' h₄ => h_ind x' inp' rest' h₂ h₃ h₄

theorem recursiveState_correct {wf : α → Prop}
    (parU : (σ → Parser ι α) → σ → Parser ι α)
    (serU : (σ → Serializer ι α wf) → σ → Serializer ι α wf)
    (validState : σ → α → Prop) (depth : α → Nat) (st : σ) (x : α) :
    (∀ st x enc rest,
      wf x → validState st x →
      (∀ inp' st' x', Input.length inp' < Input.length (Input.app enc rest) →
        depth x' < depth x → wf x' → validState st' x' → ∀ rest',
        Serializer.recurSt serU depth st' x' = .success () inp' →
        Parser.recurSt parU st' (Input.app inp' rest') = .success x' rest') →
      serU (fun st' x' =>
        if depth x' < depth x then Serializer.recurSt serU depth st' x'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          depth x x') st x = .success () enc →
      parU (fun st' rem =>
        if Input.length rem < Input.length (Input.app enc rest) then
          Parser.recurSt parU st' rem
        else Parser.recursiveProgressError "Parser.RecursiveState"
          (Input.app enc rest) rem) st (Input.app enc rest) =
        .success x rest) →
    validState st x →
    ParseOk' (Parser.recursiveState parU st)
      (Serializer.recursiveState serU depth st) x := by
  unfold Parser.recursiveState Serializer.recursiveState at *
  intro h₁ h₂ enc
  -- Proof by contradiction: extract a counterexample, then derive correctness
  -- by strong induction on `depth x`.
  apply Classical.byContradiction
  intro h_contra
  obtain ⟨enc, rest, henc⟩ : ∃ enc rest,
      wf x ∧ validState st x ∧
      Serializer.recurSt serU depth st x = .success () enc ∧
      ¬Parser.recurSt parU st (Input.app enc rest) = .success x rest := by
    unfold ParseOk'' at h_contra; simp_all +decide
    unfold ParseOk''' at h_contra; simp_all +decide
  obtain ⟨henc_wf, henc_valid, henc_ser, henc_par⟩ := henc
  have h_ind : ∀ n, (∀ x, depth x ≤ n → ∀ st, validState st x →
      ∀ enc rest, wf x → validState st x →
      Serializer.recurSt serU depth st x = .success () enc →
      Parser.recurSt parU st (Input.app enc rest) = .success x rest) := by
    intro n x hx st hst enc rest henc_wf henc_valid henc_ser
    induction' n using Nat.strong_induction_on with n ih generalizing x st enc rest
    specialize h₁ st x enc rest henc_wf henc_valid
    rw [parser_recurSt_unfold]
    apply h₁
    · exact fun inp' st' x' h₁ h₂ h₃ h₄ rest' h₅ =>
        ih _ (by linarith) _ (by linarith) _ h₄ _ _ h₃ h₄ h₅
    · rw [← henc_ser, serializer_recurSt_unfold]
  exact henc_par <| h_ind _ _ le_rfl _ henc_valid _ _ henc_wf henc_valid henc_ser

/-! ## Relational correctness (TheoremsRel) -/

section Relational

/-- Relational correctness: the parsed value is related to the serialized value
    via `R`, rather than being equal. -/
def ParseOkSimpleRel'''' {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf)
    (x x' : α) (enc rest : ι) : Prop :=
  wf x → ser x = .success () enc →
  par (Input.app enc rest) = .success x' rest ∧ R x x'

def ParseOkSimpleRel''' {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf)
    (x : α) (enc rest : ι) : Prop :=
  ∃ x', ParseOkSimpleRel'''' R par ser x x' enc rest

def ParseOkSimpleRel'' {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) (enc : ι) : Prop :=
  ∀ rest, ParseOkSimpleRel''' R par ser x enc rest

def ParseOkSimpleRel' {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) : Prop :=
  ∀ enc, ParseOkSimpleRel'' R par ser x enc

def ParseOkSimpleRel {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf) : Prop :=
  ∀ x, ParseOkSimpleRel' R par ser x

/-- Limit version of relational correctness (no trailing data). -/
def LimitParseOkSimpleRel''' {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf)
    (x x' : α) (enc : ι) : Prop :=
  wf x → ser x = .success () enc →
  par enc = .success x' Input.default ∧ R x x'

def LimitParseOkSimpleRel'' {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) (enc : ι) : Prop :=
  ∃ x', LimitParseOkSimpleRel''' R par ser x x' enc

def LimitParseOkSimpleRel' {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf) (x : α) : Prop :=
  ∀ enc, LimitParseOkSimpleRel'' R par ser x enc

def LimitParseOkSimpleRel {wf : α → Prop} (R : α → α → Prop)
    (par : Parser ι α) (ser : Serializer ι α wf) : Prop :=
  ∀ x, LimitParseOkSimpleRel' R par ser x

/-- Descriptor-parameterized relational correctness.  Allows serialization
    with descriptor `d₁` and parsing with `d₂`, relating values via `R`. -/
def ParseOkCompat {δ : Type} {wf : δ → α → Prop} (R : δ → δ → α → α → Prop)
    (par : δ → Parser ι α) (ser : ∀ d, Serializer ι α (wf d)) : Prop :=
  ∀ d₁ d₂ x enc rest,
    wf d₁ x → ser d₁ x = .success () enc →
    ∃ x', par d₂ (Input.app enc rest) = .success x' rest ∧ R d₁ d₂ x x'

/-- Limit version of descriptor-parameterized relational correctness. -/
def LimitParseOkCompat {δ : Type} {wf : δ → α → Prop}
    (R : δ → δ → α → α → Prop)
    (par : δ → Parser ι α) (ser : ∀ d, Serializer ι α (wf d)) : Prop :=
  ∀ d₁ d₂ x enc,
    wf d₁ x → ser d₁ x = .success () enc →
    ∃ x', par d₂ enc = .success x' Input.default ∧ R d₁ d₂ x x'

-- Partially-quantified versions for composing proofs
def ParseOkCompat'' {δ : Type} {wf : δ → α → Prop}
    (R : δ → δ → α → α → Prop)
    (par : δ → Parser ι α) (ser : ∀ d, Serializer ι α (wf d))
    (d₁ d₂ : δ) (x : α) : Prop :=
  ∀ enc rest,
    wf d₁ x → ser d₁ x = .success () enc →
    ∃ x', par d₂ (Input.app enc rest) = .success x' rest ∧ R d₁ d₂ x x'

def LimitParseOkCompat'' {δ : Type} {wf : δ → α → Prop}
    (R : δ → δ → α → α → Prop)
    (par : δ → Parser ι α) (ser : ∀ d, Serializer ι α (wf d))
    (d₁ d₂ : δ) (x : α) : Prop :=
  ∀ enc,
    wf d₁ x → ser d₁ x = .success () enc →
    ∃ x', par d₂ enc = .success x' Input.default ∧ R d₁ d₂ x x'

/-! ### Relational theorems -/

theorem mapCompat_correct {wfβ : β → Prop} (R : α → α → Prop)
    (ser : Serializer ι β wfβ) (to_ : α → β)
    (par : Parser ι β) (from_ : β → α) :
    ∀ x enc rest,
    R x (from_ (to_ x)) → ParseOk par ser →
    ParseOkSimpleRel'''' R (Parser.map par from_) (Serializer.map ser to_)
      x (from_ (to_ x)) enc rest := by
  intros x enc rest hR hpar h₀ h₁
  have h_map : par (Input.app enc rest) = .success (to_ x) rest :=
    hpar (to_ x) enc rest h₀ h₁
  unfold Parser.map; aesop

theorem recursiveStateCompat_correct {wf : σ → α → Prop}
    (R : σ → σ → α → α → Prop)
    (parU : (σ → Parser ι α) → σ → Parser ι α)
    (serU : (∀ s : σ, Serializer ι α (wf s)) →
      ∀ s : σ, Serializer ι α (wf s))
    (validState : σ → α → Prop) (linkedState : σ → σ → Prop)
    (depth : α → Nat) (st₁ st₂ : σ) (x : α) :
    (∀ st₁ st₂ x enc rest,
      wf st₁ x → validState st₁ x → linkedState st₁ st₂ →
      (∀ inp' st₁' st₂' x',
        Input.length inp' < Input.length (Input.app enc rest) →
        depth x' < depth x →
        wf st₁' x' → validState st₁' x' → linkedState st₁' st₂' →
        ∀ rest',
        Serializer.recurSt serU depth st₁' x' = .success () inp' →
        ∃ x'', Parser.recurSt parU st₂' (Input.app inp' rest') =
          .success x'' rest' ∧ R st₁' st₂' x' x'') →
      serU (fun st' x' =>
        if depth x' < depth x then Serializer.recurSt serU depth st' x'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          depth x x') st₁ x = .success () enc →
      ∃ x',
        parU (fun st' rem =>
          if Input.length rem < Input.length (Input.app enc rest) then
            Parser.recurSt parU st' rem
          else Parser.recursiveProgressError "Parser.RecursiveState"
            (Input.app enc rest) rem) st₂ (Input.app enc rest) =
          .success x' rest ∧ R st₁ st₂ x x') →
    validState st₁ x → linkedState st₁ st₂ →
    ParseOkCompat'' R
      (Parser.recursiveState parU) (Serializer.recursiveState serU depth)
      st₁ st₂ x := by
  intro h hx₁ hx₂ enc rest
  induction' n : depth x using Nat.strong_induction_on with n ih
    generalizing st₁ st₂ x enc rest
  contrapose! h
  refine ⟨st₁, st₂, x, enc, rest, h.1, hx₁, hx₂, ?_, ?_⟩
  · intro inp' st₁' st₂' x' _ h₂ h₃ h₄ h₅ rest' h₆
    exact ih _ (by linarith) _ _ _ h₄ h₅ _ _ rfl h₃ h₆
  · unfold Serializer.recursiveState Parser.recursiveState at h
    unfold Serializer.recurSt Parser.recurSt at h
    grind

theorem limitRecursiveStateCompat_correct {wf : σ → α → Prop}
    (R : σ → σ → α → α → Prop)
    (parU : (σ → Parser ι α) → σ → Parser ι α)
    (serU : (∀ s : σ, Serializer ι α (wf s)) →
      ∀ s : σ, Serializer ι α (wf s))
    (validState : σ → α → Prop) (linkedState : σ → σ → Prop)
    (depth : α → Nat) (st₁ st₂ : σ) (x : α) :
    (∀ st₁ st₂ x enc,
      wf st₁ x → validState st₁ x → linkedState st₁ st₂ →
      (∀ inp' st₁' st₂' x',
        Input.length inp' < Input.length enc →
        depth x' < depth x →
        wf st₁' x' → validState st₁' x' → linkedState st₁' st₂' →
        Serializer.recurSt serU depth st₁' x' = .success () inp' →
        ∃ x'', Parser.recurSt parU st₂' inp' =
          .success x'' Input.default ∧ R st₁' st₂' x' x'') →
      serU (fun st' x' =>
        if depth x' < depth x then Serializer.recurSt serU depth st' x'
        else Serializer.recursiveProgressError "Serial.RecursiveState"
          depth x x') st₁ x = .success () enc →
      ∃ x',
        parU (fun st' rem =>
          if Input.length rem < Input.length enc then
            Parser.recurSt parU st' rem
          else Parser.recursiveProgressError "Parser.RecursiveState"
            enc rem) st₂ enc =
          .success x' Input.default ∧ R st₁ st₂ x x') →
    validState st₁ x → linkedState st₁ st₂ →
    LimitParseOkCompat'' R
      (Parser.recursiveState parU) (Serializer.recursiveState serU depth)
      st₁ st₂ x := by
  unfold LimitParseOkCompat'' Parser.recursiveState Serializer.recursiveState
  intro h₁ h₂ h₃ enc h₄
  induction' n : depth x using Nat.strong_induction_on with n ih
    generalizing st₁ st₂ x enc
  intro h₅
  grind +suggestions

end Relational

end Pollux.Parse.Theorems