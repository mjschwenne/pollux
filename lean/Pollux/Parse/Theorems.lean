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
  sorry

theorem epsilon_correct :
    @ParseOk ι _ Unit _ Parser.epsilon Serializer.epsilon := by
  sorry

/-! ## Bind correctness -/

theorem bind_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (rp : α → Parser ι β) (rs : Serializer ι β wfβ)
    (tag : β → α) (ls : (r : β) → Serializer ι α (fun l => l = tag r ∧ wfα l))
    (r : β) :
    ParseOk lp (ls r) → ParseOk (rp (tag r)) rs →
    ParseOk' (Parser.bind lp rp) (Serializer.bind tag ls rs) r := by
  sorry

theorem bind'_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (ls : Serializer ι α wfα)
    (rp : α → Parser ι β) (rs : Serializer ι β wfβ) (tag : β → α) (r : β) :
    ParseOk lp ls → ParseOk' (rp (tag r)) rs r →
    ParseOk' (Parser.bind lp rp) (Serializer.bind' tag ls rs) r := by
  sorry

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
  sorry

/-! ## Concat correctness -/

theorem serialConcat_inversion {wfα : α → Prop} {wfβ : β → Prop}
    (serα : Serializer ι α wfα) (serβ : Serializer ι β wfβ)
    (a : α) (b : β) (enc : ι) :
    Serializer.concat serα serβ (a, b) = .success () enc ↔
    ∃ encα encβ, serα a = .success () encα ∧
                 serβ b = .success () encβ ∧
                 enc = Input.app encα encβ := by
  sorry

theorem concat_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (ls : Serializer ι α wfα)
    (rp : Parser ι β) (rs : Serializer ι β wfβ) :
    ParseOk lp ls → ParseOk rp rs →
    ParseOk (Parser.concat lp rp) (Serializer.concat ls rs) := by
  sorry

theorem depConcat_correct {wfα : α → Prop} {wfβ : β → Prop}
    (lp : Parser ι α) (ls : Serializer ι α wfα)
    (rp : α → Parser ι β) (rs : Serializer ι β wfβ) (l : α) (r : β) :
    ParseOk lp ls → ParseOk' (rp l) rs r →
    ParseOk' (Parser.depConcat lp rp) (Serializer.concat ls rs) (l, r) := by
  sorry

/-! ## Limit / Len correctness -/

theorem limit_correct {wf : α → Prop} (lenFn : α → Nat)
    (ser : Serializer ι α wf) (par : Parser ι α) (x : α) :
    LimitParseOk par ser → LenOk ser lenFn x →
    ParseOk' (Parser.limit par (lenFn x)) (Serializer.limit ser lenFn) x := by
  sorry

theorem len_correct {wfα : α → Prop} {wfn : Nat → Prop}
    (serLen : Serializer ι Nat wfn) (parLen : Parser ι Nat) (lenFn : α → Nat)
    (serX : Serializer ι α wfα) (parX : Parser ι α) (x : α) :
    ParseOk parLen serLen → LimitParseOk parX serX → LenOk serX lenFn x →
    ParseOk' (Parser.len parLen parX) (Serializer.len lenFn serLen serX) x := by
  sorry

theorem len'_correct {wfα : α → Prop} {wfn : Nat → Prop}
    (serLen : Serializer ι Nat wfn) (parLen : Parser ι Nat)
    (serX : Serializer ι α wfα) (parX : Parser ι α) :
    ParseOk parLen serLen → LimitParseOk parX serX →
    ParseOk (Parser.len parLen parX) (Serializer.len' serLen serX) := by
  sorry

theorem serialLen'_inversion {wfn : Nat → Prop} {wfα : α → Prop}
    (serN : Serializer ι Nat wfn) (serX : Serializer ι α wfα)
    (x : α) (enc : ι) :
    Serializer.len' serN serX x = .success () enc ↔
    ∃ encN encX, serN (Input.length encX) = .success () encN ∧
                 serX x = .success () encX ∧
                 enc = Input.app encN encX := by
  sorry

/-! ## Map correctness -/

theorem map_correct {wfβ : β → Prop}
    (par : Parser ι β) (ser : Serializer ι β wfβ)
    (to : α → β) (from_ : β → α)
    (inv : ∀ x, from_ (to x) = x) :
    ParseOk par ser →
    ParseOk (Parser.map par from_) (Serializer.map ser to) := by
  sorry

/-! ## Repetition correctness -/

theorem serialRep_first_inversion {wfα : α → Prop}
    (ser : Serializer ι α wfα) (x : α) (xs : List α) (enc : ι) :
    Serializer.rep ser (x :: xs) = .success () enc ↔
    ∃ encX encRest, ser x = .success () encX ∧
                    Serializer.rep ser xs = .success () encRest ∧
                    enc = Input.app encX encRest := by
  sorry

theorem rep_correct {wfα : α → Prop}
    (ser : Serializer ι α wfα) (par : Parser ι α) :
    (∃ msg data, par (Input.default : ι) =
      Result.failure .recoverable (.mk msg Input.default data)) →
    (∀ x enc, wfα x → ser x = .success () enc → Input.length enc > 0) →
    ParseOk par ser →
    LimitParseOk (Parser.rep par) (Serializer.rep ser) := by
  sorry

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
  sorry

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
  sorry

theorem parser_recur_unfold (underlying : Parser ι α → Parser ι α) (inp : ι) :
    Parser.recur underlying inp =
    underlying (fun rem =>
      if Input.length rem < Input.length inp then Parser.recur underlying rem
      else Parser.recursiveProgressError "Parser.Recursive" inp rem) inp := by
  sorry

theorem serializer_recur_unfold {wf : α → Prop}
    (underlying : Serializer ι α wf → Serializer ι α wf)
    (depth : α → Nat) (x : α) :
    Serializer.recur underlying depth x =
    underlying (fun x' =>
      if depth x' < depth x then Serializer.recur underlying depth x'
      else Serializer.recursiveProgressError "Serial.Recursive" depth x x') x := by
  sorry

theorem parser_recurSt_unfold
    (underlying : (σ → Parser ι α) → σ → Parser ι α) (st : σ) (inp : ι) :
    Parser.recurSt underlying st inp =
    underlying (fun st' rem =>
      if Input.length rem < Input.length inp then
        Parser.recurSt underlying st' rem
      else Parser.recursiveProgressError "Parser.RecursiveState" inp rem
    ) st inp := by
  sorry

theorem serializer_recurSt_unfold {wf : σ → α → Prop}
    (underlying : (∀ s : σ, Serializer ι α (wf s)) →
      ∀ s : σ, Serializer ι α (wf s))
    (depth : α → Nat) (st : σ) (x : α) :
    Serializer.recurSt underlying depth st x =
    underlying (fun st' x' =>
      if depth x' < depth x then Serializer.recurSt underlying depth st' x'
      else Serializer.recursiveProgressError "Serial.RecursiveState" depth x x'
    ) st x := by
  sorry

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
  sorry

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
  sorry

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
    (ser : Serializer ι β wfβ) (to : α → β)
    (par : Parser ι β) (from_ : β → α) :
    ∀ x enc rest,
    R x (from_ (to x)) → ParseOk par ser →
    ParseOkSimpleRel'''' R (Parser.map par from_) (Serializer.map ser to)
      x (from_ (to x)) enc rest := by
  sorry

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
  sorry

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
  sorry

end Relational

end Pollux.Parse.Theorems
