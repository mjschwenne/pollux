/-
  Pollux.Parse.Serializer — Serializer type and combinators.

  Corresponds to src/parse/Serializer.v in the Rocq development.

  A serializer is the dual of a parser: given a value, it produces an encoded
  byte sequence (carried in the `enc` field of `Result.success`).  Each
  serializer is parameterized by a well-formedness predicate `wf` that
  describes which values it can successfully encode; the predicate is a phantom
  parameter at the computational level and only appears in theorem statements.
-/
import Pollux.Parse.Input
import Pollux.Parse.Result

namespace Pollux.Parse

/-- A serializer encodes values of type `α` into the input type `ι`.
    The `wf` predicate constrains which values can be successfully encoded;
    it is phantom (unused computationally) and only relevant in correctness proofs. -/
abbrev Serializer (ι α : Type) (_wf : α → Prop) := α → Result ι Unit

namespace Serializer

variable {ι : Type} [Input ι]
variable {α β σ : Type}

/-- Serializer output type (same as the input type). -/
abbrev Output (ι : Type) := ι

/-- Extract the encoded output from a serializer result. -/
abbrev out (r : Result ι Unit) : ι := r.getEnc

/-- Trivial well-formedness: every value is well-formed. -/
def trivialWf : α → Prop := fun _ => True

/-! ### Basic combinators -/

/-- Produces the empty encoding for any input. -/
def succeedWith : Serializer ι α trivialWf :=
  fun _ => .success () Input.default

/-- Unit serializer producing the empty encoding. -/
def epsilon : Serializer ι Unit trivialWf := succeedWith

/-- Always fails with the given message. -/
def failWith (msg : String) (lvl : Level) : Serializer ι α trivialWf :=
  fun _ => .failure lvl ⟨msg, Input.default, .none⟩

/-- Always returns a precomputed result. -/
def resultWith (r : Result ι Unit) : Serializer ι α trivialWf :=
  fun _ => r

/-- Identity serializer: the value *is* the encoding. -/
def blob : Serializer ι ι trivialWf :=
  fun b => .success () b

/-! ### Concat -/

def concatWf (wfα : α → Prop) (wfβ : β → Prop) : α × β → Prop :=
  fun ⟨a, b⟩ => wfα a ∧ wfβ b

def concat {wfα : α → Prop} {wfβ : β → Prop}
    (left : Serializer ι α wfα) (right : Serializer ι β wfβ) :
    Serializer ι (α × β) (concatWf wfα wfβ) :=
  fun ⟨l, r⟩ =>
    match left l, right r with
    | .success () lEnc, .success () rEnc =>
      .success () (Input.app lEnc rEnc)
    | .failure lvl data, .success () rEnc =>
      .failure lvl ⟨"Concat left failed, right succeeded", rEnc, .some data⟩
    | .success () lEnc, .failure lvl data =>
      .failure lvl ⟨"Concat right failed, left succeeded", lEnc, .some data⟩
    | .failure lLvl lData, .failure rLvl rData =>
      .failure (lLvl.max rLvl)
        ⟨"Concat both failed", Input.default, .some (lData.concat rData)⟩

/-! ### Bind variants -/

def bind'Wf (wfα : α → Prop) (wfβ : β → Prop) (tag : β → α) : β → Prop :=
  fun r => wfα (tag r) ∧ wfβ r

/-- Serialize by first encoding `tag r` with `left`, then `r` with `right`,
    and appending the encodings. -/
def bind' {wfα : α → Prop} {wfβ : β → Prop}
    (tag : β → α) (left : Serializer ι α wfα) (right : Serializer ι β wfβ) :
    Serializer ι β (bind'Wf wfα wfβ tag) :=
  fun r => concat left right (tag r, r)

def bindWf (wfα : α → Prop) (wfβ : β → Prop) (tag : β → α) : β → Prop :=
  fun r => wfα (tag r) ∧ wfβ r

/-- Like `bind'`, but `left` receives the original value `r` and may produce a
    tag-specific serializer. -/
def bind {wfα : α → Prop} {wfβ : β → Prop}
    (tag : β → α)
    (left : (r : β) → Serializer ι α (fun l => l = tag r ∧ wfα l))
    (right : Serializer ι β wfβ) :
    Serializer ι β (bindWf wfα wfβ tag) :=
  fun r =>
    match left r (tag r) with
    | .success () lEnc =>
      match right r with
      | .success () rEnc => .success () (Input.app lEnc rEnc)
      | .failure lvl data =>
        .failure lvl ⟨"Bind serializing body failed", lEnc, .some data⟩
    | .failure lvl data =>
      .failure lvl ⟨"Bind serializing tag failed", Input.default, .some data⟩

def bindSucceedsWf (wfα : α → Prop) (wfβ : β → Prop) (tag : β → α) : β → Prop :=
  fun r => wfα (tag r) ∧ wfβ r

/-- Serialize body first, then use its encoding to serialize the tag.
    Dual of `Parser.bindSucceeds`. -/
def bindSucceeds {wfα : α → Prop} {wfβ : β → Prop}
    (tag : β → α)
    (left : β → ι → Serializer ι α wfα)
    (right : Serializer ι β wfβ) :
    Serializer ι β (bindSucceedsWf wfα wfβ tag) :=
  fun r =>
    match right r with
    | .success () rEnc =>
      match left r rEnc (tag r) with
      | .success () lEnc => .success () (Input.app lEnc rEnc)
      | .failure lvl data =>
        .failure lvl ⟨"BindSucceeds serializing tag failed", rEnc, .some data⟩
    | .failure lvl data =>
      .failure lvl ⟨"BindSucceeds serializing body failed", Input.default, .some data⟩

def bindResultWf (wfα : α → Prop) (wfβ : β → Prop) (tag : β → α) : β → Prop :=
  fun r => wfα (tag r) ∧ wfβ r

/-- Serialize body, then pass the raw result and encoding to the tag serializer. -/
def bindResult {wfα : α → Prop} {wfβ : β → Prop}
    (tag : β → α)
    (left : Result ι Unit → ι → Serializer ι α wfα)
    (right : Serializer ι β wfβ) :
    Serializer ι β (bindResultWf wfα wfβ tag) :=
  fun r =>
    let rRet := right r
    left rRet (out rRet) (tag r)

/-! ### Length-delimited serialization -/

/-- Identity for serializers; only meaningful for correctness proofs. -/
def limit {wf : α → Prop} (underlying : Serializer ι α wf) (_ : α → Nat) :
    Serializer ι α wf :=
  underlying

def lenWf (wfα : α → Prop) (wfn : Nat → Prop) (lenFn : α → Nat) : α → Prop :=
  fun x => wfn (lenFn x) ∧ wfα x

/-- Encode a length prefix (from `lenFn`) followed by the body. -/
def len {wfα : α → Prop} {wfn : Nat → Prop} (lenFn : α → Nat)
    (serLen : Serializer ι Nat wfn) (underlying : Serializer ι α wfα) :
    Serializer ι α (lenWf wfα wfn lenFn) :=
  bind' lenFn serLen (limit underlying lenFn)

def len'Wf {wfα : α → Prop} {wfn : Nat → Prop}
    (serLen : Serializer ι Nat wfn) (serX : Serializer ι α wfα) : α → Prop :=
  fun x =>
    match serX x with
    | .success () encX =>
      match serLen (Input.length encX) with
      | .success () _ => wfn (Input.length encX) ∧ wfα x
      | .failure _ _  => True
    | .failure _ _ => True

/-- Encode the body first, compute its length, then prepend the length encoding.
    Unlike `len`, the length is derived from the actual encoding rather than a
    separate function. -/
def len' {wfα : α → Prop} {wfn : Nat → Prop}
    (serLen : Serializer ι Nat wfn) (underlying : Serializer ι α wfα) :
    Serializer ι α (len'Wf serLen underlying) :=
  fun x =>
    match underlying x with
    | .success () enc =>
      match serLen (Input.length enc) with
      | .success () lenEnc => .success () (Input.app lenEnc enc)
      | .failure lvl data =>
        .failure lvl ⟨"Len' serializing length failed", enc, .some data⟩
    | .failure lvl data =>
      .failure lvl ⟨"Len' serializing body failed", Input.default, .some data⟩

/-! ### Mapping -/

def mapWf (wf : β → Prop) (f : α → β) : α → Prop :=
  fun a => wf (f a)

/-- Transform the input value before serializing. -/
def map {wf : β → Prop} (underlying : Serializer ι β wf) (f : α → β) :
    Serializer ι α (mapWf wf f) :=
  fun a => underlying (f a)

def partMapWf (wf : β → Prop) (f : α → Option β) : α → Prop :=
  fun a => match f a with | some b => wf b | none => True

/-- Partial map: serialize when `f` returns `some`, fail otherwise. -/
def partMap {wf : β → Prop} (underlying : Serializer ι β wf)
    (f : α → Option β) (msg : String) :
    Serializer ι α (partMapWf wf f) :=
  fun a =>
    match f a with
    | some b => underlying b
    | none   => .failure .recoverable ⟨msg, Input.default, .none⟩

/-! ### Optional -/

def optWf (wf : α → Prop) : Option α → Prop
  | some a => wf a
  | none   => True

/-- Encode `some a`; produce empty output for `none`. -/
def opt {wf : α → Prop} (underlying : Serializer ι α wf) :
    Serializer ι (Option α) (optWf wf) :=
  fun
    | some a => underlying a
    | none   => .success () Input.default

/-! ### Repetition -/

/-- Pointwise well-formedness for lists. -/
def repWf (wf : α → Prop) : List α → Prop
  | []      => True
  | x :: xs => wf x ∧ repWf wf xs

theorem repWf_iff_local {wfα wfβ : α → Prop} {l : List α}
    (h : ∀ x, x ∈ l → (wfα x ↔ wfβ x)) :
    repWf wfα l ↔ repWf wfβ l := by
  induction' l with x l ih;
  · exact Eq.to_iff rfl;
  · by_cases hx : wfα x <;> simp_all +decide [ repWf ]

/-- Internal: encode each element and concatenate the results. -/
def rep' {wfα : α → Prop} (underlying : Serializer ι α wfα) :
    List α → Result ι Unit
  | [] => .success () Input.default
  | x :: xs =>
    match underlying x, rep' underlying xs with
    | .success () xEnc, .success () restEnc =>
      .success () (Input.app xEnc restEnc)
    | .failure lvl data, .success () _ => .failure lvl data
    | .success () _, .failure lvl data => .failure lvl data
    | .failure lLvl lData, .failure rLvl rData =>
      .failure (lLvl.max rLvl) (lData.concat rData)

/-- Encode a list by encoding each element and concatenating. -/
def rep {wfα : α → Prop} (underlying : Serializer ι α wfα) :
    Serializer ι (List α) (repWf wfα) :=
  fun xs => rep' underlying xs

/-! ### Recursive serializers -/

/-- Error for recursive serializers that fail to make progress. -/
def recursiveProgressError (name : String) (depth : α → Nat) (x x' : α) :
    Result ι Unit :=
  if depth x' == depth x then
    .failure .fatal
      ⟨name ++ " no progress in recursive serializer", Input.default, .none⟩
  else
    .failure .fatal
      ⟨name ++ " fixpoint called with deeper value to serialize",
       Input.default, .none⟩

/-- Internal fixpoint for recursive serializers. -/
def recur {wf : α → Prop}
    (underlying : Serializer ι α wf → Serializer ι α wf) (depth : α → Nat)
    (x : α) : Result ι Unit :=
  underlying (fun x' =>
    if depth x' < depth x then recur underlying depth x'
    else recursiveProgressError "Serial.Recursive" depth x x'
  ) x
termination_by depth x

/-- A serializer that may call itself recursively.  Progress is enforced via a
    `depth` function that must strictly decrease at each recursive call. -/
def recursive {wf : α → Prop}
    (underlying : Serializer ι α wf → Serializer ι α wf) (depth : α → Nat) :
    Serializer ι α wf :=
  fun x => recur underlying depth x

/-- Internal fixpoint for stateful recursive serializers. -/
def recurSt {wf : σ → α → Prop}
    (underlying : (∀ s : σ, Serializer ι α (wf s)) → ∀ s : σ, Serializer ι α (wf s))
    (depth : α → Nat) (st : σ) (x : α) : Result ι Unit :=
  underlying (fun st' x' =>
    if depth x' < depth x then recurSt underlying depth st' x'
    else recursiveProgressError "Serial.RecursiveState" depth x x'
  ) st x
termination_by depth x

/-- A stateful recursive serializer with progress enforcement via `depth`. -/
def recursiveState {wf : σ → α → Prop}
    (underlying : (∀ s : σ, Serializer ι α (wf s)) → ∀ s : σ, Serializer ι α (wf s))
    (depth : α → Nat) (st : σ) :
    Serializer ι α (wf st) :=
  fun x => recurSt underlying depth st x

end Serializer
end Pollux.Parse
