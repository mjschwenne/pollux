/-
  Pollux.Parse.Result — Failure levels, error data, and parse/serialize results.

  Corresponds to src/parse/Result.v in the Rocq development.
-/

namespace Pollux.Parse

/-- Failure severity: fatal errors cannot be recovered; recoverable ones allow backtracking. -/
inductive Level where
  | fatal
  | recoverable
  deriving DecidableEq, BEq, Repr

namespace Level

def max : Level → Level → Level
  | .recoverable, .recoverable => .recoverable
  | _, _ => .fatal

end Level

/-- Structured error information forming a linked chain.
    The `remaining` field holds unconsumed input (parsers) or encoded output (serializers). -/
inductive Data (ι : Type) where
  | mk (msg : String) (remaining : ι) (next : Option (Data ι))

namespace Data

def msg {ι} : Data ι → String
  | .mk m _ _ => m

def remaining {ι} : Data ι → ι
  | .mk _ r _ => r

def next {ι} : Data ι → Option (Data ι)
  | .mk _ _ n => n

/-- Append `other` at the end of the error chain. -/
def concat {ι} : Data ι → Data ι → Data ι
  | .mk msg rem .none, other => .mk msg rem (.some other)
  | .mk msg rem (.some n), other => .mk msg rem (.some (n.concat other))

end Data

/-- A parse or serialization result.
    - `success result enc`: succeeded with value `result`; `enc` is the remaining input
      (for parsers) or the encoded output (for serializers).
    - `failure level data`: failed with the given severity and error chain. -/
inductive Result (ι : Type) (α : Type) where
  | success (result : α) (enc : ι)
  | failure (level : Level) (data : Data ι)

namespace Result

/-- Extract the `enc` field (remaining input or encoded output). -/
def getEnc : Result ι α → ι
  | .success _ enc => enc
  | .failure _ d => d.remaining

def isFailure : Result ι α → Bool
  | .failure _ _ => true
  | .success _ _ => false

def isFatalFailure : Result ι α → Bool
  | .failure .fatal _ => true
  | _ => false

def isFailureProp : Result ι α → Prop
  | .failure _ _ => True
  | .success _ _ => False

def isSuccess : Result ι α → Bool
  | .success _ _ => true
  | .failure _ _ => false

def isSuccessProp : Result ι α → Prop
  | .success _ _ => True
  | .failure _ _ => False

/-- Re-type a failure from `Result ι α` to `Result ι β`.
    The proof witness ensures this is only called on failures. -/
def propagate : (r : Result ι α) → r.isFailureProp → Result ι β
  | .failure lvl data, _ => .failure lvl data

/-- Unwrap a success result. The proof witness ensures this is only called on successes. -/
def extract : (r : Result ι α) → r.isSuccessProp → α × ι
  | .success x enc, _ => (x, enc)

/-- Functor map over the success value. -/
def map (r : Result ι α) (f : α → β) : Result ι β :=
  match r with
  | .success x enc => .success (f x) enc
  | .failure lvl data => .failure lvl data

/-- Replace the error data of a recoverable failure; leave other results unchanged. -/
def mapRecoverableError (r : Result ι α) (f : Data ι → Data ι) : Result ι α :=
  match r with
  | .failure .recoverable data => .failure .recoverable (f data)
  | _ => r

/-- True when the result is a recoverable failure whose remaining input equals `input`,
    meaning no input was consumed and an alternative parser may be tried. -/
def needsAlternative [DecidableEq ι] (r : Result ι α) (input : ι) : Bool :=
  match r with
  | .failure .recoverable (.mk _ rem _) => rem == input
  | _ => false

end Result

section ResultEquiv

variable {ι α : Type}

/-- Two results are equivalent when they agree on success values and encodings,
    or on failure levels (ignoring error messages). -/
def resultEquiv : Result ι α → Result ι α → Prop
  | .success r₁ e₁, .success r₂ e₂ => r₁ = r₂ ∧ e₁ = e₂
  | .failure l₁ _, .failure l₂ _ => l₁ = l₂
  | _, _ => False

scoped notation:50 r₁ " ≡ᵣ " r₂ => resultEquiv r₁ r₂

theorem resultEquiv_refl (r : Result ι α) : resultEquiv r r := by
  cases r <;> simp [resultEquiv]

theorem resultEquiv_symm {r₁ r₂ : Result ι α} (h : resultEquiv r₁ r₂) :
    resultEquiv r₂ r₁ := by
  cases r₁ <;> cases r₂ <;> simp_all [resultEquiv]

theorem resultEquiv_trans {r₁ r₂ r₃ : Result ι α} (h₁ : resultEquiv r₁ r₂)
    (h₂ : resultEquiv r₂ r₃) : resultEquiv r₁ r₃ := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> simp_all [resultEquiv]

theorem resultEquiv_success_iff (r : Result ι α) (x : α) (enc : ι) :
    resultEquiv r (.success x enc) ↔ r = .success x enc := by
  constructor
  · intro h; cases r <;> simp_all [resultEquiv]
  · intro h; subst h; exact resultEquiv_refl _

end ResultEquiv

end Pollux.Parse
