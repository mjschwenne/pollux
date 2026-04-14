/-
  Pollux.Parse.Parser — Parser type and combinators.

  Corresponds to src/parse/Parser.v in the Rocq development.

  A parser is a total function from input to a `Result`: it always terminates
  and never panics, returning either a parsed value with remaining input, or
  a structured failure.
-/
import Pollux.Parse.Input
import Pollux.Parse.Result

namespace Pollux.Parse

/-- A parser is a total function from input to a parse result. -/
abbrev Parser (ι α : Type) := ι → Result ι α

namespace Parser

variable {ι : Type} [Input ι]
variable {α β γ σ : Type}

/-- The unconsumed input after a successful parse. -/
abbrev remaining (r : Result ι α) : ι := r.getEnc

/-! ### Basic combinators -/

/-- Always succeeds with `x`, consuming no input. -/
def succeedWith (x : α) : Parser ι α :=
  fun inp => .success x inp

/-- Always succeeds with `()`, consuming no input. -/
def epsilon : Parser ι Unit := succeedWith ()

/-- Always fails with the given message and level. -/
def failWith (msg : String) (lvl : Level) : Parser ι α :=
  fun inp => .failure lvl ⟨msg, inp, .none⟩

/-- Always returns the given precomputed result, ignoring input. -/
def resultWith (r : Result ι α) : Parser ι α :=
  fun _ => r

/-- Succeeds only when the input has been entirely consumed. -/
def endOfInput : Parser ι Unit :=
  fun inp =>
    if Input.length inp == 0 then .success () inp
    else .failure .recoverable ⟨"expected end of input", inp, .none⟩

/-! ### Sequential composition -/

/-- Monadic bind: parse `left`, then feed its result to `right`. -/
def bind (left : Parser ι α) (right : α → Parser ι β) : Parser ι β :=
  fun inp =>
    match left inp with
    | .success lRes lRem =>
      match right lRes lRem with
      | .success rRes rRem => .success rRes rRem
      | .failure lvl data  => .failure lvl ⟨"Bind right failed", lRem, .some data⟩
    | .failure lvl data => .failure lvl ⟨"Bind left failed", inp, .some data⟩

/-- Like `bind`, but `right` also receives the remaining input from `left`. -/
def bindSucceeds (left : Parser ι α) (right : α → ι → Parser ι β) : Parser ι β :=
  fun inp =>
    match left inp with
    | .success lRes lRem =>
      match right lRes lRem lRem with
      | .success rRes rRem => .success rRes rRem
      | .failure lvl data  => .failure lvl ⟨"BindSucceeds right failed", lRem, .some data⟩
    | .failure lvl data => .failure lvl ⟨"BindSucceeds left failed", inp, .some data⟩

/-- Parse `left`, then pass both the full result and the original input to `right`. -/
def bindResult (left : Parser ι α) (right : Result ι α → ι → Parser ι β) : Parser ι β :=
  fun inp => right (left inp) inp inp

/-! ### Pairing combinators -/

/-- Parse `left` then `right` sequentially, returning the pair of results. -/
def concat (left : Parser ι α) (right : Parser ι β) : Parser ι (α × β) :=
  fun inp =>
    match left inp with
    | .success lRes lRem =>
      match right lRem with
      | .success rRes rRem => .success (lRes, rRes) rRem
      | .failure lvl data  => .failure lvl ⟨"Concat right failed", lRem, .some data⟩
    | .failure lvl data => .failure lvl ⟨"Concat left failed", inp, .some data⟩

/-- Like `concat`, but the right parser depends on the left result. -/
def depConcat (left : Parser ι α) (right : α → Parser ι β) : Parser ι (α × β) :=
  fun inp =>
    match left inp with
    | .success lRes lRem =>
      match right lRes lRem with
      | .success rRes rRem => .success (lRes, rRes) rRem
      | .failure lvl data  => .failure lvl ⟨"DepConcat right failed", lRem, .some data⟩
    | .failure lvl data => .failure lvl ⟨"DepConcat left failed", inp, .some data⟩

/-- Parse `left` then `right`, combining their results with `f`. -/
def concatMap (left : Parser ι α) (right : Parser ι β) (f : α → β → γ) : Parser ι γ :=
  fun inp =>
    match left inp with
    | .success lRes lRem =>
      match right lRem with
      | .success rRes rRem => .success (f lRes rRes) rRem
      | .failure lvl data  => .failure lvl ⟨"ConcatMap right failed", lRem, .some data⟩
    | .failure lvl data => .failure lvl ⟨"ConcatMap left failed", inp, .some data⟩

/-- Parse `left` then `right`, keeping only the right result. -/
def concatKeepRight (left : Parser ι α) (right : Parser ι β) : Parser ι β :=
  concatMap left right fun _ r => r

/-- Parse `left` then `right`, keeping only the left result. -/
def concatKeepLeft (left : Parser ι α) (right : Parser ι β) : Parser ι α :=
  concatMap left right fun l _ => l

/-! ### Length-delimited parsing -/

/-- Restrict the parser to see only the first `n` elements of input. -/
def limit (underlying : Parser ι α) (n : Nat) : Parser ι α :=
  fun inp =>
    let inp' := Input.slice inp 0 n
    match underlying inp' with
    | .success r rem => .success r (Input.app rem (Input.drop inp n))
    | .failure lvl data => .failure lvl ⟨"Limit underlying failed", inp', .some data⟩

/-- Parse a length prefix with `lenParser`, then parse the body limited to that many elements. -/
def len (lenParser : Parser ι Nat) (underlying : Parser ι α) : Parser ι α :=
  bind lenParser fun l => limit underlying l

/-! ### Mapping -/

/-- Transform the parsed value, leaving remaining input unchanged. -/
def map (underlying : Parser ι α) (f : α → β) : Parser ι β :=
  fun inp =>
    match underlying inp with
    | .success result rem => .success (f result) rem
    | .failure lvl data   => .failure lvl ⟨"Map underlying failed", inp, .some data⟩

/-! ### Negation and conjunction -/

/-- Succeeds with `()` when the underlying parser fails non-fatally, and vice versa.
    Does not consume input on success. -/
def not (underlying : Parser ι α) : Parser ι Unit :=
  fun inp =>
    match underlying inp with
    | .success _ _              => .failure .recoverable ⟨"Not failed", inp, .none⟩
    | .failure .fatal data      => .failure .fatal data
    | .failure .recoverable _   => .success () inp

/-- Run both parsers on the same input. Succeed with the pair if both succeed;
    the remaining input comes from `right`. -/
def and (left : Parser ι α) (right : Parser ι β) : Parser ι (α × β) :=
  fun inp =>
    match left inp, right inp with
    | .success a _, .success b rr =>
      .success (a, b) rr
    | .failure lvl data, .success _ _ =>
      .failure lvl ⟨"And left failed", inp, .some data⟩
    | .success _ _, .failure lvl data =>
      .failure lvl ⟨"And right failed", inp, .some data⟩
    | .failure lLvl lData, .failure rLvl rData =>
      .failure (lLvl.max rLvl) ⟨"And both parsers failed", inp, .some (lData.concat rData)⟩

/-! ### Alternation -/

/-- Try `left`; on a recoverable failure that consumed no input, try `right`. -/
def or (left right : Parser ι α) : Parser ι α :=
  fun inp =>
    let p := left inp
    match p with
    | .success _ _ => p
    | .failure _ data =>
      if p.needsAlternative inp then
        let p2 := right inp
        if p2.needsAlternative inp then
          p2.mapRecoverableError fun dataRight =>
            ⟨"Or both options failed", inp, .some (data.concat dataRight)⟩
        else p2
      else p

/-- Try each alternative in order until one succeeds or commits. -/
def orSeq : List (Parser ι α) → Parser ι α
  | []        => failWith "no alternatives" .recoverable
  | [alt]     => alt
  | alt :: as => or alt (orSeq as)

/-! ### Lookahead and backtracking -/

/-- Parse without consuming input. Fatal failures propagate unchanged. -/
def lookahead (underlying : Parser ι α) : Parser ι α :=
  fun inp =>
    match underlying inp with
    | .success r _              => .success r inp
    | .failure .fatal data      => .failure .fatal data
    | .failure .recoverable data => .failure .recoverable ⟨data.msg, inp, .none⟩

/-- Like the underlying parser, but a recoverable failure resets remaining input
    to the original (enabling backtracking in `or`). -/
def opt (underlying : Parser ι α) : Parser ι α :=
  fun inp =>
    match underlying inp with
    | .success r rem             => .success r rem
    | .failure .fatal data       => .failure .fatal data
    | .failure .recoverable data => .failure .recoverable ⟨data.msg, inp, .none⟩

/-- Conditionally parse: succeed with `some` on success, `none` on a recoverable
    failure that consumed no input. Fatal failures and input-consuming failures propagate. -/
def maybe (underlying : Parser ι α) : Parser ι (Option α) :=
  fun inp =>
    match underlying inp with
    | .success r rem => .success (some r) rem
    | .failure .fatal data => .failure .fatal data
    | .failure .recoverable data =>
      let r : Result ι α := .failure .recoverable data
      if r.needsAlternative inp then .success none inp
      else .failure .recoverable data

/-- If the condition parser succeeds (via lookahead), run `succeed`. -/
def ifThen (condition : Parser ι α) (succeed : Parser ι β) : Parser ι β :=
  bind (lookahead condition) fun _ => succeed

/-! ### Repetition -/

/-- Internal: repeated parse, well-founded on input length. -/
def rep' (underlying : Parser ι α) (inp : ι) : Result ι (List α) :=
  match underlying inp with
  | .success x rem =>
    if _h : Input.length rem < Input.length inp then
      match rep' underlying rem with
      | .success xs rest       => .success (x :: xs) rest
      | .failure .recoverable _ => .success [x] rem
      | .failure .fatal data   => .failure .fatal data
    else
      .failure .fatal ⟨"Parser.Rep underlying increased input length", rem, .none⟩
  | .failure .recoverable ⟨_, rem, _⟩ => .success [] rem
  | .failure .fatal data => .failure .fatal data
termination_by Input.length inp

/-- Repeat the parser until the first non-consuming or fatal failure. -/
def rep (underlying : Parser ι α) : Parser ι (List α) :=
  fun inp => rep' underlying inp

/-- Internal: folding repeat, well-founded on input length. -/
def repFold' (underlying : Parser ι β) (combine : α → β → α) (acc : α)
    (inp : ι) : Result ι α :=
  match underlying inp with
  | .success ret rem =>
    if _h : Input.length rem < Input.length inp then
      repFold' underlying combine (combine acc ret) rem
    else .success acc inp
  | .failure lvl data =>
    let r : Result ι β := .failure lvl data
    if r.needsAlternative inp then .success acc inp
    else .failure lvl data
termination_by Input.length inp

/-- Repeat, folding results into an accumulator. -/
def repFold (underlying : Parser ι β) (combine : α → β → α) (acc : α) : Parser ι α :=
  fun inp => repFold' underlying combine acc inp

/-- Repeat exactly `n` times, folding results into an accumulator. -/
def repN (underlying : Parser ι β) (combine : α → β → α) : Nat → α → Parser ι α
  | 0, acc => fun inp => .success acc inp
  | n + 1, acc => fun inp =>
    match underlying inp with
    | .success b rem => repN underlying combine n (combine acc b) rem
    | .failure lvl data =>
      .failure lvl ⟨"RepN underlying failed before N", inp, .some data⟩

/-- Repeat with a separator, collecting results into a list. -/
def repSep (underlying : Parser ι α) (separator : Parser ι β) : Parser ι (List α) :=
  bind (maybe underlying) fun
    | some ret => repFold (concatKeepRight separator underlying)
        (fun acc a => acc ++ [a]) [ret]
    | none => succeedWith []

/-- Repeat with a separator exactly `n` times. -/
def repSepN (underlying : Parser ι α) (separator : Parser ι β) (n : Nat) :
    Parser ι (List α) :=
  bind (maybe underlying) fun
    | some ret => repN (concatKeepRight separator underlying)
        (fun acc a => acc ++ [a]) (n - 1) [ret]
    | none => succeedWith []

/-- Repeat, merging results with a binary operation. -/
def repMerge (underlying : Parser ι α) (merge : α → α → α) : Parser ι α :=
  bind (maybe underlying) fun
    | some ret => repFold underlying merge ret
    | none => failWith "No first element in RepMerge" .recoverable

/-- Repeat N times, merging results. -/
def repMergeN (underlying : Parser ι α) (merge : α → α → α) (n : Nat) : Parser ι α :=
  bind (maybe underlying) fun
    | some ret => repN underlying merge (n - 1) ret
    | none => failWith "No first element in RepMergeN" .recoverable

/-- Repeat with separator, merging results. -/
def repSepMerge (underlying : Parser ι α) (separator : Parser ι β)
    (merge : α → α → α) : Parser ι α :=
  bind (maybe underlying) fun
    | some ret => repFold (concatKeepRight separator underlying) merge ret
    | none => failWith "No first element in RepSepMerge" .recoverable

/-- Repeat with separator N times, merging results. -/
def repSepMergeN (underlying : Parser ι α) (separator : Parser ι β)
    (merge : α → α → α) (n : Nat) : Parser ι α :=
  bind (maybe underlying) fun
    | some ret => repN (concatKeepRight separator underlying) merge (n - 1) ret
    | none => failWith "No first element in RepSepMergeN" .recoverable

/-- Zero or more repetitions, collecting into a list. -/
def zeroOrMore (underlying : Parser ι α) : Parser ι (List α) :=
  repFold underlying (fun acc x => acc ++ [x]) []

/-- One or more repetitions. -/
def oneOrMore (underlying : Parser ι α) : Parser ι (List α) :=
  bind underlying fun x => map (rep underlying) fun xs => x :: xs

/-- Exactly `n` repetitions, collecting into a list. -/
def seqN (underlying : Parser ι α) (n : Nat) : Parser ι (List α) :=
  repN underlying (fun acc x => acc ++ [x]) n []

/-! ### Recursive parsers -/

/-- Error for recursive parsers that fail to make progress. -/
def recursiveProgressError (name : String) (inp rem : ι) : Result ι α :=
  if Input.length rem == Input.length inp then
    .failure .recoverable ⟨name ++ " no progress in recursive parser", rem, .none⟩
  else
    .failure .fatal
      ⟨name ++ " fixpoint called with an increasing remaining sequence", rem, .none⟩

/-- Step function for the recursive parser fixpoint (used in theorem statements). -/
def recurStep (underlying : Parser ι α → Parser ι α) (inp : ι)
    (recCall : (rem : ι) → Input.length rem < Input.length inp → Result ι α)
    (rem : ι) : Result ι α :=
  if h : Input.length rem < Input.length inp then recCall rem h
  else recursiveProgressError "Parser.Recursive" inp rem

/-- Internal fixpoint for recursive parsers. -/
def recur (underlying : Parser ι α → Parser ι α) (inp : ι) : Result ι α :=
  underlying (fun rem =>
    if Input.length rem < Input.length inp then recur underlying rem
    else recursiveProgressError "Parser.Recursive" inp rem
  ) inp
termination_by Input.length inp

/-- A parser that may call itself recursively.  Progress (strictly decreasing
    input length) is enforced at each recursive call. -/
def recursive (underlying : Parser ι α → Parser ι α) : Parser ι α :=
  fun inp => recur underlying inp

/-- Step function for stateful recursive parser (used in theorem statements). -/
def recurStepSt (underlying : (σ → Parser ι α) → σ → Parser ι α) (inp : ι)
    (recCall : σ → (rem : ι) → Input.length rem < Input.length inp → Result ι α)
    (st : σ) (rem : ι) : Result ι α :=
  if h : Input.length rem < Input.length inp then recCall st rem h
  else recursiveProgressError "Parser.RecursiveState" inp rem

/-- Internal fixpoint for stateful recursive parsers. -/
def recurSt (underlying : (σ → Parser ι α) → σ → Parser ι α) (st : σ)
    (inp : ι) : Result ι α :=
  underlying (fun st' rem =>
    if Input.length rem < Input.length inp then recurSt underlying st' rem
    else recursiveProgressError "Parser.RecursiveState" inp rem
  ) st inp
termination_by Input.length inp

/-- A stateful recursive parser.  The state `st` is threaded through recursive calls. -/
def recursiveState (underlying : (σ → Parser ι α) → σ → Parser ι α) (st : σ) :
    Parser ι α :=
  fun inp => recurSt underlying st inp

end Parser
end Pollux.Parse
