/-
  Pollux.InterParse.Theorems.Compatible - The full (cross-descriptor)
  compatibility relation for the intermediate format.

  This is the Lean transcription of section "Full Compatibility Relation"
  (`sec:ip-compat-rel`) of the written report.  Four mutually-recursive
  relations:

  - `ValCompat   v₁ f₁ v₂ f₂`  (`≺`)  -- value  v₁ : f₁ becomes v₂ : f₂
  - `FieldCompat f₁ f₂`        (`∝`)  -- f₁ is type-compatible with f₂
  - `DescCompat  d₁ d₂`        (`≪`)  -- d₁ is descriptor-compatible with d₂
  - `MsgCompat   m₁ d₁ m₂ d₂`  (`≼`)  -- message m₁ : d₁ becomes m₂ : d₂

  They must be defined in a single `mutual` block because they reference each
  other: `V-Msg → ≼`, `F-Msg → ≪`, `D-Chg → ∝`, `M-Update → ≺` and `∝`.

  `≼`'s ninth rule, `M-Declare`, is load-bearing rather than convenient:
  without it the relation cannot express a writer that declares a field its own
  value leaves unset — a configuration `serialValue`/`parseValue` produce
  routinely, and one `valueWf` permits — so the round-trip theorem would be
  false even at `d₁ = d₂`.  See `MsgCompat.declare` and
  `msgCompat_of_idCompatible`.

  Unlike `SchemaCorrectCompatible` and `IdCompatible`, this relation is
  genuinely two-descriptor: it is the relation that makes
  `LimitParseOkCompat'' R parseValue serialValue d₁ d₂ v` interesting for
  `d₁ ≠ d₂`, with `DescCompat` filling the `linkedState` slot of
  `limitRecursiveStateCompat_correct`.

  This file contains only the relations and the structural lemmas about
  `DescCompat` needed to thread the relation through nested messages.  The
  round-trip theorem is not here.
-/
import Pollux.InterParse.Theorems.SchemaCorrect
import Pollux.InterParse.Theorems.Validity
import Pollux.InterParse.Theorems.IdCompatible
import Mathlib

namespace Pollux.InterParse

/-! ## The four relations

  Transcribed from the report.  Three systematic adjustments were needed
  because the report's rules use partial map lookups (`d[k]`) where Lean needs
  a total function:

  * `D-Chg`'s premise `d[k] ∝ f` becomes `d.get? k = some f₀` together with
    `FieldCompat f₀ f`.
  * `M-Update`'s premises `m₁[k] : d₁[k] ≺ v : f` and `d₁[k] ∝ f` likewise
    become explicit `get?` hypotheses.
  * `insert` overwrites, so rules that extend a map carry `get? k = none`
    premises on *both* sides (the report states these only for the left-hand
    pair in `M-Missing`/`M-Declare` and only for the right-hand pair in
    `M-Drop`).

  **`M-Add` is deliberately omitted.**  The report's `M-Add` lets the reader
  gain a field carrying *any* value matching its declared type, at a key the
  writer's descriptor never declared.  No round trip produces that: the writer
  emits nothing for such a key and `parseVal` injects `.missing`, which is
  exactly `M-Missing`.  Because `≼` occurs only positively in
  `LimitParseOkCompat''`, keeping `M-Add` would have been sound — but it would
  let a derivation conjure values out of thin air, so `≼` could not be read as
  a specification of what parsing produces.  `M-Missing` covers the real case.

  Well-formedness (`Desc.WF` / `Value.WF`) is *not* required by the
  constructors; as with `SchemaCorrect` and `IdCompatible` it is carried
  separately by the callers, since `insert` only preserves sortedness on
  well-formed inputs.
-/

mutual

/-- Value relation (`≺`).  "Value `v₁ : f₁` becomes `v₂ : f₂`." -/
inductive ValCompat : Val → Field → Val → Field → Prop where
  /-- V-Bool-Int: booleans and integers share a 4-byte little-endian encoding,
      so a `bool` field may be reinterpreted as the indicator integer. -/
  | boolInt (b : Bool) (z : Int) :
    z = (if b then 1 else 0) →
    ValCompat (.bool b) .bool (.int z) .int
  /-- V-Int-Bool: the reverse direction, `0 ↦ false` and everything else
      `↦ true`.  Note this is lossy, which is why `V-Trans` is not derivable
      from `V-Refl`. -/
  | intBool (z : Int) (b : Bool) :
    b = (if z = 0 then false else true) →
    ValCompat (.int z) .int (.bool b) .bool
  /-- V-Msg: nested messages relate when their contents relate. -/
  | msg (m₁ : Value) (d₁ : Desc) (m₂ : Value) (d₂ : Desc) :
    MsgCompat m₁ d₁ m₂ d₂ →
    ValCompat (.msg m₁) (.msg d₁) (.msg m₂) (.msg d₂)
  /-- V-Refl -/
  | refl (v : Val) (f : Field) : ValCompat v f v f
  /-- V-Trans -/
  | trans (v₁ : Val) (f₁ : Field) (v₂ : Val) (f₂ : Field) (v₃ : Val) (f₃ : Field) :
    ValCompat v₁ f₁ v₂ f₂ → ValCompat v₂ f₂ v₃ f₃ → ValCompat v₁ f₁ v₃ f₃

/-- Field type relation (`∝`).  "`f₁` is type-compatible with `f₂`." -/
inductive FieldCompat : Field → Field → Prop where
  /-- F-Bool-Int -/
  | boolInt : FieldCompat .bool .int
  /-- F-Int-Bool -/
  | intBool : FieldCompat .int .bool
  /-- F-Msg -/
  | msg (d₁ d₂ : Desc) : DescCompat d₁ d₂ → FieldCompat (.msg d₁) (.msg d₂)
  /-- F-Refl -/
  | refl (f : Field) : FieldCompat f f
  /-- F-Trans -/
  | trans (f₁ f₂ f₃ : Field) :
    FieldCompat f₁ f₂ → FieldCompat f₂ f₃ → FieldCompat f₁ f₃

/-- Descriptor type relation (`≪`).  "`d₁` is descriptor-compatible with
    `d₂`."  Width and depth subtyping for record types: fields may be added or
    retyped, but never removed.  This directionality is what makes the wire
    format sound — see `descCompat_isSome` below. -/
inductive DescCompat : Desc → Desc → Prop where
  /-- D-Emp -/
  | emp : DescCompat (∅ : Desc) (∅ : Desc)
  /-- D-Add: widening, a new field the reader knows about. -/
  | add (d : Desc) (k : Int) (f : Field) :
    d.get? k = none → DescCompat d (d.insert k f)
  /-- D-Chg: retyping an existing field along `∝`. -/
  | chg (d : Desc) (k : Int) (f₀ f : Field) :
    d.get? k = some f₀ → FieldCompat f₀ f → DescCompat d (d.insert k f)
  /-- D-Refl -/
  | refl (d : Desc) : DescCompat d d
  /-- D-Trans -/
  | trans (d₁ d₂ d₃ : Desc) :
    DescCompat d₁ d₂ → DescCompat d₂ d₃ → DescCompat d₁ d₃

/-- Message relation (`≼`).  "Message `m₁ : d₁` becomes `m₂ : d₂`." -/
inductive MsgCompat : Value → Desc → Value → Desc → Prop where
  /-- M-Emp -/
  | emp : MsgCompat (∅ : Value) (∅ : Desc) (∅ : Value) (∅ : Desc)
  /-- M-Missing: the reader declares a field the writer never had, so parsing
      injects `V_MISSING`.  This is the *only* rule that gives the reader a key
      the writer's descriptor did not declare, and the value it gives is always
      `.missing` — see the note on `M-Add` in the module header. -/
  | missing (m₁ : Value) (d₁ : Desc) (m₂ : Value) (d₂ : Desc) (k : Int)
      (f : Field) :
    MsgCompat m₁ d₁ m₂ d₂ →
    m₁.get? k = none → d₁.get? k = none →
    m₂.get? k = none → d₂.get? k = none →
    MsgCompat m₁ d₁ (m₂.insert k .missing) (d₂.insert k f)
  /-- M-Declare: the writer *declares* a field its own value never populates,
      so parsing injects `V_MISSING` on the reader's side.  This is `M-Missing`
      with `d₁` extended alongside `d₂`.

      Not optional: without it `≼` cannot follow `IdCompatible.addMissing`, and
      the cross-descriptor round-trip theorem is *false* already at `d₁ = d₂`.
      `serialValue` emits nothing for a declared-but-absent key and
      `parseValue` reads it back as `.missing`; `valueWf` permits exactly that
      (it constrains only the keys the value actually carries), so the
      configuration is reachable from the top-level theorem's hypotheses and no
      other rule produces it. -/
  | declare (m₁ : Value) (d₁ : Desc) (m₂ : Value) (d₂ : Desc) (k : Int)
      (f : Field) :
    MsgCompat m₁ d₁ m₂ d₂ →
    m₁.get? k = none → d₁.get? k = none →
    m₂.get? k = none → d₂.get? k = none →
    MsgCompat m₁ (d₁.insert k f) (m₂.insert k .missing) (d₂.insert k f)
  /-- M-Update: an existing field changes value and type together. -/
  | update (m₁ : Value) (d₁ : Desc) (m₂ : Value) (d₂ : Desc) (k : Int)
      (v₁ : Val) (f₁ : Field) (v : Val) (f : Field) :
    MsgCompat m₁ d₁ m₂ d₂ →
    m₁.get? k = some v₁ → d₁.get? k = some f₁ →
    ValCompat v₁ f₁ v f →
    FieldCompat f₁ f →
    MsgCompat m₁ d₁ (m₂.insert k v) (d₂.insert k f)
  /-- M-Drop: the updated version discards a field it no longer needs, removing
      it from the descriptor and the value together. -/
  | drop (m₁ : Value) (d₁ : Desc) (m₂ : Value) (d₂ : Desc) (k : Int)
      (v : Val) (f : Field) :
    MsgCompat m₁ d₁ m₂ d₂ →
    m₁.get? k = none → d₁.get? k = none →
    m₂.get? k = none → d₂.get? k = none →
    MsgCompat (m₁.insert k v) (d₁.insert k f) m₂ d₂
  /-- M-Drop-Unknown: the writer's *value* carries a key its own descriptor
      never declared.  `serialVal`'s `none` branch emits nothing for such an
      entry, so it simply disappears across a round trip.  Note there is no
      constraint on `v` and no change to `d₁` — this is `IdCompatible.drop`,
      and it is what lets a value be related while carrying entries outside its
      schema. -/
  | dropUnknown (m₁ : Value) (d₁ : Desc) (m₂ : Value) (d₂ : Desc) (k : Int)
      (v : Val) :
    MsgCompat m₁ d₁ m₂ d₂ →
    m₁.get? k = none → d₁.get? k = none →
    MsgCompat (m₁.insert k v) d₁ m₂ d₂
  /-- M-Refl -/
  | refl (m : Value) (d : Desc) : MsgCompat m d m d
  /-- M-Trans -/
  | trans (m₁ : Value) (d₁ : Desc) (m₂ : Value) (d₂ : Desc) (m₃ : Value) (d₃ : Desc) :
    MsgCompat m₁ d₁ m₂ d₂ → MsgCompat m₂ d₂ m₃ d₃ → MsgCompat m₁ d₁ m₃ d₃

end

@[inherit_doc] notation "⟨ " v₁ " ∷ " f₁ " ⟩≺⟨ " v₂ " ∷ " f₂ " ⟩" =>
  ValCompat v₁ f₁ v₂ f₂
@[inherit_doc] infix:50 " ∝ " => FieldCompat
@[inherit_doc] infix:50 " ⋘ " => DescCompat
@[inherit_doc] notation "⟨ " m₁ " ∷ " d₁ " ⟩⪯⟨ " m₂ " ∷ " d₂ " ⟩" =>
  MsgCompat m₁ d₁ m₂ d₂

/-- The shim that lets `MsgCompat` slot into `LimitParseOkCompat''`, whose
    relation argument has type `δ → δ → α → α → Prop`.  Compare
    `IdCompatibleWrapper`. -/
def MsgCompatWrapper (d₁ d₂ : Desc) (v₁ v₂ : Value) : Prop :=
  MsgCompat v₁ d₁ v₂ d₂

/-! ## Recovering `IdCompatible`

  `MsgCompat` subsumes `IdCompatible` at `d₁ = d₂ = d`: the sanity check saying
  the new relation really is a generalization of the old one.  It is not needed
  for the round-trip theorem, which only ever *constructs* `MsgCompat`
  derivations.

  The subsumption is what forced `M-Declare` into the rule set.  Without it `≼`
  has no rule extending the writer's descriptor `d₁` while leaving the writer's
  value `m₁` alone — `M-Missing` extends `m₂`/`d₂` only and `M-Drop` extends
  `m₁` and `d₁` in lockstep — so it cannot follow `IdCompatible.addMissing`, and
  the witness `d = {0 ↦ int}`, `v₁ = ∅`, `v₂ = {0 ↦ missing}` is a genuine
  round trip that no derivation reaches.  See `MsgCompat.declare`.

  Note the cost, recorded in `not_msgCompat_dom`: with `M-Declare` present `≼`
  no longer constrains the four domains at all.  That is not a soundness
  problem — `≼` occurs only positively in `LimitParseOkCompat''`, and the
  constraint on which `(writer, reader)` descriptor pairs the theorem covers
  comes from `≪` in the `linkedState` slot, never from `≼`. -/

/-! ### A single-relation eliminator for `≼`

  Same construction as `DescCompat.ind` below: `MsgCompat.rec` is fed `True`
  motives for `≺`, `∝` and `≪`.  An earlier note in this file said this cannot
  work because `M-Update` "genuinely depends on both" `≺` and `∝` — that is
  true of a motive that has to *inspect* the value relation, but for a motive
  that only tracks the four maps (as `not_msgCompat_dom` below does) the two
  premises can simply be handed back unanalyzed, exactly as `F-Msg` hands back
  a raw `≪` in `FieldCompat.ind`. -/

/-- Induction principle for `MsgCompat` alone.  Use it as
    `refine MsgCompat.ind (motive := fun m₁ d₁ m₂ d₂ => …) ?_ … h`. -/
theorem MsgCompat.ind {motive : Value → Desc → Value → Desc → Prop}
    (hemp : motive ∅ ∅ ∅ ∅)
    (hmissing : ∀ m₁ d₁ m₂ d₂ k f, (⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩) →
      m₁.get? k = none → d₁.get? k = none → m₂.get? k = none → d₂.get? k = none →
      motive m₁ d₁ m₂ d₂ → motive m₁ d₁ (m₂.insert k .missing) (d₂.insert k f))
    (hdeclare : ∀ m₁ d₁ m₂ d₂ k f, (⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩) →
      m₁.get? k = none → d₁.get? k = none → m₂.get? k = none → d₂.get? k = none →
      motive m₁ d₁ m₂ d₂ →
      motive m₁ (d₁.insert k f) (m₂.insert k .missing) (d₂.insert k f))
    (hupdate : ∀ m₁ d₁ m₂ d₂ k v₁ f₁ v f, (⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩) →
      m₁.get? k = some v₁ → d₁.get? k = some f₁ →
      (⟨ v₁ ∷ f₁ ⟩≺⟨ v ∷ f ⟩) → (f₁ ∝ f) →
      motive m₁ d₁ m₂ d₂ → motive m₁ d₁ (m₂.insert k v) (d₂.insert k f))
    (hdrop : ∀ m₁ d₁ m₂ d₂ k v f, (⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩) →
      m₁.get? k = none → d₁.get? k = none → m₂.get? k = none → d₂.get? k = none →
      motive m₁ d₁ m₂ d₂ → motive (m₁.insert k v) (d₁.insert k f) m₂ d₂)
    (hdropUnknown : ∀ m₁ d₁ m₂ d₂ k v, (⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩) →
      m₁.get? k = none → d₁.get? k = none →
      motive m₁ d₁ m₂ d₂ → motive (m₁.insert k v) d₁ m₂ d₂)
    (hrefl : ∀ m d, motive m d m d)
    (htrans : ∀ m₁ d₁ m₂ d₂ m₃ d₃, (⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩) → (⟨ m₂ ∷ d₂ ⟩⪯⟨ m₃ ∷ d₃ ⟩) →
      motive m₁ d₁ m₂ d₂ → motive m₂ d₂ m₃ d₃ → motive m₁ d₁ m₃ d₃)
    {m₁ : Value} {d₁ : Desc} {m₂ : Value} {d₂ : Desc}
    (h : ⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩) : motive m₁ d₁ m₂ d₂ := by
  refine MsgCompat.rec
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ => True)
    (motive_4 := fun a b c e _ => motive a b c e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals try (intros; exact trivial)
  case _ => exact hemp
  case _ =>
    intro a b c e k f hmc h1 h2 h3 h4 ih
    exact hmissing a b c e k f hmc h1 h2 h3 h4 ih
  case _ =>
    intro a b c e k f hmc h1 h2 h3 h4 ih
    exact hdeclare a b c e k f hmc h1 h2 h3 h4 ih
  case _ =>
    intro a b c e k v₁ f₁ v f hmc h1 h2 hv hf ih _ _
    exact hupdate a b c e k v₁ f₁ v f hmc h1 h2 hv hf ih
  case _ =>
    intro a b c e k v f hmc h1 h2 h3 h4 ih
    exact hdrop a b c e k v f hmc h1 h2 h3 h4 ih
  case _ =>
    intro a b c e k v hmc h1 h2 ih
    exact hdropUnknown a b c e k v hmc h1 h2 ih
  case _ => intro m d; exact hrefl m d
  case _ =>
    intro a b c e g i h1 h2 ih1 ih2
    exact htrans a b c e g i h1 h2 ih1 ih2

/-! ### The domain invariant of `≼` collapses

  Before `M-Declare`, `≼` satisfied a genuine domain invariant: every key of
  the reader's value was a key of the writer's value or a key the writer's
  descriptor did not declare, and every key the writer declared was declared by
  the reader or populated in the writer's value.  That invariant is what showed
  the subsumption of `IdCompatible` to be underivable, and so it is the reason
  `M-Declare` exists.

  `M-Declare` destroys it outright.  Both halves fail, and the second fails
  even though `M-Declare` does not obviously bear on it: composing `M-Declare`
  with `M-Drop` yields `⟨ ∅ ∷ {0 ↦ int} ⟩⪯⟨ ∅ ∷ ∅ ⟩`, a derivation whose writer
  declares a key that neither the reader's descriptor nor the writer's value
  mentions.  `not_msgCompat_dom` records this.

  Nothing downstream depended on the invariant, and nothing can: `≼` occurs
  only positively in `LimitParseOkCompat''`, so it never constrains anything —
  the constraint on which `(writer, reader)` descriptor pairs the top-level
  theorem covers comes from `≪` in the `linkedState` slot.  `MsgCompat.ind` is
  kept regardless: the mutual block admits no `induction` tactic, so it is the
  only route to any future proof about `≼`. -/

/-- The domain invariant of `≼`, as it stood before `M-Declare`, is false.

    Witness: `M-Declare` at key `0` builds
    `⟨ ∅ ∷ {0 ↦ int} ⟩⪯⟨ {0 ↦ missing} ∷ {0 ↦ int} ⟩` and `M-Drop` at the same
    key builds `⟨ {0 ↦ missing} ∷ {0 ↦ int} ⟩⪯⟨ ∅ ∷ ∅ ⟩`; `M-Trans` composes
    them into `⟨ ∅ ∷ {0 ↦ int} ⟩⪯⟨ ∅ ∷ ∅ ⟩`, refuting the second conjunct at
    `k = 0`.  The first conjunct fails on the `M-Declare` step alone. -/
theorem not_msgCompat_dom :
    ¬ ∀ (m₁ : Value) (d₁ : Desc) (m₂ : Value) (d₂ : Desc),
      (⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩) →
      (∀ k, (m₂.get? k).isSome → (m₁.get? k).isSome ∨ d₁.get? k = none) ∧
      (∀ k, (d₁.get? k).isSome → (d₂.get? k).isSome ∨ (m₁.get? k).isSome) := by
  intro h
  have hdecl : ⟨ (∅ : Value) ∷ (∅ : Desc).insert 0 .int ⟩⪯⟨
      (∅ : Value).insert 0 .missing ∷ (∅ : Desc).insert 0 .int ⟩ :=
    MsgCompat.declare ∅ ∅ ∅ ∅ 0 .int MsgCompat.emp rfl rfl rfl rfl
  have hdrop : ⟨ (∅ : Value).insert 0 .missing ∷ (∅ : Desc).insert 0 .int ⟩⪯⟨
      (∅ : Value) ∷ (∅ : Desc) ⟩ :=
    MsgCompat.drop ∅ ∅ ∅ ∅ 0 .missing .int MsgCompat.emp rfl rfl rfl rfl
  have hcomp := MsgCompat.trans _ _ _ _ _ _ hdecl hdrop
  rcases (h _ _ _ _ hcomp).2 0 (by rw [Desc.get?_insert_same]; rfl) with hh | hh
  · simp [Desc.get?, Desc.fields] at hh
  · simp [Value.get?, Value.vals] at hh

/-- `MsgCompat` subsumes `IdCompatible`, via `M-Declare`.

    * `emp` is `M-Emp`.
    * `drop` is `M-Drop-Unknown` — the two rules are the same shape.
    * each `insert*` case needs *two* steps, because no single rule extends all
      four of `m₁, d₁, m₂, d₂` at once: first `M-Drop` to extend `m₁` and `d₁`,
      then `M-Update` at `V-Refl`/`F-Refl` to extend `m₂` and `d₂`.
    * `addMissing` is `M-Declare`, the rule added for exactly this case.
    * `inputMissing` is `M-Drop` followed by `M-Update` — *not* `M-Missing`,
      whose `m₁.get? k = none` premise fails once `M-Drop` has put `k` into
      `m₁`.

    No well-formedness hypotheses are needed: the `M-Update` steps read the
    just-inserted entries back with `Value.get?_insert_same` /
    `Desc.get?_insert_same`, which carry no `WF` side condition. -/
theorem msgCompat_of_idCompatible (d : Desc) (v₁ v₂ : Value) :
    (⟨ v₁ ≼ v₂ ⟩∷ d) → ⟨ v₁ ∷ d ⟩⪯⟨ v₂ ∷ d ⟩ := by
  intro h
  induction h with
  | emp => exact MsgCompat.emp
  | insertInt d v1 v2 k z _ hd hv1 hv2 ih =>
    exact MsgCompat.update _ _ v2 d k (.int z) .int (.int z) .int
      (MsgCompat.drop v1 d v2 d k (.int z) .int ih hv1 hd hv2 hd)
      (Value.get?_insert_same v1 k _) (Desc.get?_insert_same d k _)
      (ValCompat.refl _ _) (FieldCompat.refl _)
  | insertBool d v1 v2 k b _ hd hv1 hv2 ih =>
    exact MsgCompat.update _ _ v2 d k (.bool b) .bool (.bool b) .bool
      (MsgCompat.drop v1 d v2 d k (.bool b) .bool ih hv1 hd hv2 hd)
      (Value.get?_insert_same v1 k _) (Desc.get?_insert_same d k _)
      (ValCompat.refl _ _) (FieldCompat.refl _)
  | insertMsg d d' v1 v2 v1' v2' k _ _ hd hv1 hv2 ih ih' =>
    exact MsgCompat.update _ _ v2 d k (.msg v1') (.msg d') (.msg v2') (.msg d')
      (MsgCompat.drop v1 d v2 d k (.msg v1') (.msg d') ih hv1 hd hv2 hd)
      (Value.get?_insert_same v1 k _) (Desc.get?_insert_same d k _)
      (ValCompat.msg v1' d' v2' d' ih') (FieldCompat.refl _)
  | drop d v1 v2 k val _ hd hv1 ih =>
    exact MsgCompat.dropUnknown v1 d v2 d k val ih hv1 hd
  | addMissing d v1 v2 k f _ hd hv1 hv2 ih =>
    exact MsgCompat.declare v1 d v2 d k f ih hv1 hd hv2 hd
  | inputMissing d v1 v2 k f _ hd hv1 hv2 ih =>
    exact MsgCompat.update _ _ v2 d k .missing f .missing f
      (MsgCompat.drop v1 d v2 d k .missing f ih hv1 hd hv2 hd)
      (Value.get?_insert_same v1 k _) (Desc.get?_insert_same d k _)
      (ValCompat.refl _ _) (FieldCompat.refl _)

/-! ### `IdCompatible` on schema-correct writers

  Worth recording separately, because it says the subsumption above carries no
  information in the schema-correct case.  `SchemaCorrect` rules out the three
  `IdCompatible` rules that move anything — `addMissing` (a declared key the
  writer's value omits), `inputMissing` (a declared key explicitly set to
  `V_MISSING`) and `drop` (an entry whose key the descriptor never declared) —
  leaving `emp` and the three `insert*` rules, which build the two values in
  lockstep.  `IdCompatible` therefore degenerates to equality, and
  `msgCompat_of_idCompatible` to `M-Refl`.

  The two inversion lemmas the induction needs are recorded first; both are
  ordinary facts about `SchemaCorrect` that the existing files did not have. -/

/-- Erasing a freshly inserted key undoes the insert. -/
theorem desc_erase_insert_self (d : Desc) (k : Int) (f : Field) (h : d.get? k = none) :
    (d.insert k f).erase k = d := by
  cases d with | mk fs =>
  show Desc.mk (Desc.sortedErase k (Desc.sortedInsert k f fs)) = Desc.mk fs
  rw [desc_sortedErase_sortedInsert_same k f fs h]

@[inherit_doc desc_erase_insert_self]
theorem value_erase_insert_self (v : Value) (k : Int) (a : Val) (h : v.get? k = none) :
    (v.insert k a).erase k = v := by
  cases v with | mk vs =>
  show Value.mk (Value.sortedErase k (Value.sortedInsert k a vs)) = Value.mk vs
  rw [value_sortedErase_sortedInsert_same k a vs h]

/-- Inversion for `SchemaCorrect` at a simultaneous insert on a fresh key. -/
theorem sc_insert_inv (d : Desc) (v : Value) (k : Int) (f : Field) (a : Val)
    (hd : d.get? k = none) (hv : v.get? k = none)
    (h : ⟨ v.insert k a ∷ d.insert k f ⟩) : ⟨ v ∷ d ⟩ := by
  have h' := sc_delete_key _ _ k h
  rwa [desc_erase_insert_self d k f hd, value_erase_insert_self v k a hv] at h'

/-- A nested message of a schema-correct value is schema-correct for the nested
    descriptor.  This is `sc_implies_nested_correct` read off at one key. -/
theorem sc_nested_inv (d : Desc) (v : Value) (k : Int) (d' : Desc) (v' : Value)
    (hd : d.get? k = some (.msg d')) (hv : v.get? k = some (.msg v'))
    (h : ⟨ v ∷ d ⟩) : ⟨ v' ∷ d' ⟩ := by
  have hmem : (k, Val.msg v') ∈ v.vals := by
    cases v with | mk vs => exact mem_of_lookup_val vs k _ hv
  have hnc := sc_implies_nested_correct d v h (k, Val.msg v') hmem
  unfold nestedCorrect at hnc
  have hlk : d.fields.lookup k = some (.msg d') := hd
  rw [hlk] at hnc
  exact hnc

/-- Under a schema-correct writer, `IdCompatible` degenerates to equality. -/
theorem idCompatible_eq_of_schemaCorrect (d : Desc) (v₁ v₂ : Value) :
    (⟨ v₁ ≼ v₂ ⟩∷ d) → ⟨ v₁ ∷ d ⟩ → v₁ = v₂ := by
  intro h
  induction h with
  | emp => intro _; rfl
  | insertInt d v1 v2 k z _ hd hv1 hv2 ih =>
    intro hsc; rw [ih (sc_insert_inv d v1 k .int (.int z) hd hv1 hsc)]
  | insertBool d v1 v2 k b _ hd hv1 hv2 ih =>
    intro hsc; rw [ih (sc_insert_inv d v1 k .bool (.bool b) hd hv1 hsc)]
  | insertMsg d d' v1 v2 v1' v2' k _ _ hd hv1 hv2 ih ih' =>
    intro hsc
    have hinner : ⟨ v1' ∷ d' ⟩ :=
      sc_nested_inv (d.insert k (.msg d')) (v1.insert k (.msg v1')) k d' v1'
        (Desc.get?_insert_same d k _) (Value.get?_insert_same v1 k _) hsc
    rw [ih (sc_insert_inv d v1 k (.msg d') (.msg v1') hd hv1 hsc), ih' hinner]
  | drop d v1 v2 k val _ hd hv1 _ =>
    intro hsc
    obtain ⟨f, hf⟩ :=
      sc_implies_val_in_desc d _ hsc k val (Value.get?_insert_same v1 k val)
    rw [hd] at hf
    exact absurd hf (by simp)
  | addMissing d v1 v2 k f _ _ hv1 _ _ =>
    intro hsc
    obtain ⟨val, hval⟩ :=
      sc_implies_desc_in_val _ v1 hsc k f (Desc.get?_insert_same d k f)
    rw [hv1] at hval
    exact absurd hval (by simp)
  | inputMissing d v1 v2 k f _ _ _ _ _ =>
    intro hsc
    exact absurd (Value.get?_insert_same v1 k .missing)
      (sc_implies_no_missing _ _ hsc k)

/-- Hence `msgCompat_of_idCompatible` is `M-Refl` in disguise on schema-correct
    writers. -/
theorem msgCompat_of_idCompatible_of_schemaCorrect (d : Desc) (v₁ v₂ : Value) :
    (⟨ v₁ ≼ v₂ ⟩∷ d) → ⟨ v₁ ∷ d ⟩ → ⟨ v₁ ∷ d ⟩⪯⟨ v₂ ∷ d ⟩ := by
  intro h hsc
  rw [← idCompatible_eq_of_schemaCorrect d v₁ v₂ h hsc]
  exact MsgCompat.refl v₁ d

/-! ### The two dropping rules

  `≼` has two distinct ways for something on the left to vanish, and they are
  not interchangeable.

  `M-Drop` peels the key off *both* `m₁` and `d₁`.  It models an updated
  version deliberately discarding a field it no longer needs; the field was
  properly declared and properly populated, and the new schema simply stops
  carrying it.

  `M-Drop-Unknown` peels the key off `m₁` alone, with `k ∉ dom(d₁)`.  It models
  a value that carries an entry its own schema never declared — junk, or a
  leftover from a schema the writer no longer has.  `serialVal` never emits
  such entries, so a round trip loses them.  This is the configuration
  `idInterParseOk` was generalized to allow when `valid' d v` was dropped in
  favour of `valueWf d v` (which is vacuous on keys outside the descriptor).

  Only `M-Drop` keeps `dom(mᵢ) = dom(dᵢ)`; `M-Drop-Unknown` is precisely the
  rule that breaks that invariant, which is why both are needed.

  **Asymmetry with `≪`, deliberate.**  `≼` occurs only *positively* in
  `LimitParseOkCompat''` (the conclusion `∃ x', … ∧ R d₁ d₂ x x'`), so extra
  rules weaken the statement and can never make it unsound.  `≪` occurs
  *negatively*, as the `linkedState` hypothesis constraining which
  `(writer, reader)` descriptor pairs the theorem covers, and it has no drop
  rule at all — see `descCompat_isSome`.  Adding one would make the top-level
  theorem false: `parseVal`'s `none` branch consumes the tag byte but not the
  payload, so a reader whose descriptor lacks a key the writer encoded
  desynchronizes the byte stream and misparses every following field.  A
  consequence worth stating once: `⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩` does *not* imply
  `d₁ ⋘ d₂`. -/

/-! ## Structural lemmas for `DescCompat`

  These are what `limitRecursiveStateCompat_correct` needs: from
  `linkedState d₁ d₂` at the outer level it must re-establish
  `linkedState d₁' d₂'` at each nested message.  Everything here is an
  induction over a relation that has an explicit `trans` constructor, which is
  why the statements are phrased so that transitivity composes directly.
-/

/-! ### A single-relation eliminator

  Because the four relations form a `mutual` block, Lean's `induction` tactic
  refuses them outright ("does not support the type ... because it is mutually
  inductive") and only the joint four-motive `DescCompat.rec` is available.
  `DescCompat.ind` specializes that recursor with `True` motives for the other
  three relations, recovering ordinary induction on `≪`.  Every proof below
  goes through it.

  `MsgCompat.ind` above is the same construction.  It works for the same
  reason: a motive that only tracks the four maps can hand `M-Update`'s `≺` and
  `∝` premises back unanalyzed.  A motive that has to *inspect* the value
  relation would need a proper simultaneous induction.

  **Maintenance note.**  All three eliminators feed `.rec` one `?_` per
  constructor across the *whole* mutual block — currently 5 + 5 + 5 + 8 = 23.
  Adding a rule to any of the four relations breaks all three `refine`s with a
  confusing "application type mismatch" on the major premise; the fix is to add
  one more `?_`, not to change the motives. -/

/-- Induction principle for `DescCompat` alone.  Use it as
    `refine DescCompat.ind (motive := fun a b => …) ?_ ?_ ?_ ?_ ?_ h` — the
    `induction … using` tactic rejects it because the motive does not range
    over the proof term. -/
theorem DescCompat.ind {motive : Desc → Desc → Prop}
    (hemp : motive ∅ ∅)
    (hadd : ∀ d k f, d.get? k = none → motive d (d.insert k f))
    (hchg : ∀ d k f₀ f, d.get? k = some f₀ → (f₀ ∝ f) → motive d (d.insert k f))
    (hrefl : ∀ d, motive d d)
    (htrans : ∀ a b c, a ⋘ b → b ⋘ c → motive a b → motive b c → motive a c)
    {d₁ d₂ : Desc} (h : d₁ ⋘ d₂) : motive d₁ d₂ := by
  refine DescCompat.rec
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun _ _ _ => True)
    (motive_3 := fun a b _ => motive a b) (motive_4 := fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;>
  intros <;>
  first
    | trivial
    | exact hemp
    | (rename_i d k f hk; exact hadd d k f hk)
    | (rename_i d k f₀ f hk hf _; exact hchg d k f₀ f hk hf)
    | (rename_i a b c hab hbc iha ihb; exact htrans a b c hab hbc iha ihb)
    | (rename_i d; exact hrefl d)

/-- Induction principle for `FieldCompat` alone.  Same construction as
    `DescCompat.ind`; the `F-Msg` case hands back the raw `≪` hypothesis
    rather than an induction hypothesis, which is enough for every use here. -/
theorem FieldCompat.ind {motive : Field → Field → Prop}
    (hboolInt : motive .bool .int)
    (hintBool : motive .int .bool)
    (hmsg : ∀ d₁ d₂, d₁ ⋘ d₂ → motive (.msg d₁) (.msg d₂))
    (hrefl : ∀ f, motive f f)
    (htrans : ∀ f₁ f₂ f₃, (f₁ ∝ f₂) → (f₂ ∝ f₃) → motive f₁ f₂ → motive f₂ f₃ →
      motive f₁ f₃)
    {f₁ f₂ : Field} (h : f₁ ∝ f₂) : motive f₁ f₂ := by
  refine FieldCompat.rec
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun a b _ => motive a b)
    (motive_3 := fun _ _ _ => True) (motive_4 := fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h <;>
  intros <;>
  first
    | trivial
    | exact hboolInt
    | exact hintBool
    | (rename_i a b hab _; exact hmsg a b hab)
    | (rename_i a b c hab hbc iha ihb; exact htrans a b c hab hbc iha ihb)
    | (rename_i f; exact hrefl f)

/-- `≪` preserves the sorted/no-duplicate-keys invariant.  No longer needed by
    the lemmas below — `Desc.get?_insert_same` and `Desc.get?_insert_ne` hold
    unconditionally — but kept as the structural counterpart of
    `not_descCompat_allWF`: `WF` lifts along `≪`, the recursive `AllWF` does
    not. -/
theorem descCompat_wf (d₁ d₂ : Desc) : d₁ ⋘ d₂ → d₁.WF → d₂.WF := by
  intro h
  refine DescCompat.ind (motive := fun a b => a.WF → b.WF) ?_ ?_ ?_ ?_ ?_ h
  · exact fun _ => Desc.empty_wf
  · exact fun d k f _ hwf => Desc.insert_wf d k f hwf
  · exact fun d k f₀ f _ _ hwf => Desc.insert_wf d k f hwf
  · exact fun _ hwf => hwf
  · exact fun _ _ _ _ _ ih₁ ih₂ hwf => ih₂ (ih₁ hwf)

/-- Widening never removes a key: `≪` only ever grows the domain.  This is the
    property that makes parsing under `d₂` sound — `parseVal`'s `none` branch
    consumes the tag byte but not the payload, so a reader that is missing a
    key the writer encoded would desynchronize the byte stream. -/
theorem descCompat_isSome (d₁ d₂ : Desc) (k : Int) :
    d₁ ⋘ d₂ → (d₁.get? k).isSome → (d₂.get? k).isSome := by
  intro h
  refine DescCompat.ind
    (motive := fun a b => (a.get? k).isSome → (b.get? k).isSome)
    ?_ ?_ ?_ ?_ ?_ h
  · exact id
  · intro d k' f _ hk
    rcases eq_or_ne k' k with rfl | hne
    · simp [Desc.get?_insert_same d k' f]
    · rw [Desc.get?_insert_ne d k' k f hne]; exact hk
  · intro d k' f₀ f _ _ hk
    rcases eq_or_ne k' k with rfl | hne
    · simp [Desc.get?_insert_same d k' f]
    · rw [Desc.get?_insert_ne d k' k f hne]; exact hk
  · exact fun _ => id
  · exact fun _ _ _ _ _ ih₁ ih₂ hk => ih₂ (ih₁ hk)

/-- The field type at a shared key evolves along `∝`.  This is the load-bearing
    inversion lemma: it has to survive `D-Trans`, which is why it is phrased as
    an existential over the target type rather than as an equality. -/
theorem descCompat_field (d₁ d₂ : Desc) (k : Int) :
    d₁ ⋘ d₂ → ∀ f₁, d₁.get? k = some f₁ →
    ∃ f₂, d₂.get? k = some f₂ ∧ (f₁ ∝ f₂) := by
  intro h
  refine DescCompat.ind
    (motive := fun a b => ∀ f₁, a.get? k = some f₁ →
      ∃ f₂, b.get? k = some f₂ ∧ (f₁ ∝ f₂))
    ?_ ?_ ?_ ?_ ?_ h
  · intro f₁ hk; simp [Desc.get?, Desc.fields] at hk
  · intro d k' f hnone f₁ hk
    rcases eq_or_ne k' k with rfl | hne
    · rw [hnone] at hk; exact absurd hk (by simp)
    · exact ⟨f₁, by rw [Desc.get?_insert_ne d k' k f hne]; exact hk,
        FieldCompat.refl f₁⟩
  · intro d k' f₀ f hsome hf f₁ hk
    rcases eq_or_ne k' k with rfl | hne
    · rw [hsome] at hk
      exact ⟨f, Desc.get?_insert_same d k' f, by cases hk; exact hf⟩
    · exact ⟨f₁, by rw [Desc.get?_insert_ne d k' k f hne]; exact hk,
        FieldCompat.refl f₁⟩
  · exact fun _ f₁ hk => ⟨f₁, hk, FieldCompat.refl f₁⟩
  · intro a b _ _ _ ih₁ ih₂ f₁ hk
    obtain ⟨f₂, hf₂, hc₂⟩ := ih₁ f₁ hk
    obtain ⟨f₃, hf₃, hc₃⟩ := ih₂ f₂ hf₂
    exact ⟨f₃, hf₃, FieldCompat.trans f₁ f₂ f₃ hc₂ hc₃⟩

/-- `∝` never crosses the scalar/message boundary: there is no derivation from
    `.msg _` to `.bool`/`.int` or back.  Needed before `descCompat_msg`, since
    without it a nested descriptor could in principle be retyped to a scalar,
    which would change the field's encoded width. -/
theorem fieldCompat_msg_inv' (f₁ f₂ : Field) :
    (f₁ ∝ f₂) → ∀ d₁, f₁ = .msg d₁ → ∃ d₂, f₂ = .msg d₂ ∧ (d₁ ⋘ d₂) := by
  intro h
  refine FieldCompat.ind
    (motive := fun a b => ∀ d₁, a = .msg d₁ → ∃ d₂, b = .msg d₂ ∧ (d₁ ⋘ d₂))
    ?_ ?_ ?_ ?_ ?_ h
  · exact fun d₁ hk => absurd hk (by simp)
  · exact fun d₁ hk => absurd hk (by simp)
  · rintro a b hab d₁ ⟨rfl⟩; exact ⟨b, rfl, hab⟩
  · rintro f d₁ rfl; exact ⟨d₁, rfl, DescCompat.refl d₁⟩
  · rintro a b c _ _ ih₁ ih₂ d₁ rfl
    obtain ⟨d₂, rfl, h₁⟩ := ih₁ d₁ rfl
    obtain ⟨d₃, rfl, h₂⟩ := ih₂ d₂ rfl
    exact ⟨d₃, rfl, DescCompat.trans d₁ d₂ d₃ h₁ h₂⟩

@[inherit_doc fieldCompat_msg_inv']
theorem fieldCompat_msg_inv (d₁ : Desc) (f₂ : Field) :
    ((.msg d₁ : Field) ∝ f₂) → ∃ d₂, f₂ = .msg d₂ ∧ (d₁ ⋘ d₂) :=
  fun h => fieldCompat_msg_inv' _ f₂ h d₁ rfl

/-- Scalars stay scalars: the mirror image of `fieldCompat_msg_inv`.  Together
    the two say `∝` preserves the encoded width of a field, which is what keeps
    the byte stream synchronized when the reader's descriptor differs from the
    writer's. -/
theorem fieldCompat_scalar_inv (f₁ f₂ : Field) :
    (f₁ ∝ f₂) → (∀ d, f₁ ≠ .msg d) → ∀ d, f₂ ≠ .msg d := by
  intro h
  refine FieldCompat.ind
    (motive := fun a b => (∀ d, a ≠ .msg d) → ∀ d, b ≠ .msg d) ?_ ?_ ?_ ?_ ?_ h
  · exact fun _ d => by simp
  · exact fun _ d => by simp
  · exact fun a b _ hne => absurd rfl (hne a)
  · exact fun _ hne => hne
  · exact fun _ _ _ _ _ ih₁ ih₂ hne => ih₂ (ih₁ hne)

/-- The lemma `limitRecursiveStateCompat_correct` actually consumes: a nested
    message in `d₁` is still a nested message in `d₂`, with `≪`-related inner
    descriptors.  Follows from `descCompat_field` and `fieldCompat_msg_inv`. -/
theorem descCompat_msg (d₁ d₂ : Desc) (k : Int) (d₁' : Desc) :
    d₁ ⋘ d₂ → d₁.get? k = some (.msg d₁') →
    ∃ d₂', d₂.get? k = some (.msg d₂') ∧ (d₁' ⋘ d₂') := by
  intro hd hk
  obtain ⟨f₂, hf₂, hcompat⟩ := descCompat_field d₁ d₂ k hd (.msg d₁') hk
  obtain ⟨d₂', rfl, hd'⟩ := fieldCompat_msg_inv d₁' f₂ hcompat
  exact ⟨d₂', hf₂, hd'⟩

/-! ### `≪` does *not* preserve `AllWF`

  `descCompat_wf` above lifts `Desc.WF` along `≪`, because `D-Add`/`D-Chg` go
  through `Desc.insert` and `Desc.insert_wf` covers exactly that.  The
  recursive `Desc.AllWF` is a different story: `D-Add` inserts a completely
  unconstrained field, including a `.msg` whose own key list is unsorted.

  This matters for the eventual top-level theorem.  `validState` in
  `limitRecursiveStateCompat_correct` is threaded on the writer's descriptor,
  so `d₂.AllWF` has to be an explicit hypothesis of the theorem rather than
  something recovered from `d₁.AllWF` and `d₁ ⋘ d₂`.  (Alternatively `D-Add`
  and `D-Chg` could carry a `fieldAllWF f` premise, which would make the
  relation itself preserve `AllWF` — worth considering, since the report's
  rules are silent on well-formedness and every other relation in the
  development leaves it to the caller.) -/

/-- Counterexample: `∅ ≪ ∅[1 ↦ msg (unsorted)]` while the right-hand side is
    not `AllWF`. -/
theorem not_descCompat_allWF :
    ¬ (∀ d₁ d₂ : Desc, d₁ ⋘ d₂ → d₁.AllWF → d₂.AllWF) := by
  intro h
  have hbad : ((∅ : Desc).insert 1 (.msg (.mk [(2, .int), (1, .int)]))).AllWF :=
    h ∅ _ (DescCompat.add ∅ 1 _ rfl) ⟨Desc.empty_wf, trivial⟩
  have hsorted : Desc.Sorted (.mk [(2, Field.int), (1, Field.int)]) := hbad.2.1.1.1
  simp [Desc.Sorted] at hsorted

end Pollux.InterParse
