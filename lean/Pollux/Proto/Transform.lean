/-
  Pollux.Proto.Transform — the value a round trip actually yields.

  The successor of InterParse's `compatTransform`, and the same strategy:
  rather than proving a round-trip relation directly, compute the value
  the reader ends up with and prove (a) parsing produces exactly it, and
  (b) it stands in the compatibility relation to the original. This file
  supplies the function and the structural facts about it; the two legs
  arrive with the parser and the compatibility relations respectively.

  As in InterParse, the recursion is driven by the **reader's** field
  list, consulting the writer's descriptor and value by key lookup — the
  reader must produce a value total over its own descriptor, so its
  domain is what the walk enumerates. The termination measure is
  therefore `descSize d₂`, through the kernel's public
  `descSize_lt_of_get?_msg`/`fieldSize_lt_of_mem`; nothing recurses on
  the value.

  Three cases per key, which is the whole cross-descriptor story:

  * **shared** — both descriptors declare it: carry the payload across,
    recursing at nested messages;
  * **reader-only** — `d₂` declares it and `d₁` does not: inject
    `Field.init`, the value denoted by silence;
  * **writer-only** — `d₁` declares it and `d₂` does not: drop it.

  The drop case is new relative to InterParse, where `≪` deliberately had
  no drop rule: there, `parseVal`'s `none` branch consumed the tag byte
  but not the payload, so a reader missing a key desynchronized the
  stream. Real protobuf tags carry a wire type, so unknown fields are
  skippable and dropping is sound. (Preserving them, as protobuf ≥ 3.5
  does, would require an unparsed-bytes region in `Value`; deferred —
  see `proto-design.org`.)

  **Deferred: scalar type changes.** Protobuf permits a number of
  wire-compatible scalar retypings (`int32`/`int64`/`uint32`/`uint64`/
  `bool` share a varint representation, `sint32`/`sint64` share zig-zag,
  and so on). `Payload.reinterpret` currently carries a scalar across
  only when the two types are *equal*, and otherwise falls back to the
  default. Widening this to the compatible-retyping table is future work
  and will be what forces the field relation `∝` to be more than
  equality.
-/
import Pollux.Proto.Validity

namespace Pollux.Proto

/-- Does this cardinality give the field explicit presence? True for
    `optional` and for oneof members, which are `optional`-shaped at the
    value level. -/
def Cardinality.explicit : Cardinality → Bool
  | .optional | .oneof _ => true
  | .singular | .repeated => false

theorem descSize_entries (d : Desc) :
    descSize d = 1 + entryListSize d.entries := by
  cases d; rfl

theorem fieldSize_pos (f : Field) : 0 < fieldSize f := by
  cases f; simp [fieldSize]

theorem fieldSize_ty (f : Field) : fieldSize f = 1 + fieldTypeSize f.ty := by
  cases f; rfl

/-! ## The transform

The termination measure is the reader-side structural size that shrinks
at nested messages — `descSize` → `entryListSize` → `fieldSize` →
`fieldTypeSize` → `descSize` — scaled by 4 with per-step offsets, so
that the steps *within* one layer (where the raw size only weakly
decreases) still decrease strictly. Splitting the entry walk into its
own function is what keeps the chain honest: with a `List.map` over
`attach`, the same obligation has to be discharged from a membership
proof instead. -/

mutual

/-- The value a reader with descriptor `d₂` obtains from a writer's value
    `v` written against `d₁`. -/
def Value.reinterpret (d₁ d₂ : Desc) (v : Value) : Value :=
  .mk (Value.reinterpretEntries d₁ v d₂.entries)
termination_by 4 * descSize d₂
decreasing_by rw [descSize_entries]; omega

/-- The walk over the reader's field list. Structural, so the reader's
    ordering is what the output inherits — which is why the result is
    sorted whenever `d₂` is. -/
def Value.reinterpretEntries (d₁ : Desc) (v : Value) :
    List ((_ : Int) × Field) → List ((_ : Int) × Slot)
  | [] => []
  | ⟨k, f₂⟩ :: rest =>
      ⟨k, Value.reinterpretAt d₁ v k f₂⟩ ::
        Value.reinterpretEntries d₁ v rest
termination_by es => 4 * entryListSize es + 3
decreasing_by
  all_goals (have hp := fieldSize_pos f₂; simp only [entryListSize]; omega)

/-- The reader's value at one of its own declared keys: the three-case
    split described in the header. -/
def Value.reinterpretAt (d₁ : Desc) (v : Value) (k : Int) (f₂ : Field) : Slot :=
  match d₁.get? k, v.get? k with
  | some f₁, some x => (Slot.reinterpret f₁ f₂ x).getD f₂.init
  | _, _ => f₂.init
termination_by 4 * fieldSize f₂ + 2
decreasing_by omega

/-- Carry one field's value from the writer's declaration to the
    reader's. `none` means "not carryable" — the caller falls back to
    `Field.init`, which is exactly what a reader sees when the writer's
    bytes do not populate the field. -/
def Slot.reinterpret (f₁ f₂ : Field) (x : Slot) : Option Slot :=
  match x, f₁.card, f₂.card with
  | .implicit p, .singular, .singular =>
      (Payload.reinterpret f₁.ty f₂.ty p).map .implicit
  | .optional none, c₁, c₂ =>
      if c₁.explicit && c₂.explicit then some (.optional none) else none
  | .optional (some p), c₁, c₂ =>
      if c₁.explicit && c₂.explicit then
        (Payload.reinterpret f₁.ty f₂.ty p).map (fun q => .optional (some q))
      else none
  | .repeated ps, .repeated, .repeated =>
      some (.repeated (ps.filterMap (fun p => Payload.reinterpret f₁.ty f₂.ty p)))
  | _, _, _ => none
termination_by 4 * fieldSize f₂ + 1
decreasing_by all_goals (rw [fieldSize_ty]; omega)

/-- Carry a payload across a type change. Nested messages recurse; equal
    scalar types carry through; everything else fails (see the header on
    deferred scalar retyping). -/
def Payload.reinterpret (t₁ t₂ : FieldType) (p : Payload) : Option Payload :=
  match t₁, t₂, p with
  | .msg d₁', .msg d₂', .msg v' => some (.msg (Value.reinterpret d₁' d₂' v'))
  | .scalar s₁, .scalar s₂, q => if s₁ = s₂ then some q else none
  | _, _, _ => none
termination_by 4 * fieldTypeSize t₂ + 3
decreasing_by simp only [fieldTypeSize]; omega

end

/-! ## Structural facts

These are the statements the round-trip proofs consume. Proofs are left
open — they are routine inductions over the reader's field list, but they
are not what this pass is for. -/

/-- The entry walk is a key-preserving map. Recorded separately because
    the definition had to be written as an explicit recursion to keep the
    termination measure honest. -/
theorem Value.reinterpretEntries_eq_map (d₁ : Desc) (v : Value)
    (es : List ((_ : Int) × Field)) :
    Value.reinterpretEntries d₁ v es =
      es.map (fun e => (⟨e.1, Value.reinterpretAt d₁ v e.1 e.2⟩ : (_ : Int) × Slot)) := by
  induction es with
  | nil => simp [Value.reinterpretEntries]
  | cons hd tl ih => obtain ⟨k, f⟩ := hd; simp [Value.reinterpretEntries, ih]

theorem Value.dlookup_reinterpretEntries (d₁ : Desc) (v : Value) (k : Int)
    (es : List ((_ : Int) × Field)) :
    (Value.reinterpretEntries d₁ v es).dlookup k =
      (es.dlookup k).map (fun f₂ => Value.reinterpretAt d₁ v k f₂) := by
  induction es with
  | nil => simp [Value.reinterpretEntries]
  | cons hd tl ih =>
    obtain ⟨k', f'⟩ := hd
    by_cases h : k' = k <;>
      simp [Value.reinterpretEntries, List.dlookup, h, ih]

/-- The reader's output is addressed by its own descriptor's keys, at the
    reader's own declarations. This is the interface-level specification
    of `reinterpret`, and everything below follows from it. -/
theorem Value.get?_reinterpret (d₁ d₂ : Desc) (v : Value) (k : Int) :
    (Value.reinterpret d₁ d₂ v).get? k =
      (d₂.get? k).map (fun f₂ => Value.reinterpretAt d₁ v k f₂) := by
  simp only [Desc.get?_eq_dlookup, Value.get?, Value.reinterpret, Value.entries_mk]
  exact Value.dlookup_reinterpretEntries d₁ v k d₂.entries

theorem Value.reinterpret_wf {d₁ d₂ : Desc} (v : Value) (h : d₂.WF) :
    (Value.reinterpret d₁ d₂ v).WF := by
  simp only [Value.WF, Value.reinterpret, Value.entries_mk,
    Value.reinterpretEntries_eq_map]
  exact List.Pairwise.map _ (fun _ _ h => h) h

/-- **Totality is descriptor-relative.** The writer's value is total over
    `d₁`; the reader's output is total over `d₂`. There is no state in
    between in which a value fails to be total, which is what makes
    schema evolution compatible with the totality invariant. -/
theorem Value.reinterpret_total (d₁ d₂ : Desc) (v : Value) :
    Value.Total d₂ (Value.reinterpret d₁ d₂ v) := by
  intro k
  rw [Value.get?_reinterpret]
  simp

/-- The engine of `reinterpret_self`: strong induction on the descriptor
    size, so that the nested-message case can appeal to the statement one
    layer down. -/
private theorem Value.reinterpret_self_aux :
    ∀ (n : Nat) (d : Desc), descSize d ≤ n → d.AllWF →
      ∀ v : Value, Value.Valid d v → Value.reinterpret d d v = v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro d hn hd v hv
  have hrec : ∀ d' : Desc, descSize d' < descSize d → d'.AllWF →
      ∀ v' : Value, Value.Valid d' v' → Value.reinterpret d' d' v' = v' :=
    fun d' hlt hd' v' hv' => IH (descSize d') (by omega) d' le_rfl hd' v' hv'
  have hpay : ∀ t : FieldType,
      (∀ d', t = .msg d' → descSize d' < descSize d ∧ d'.AllWF) →
      ∀ p : Payload, Payload.Matches p t →
        Payload.reinterpret t t p = some p := by
    intro t ht p hm
    cases t with
    | scalar s => simp [Payload.reinterpret]
    | msg d' =>
      obtain ⟨hlt, hall⟩ := ht d' rfl
      cases p with
      | msg v' =>
        rw [Payload.Matches] at hm
        rw [Payload.reinterpret, hrec d' hlt hall v' hm]
      | _ => simp [Payload.Matches] at hm
  have hlist : ∀ t : FieldType,
      (∀ d', t = .msg d' → descSize d' < descSize d ∧ d'.AllWF) →
      ∀ ps : List Payload, Payload.MatchesAll ps t →
        ps.filterMap (fun p => Payload.reinterpret t t p) = ps := by
    intro t ht ps
    induction ps with
    | nil => intro _; rfl
    | cons p rest ih =>
      intro hm
      rw [Payload.MatchesAll] at hm
      rw [List.filterMap_cons, hpay t ht p hm.1, ih hm.2]
  have hslot : ∀ (k : Int) (f : Field), d.get? k = some f →
      ∀ x : Slot, Slot.Matches x f → Slot.reinterpret f f x = some x := by
    intro k f hget x hm
    obtain ⟨c, t⟩ := f
    have ht : ∀ d', t = .msg d' → descSize d' < descSize d ∧ d'.AllWF := by
      rintro d' rfl
      exact ⟨descSize_lt_of_get?_msg hget, ((Desc.allWF_def d).mp hd).2 k c d' hget⟩
    cases x with
    | implicit p =>
      cases c with
      | singular =>
        cases t with
        | scalar s =>
          rw [Slot.Matches] at hm
          simp [Slot.reinterpret, Field.card, Field.ty, Payload.reinterpret]
        | msg d' => simp [Slot.Matches] at hm
      | _ => simp [Slot.Matches] at hm
    | optional op =>
      cases op with
      | none =>
        cases c with
        | optional => simp [Slot.reinterpret, Field.card, Cardinality.explicit]
        | oneof g => simp [Slot.reinterpret, Field.card, Cardinality.explicit]
        | _ => simp [Slot.Matches] at hm
      | some p =>
        have hp : Payload.Matches p t := by
          cases c with
          | optional => rw [Slot.Matches] at hm; exact hm
          | oneof g => rw [Slot.Matches] at hm; exact hm
          | _ => simp [Slot.Matches] at hm
        cases c with
        | optional =>
          simp [Slot.reinterpret, Field.card, Field.ty, Cardinality.explicit,
            hpay t ht p hp]
        | oneof g =>
          simp [Slot.reinterpret, Field.card, Field.ty, Cardinality.explicit,
            hpay t ht p hp]
        | _ => simp [Slot.Matches] at hm
    | repeated ps =>
      cases c with
      | repeated =>
        rw [Slot.Matches] at hm
        simp [Slot.reinterpret, Field.card, Field.ty, hlist t ht ps hm]
      | _ => simp [Slot.Matches] at hm
  refine Value.ext_lookup (Value.reinterpret_wf v hd.wf) hv.wf fun k => ?_
  rw [Value.get?_reinterpret]
  cases hget : d.get? k with
  | none =>
    have : v.get? k = none := by
      have h2 := hv.total k
      rw [hget] at h2
      simpa using h2
    simp [this]
  | some f =>
    obtain ⟨x, hx⟩ : ∃ x, v.get? k = some x := by
      have h2 := (hv.total k).mpr (by rw [hget]; rfl)
      exact Option.isSome_iff_exists.mp h2
    rw [hx]
    simp only [Option.map_some, Option.some.injEq]
    simp only [Value.reinterpretAt, hget, hx,
      hslot k f hget x (hv.matches hx hget), Option.getD_some]

/-- **The identity round trip.** Under one descriptor the transform does
    nothing: this is the payoff of totality plus `init`, and the reason
    the same-descriptor theorem should conclude a genuine equality rather
    than the looser `IdCompatible`-style relation InterParse needed.

    In particular `optional (some p)` with `p` the type's default — set
    explicitly, so emitted — survives as itself rather than collapsing
    into `optional none`, which is exactly what explicit presence is
    for. -/
theorem Value.reinterpret_self {d : Desc} {v : Value}
    (hd : d.AllWF) (h : Value.Valid d v) :
    Value.reinterpret d d v = v :=
  Value.reinterpret_self_aux (descSize d) d le_rfl hd v h

/-- Reader-only keys receive the value denoted by silence. The
    determinate form of what InterParse called `M-Add` — that rule was
    dropped there because no round trip produced it; here one does, but
    pinned to `Field.init` rather than an arbitrary type-matching
    value. -/
theorem Value.reinterpretAt_of_writer_missing {d₁ : Desc} {v : Value}
    {k : Int} {f₂ : Field} (h : d₁.get? k = none) :
    Value.reinterpretAt d₁ v k f₂ = f₂.init := by
  rw [Value.reinterpretAt, h]

/-- Keys the writer's *value* does not carry also receive `Field.init`.
    (Unreachable when the writer's value is total over `d₁`, but the
    transform is total, so the case has to be discharged.) -/
theorem Value.reinterpretAt_of_value_missing {d₁ : Desc} {v : Value}
    {k : Int} {f₂ : Field} (h : v.get? k = none) :
    Value.reinterpretAt d₁ v k f₂ = f₂.init := by
  rw [Value.reinterpretAt, h]
  cases d₁.get? k <;> rfl

/-- Shared keys: the writer's value is carried across, with `Field.init`
    as the fallback when the declarations are incompatible. -/
theorem Value.reinterpretAt_of_shared {d₁ : Desc} {v : Value} {k : Int}
    {f₁ f₂ : Field} {x : Slot} (hd : d₁.get? k = some f₁)
    (hv : v.get? k = some x) :
    Value.reinterpretAt d₁ v k f₂ = (Slot.reinterpret f₁ f₂ x).getD f₂.init := by
  rw [Value.reinterpretAt, hd, hv]

/-- Writer-only keys are dropped: they do not appear in the output at
    all, because the walk enumerates the reader's domain. -/
theorem Value.get?_reinterpret_of_reader_missing {d₁ d₂ : Desc} {v : Value}
    {k : Int} (h : d₂.get? k = none) :
    (Value.reinterpret d₁ d₂ v).get? k = none := by
  rw [Value.get?_reinterpret, h]; rfl

/-- The reader does not *merge* oneof groups: two of its own keys that
    share a group tag were already in one group for the writer.

    This is the side condition the design notes predicted would be
    forced, and it is the first genuinely non-pointwise one — it
    constrains *pairs* of fields, so it cannot live in a field-by-field
    relation. Without it `reinterpret_valid` is false: a writer that
    legitimately sets two ungrouped fields hands a reader that groups
    them a value violating `OneofOk`.

    Stated in the direction that preserves validity (reader-group ⇒
    writer-group). The alternative to assuming it is to make the
    transform implement protobuf's cross-member last-wins — clearing all
    but one member — which is what a spec-faithful parser does and what
    the relational `Encodes` spec will require. Deferred with the rest of
    that work. -/
def Desc.OneofPreserved (d₁ d₂ : Desc) : Prop :=
  ∀ k₁ k₂ f₁ f₂ f₁' f₂' g,
    k₁ ≠ k₂ →
    d₁.get? k₁ = some f₁ → d₁.get? k₂ = some f₂ →
    d₂.get? k₁ = some f₁' → d₂.get? k₂ = some f₂' →
    f₁'.card = .oneof g → f₂'.card = .oneof g →
    ∃ g₀, f₁.card = .oneof g₀ ∧ f₂.card = .oneof g₀

/-- The recursive closure of `Desc.OneofPreserved`.

    The one-layer condition is *not* enough for
    `Value.reinterpret_valid`: the transform recurses into nested message
    fields, and a reader may merge two of its *nested* descriptor's
    fields into a oneof group while nothing at the top layer is grouped
    at all. The nested value the transform then builds violates
    `Value.OneofOk` one layer down, so with only the one-layer
    hypothesis the statement is false — see
    `OneofCounterexample.not_reinterpret_valid_one_layer` in
    `Proto/OneofCounterexample.lean` for a concrete witness.

    This is the hypothesis the proof actually needs: `OneofPreserved`
    holds at this layer, and again at every pair of nested message
    descriptors the transform can reach at a common key (which is the
    only way it recurses). Like `Desc.AllWF` and `Desc.Legal` it is
    defined by well-founded recursion on `descSize d₂`. -/
def Desc.OneofPreservedAll (d₁ d₂ : Desc) : Prop :=
  Desc.OneofPreserved d₁ d₂ ∧
    ∀ k c₁ d₁' c₂ d₂',
      d₁.get? k = some (.mk c₁ (.msg d₁')) →
      d₂.get? k = some (.mk c₂ (.msg d₂')) →
      Desc.OneofPreservedAll d₁' d₂'
termination_by descSize d₂
decreasing_by exact descSize_lt_of_get?_msg (by assumption)

theorem Desc.oneofPreservedAll_def (d₁ d₂ : Desc) :
    Desc.OneofPreservedAll d₁ d₂ ↔
      Desc.OneofPreserved d₁ d₂ ∧
        ∀ k c₁ d₁' c₂ d₂',
          d₁.get? k = some (.mk c₁ (.msg d₁')) →
          d₂.get? k = some (.mk c₂ (.msg d₂')) →
          Desc.OneofPreservedAll d₁' d₂' := by
  rw [Desc.OneofPreservedAll]

theorem Desc.OneofPreservedAll.oneLayer {d₁ d₂ : Desc}
    (h : Desc.OneofPreservedAll d₁ d₂) : Desc.OneofPreserved d₁ d₂ :=
  ((Desc.oneofPreservedAll_def d₁ d₂).mp h).1

/-- Only an explicitly-set optional value can transform into one: the
    other three value shapes either fail to carry across or carry across
    as themselves. Used for the oneof conjunct, which has to trace an
    output `optional (some _)` back to the writer's value. -/
private theorem Slot.reinterpret_eq_optional_some {f₁ f₂ : Field} {x : Slot}
    {p : Payload} (h : Slot.reinterpret f₁ f₂ x = some (.optional (some p))) :
    ∃ q, x = .optional (some q) := by
  obtain ⟨c₁, t₁⟩ := f₁
  obtain ⟨c₂, t₂⟩ := f₂
  cases x with
  | implicit p' =>
    cases c₁ with
    | singular =>
      cases c₂ with
      | singular =>
        simp only [Slot.reinterpret, Field.card, Field.ty,
          Option.map_eq_some_iff] at h
        obtain ⟨q, _, hq⟩ := h
        exact absurd hq (by simp)
      | _ => simp [Slot.reinterpret, Field.card] at h
    | _ => simp [Slot.reinterpret, Field.card] at h
  | optional op =>
    cases op with
    | none =>
      simp only [Slot.reinterpret, Field.card] at h
      split at h
      · exact absurd (Option.some.inj h) (by simp)
      · exact absurd h (by simp)
    | some q => exact ⟨q, rfl⟩
  | repeated ps =>
    cases c₁ with
    | repeated =>
      cases c₂ with
      | repeated =>
        simp only [Slot.reinterpret, Field.card, Field.ty] at h
        exact absurd (Option.some.inj h) (by simp)
      | _ => simp [Slot.reinterpret, Field.card] at h
    | _ => simp [Slot.reinterpret, Field.card] at h

/-- The engine of `reinterpret_valid`: strong induction on the reader
    descriptor's size, so the nested-message case can appeal to the
    statement one layer down. -/
private theorem Value.reinterpret_valid_aux :
    ∀ (n : Nat) (d₁ d₂ : Desc) (v : Value), descSize d₂ ≤ n →
      Value.Valid d₁ v → d₂.AllWF → d₂.Legal →
      Desc.OneofPreservedAll d₁ d₂ →
      Value.Valid d₂ (Value.reinterpret d₁ d₂ v) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro d₁ d₂ v hn h₁ hwf hleg hone
  have hfo : ∀ k f, d₂.get? k = some f → Desc.FieldOk k f :=
    ((Desc.legal_def d₂).mp hleg).1
  -- What the reader's nested descriptors inherit at a shared message key.
  have hcond : ∀ (k : Int) (c₁ c₂ : Cardinality) (t₁ t₂ : FieldType),
      d₁.get? k = some (.mk c₁ t₁) → d₂.get? k = some (.mk c₂ t₂) →
      ∀ d₁' d₂', t₁ = .msg d₁' → t₂ = .msg d₂' →
        descSize d₂' < descSize d₂ ∧ d₂'.AllWF ∧ d₂'.Legal ∧
          Desc.OneofPreservedAll d₁' d₂' := by
    rintro k c₁ c₂ t₁ t₂ hg1 hg2 d₁' d₂' rfl rfl
    exact ⟨descSize_lt_of_get?_msg hg2,
      ((Desc.allWF_def d₂).mp hwf).2 k c₂ d₂' hg2,
      ((Desc.legal_def d₂).mp hleg).2 k c₂ d₂' hg2,
      ((Desc.oneofPreservedAll_def d₁ d₂).mp hone).2 k c₁ d₁' c₂ d₂' hg1 hg2⟩
  -- One payload across a type change.
  have hpay : ∀ t₁ t₂ : FieldType,
      (∀ d₁' d₂', t₁ = .msg d₁' → t₂ = .msg d₂' →
        descSize d₂' < descSize d₂ ∧ d₂'.AllWF ∧ d₂'.Legal ∧
          Desc.OneofPreservedAll d₁' d₂') →
      ∀ p q : Payload, Payload.Matches p t₁ →
        Payload.reinterpret t₁ t₂ p = some q → Payload.Matches q t₂ := by
    intro t₁ t₂ ht p q hm hr
    cases t₂ with
    | scalar s₂ =>
      cases t₁ with
      | scalar s₁ =>
        simp only [Payload.reinterpret] at hr
        split at hr
        · rename_i hs
          subst hs
          obtain rfl := Option.some.inj hr
          exact hm
        · exact absurd hr (by simp)
      | msg d₁' => cases p <;> simp [Payload.reinterpret] at hr
    | msg d₂' =>
      cases t₁ with
      | scalar s₁ => cases p <;> simp [Payload.reinterpret] at hr
      | msg d₁' =>
        cases p with
        | msg v' =>
          obtain ⟨hlt, ha, hl, ho⟩ := ht d₁' d₂' rfl rfl
          rw [Payload.Matches] at hm
          simp only [Payload.reinterpret] at hr
          obtain rfl := Option.some.inj hr
          rw [Payload.Matches]
          exact IH (descSize d₂') (by omega) d₁' d₂' v' le_rfl hm ha hl ho
        | _ => simp [Payload.reinterpret] at hr
  -- The elementwise version, for repeated fields.
  have hlist : ∀ t₁ t₂ : FieldType,
      (∀ d₁' d₂', t₁ = .msg d₁' → t₂ = .msg d₂' →
        descSize d₂' < descSize d₂ ∧ d₂'.AllWF ∧ d₂'.Legal ∧
          Desc.OneofPreservedAll d₁' d₂') →
      ∀ ps : List Payload, Payload.MatchesAll ps t₁ →
        Payload.MatchesAll
          (ps.filterMap (fun p => Payload.reinterpret t₁ t₂ p)) t₂ := by
    intro t₁ t₂ ht ps
    induction ps with
    | nil =>
      intro _
      simp only [List.filterMap_nil]
      rw [Payload.MatchesAll]
      trivial
    | cons p rest ih =>
      intro hm
      rw [Payload.MatchesAll] at hm
      cases hq : Payload.reinterpret t₁ t₂ p with
      | none => simpa only [List.filterMap_cons, hq] using ih hm.2
      | some q =>
        simp only [List.filterMap_cons, hq]
        rw [Payload.MatchesAll]
        exact ⟨hpay t₁ t₂ ht p q hm.1 hq, ih hm.2⟩
  -- One field's value across a declaration change.
  have hslot : ∀ (k : Int) (f₁ f₂ : Field), d₁.get? k = some f₁ →
      d₂.get? k = some f₂ → ∀ x y : Slot, Slot.Matches x f₁ →
      Slot.reinterpret f₁ f₂ x = some y → Slot.Matches y f₂ := by
    intro k f₁ f₂ hg1 hg2 x y hm hr
    obtain ⟨c₁, t₁⟩ := f₁
    obtain ⟨c₂, t₂⟩ := f₂
    have hct := hcond k c₁ c₂ t₁ t₂ hg1 hg2
    cases x with
    | implicit p =>
      cases c₁ with
      | singular =>
        cases c₂ with
        | singular =>
          obtain ⟨s₂, hs₂⟩ := (hfo k ⟨.singular, t₂⟩ hg2).2 rfl
          simp only [Field.ty] at hs₂
          subst hs₂
          cases t₁ with
          | scalar s₁ =>
            simp only [Slot.reinterpret, Field.card, Field.ty,
              Option.map_eq_some_iff] at hr
            obtain ⟨q, hq, rfl⟩ := hr
            rw [Slot.Matches] at hm
            rw [Slot.Matches]
            have := hpay (.scalar s₁) (.scalar s₂) hct p q (by rw [Payload.Matches]; exact hm) hq
            rwa [Payload.Matches] at this
          | msg d₁' => simp [Slot.Matches] at hm
        | _ => simp [Slot.reinterpret, Field.card] at hr
      | _ => simp [Slot.reinterpret, Field.card] at hr
    | optional op =>
      cases op with
      | none =>
        simp only [Slot.reinterpret, Field.card] at hr
        split at hr
        · rename_i hc
          obtain rfl := Option.some.inj hr
          cases c₂ with
          | singular => simp [Cardinality.explicit] at hc
          | repeated => simp [Cardinality.explicit] at hc
          | optional => rw [Slot.Matches]; trivial
          | oneof g => rw [Slot.Matches]; trivial
        · exact absurd hr (by simp)
      | some p =>
        simp only [Slot.reinterpret, Field.card, Field.ty] at hr
        split at hr
        · rename_i hc
          rw [Option.map_eq_some_iff] at hr
          obtain ⟨q, hq, rfl⟩ := hr
          have hmp : Payload.Matches p t₁ := by
            cases c₁ with
            | singular => simp [Cardinality.explicit] at hc
            | repeated => simp [Cardinality.explicit] at hc
            | optional => rw [Slot.Matches] at hm; exact hm
            | oneof g => rw [Slot.Matches] at hm; exact hm
          have hmq := hpay t₁ t₂ hct p q hmp hq
          cases c₂ with
          | singular => simp [Cardinality.explicit] at hc
          | repeated => simp [Cardinality.explicit] at hc
          | optional => rw [Slot.Matches]; exact hmq
          | oneof g => rw [Slot.Matches]; exact hmq
        · exact absurd hr (by simp)
    | repeated ps =>
      cases c₁ with
      | repeated =>
        cases c₂ with
        | repeated =>
          simp only [Slot.reinterpret, Field.card, Field.ty] at hr
          obtain rfl := Option.some.inj hr
          rw [Slot.Matches] at hm
          rw [Slot.Matches]
          exact hlist t₁ t₂ hct ps hm
        | _ => simp [Slot.reinterpret, Field.card] at hr
      | _ => simp [Slot.reinterpret, Field.card] at hr
  -- The reader's value at one of its own keys matches its declaration.
  have hat : ∀ (k : Int) (f₂ : Field), d₂.get? k = some f₂ →
      Slot.Matches (Value.reinterpretAt d₁ v k f₂) f₂ := by
    intro k f₂ hg2
    have hinit : Slot.Matches f₂.init f₂ := Field.matches_init (hfo k f₂ hg2)
    cases hg1 : d₁.get? k with
    | none => rw [Value.reinterpretAt_of_writer_missing hg1]; exact hinit
    | some f₁ =>
      cases hvx : v.get? k with
      | none => rw [Value.reinterpretAt_of_value_missing hvx]; exact hinit
      | some x =>
        rw [Value.reinterpretAt_of_shared hg1 hvx]
        cases hy : Slot.reinterpret f₁ f₂ x with
        | none => rw [Option.getD_none]; exact hinit
        | some y =>
          rw [Option.getD_some]
          exact hslot k f₁ f₂ hg1 hg2 x y (h₁.matches hvx hg1) hy
  -- The oneof conjunct: the reader groups only what the writer grouped.
  have honeok : Value.OneofOk d₂ (Value.reinterpret d₁ d₂ v) := by
    have hex : ∀ (k : Int) (f₂ : Field) (p : Payload),
        d₂.get? k = some f₂ →
        (Value.reinterpret d₁ d₂ v).get? k = some (.optional (some p)) →
        ∃ f₁ q, d₁.get? k = some f₁ ∧ v.get? k = some (.optional (some q)) := by
      intro k f₂ p hg2 hget
      rw [Value.get?_reinterpret, hg2, Option.map_some, Option.some.injEq] at hget
      cases hg1 : d₁.get? k with
      | none =>
        rw [Value.reinterpretAt_of_writer_missing hg1] at hget
        exact absurd hget (Field.init_ne_optional_some f₂ p)
      | some f₁ =>
        cases hvx : v.get? k with
        | none =>
          rw [Value.reinterpretAt_of_value_missing hvx] at hget
          exact absurd hget (Field.init_ne_optional_some f₂ p)
        | some x =>
          rw [Value.reinterpretAt_of_shared hg1 hvx] at hget
          cases hy : Slot.reinterpret f₁ f₂ x with
          | none =>
            rw [hy, Option.getD_none] at hget
            exact absurd hget (Field.init_ne_optional_some f₂ p)
          | some y =>
            rw [hy, Option.getD_some] at hget
            subst hget
            obtain ⟨q, rfl⟩ := Slot.reinterpret_eq_optional_some hy
            exact ⟨f₁, q, rfl, rfl⟩
    intro k₁ k₂ f₁' f₂' g p₁ p₂ hne hg1 hg2 hc1 hc2 hv1 hv2
    obtain ⟨e₁, q₁, he₁, hq₁⟩ := hex k₁ f₁' p₁ hg1 hv1
    obtain ⟨e₂, q₂, he₂, hq₂⟩ := hex k₂ f₂' p₂ hg2 hv2
    obtain ⟨g₀, hg₀1, hg₀2⟩ :=
      hone.oneLayer k₁ k₂ e₁ e₂ f₁' f₂' g hne he₁ he₂ hg1 hg2 hc1 hc2
    exact h₁.oneofOk k₁ k₂ e₁ e₂ g₀ q₁ q₂ hne he₁ he₂ hg₀1 hg₀2 hq₁ hq₂
  refine Value.valid_of_get? (Value.reinterpret_wf v hwf.wf)
    (Value.reinterpret_total d₁ d₂ v) honeok ?_
  intro k x f₂ hx hg2
  rw [Value.get?_reinterpret, hg2, Option.map_some, Option.some.injEq] at hx
  subst hx
  exact hat k f₂ hg2

/-  The originally stated form of the theorem below assumed only the
    one-layer `Desc.OneofPreserved d₁ d₂`:

      theorem Value.reinterpret_valid {d₁ d₂ : Desc} {v : Value}
          (h₁ : Value.Valid d₁ v) (hwf : d₂.AllWF) (hleg : d₂.Legal)
          (hone : Desc.OneofPreserved d₁ d₂) :
          Value.Valid d₂ (Value.reinterpret d₁ d₂ v)

    That statement is **false**: `Desc.OneofPreserved` constrains only
    the two descriptors' own field lists, while the transform recurses
    into nested message fields, where the reader may group fields the
    writer left ungrouped. `Proto/OneofCounterexample.lean` exhibits a
    witness and proves the negation
    (`OneofCounterexample.not_reinterpret_valid_one_layer`). The
    corrected statement below replaces the hypothesis by its recursive closure
    `Desc.OneofPreservedAll`, which is implied by the original at every
    layer and is what the proof needs; nothing else changes. -/

/-- The transform lands in the validity predicate — the well-formedness
    leg of the eventual round-trip theorem.

    `d₂`'s invariants are explicit hypotheses rather than recovered from
    `d₁`, for the same reason `AllWF` was in InterParse: descriptor-side
    invariants do not lift along the compatibility relation, which may
    add unconstrained fields. `AllWF` rather than `WF` because the nested
    `Value.Valid d₂' _` obligations need well-formedness one layer down;
    `Legal` is what rules out `singular`/`msg`, which the transform would
    otherwise be able to populate with a message payload that
    `Slot.Matches` rejects.

    The oneof hypothesis is `Desc.OneofPreservedAll`, the recursive
    closure of `Desc.OneofPreserved`; see the note above on why the
    one-layer form does not suffice. -/
theorem Value.reinterpret_valid {d₁ d₂ : Desc} {v : Value}
    (h₁ : Value.Valid d₁ v) (hwf : d₂.AllWF) (hleg : d₂.Legal)
    (hone : Desc.OneofPreservedAll d₁ d₂) :
    Value.Valid d₂ (Value.reinterpret d₁ d₂ v) :=
  Value.reinterpret_valid_aux (descSize d₂) d₁ d₂ v le_rfl h₁ hwf hleg hone

end Pollux.Proto
