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
    List ((_ : Int) × Field) → List ((_ : Int) × Val)
  | [] => []
  | ⟨k, f₂⟩ :: rest =>
      ⟨k, Value.reinterpretAt d₁ v k f₂⟩ ::
        Value.reinterpretEntries d₁ v rest
termination_by es => 4 * entryListSize es + 3
decreasing_by
  all_goals (have hp := fieldSize_pos f₂; simp only [entryListSize]; omega)

/-- The reader's value at one of its own declared keys: the three-case
    split described in the header. -/
def Value.reinterpretAt (d₁ : Desc) (v : Value) (k : Int) (f₂ : Field) : Val :=
  match d₁.get? k, v.get? k with
  | some f₁, some x => (Val.reinterpret f₁ f₂ x).getD f₂.init
  | _, _ => f₂.init
termination_by 4 * fieldSize f₂ + 2
decreasing_by omega

/-- Carry one field's value from the writer's declaration to the
    reader's. `none` means "not carryable" — the caller falls back to
    `Field.init`, which is exactly what a reader sees when the writer's
    bytes do not populate the field. -/
def Val.reinterpret (f₁ f₂ : Field) (x : Val) : Option Val :=
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
      es.map (fun e => (⟨e.1, Value.reinterpretAt d₁ v e.1 e.2⟩ : (_ : Int) × Val)) := by
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
    Value.reinterpret d d v = v := by
  sorry

/-- Reader-only keys receive the value denoted by silence. The
    determinate form of what InterParse called `M-Add` — that rule was
    dropped there because no round trip produced it; here one does, but
    pinned to `Field.init` rather than an arbitrary type-matching
    value. -/
theorem Value.reinterpretAt_of_writer_missing {d₁ : Desc} {v : Value}
    {k : Int} {f₂ : Field} (h : d₁.get? k = none) :
    Value.reinterpretAt d₁ v k f₂ = f₂.init := by
  rw [Value.reinterpretAt, h]

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
    d₁.get? k₁ = some f₁ → d₁.get? k₂ = some f₂ →
    d₂.get? k₁ = some f₁' → d₂.get? k₂ = some f₂' →
    f₁'.card = .oneof g → f₂'.card = .oneof g →
    ∃ g₀, f₁.card = .oneof g₀ ∧ f₂.card = .oneof g₀

/-- The transform lands in the validity predicate — the well-formedness
    leg of the eventual round-trip theorem.

    `d₂`'s invariants are explicit hypotheses rather than recovered from
    `d₁`, for the same reason `AllWF` was in InterParse: descriptor-side
    invariants do not lift along the compatibility relation, which may
    add unconstrained fields. `AllWF` rather than `WF` because the nested
    `Value.Valid d₂' _` obligations need well-formedness one layer down;
    `Legal` is what rules out `singular`/`msg`, which the transform would
    otherwise be able to populate with a message payload that
    `Val.Matches` rejects. -/
theorem Value.reinterpret_valid {d₁ d₂ : Desc} {v : Value}
    (h₁ : Value.Valid d₁ v) (hwf : d₂.AllWF) (hleg : d₂.Legal)
    (hone : Desc.OneofPreserved d₁ d₂) :
    Value.Valid d₂ (Value.reinterpret d₁ d₂ v) := by
  sorry

end Pollux.Proto
