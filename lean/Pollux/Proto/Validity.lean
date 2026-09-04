/-
  Pollux.Proto.Validity — descriptor legality and value validity.

  The successor of InterParse's `valueWf`, split in two along the line
  protobuf itself draws:

  * `Desc.Legal` collects the rules **protoc enforces on a schema**: field
    numbers in range, and implicit presence only on scalar fields. These
    are descriptor facts, so they live descriptor-side rather than being
    re-checked at every value (InterParse folded its `0 ≤ k < 256` bound
    into `valWfFold` only because it had no descriptor-side predicate
    beyond sortedness).
  * `Value.Valid` is the serializer's phantom well-formedness: the value
    is sorted, **total** over the descriptor, respects the oneof
    partition, and every entry's payload matches its declared type and
    range.

  Range checking is where the twelve-integer-types-share-one-carrier
  decision is paid for, and it is a small bill: one arm per scalar type in
  `Payload.MatchesScalar`. Note that `float`/`double` need no range
  condition at all — their `UInt32`/`UInt64` bit carriers are already
  width-exact, which is a second dividend of representing floating point
  as bits.

  Following InterParse's `valueWf`, the recursion is **structural on the
  value**, with the descriptor consulted by `get?` (a function call, not a
  recursive argument), so no termination measure is needed. `Desc.Legal`
  is the exception: it recurses on the descriptor and so uses well-founded
  recursion on `descSize` through `descSize_lt_of_get?_msg`, exactly like
  `Desc.AllWF`.
-/
import Pollux.Proto.Value

namespace Pollux.Proto

/-! ## Descriptor legality -/

/-- Protobuf's field-number range: 1 to 2^29 − 1, excluding the reserved
    block 19000–19999. -/
def FieldNumber.Valid (k : Int) : Prop :=
  1 ≤ k ∧ k ≤ 2 ^ 29 - 1 ∧ ¬(19000 ≤ k ∧ k ≤ 19999)

/-- The one-layer legality of a single declaration.

    The second conjunct records that **implicit presence applies only to
    scalars**: in proto3 a singular message field has *explicit* presence
    (`has_foo()` is generated for it). This is what makes
    `Payload.isDefault` a non-recursive match, and what makes
    `Field.init`'s `singular`/`msg` arm unreachable. -/
def Desc.FieldOk (k : Int) (f : Field) : Prop :=
  FieldNumber.Valid k ∧ (f.card = .singular → ∃ s, f.ty = .scalar s)

/-- Recursive descriptor legality: every declaration reachable by lookup
    satisfies `FieldOk`. Orthogonal to `Desc.AllWF`, which is about the
    sorted-list representation rather than about protobuf's rules. -/
def Desc.Legal (d : Desc) : Prop :=
  (∀ k f, d.get? k = some f → Desc.FieldOk k f) ∧
  (∀ k c d', d.get? k = some (.mk c (.msg d')) → Desc.Legal d')
termination_by descSize d
decreasing_by exact descSize_lt_of_get?_msg (by assumption)

theorem Desc.legal_def (d : Desc) :
    d.Legal ↔
      (∀ k f, d.get? k = some f → Desc.FieldOk k f) ∧
      (∀ k c d', d.get? k = some (.mk c (.msg d')) → d'.Legal) := by
  rw [Desc.Legal]

theorem Desc.legal_empty : (∅ : Desc).Legal := by
  rw [Desc.legal_def]
  exact ⟨fun k f hf => by simp at hf, fun k c d' hf => by simp at hf⟩

/-! ## The oneof partition

At most one member of a oneof group may be set. Stated one layer at a
time and quantified over *pairs* of keys — this is the one protobuf
constraint that is not pointwise, which is also why cross-descriptor
oneof compatibility will not fit in the pointwise field relation.

Group tags are compared only within a single descriptor: tag-equality
*is* the grouping. -/

/-- No two distinct keys of the same oneof group are both set. -/
def Value.OneofOk (d : Desc) (v : Value) : Prop :=
  ∀ k₁ k₂ f₁ f₂ g p₁ p₂,
    k₁ ≠ k₂ →
    d.get? k₁ = some f₁ → d.get? k₂ = some f₂ →
    f₁.card = .oneof g → f₂.card = .oneof g →
    v.get? k₁ = some (.optional (some p₁)) →
    v.get? k₂ = some (.optional (some p₂)) →
    False

/-! ## Type and range matching -/

/-- Does a payload inhabit a scalar type, in constructor *and* range?

    The ten integer types share the `Int` carrier and are separated here
    by their ranges alone; `sint`/`fixed`/`sfixed` differ from their plain
    counterparts only in encoding, which is the serializer's business.
    `float`/`double` carry width-exact bit patterns, so they need no
    condition. -/
def Payload.MatchesScalar : Payload → ScalarType → Prop
  | .int z, .int32    => -(2 ^ 31) ≤ z ∧ z < 2 ^ 31
  | .int z, .sint32   => -(2 ^ 31) ≤ z ∧ z < 2 ^ 31
  | .int z, .sfixed32 => -(2 ^ 31) ≤ z ∧ z < 2 ^ 31
  | .int z, .int64    => -(2 ^ 63) ≤ z ∧ z < 2 ^ 63
  | .int z, .sint64   => -(2 ^ 63) ≤ z ∧ z < 2 ^ 63
  | .int z, .sfixed64 => -(2 ^ 63) ≤ z ∧ z < 2 ^ 63
  | .int z, .uint32   => 0 ≤ z ∧ z < 2 ^ 32
  | .int z, .fixed32  => 0 ≤ z ∧ z < 2 ^ 32
  | .int z, .uint64   => 0 ≤ z ∧ z < 2 ^ 64
  | .int z, .fixed64  => 0 ≤ z ∧ z < 2 ^ 64
  | .bool _, .bool     => True
  | .string _, .string => True
  | .bytes _, .bytes   => True
  | .float _, .float   => True
  | .double _, .double => True
  | _, _ => False

/-! ## Value validity

Structural recursion on the value; the descriptor is consulted by `get?`
and changes at nested messages, which is fine because it is a parameter
rather than a recursive argument. This is InterParse's `valueWf` pattern,
restated one layer at a time through the descriptor seal. -/

mutual

/-- The serializer's phantom well-formedness: sorted, total over `d`,
    oneof-respecting, and entrywise type- and range-correct. -/
def Value.Valid (d : Desc) : Value → Prop
  | .mk es =>
      SortedMap.WF es ∧
      Value.Total d (.mk es) ∧
      Value.OneofOk d (.mk es) ∧
      Value.ValidEntries d es

/-- Entrywise validity. Representation-level; consumers should go through
    `Value.Valid.matches`, which is stated with `get?`. -/
def Value.ValidEntries (d : Desc) : List ((_ : Int) × Val) → Prop
  | [] => True
  | ⟨k, x⟩ :: rest =>
      (∃ f, d.get? k = some f ∧ Val.Matches x f) ∧ Value.ValidEntries d rest

/-- The presence shape of the value agrees with the declared cardinality,
    and the payload matches the declared type.

    Oneof members are `optional`-shaped, so they share the `optional`
    arms; what distinguishes them is the cross-field `Value.OneofOk`. The
    `implicit`/`msg` combination is absent because implicit presence never
    applies to a message field (`Desc.FieldOk`). -/
def Val.Matches : Val → Field → Prop
  | .implicit p, .mk .singular (.scalar s) => Payload.MatchesScalar p s
  | .optional none, .mk .optional _ => True
  | .optional (some p), .mk .optional t => Payload.Matches p t
  | .optional none, .mk (.oneof _) _ => True
  | .optional (some p), .mk (.oneof _) t => Payload.Matches p t
  | .repeated ps, .mk .repeated t => Payload.MatchesAll ps t
  | _, _ => False

/-- A payload matches a field type: scalars by `MatchesScalar`, nested
    messages by recursive validity against the nested descriptor. -/
def Payload.Matches : Payload → FieldType → Prop
  | p, .scalar s => Payload.MatchesScalar p s
  | .msg v, .msg d' => Value.Valid d' v
  | _, .msg _ => False

/-- Every element of a repeated field matches. -/
def Payload.MatchesAll : List Payload → FieldType → Prop
  | [], _ => True
  | p :: rest, t => Payload.Matches p t ∧ Payload.MatchesAll rest t

end

/-! ### Projections

`Value.Valid` is a bundle; these are its components, plus the
interface-level form of `ValidEntries` that downstream proofs should
use. -/

theorem Value.Valid.wf {d : Desc} {v : Value} (h : Value.Valid d v) : v.WF := by
  cases v with | mk es => exact (by rw [Value.Valid] at h; exact h.1)

theorem Value.Valid.total {d : Desc} {v : Value} (h : Value.Valid d v) :
    Value.Total d v := by
  cases v with | mk es => exact (by rw [Value.Valid] at h; exact h.2.1)

theorem Value.Valid.oneofOk {d : Desc} {v : Value} (h : Value.Valid d v) :
    Value.OneofOk d v := by
  cases v with | mk es => exact (by rw [Value.Valid] at h; exact h.2.2.1)

/-- The usable form of entrywise validity: stated through `get?` rather
    than the entry list. -/
theorem Value.Valid.matches {d : Desc} {v : Value} {k : Int} {x : Val}
    {f : Field} (h : Value.Valid d v) (hv : v.get? k = some x)
    (hd : d.get? k = some f) : Val.Matches x f := by
  sorry

/-- Every declared field is present in a valid value, and nothing else
    is. Immediate from `Total`, recorded because it is the form the
    round-trip proofs consume. -/
theorem Value.Valid.isSome_iff {d : Desc} {v : Value} (h : Value.Valid d v)
    (k : Int) : (v.get? k).isSome ↔ (d.get? k).isSome := h.total k

/-! ### `init` is valid

The base case of the round-trip story: the value denoted by an empty
encoding is a valid value. `Desc.Legal` is needed for the presence rule —
without it a `singular` message field would force `Field.init` into its
unreachable arm, which `Val.Matches` rejects. Only the one-layer part of
`Legal` is used, since `Field.init` never produces a nested message. -/
theorem Value.init_valid {d : Desc} (hwf : d.WF) (hleg : d.Legal) :
    Value.Valid d (Value.init d) := by
  sorry

/-- Each default payload inhabits its own type — the scalar core of
    `init_valid`. -/
theorem ScalarType.matchesScalar_defaultPayload (s : ScalarType) :
    Payload.MatchesScalar (ScalarType.defaultPayload s) s := by
  cases s <;> simp [ScalarType.defaultPayload, Payload.MatchesScalar]

/-- `Field.init` produces a value matching its own declaration, provided
    the declaration is legal. -/
theorem Field.matches_init {k : Int} {f : Field} (h : Desc.FieldOk k f) :
    Val.Matches f.init f := by
  sorry

end Pollux.Proto
