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

/-- The bundle, unfolded at a concrete entry list. -/
theorem Value.valid_mk (d : Desc) (es : List ((_ : Int) × Val)) :
    Value.Valid d (.mk es) ↔
      SortedMap.WF es ∧ Value.Total d (.mk es) ∧ Value.OneofOk d (.mk es) ∧
        Value.ValidEntries d es := by
  rw [Value.Valid]

/-- Entrywise validity follows from a pointwise condition on the entry
    list — the convenient way to *build* a `ValidEntries`. -/
theorem Value.validEntries_of_mem {d : Desc} {es : List ((_ : Int) × Val)}
    (h : ∀ e ∈ es, ∃ f, d.get? e.1 = some f ∧ Val.Matches e.2 f) :
    Value.ValidEntries d es := by
  induction es with
  | nil => rw [Value.ValidEntries]; trivial
  | cons e rest ih =>
    obtain ⟨k, x⟩ := e
    rw [Value.ValidEntries]
    exact ⟨h ⟨k, x⟩ (by simp), ih fun e' he' => h e' (by simp [he'])⟩

/-- The introduction rule for `Value.Valid`, stated entrywise over the
    representation but with the payload condition in `get?` form. -/
theorem Value.valid_of_mem {d : Desc} {v : Value} (hwf : v.WF)
    (htot : Value.Total d v) (hone : Value.OneofOk d v)
    (hm : ∀ e ∈ v.entries, ∃ f, d.get? e.1 = some f ∧ Val.Matches e.2 f) :
    Value.Valid d v := by
  cases v with | mk es =>
  rw [Value.valid_mk]
  exact ⟨hwf, htot, hone, Value.validEntries_of_mem hm⟩

/-- **The introduction rule callers should use.** Same as `valid_of_mem`,
    but the payload condition is stated entirely through `get?` on both
    sides, so a caller never has to walk an entry list — in particular
    never the *descriptor's*, which is sealed. Totality supplies the
    declaration for each entry, and `v.WF` turns membership into a lookup.

    Both consumers (`Value.init_valid` here and `reinterpret_valid` in
    `Proto/Transform.lean`) already have a `get?`-form description of the
    value they are building (`get?_init`, `get?_reinterpret`), so this is
    the form that matches them. -/
theorem Value.valid_of_get? {d : Desc} {v : Value} (hwf : v.WF)
    (htot : Value.Total d v) (hone : Value.OneofOk d v)
    (hm : ∀ k x f, v.get? k = some x → d.get? k = some f → Val.Matches x f) :
    Value.Valid d v := by
  refine Value.valid_of_mem hwf htot hone fun e he => ?_
  obtain ⟨k, x⟩ := e
  have hv : v.get? k = some x := by
    cases v with | mk es =>
    simpa [Value.get?] using List.mem_dlookup hwf.nodupKeys he
  obtain ⟨f, hf⟩ : ∃ f, d.get? k = some f :=
    Option.isSome_iff_exists.mp ((htot k).mp (by rw [hv]; rfl))
  exact ⟨f, hf, hm k x f hv hf⟩

/-- Entrywise validity, consumed at a key. -/
theorem Value.ValidEntries.dlookup_matches {d : Desc}
    {es : List ((_ : Int) × Val)} (h : Value.ValidEntries d es) {k : Int}
    {x : Val} {f : Field} (hv : es.dlookup k = some x)
    (hd : d.get? k = some f) : Val.Matches x f := by
  induction es with
  | nil => simp at hv
  | cons e rest ih =>
    obtain ⟨k', x'⟩ := e
    rw [Value.ValidEntries] at h
    by_cases hk : k' = k
    · subst hk
      rw [List.dlookup_cons_eq] at hv
      obtain ⟨f', hf', hmatch⟩ := h.1
      rw [hd] at hf'
      cases hf'
      cases hv
      exact hmatch
    · exact ih h.2 (by rwa [List.dlookup_cons_ne _ _ (Ne.symm hk)] at hv)

/-- The usable form of entrywise validity: stated through `get?` rather
    than the entry list. -/
theorem Value.Valid.matches {d : Desc} {v : Value} {k : Int} {x : Val}
    {f : Field} (h : Value.Valid d v) (hv : v.get? k = some x)
    (hd : d.get? k = some f) : Val.Matches x f := by
  cases v with | mk es =>
  rw [Value.valid_mk] at h
  exact h.2.2.2.dlookup_matches (by simpa [Value.get?] using hv) hd

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

/-- Each default payload inhabits its own type — the scalar core of
    `init_valid`. -/
theorem ScalarType.matchesScalar_defaultPayload (s : ScalarType) :
    Payload.MatchesScalar (ScalarType.defaultPayload s) s := by
  cases s <;> simp [ScalarType.defaultPayload, Payload.MatchesScalar]

/-- `Field.init` produces a value matching its own declaration, provided
    the declaration is legal. -/
theorem Field.matches_init {k : Int} {f : Field} (h : Desc.FieldOk k f) :
    Val.Matches f.init f := by
  obtain ⟨c, t⟩ := f
  cases c with
  | singular =>
    obtain ⟨s, hs⟩ := h.2 rfl
    simp only [Field.ty] at hs
    subst hs
    exact ScalarType.matchesScalar_defaultPayload s
  | optional => exact trivial
  | repeated => exact trivial
  | oneof g => exact trivial

/-- `Field.init` is never an explicitly-set optional payload: it is the
    value denoted by silence. -/
theorem Field.init_ne_optional_some (f : Field) (p : Payload) :
    f.init ≠ .optional (some p) := by
  obtain ⟨c, t⟩ := f
  cases c <;> cases t <;> simp [Field.init]

/-- **The value denoted by silence is valid.** Totality is immediate
    (`init` enumerates exactly the declared fields) and the oneof conjunct
    is free: `Field.init` never produces an explicitly-set optional
    payload, so no two members of a group can both be set. What is left is
    the entrywise condition, which is `Field.matches_init` at every key. -/
theorem Value.init_valid {d : Desc} (hwf : d.WF) (hleg : d.Legal) :
    Value.Valid d (Value.init d) := by
  have hfo : ∀ k f, d.get? k = some f → Desc.FieldOk k f :=
    ((Desc.legal_def d).mp hleg).1
  have hnone : ∀ (k : Int) (p : Payload),
      (Value.init d).get? k ≠ some (.optional (some p)) := by
    intro k p hk
    rw [Value.get?_init] at hk
    cases hd : d.get? k with
    | none => rw [hd] at hk; simp at hk
    | some f =>
      rw [hd] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      exact Field.init_ne_optional_some f p hk
  refine Value.valid_of_get? (Value.init_wf hwf) (Value.init_total d)
    (fun k₁ k₂ f₁ f₂ g p₁ p₂ _ _ _ _ _ hv₁ _ => hnone k₁ p₁ hv₁) ?_
  intro k x f hx hf
  rw [Value.get?_init, hf, Option.map_some, Option.some.injEq] at hx
  subst hx
  exact Field.matches_init (hfo k f hf)

end Pollux.Proto
