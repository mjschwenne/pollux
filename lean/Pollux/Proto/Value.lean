/-
  Pollux.Proto.Value — the value layer for the protobuf format.

  The counterpart of `Proto/Descriptor.lean`, and deliberately its
  opposite in one respect: **values are not sealed**. Descriptors are
  *observed* one layer at a time (hence `explode`); values are *traversed*
  — they are the induction skeleton of every round-trip proof, and the
  serializer's termination recurses on them. So `entries` is public here
  and `get?` is plain `dlookup`, with no `Finmap` in between.

  ## Presence lives in the value

  Protobuf's field-presence taxonomy is four-valued (`Cardinality`), but
  the *value* shape is three-valued, because oneof's fourth-ness is a
  cross-field constraint rather than a shape: a oneof member is
  `optional`-shaped, and at-most-one-member-set is a conjunct of the
  validity predicate (`Proto/Validity.lean`).

  The consequence that shapes this whole layer: a well-formed value is
  **total over its descriptor** — it carries a slot for every declared
  field, with absence expressed *inside* the presence wrapper
  (`optional none`, `repeated []`). This is not an artifact; it is
  protobuf's own data model. Implicit presence means the default is
  indistinguishable from unset, so `msg.x` always denotes something and
  there is no haser. What is optional is only whether a field costs bytes,
  which is the serializer's skip-defaults rule, not a fact about values.

  `Value.init` is where the two levels meet: it is the value denoted by
  "nothing on the wire". Its payoff is that the same-descriptor round trip
  becomes an identity rather than a transform — in particular
  `optional (some 0)` (explicitly set to the default, emitted) stays
  distinct from `optional none` (unset, not emitted), which is the entire
  point of explicit presence.

  Totality is **descriptor-relative**, so it does not conflict with schema
  evolution: `Total d₁ v` is a hypothesis on the writer's value, and
  `Total d₂ (reinterpret d₁ d₂ v)` is a lemma about the reader's
  (`Proto/Transform.lean`). There is no intermediate state in which a
  value is "not yet total" to reason about.

  ## Scalar payloads

  Twelve of the fifteen scalar types differ only in *encoding* and
  *range*, both of which the descriptor already records, so they share one
  `Int` carrier and their ranges go to the validity predicate — exactly as
  the field-number bounds do. `double`/`float` carry their IEEE-754 **bit
  patterns** (`UInt64`/`UInt32`) rather than `Float`: that is literally
  what the wire format stores, it makes the round trip an honest bit
  equality, and it avoids `Float` entirely — Lean's `Float` is opaque,
  has essentially no equational theory, and IEEE equality is not reflexive
  (NaN), so an equality-concluding round-trip theorem over it would be
  unprovable or false. Interpreting bits as `Float` is a derived view, the
  same "functions out of the type are free" move as `explode`.
-/
import Pollux.Proto.Descriptor
import Pollux.Proto.SortedMap

namespace Pollux.Proto

open List

/-! ## The value tree

`Value` mirrors `Desc`'s key-sorted sigma list; the list type is written
out in full because a parameterized synonym is rejected by the kernel (see
`Proto/SortedMap.lean`). Presence sits *outside* the payload so that the
wrapper is written once rather than duplicated across every payload
constructor, and so that a repeated message field is a genuine
`List Payload`.

The middle layer is `Slot`, not `Val`: it is the value-side counterpart of
`Field` — the descriptor declares a slot, the value fills it — and the name
keeps both the type and its derived metrics (`slotSize` beside `valueSize`)
clearly distinct from `Value`. -/
mutual
/-- A message value: field numbers to slots. -/
inductive Value where
  | mk (es : List ((_ : Int) × Slot))
/-- One field's contents, wrapped in its presence shape. `implicit` is
    implicit presence (the default is indistinguishable from unset),
    `optional` is explicit presence, `repeated` is a list. Oneof members
    are `optional`-shaped. -/
inductive Slot where
  | implicit (p : Payload)
  | optional (p : Option Payload)
  | repeated (ps : List Payload)
/-- A payload: a scalar, or a nested message value. Floating point is
    carried as IEEE-754 bits. -/
inductive Payload where
  | int (z : Int)
  | bool (b : Bool)
  | string (s : String)
  | bytes (bs : List UInt8)
  | float (bits : UInt32)
  | double (bits : UInt64)
  | msg (v : Value)
end

namespace Value

/-! ### The map interface

Public, unlike `Desc`'s: values are traversed. The operations are the
generic `SortedMap` theory instantiated at `β := Slot`. -/

/-- The entry list. Public — values are not sealed. -/
def entries : Value → List ((_ : Int) × Slot) | .mk es => es

@[simp] theorem entries_mk (es : List ((_ : Int) × Slot)) :
    (Value.mk es).entries = es := rfl

instance : EmptyCollection Value := ⟨.mk []⟩

@[simp] theorem entries_empty : (∅ : Value).entries = [] := rfl

/-- Field lookup. -/
def get? (v : Value) (k : Int) : Option Slot := v.entries.dlookup k

/-- Insert (or replace) a field value. -/
def insert (v : Value) (k : Int) (x : Slot) : Value :=
  .mk (SortedMap.sortedInsert k x v.entries)

/-- Remove a field value. -/
def erase (v : Value) (k : Int) : Value :=
  .mk (List.kerase k v.entries)

/-- Well-formedness of the representation: strictly sorted by key. -/
def WF (v : Value) : Prop := SortedMap.WF v.entries

theorem WF.nodupKeys {v : Value} (h : v.WF) : v.entries.NodupKeys :=
  SortedMap.WF.nodupKeys h

/-! ### Lookup laws

The `insert` laws carry no well-formedness hypothesis, for the same
reason as their `Desc` counterparts: `sortedInsert` is a single pass that
only ever adds or replaces at `k`. -/

@[simp] theorem get?_empty (k : Int) : (∅ : Value).get? k = none := by
  simp [get?]

@[simp] theorem get?_insert_same (v : Value) (k : Int) (x : Slot) :
    (v.insert k x).get? k = some x :=
  SortedMap.dlookup_sortedInsert_self k x v.entries

theorem get?_insert_ne (v : Value) (k k' : Int) (x : Slot) (h : k ≠ k') :
    (v.insert k x).get? k' = v.get? k' :=
  SortedMap.dlookup_sortedInsert_ne k k' x h v.entries

theorem isSome_get?_insert (v : Value) (k k' : Int) (x : Slot) :
    (v.get? k').isSome → ((v.insert k x).get? k').isSome := by
  intro h
  rcases eq_or_ne k k' with rfl | hne
  · simp
  · rwa [get?_insert_ne v k k' x hne]

theorem get?_erase_same (v : Value) (k : Int) (h : v.WF) :
    (v.erase k).get? k = none :=
  dlookup_kerase _ h.nodupKeys

theorem get?_erase_ne (v : Value) (k k' : Int) (h : k ≠ k') :
    (v.erase k).get? k' = v.get? k' :=
  dlookup_kerase_ne (Ne.symm h)

/-! ### Well-formedness preservation -/

theorem empty_wf : (∅ : Value).WF := SortedMap.wf_nil

theorem insert_wf (v : Value) (k : Int) (x : Slot) (h : v.WF) :
    (v.insert k x).WF :=
  SortedMap.sortedInsert_wf k x h

theorem erase_wf (v : Value) (k : Int) (h : v.WF) : (v.erase k).WF :=
  SortedMap.kerase_wf k h

/-- Extensionality: well-formed values with the same lookups are equal.
    Consumed at several sites downstream, which is one reason values are
    not sealed. -/
theorem ext_lookup {v₁ v₂ : Value} (h₁ : v₁.WF) (h₂ : v₂.WF)
    (h : ∀ k, v₁.get? k = v₂.get? k) : v₁ = v₂ := by
  cases v₁ with | mk l₁ => cases v₂ with | mk l₂ =>
  exact congrArg _ (SortedMap.eq_of_dlookup_eq h₁ h₂ h)

end Value

/-! ## Size metrics

Termination measures for definitions that recurse through nested
messages on the *value* side. (The reader-driven transform in
`Proto/Transform.lean` recurses on `descSize` instead; these are for the
serializer and the value-indexed predicates.) -/

mutual
def valueSize : Value → Nat
  | .mk es => 1 + valueEntriesSize es
def slotSize : Slot → Nat
  | .implicit p => 1 + payloadSize p
  | .optional none => 1
  | .optional (some p) => 1 + payloadSize p
  | .repeated ps => 1 + payloadListSize ps
def payloadSize : Payload → Nat
  | .msg v => 1 + valueSize v
  | .int _ | .bool _ | .string _ | .bytes _ | .float _ | .double _ => 1
def valueEntriesSize : List ((_ : Int) × Slot) → Nat
  | [] => 0
  | ⟨_, x⟩ :: rest => slotSize x + valueEntriesSize rest
def payloadListSize : List Payload → Nat
  | [] => 0
  | p :: rest => payloadSize p + payloadListSize rest
end

theorem slotSize_lt_of_mem {l : List ((_ : Int) × Slot)} {k : Int} {x : Slot}
    (h : (⟨k, x⟩ : (_ : Int) × Slot) ∈ l) :
    slotSize x < 1 + valueEntriesSize l := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    obtain ⟨k', x'⟩ := hd
    rcases List.mem_cons.mp h with heq | hmem
    · obtain ⟨rfl, rfl⟩ := Sigma.mk.injEq .. ▸ heq
      simp only [valueEntriesSize]; omega
    · have := ih hmem
      simp only [valueEntriesSize]; omega

/-- The value-side termination lemma, mirroring `descSize_lt_of_get?_msg`. -/
theorem slotSize_lt_of_get?_msg {v : Value} {k : Int} {x : Slot}
    (h : v.get? k = some x) : slotSize x < valueSize v := by
  have hmem : (⟨k, x⟩ : (_ : Int) × Slot) ∈ v.entries :=
    List.of_mem_dlookup (by simpa [Value.get?] using h)
  have := slotSize_lt_of_mem hmem
  cases v with | mk es =>
  simpa [valueSize] using this

/-! ## Defaults and initialization

`Value.init d` is the value denoted by an empty encoding against `d`: the
semantic counterpart of the serializer's skip-defaults rule, and the
descendant of the Rocq development's `init_deco`. -/

/-- The protobuf default value for each scalar type. The ten integer
    types share the `Int` carrier and so share the default `0`. -/
def ScalarType.defaultPayload : ScalarType → Payload
  | .double => .double 0
  | .float => .float 0
  | .bool => .bool false
  | .string => .string ""
  | .bytes => .bytes []
  | .int32 | .int64 | .uint32 | .uint64 | .sint32 | .sint64
  | .fixed32 | .fixed64 | .sfixed32 | .sfixed64 => .int 0

/-- Is this payload its type's default — i.e. does the serializer skip it
    under implicit presence?

    Note this needs no `DecidableEq`: it is a direct match on the scalar
    constructors, which matters because `Desc`/`Field`/`FieldType` do not
    derive one. It never has to recurse into a nested `Value`, because
    implicit presence never applies to a message field (in proto3 singular
    message fields have *explicit* presence — see `Desc.PresenceOk`). -/
def Payload.isDefault : Payload → Bool
  | .int 0 | .bool false | .float 0 | .double 0 => true
  | .string s => s.isEmpty
  | .bytes bs => bs.isEmpty
  | _ => false

/-- The slot a field takes when the encoding says nothing about it.

    The `singular`/`msg` case is unreachable in a well-formed descriptor
    (`Desc.PresenceOk` forbids implicit presence on message fields); it is
    mapped to `optional none`, which is what protobuf actually gives
    message fields, so that this function is total. -/
def Field.init : Field → Slot
  | .mk .singular (.scalar s) => .implicit (ScalarType.defaultPayload s)
  | .mk .singular (.msg _) => .optional none
  | .mk .optional _ => .optional none
  | .mk .repeated _ => .repeated []
  | .mk (.oneof _) _ => .optional none

/-- The value denoted by an empty encoding against `d`: every declared
    field present, at its "nothing on the wire" value.

    This is one of the two places that legitimately reach through the
    descriptor seal (the other being the parser's missing-field
    injection), because it is the one descriptor-order-dependent step. It
    is an *implementation*: the specification is `Value.get?_init`, stated
    entirely through the interface. -/
def Value.init (d : Desc) : Value :=
  .mk (d.entries.map (fun e => (⟨e.1, Field.init e.2⟩ : (_ : Int) × Slot)))

/-- The interface-level specification of `Value.init`: it is `Field.init`
    applied pointwise under lookup. Everything downstream should use this
    rather than the entry-list implementation above. -/
theorem Value.get?_init (d : Desc) (k : Int) :
    (Value.init d).get? k = (d.get? k).map Field.init := by
  rw [Desc.get?_eq_dlookup]
  simpa [Value.get?, Value.init] using
    SortedMap.dlookup_mapVal (β := Field) (γ := Slot) k Field.init d.entries

theorem Value.init_wf {d : Desc} (h : d.WF) : (Value.init d).WF :=
  SortedMap.mapVal_wf (β := Field) (γ := Slot) Field.init h

/-! ## Totality

A value is total over a descriptor when their domains agree *exactly*.
The forward direction is what makes the round trip an identity (every
declared field is present, so nothing has to be injected); the backward
direction is what makes unknown-field junk unrepresentable, so the drop
rule fires only across descriptors, never on our own serializer's
output. -/

/-- `v` carries a slot for exactly the fields `d` declares. -/
def Value.Total (d : Desc) (v : Value) : Prop :=
  ∀ k, (v.get? k).isSome ↔ (d.get? k).isSome

theorem Value.init_total (d : Desc) : Value.Total d (Value.init d) := by
  intro k
  simp [Value.get?_init]

theorem Value.total_empty : Value.Total (∅ : Desc) (∅ : Value) := by
  intro k; simp

end Pollux.Proto
