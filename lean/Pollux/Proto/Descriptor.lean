/-
  Pollux.Proto.Descriptor — the sealed descriptor kernel for the protobuf layer.

  First file of `Pollux.Proto`, the real-protobuf successor to `InterParse`
  (Rocq's `ProtoParse`/`Varint`/`SimplParse` are its ancestors, not its
  sources). The full design rationale — including the experiments that ruled
  out the alternative representations — is in `lean/proto-design.org`; this
  header records only the decisions themselves.

  ## The representation

  Descriptors are a mutual inductive whose field map is stored as a
  **key-sorted sigma list** `List ((_ : Int) × Field)`:

  * A proper map type cannot appear *inside* the inductive: the
    nested-inductive translation rewrites `List ((_ : Int) × Field)` to an
    internal `_nested.List` type, and any structure bundling a proof about
    the list (`AList`, `Finmap`, a `Subtype` of sorted lists) then fails to
    typecheck in the kernel. `Std.TreeMap.Raw` is accepted but rejected here:
    its recursor drags balanced-tree internals into every structural
    recursion, and equal contents can have different tree shapes, so
    extensionality would only ever hold up to `Equiv` — while this project's
    round-trip theorems conclude genuine equalities.
  * Sigma pairs rather than `Int × Field` because mathlib's association-list
    theory (`Mathlib/Data/List/Sigma.lean`: `dlookup`, `kerase`,
    `dedupKeys`, `lookup_ext`, …) is stated for `List (Sigma β)`. This is
    `AList`'s internals, available unbundled.

  The operations on that list — `sortedInsert`, `WF`, the lookup laws,
  extensionality — are **not** defined here: they live in
  `Proto/SortedMap.lean`, stated for a general payload `β` and shared with
  `Value`. Only the constructor's list type has to be repeated per
  inductive, because a parameterized synonym in constructor position is
  rejected by the kernel (that experiment is recorded in
  `Proto/SortedMap.lean`).

  ## The seal

  The list encoding is **kernel-internal by convention** (Lean's `private`
  is file-scoped, so the boundary is enforced by review): outside this file,
  nothing may mention `entries`, `sortedInsert`, or any list-level lemma.
  The public interface is

  * `explode : Desc → Finmap (fun _ : Int => Field)` — a one-layer unwrap
    into a genuine mathlib map; nested `.msg` descriptors stay sealed `Desc`
    handles. Legal because the positivity restriction constrains
    *constructor arguments*, not *functions out of the type*.
  * `get?`, `insert`, `erase`, `ofList`, `∅` — constructors and lookup.

  Because `Finmap` is a quotient by permutation, the sorted-list invariant
  is invisible at the interface: `explode_insert` and the `get?_insert`
  lemmas hold with **no well-formedness hypothesis**, and interface-level
  extensionality is mathlib's `Finmap.ext_lookup`. `WF` (a single
  `Pairwise`; no-dup keys is derived) appears only where genuinely needed:
  the `erase` law at the erased key, and `eq_of_explode_eq` — well-formed
  descriptors are canonical representatives of their `explode` image.

  ## Recursion through the interface

  Structural recursion on the representation is replaced by well-founded
  recursion on `descSize` through `get?`: `descSize_lt_of_get?_msg` says a
  nested message descriptor reached by lookup is strictly smaller. `AllWF`
  is *defined* this way, directly in its one-layer form — there is no
  structural `fieldListAllWF` to keep in sync with it.

  ## Scope

  Field numbers are `Int` for continuity with the InterParse compatibility
  relations; protobuf's range bounds (1 to 2^29 − 1, minus the reserved
  19000–19999) belong in the serializer-layer validity predicate, as
  `valueWf`'s bounds did in InterParse. Oneof membership is a presence
  mode (`Cardinality.oneof`), not structure: the group tag transcribes
  `FieldDescriptorProto.oneof_index`, and its semantics — at most one
  member set, cross-member last-wins — land in the validity predicate and
  the relational spec respectively (`proto-design.org` records the
  argument against the folded representation). Map fields need no
  descriptor support at all: the wire format defines `map<K,V>` as
  `repeated MapEntry`, so they arrive pre-desugared. The value layer is in
  `Proto/Value.lean`, and stays *unsealed* — values are the induction
  skeleton of the round-trip proofs, so they are traversed where
  descriptors are only observed. Deliberately absent for now (see
  `proto-design.org`): enums, groups, and the flat symbol-table
  representation that recursive message types will require once the
  `FileDescriptorSet` import path arrives — `explode` is exactly the
  interface that makes that swap non-breaking.
-/
import Pollux.Proto.SortedMap

namespace Pollux.Proto

/-- The protobuf scalar types (proto3). `group` is deprecated upstream and
    deliberately absent; enums are future work (they need a name table). -/
inductive ScalarType where
  | double | float
  | int32 | int64 | uint32 | uint64
  | sint32 | sint64
  | fixed32 | fixed64 | sfixed32 | sfixed64
  | bool | string | bytes
  deriving DecidableEq, Repr

/-- Field cardinality under the proto3 presence discipline, four-valued as
    in protobuf's own field-presence taxonomy: `singular` is implicit
    presence, `optional` explicit presence, `repeated` a list, and
    `oneof group` explicit presence plus mutual exclusion among the
    message's fields carrying the same `group` tag.

    The tag transcribes `FieldDescriptorProto.oneof_index` (descriptor form
    is flat — the folded `.proto` block is surface syntax) and is
    meaningful only within one descriptor: tag-equality *is* the grouping,
    and nothing ever compares tags across descriptors (compatibility will
    compare the induced partitions). A field carries exactly one
    `Cardinality`, so membership in two groups, repeated oneof members,
    and empty groups are all unrepresentable. Synthetic oneofs (proto3
    `optional` sugar) import as `.optional`, not `.oneof`.

    Whether a repeated scalar field is packed is an encoding-layer concern,
    not a descriptor one; the at-most-one-member-set constraint is a
    serializer-layer validity concern, like the field-number bounds. -/
inductive Cardinality where
  | singular | optional | repeated
  | oneof (group : Nat)
  deriving DecidableEq, Repr

-- The descriptor tree. The `List ((_ : Int) × Field)` argument is the
-- kernel-internal sorted-list representation — see the header; outside this
-- file, consume descriptors through `Desc.explode` / `Desc.get?` only.
mutual
/-- A message descriptor: field numbers to field declarations. -/
inductive Desc where
  | mk (es : List ((_ : Int) × Field))
/-- A field declaration: cardinality plus type. -/
inductive Field where
  | mk (card : Cardinality) (ty : FieldType)
/-- A field's type: scalar, or a nested message descriptor. -/
inductive FieldType where
  | scalar (s : ScalarType)
  | msg (d : Desc)
end

def Field.card : Field → Cardinality | .mk c _ => c
def Field.ty : Field → FieldType | .mk _ t => t

namespace Desc
open List

/-! ### Kernel internals

The raw entry list. Everything in this section is representation; nothing
below `explode` should be used outside this file. The insertion itself and
its theory come from `SortedMap`. -/

/-- The raw entry list. Kernel-internal. -/
def entries : Desc → List ((_ : Int) × Field) | .mk es => es

@[simp] theorem entries_mk (es : List ((_ : Int) × Field)) :
    (Desc.mk es).entries = es := rfl

/-! ### Constructors and the public interface -/

instance : EmptyCollection Desc := ⟨.mk []⟩

@[simp] theorem entries_empty : (∅ : Desc).entries = [] := rfl

/-- Insert (or replace) a field declaration. -/
def insert (d : Desc) (k : Int) (f : Field) : Desc :=
  .mk (SortedMap.sortedInsert k f d.entries)

/-- Remove a field declaration. -/
def erase (d : Desc) (k : Int) : Desc :=
  .mk (List.kerase k d.entries)

/-- **The interface**: one-layer view of a descriptor as a genuine mathlib
    map. Nested `.msg` payloads remain sealed `Desc` handles. All theorem
    statements outside this file consume descriptors through `explode` and
    its derived lookup `get?`. -/
def explode (d : Desc) : Finmap (fun _ : Int => Field) :=
  d.entries.toFinmap

/-- Field lookup, defined through the interface. -/
def get? (d : Desc) (k : Int) : Option Field :=
  d.explode.lookup k

/-- Well-formedness of the representation: the entry list is strictly sorted
    by key. No-duplicate-keys is a consequence (`WF.nodupKeys`), not a second
    conjunct. Interface-level statements should not need this — see the
    header. -/
def WF (d : Desc) : Prop := SortedMap.WF d.entries

theorem WF.nodupKeys {d : Desc} (h : d.WF) : d.entries.NodupKeys :=
  SortedMap.WF.nodupKeys h

/-! ### Bridge lemma (kernel-internal)

The one fact tying the `Finmap` view back to the raw list; the interface
lemmas in the next section are stated on top of it. -/

theorem get?_eq_dlookup (d : Desc) (k : Int) :
    d.get? k = d.entries.dlookup k := by
  simp [get?, explode]

/-! ### Well-formedness preservation

All three are the `SortedMap` theory at `β := Field`. -/

theorem empty_wf : (∅ : Desc).WF := SortedMap.wf_nil

theorem insert_wf (d : Desc) (k : Int) (f : Field) :
    d.WF → (d.insert k f).WF :=
  fun h => SortedMap.sortedInsert_wf k f h

theorem erase_wf (d : Desc) (k : Int) : d.WF → (d.erase k).WF :=
  fun h => SortedMap.kerase_wf k h

/-! ### The interface's equational theory

`explode` turns the kernel constructors into `Finmap` operations. The
`insert` laws are unconditional — the quotient absorbed the sorted-list
invariant; only the `erase` law at the erased key needs `WF` (`kerase` on a
duplicated list removes the first hit only). -/

@[simp] theorem explode_empty : (∅ : Desc).explode = ∅ := by
  apply Finmap.ext_lookup; intro k
  simp [explode]

@[simp] theorem get?_empty (k : Int) : (∅ : Desc).get? k = none := by
  simp [get?]

/-- `explode` commutes with `insert` — no well-formedness hypothesis. -/
@[simp] theorem explode_insert (d : Desc) (k : Int) (f : Field) :
    (d.insert k f).explode = d.explode.insert k f := by
  apply Finmap.ext_lookup
  intro k'
  rcases eq_or_ne k k' with rfl | hne
  · rw [Finmap.lookup_insert]
    simp [explode, insert, entries, SortedMap.dlookup_sortedInsert_self]
  · rw [Finmap.lookup_insert_of_ne _ (Ne.symm hne)]
    simp [explode, insert, entries, SortedMap.dlookup_sortedInsert_ne k k' f hne]

@[simp] theorem get?_insert_same (d : Desc) (k : Int) (f : Field) :
    (d.insert k f).get? k = some f := by
  simp [get?, Finmap.lookup_insert]

theorem get?_insert_ne (d : Desc) (k k' : Int) (f : Field) (h : k ≠ k') :
    (d.insert k f).get? k' = d.get? k' := by
  simp [get?, Finmap.lookup_insert_of_ne _ (Ne.symm h)]

/-- `insert` only ever grows the domain of a descriptor. -/
theorem isSome_get?_insert (d : Desc) (k k' : Int) (f : Field) :
    (d.get? k').isSome → ((d.insert k f).get? k').isSome := by
  intro h
  rcases eq_or_ne k k' with rfl | hne
  · simp
  · rwa [get?_insert_ne d k k' f hne]

/-- `explode` commutes with `erase`, on well-formed descriptors. -/
theorem explode_erase (d : Desc) (k : Int) (h : d.WF) :
    (d.erase k).explode = d.explode.erase k := by
  apply Finmap.ext_lookup
  intro k'
  rcases eq_or_ne k k' with rfl | hne
  · rw [Finmap.lookup_erase]
    simp only [explode, erase, entries_mk, Finmap.dlookup_list_toFinmap]
    exact dlookup_kerase _ h.nodupKeys
  · rw [Finmap.lookup_erase_ne (Ne.symm hne)]
    simp only [explode, erase, entries_mk, Finmap.dlookup_list_toFinmap]
    exact dlookup_kerase_ne (Ne.symm hne)

theorem get?_erase_same (d : Desc) (k : Int) (h : d.WF) :
    (d.erase k).get? k = none := by
  rw [get?_eq_dlookup]
  exact dlookup_kerase _ h.nodupKeys

/-- Lookup after erase at a different key — no well-formedness hypothesis
    (`kerase` and `dlookup` both target the first occurrence). -/
theorem get?_erase_ne (d : Desc) (k k' : Int) (h : k ≠ k') :
    (d.erase k).get? k' = d.get? k' := by
  rw [get?_eq_dlookup, get?_eq_dlookup]
  exact dlookup_kerase_ne (Ne.symm h)

/-- Interface-level extensionality is mathlib's, with no `WF` anywhere. -/
theorem explode_ext {d₁ d₂ : Desc} (h : ∀ k, d₁.get? k = d₂.get? k) :
    d₁.explode = d₂.explode :=
  Finmap.ext_lookup h

/-- Well-formed descriptors are canonical representatives: `explode` is
    injective on them. The representation-level counterpart of
    `explode_ext`, and the only interface lemma that genuinely needs `WF`
    on both sides. -/
theorem eq_of_explode_eq {d₁ d₂ : Desc} (h₁ : d₁.WF) (h₂ : d₂.WF)
    (h : d₁.explode = d₂.explode) : d₁ = d₂ := by
  have hk : ∀ k, d₁.entries.dlookup k = d₂.entries.dlookup k := fun k => by
    have := congrArg (Finmap.lookup k) h
    simpa [explode] using this
  cases d₁ with | mk l₁ => cases d₂ with | mk l₂ =>
  simp only [entries_mk] at hk
  exact congrArg _ (SortedMap.eq_of_dlookup_eq h₁ h₂ hk)

end Desc

/-! ## Size metrics

Structural sizes, defined inside the seal; the public face is
`descSize_lt_of_get?_msg`, which is what lets definitions recurse on nested
message descriptors reached through `get?`. -/

mutual
def descSize : Desc → Nat
  | .mk es => 1 + entryListSize es
def fieldSize : Field → Nat
  | .mk _ t => 1 + fieldTypeSize t
def fieldTypeSize : FieldType → Nat
  | .scalar _ => 1
  | .msg d => 1 + descSize d
def entryListSize : List ((_ : Int) × Field) → Nat
  | [] => 0
  | ⟨_, f⟩ :: rest => fieldSize f + entryListSize rest
end

theorem fieldSize_lt_of_mem {l : List ((_ : Int) × Field)} {k : Int}
    {f : Field} (h : ⟨k, f⟩ ∈ l) : fieldSize f < 1 + entryListSize l := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    obtain ⟨k', f'⟩ := hd
    rcases List.mem_cons.mp h with heq | hmem
    · obtain ⟨rfl, rfl⟩ := Sigma.mk.injEq .. ▸ heq
      simp only [entryListSize]
      omega
    · have := ih hmem
      simp only [entryListSize]
      omega

/-- The interface-level termination lemma: a nested message descriptor
    reached through `get?` is strictly smaller. Any definition recursing
    into nested messages uses well-founded recursion on `descSize` with
    this lemma — see `Desc.AllWF`. -/
theorem descSize_lt_of_get?_msg {d : Desc} {k : Int} {c : Cardinality}
    {d' : Desc} (h : d.get? k = some (.mk c (.msg d'))) :
    descSize d' < descSize d := by
  rw [Desc.get?_eq_dlookup] at h
  have hmem : (⟨k, Field.mk c (.msg d')⟩ : (_ : Int) × Field) ∈ d.entries :=
    List.of_mem_dlookup (by simp [h])
  have hsize := fieldSize_lt_of_mem hmem
  cases d with | mk es =>
  simp only [Desc.entries_mk] at hsize
  simp only [descSize, fieldSize, fieldTypeSize] at *
  omega

/-! ## Recursive well-formedness

Defined directly in one-layer form by well-founded recursion on `descSize` —
the sealed replacement for InterParse's structural
`fieldListAllWF`/`fieldAllWF` mutual block. -/

/-- Recursive well-formedness: the descriptor is `WF` and so is every nested
    message descriptor reachable through `get?`. -/
def Desc.AllWF (d : Desc) : Prop :=
  d.WF ∧ ∀ k c d', d.get? k = some (.mk c (.msg d')) → Desc.AllWF d'
termination_by descSize d
decreasing_by exact descSize_lt_of_get?_msg (by assumption)

/-- One-layer recursive well-formedness of a field declaration. -/
def Field.AllWF : Field → Prop
  | .mk _ (.msg d) => d.AllWF
  | .mk _ (.scalar _) => True

theorem Desc.allWF_def (d : Desc) :
    d.AllWF ↔ d.WF ∧ ∀ k c d', d.get? k = some (.mk c (.msg d')) → d'.AllWF := by
  rw [Desc.AllWF]

/-- `AllWF` phrased through `Field.AllWF`: every field reachable by lookup
    is recursively well-formed. -/
theorem Desc.allWF_iff (d : Desc) :
    d.AllWF ↔ d.WF ∧ ∀ k f, d.get? k = some f → f.AllWF := by
  rw [d.allWF_def]
  constructor
  · rintro ⟨hwf, h⟩
    refine ⟨hwf, fun k f hf => ?_⟩
    obtain ⟨c, t⟩ := f
    cases t with
    | scalar s => trivial
    | msg d' => exact h k c d' hf
  · rintro ⟨hwf, h⟩
    exact ⟨hwf, fun k c d' hf => h k _ hf⟩

theorem Desc.AllWF.wf {d : Desc} (h : d.AllWF) : d.WF :=
  (d.allWF_def.mp h).1

theorem Desc.allWF_empty : (∅ : Desc).AllWF := by
  rw [Desc.allWF_iff]
  exact ⟨Desc.empty_wf, fun k f hf => by simp at hf⟩

theorem Desc.AllWF.insert {d : Desc} {f : Field} (k : Int)
    (hd : d.AllWF) (hf : f.AllWF) : (d.insert k f).AllWF := by
  rw [Desc.allWF_iff] at hd ⊢
  refine ⟨Desc.insert_wf _ _ _ hd.1, fun k' f' hf' => ?_⟩
  rcases eq_or_ne k k' with rfl | hne
  · rw [Desc.get?_insert_same] at hf'
    cases hf'
    exact hf
  · rw [Desc.get?_insert_ne _ _ _ _ hne] at hf'
    exact hd.2 k' f' hf'

/-! ## Building descriptors from unordered entries

The constructor the `FileDescriptorSet` import path will use: fold `insert`
over a plain pair list (later entries win, though a well-formed descriptor
proto has no duplicate field numbers to begin with). -/

/-- Build a descriptor from an unordered list of field declarations. -/
def Desc.ofList (l : List (Int × Field)) : Desc :=
  l.foldl (fun d kf => d.insert kf.1 kf.2) ∅

private theorem foldl_insert_wf :
    ∀ (l : List (Int × Field)) (d : Desc), d.WF →
      (l.foldl (fun d kf => d.insert kf.1 kf.2) d).WF
  | [], _, h => h
  | kf :: rest, d, h => foldl_insert_wf rest _ (Desc.insert_wf d kf.1 kf.2 h)

theorem Desc.ofList_wf (l : List (Int × Field)) : (Desc.ofList l).WF :=
  foldl_insert_wf l ∅ Desc.empty_wf

private theorem foldl_insert_allWF :
    ∀ (l : List (Int × Field)) (d : Desc), d.AllWF →
      (∀ kf ∈ l, kf.2.AllWF) →
      (l.foldl (fun d kf => d.insert kf.1 kf.2) d).AllWF
  | [], _, hd, _ => hd
  | kf :: rest, d, hd, hl =>
    foldl_insert_allWF rest _ (hd.insert kf.1 (hl kf (by simp)))
      (fun kf' h => hl kf' (by simp [h]))

/-- The import path's well-formedness lemma: if every field declaration in
    the list is recursively well-formed, so is the built descriptor. -/
theorem Desc.ofList_allWF (l : List (Int × Field))
    (h : ∀ kf ∈ l, kf.2.AllWF) : (Desc.ofList l).AllWF :=
  foldl_insert_allWF l ∅ Desc.allWF_empty h

end Pollux.Proto
