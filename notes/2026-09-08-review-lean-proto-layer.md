# The Lean Protobuf Layer: a Reader's Guide

Review of `pollux/lean/Pollux/Proto/` as of commit `e3f436f` (2026-09-08),
written as source material for a rewrite of report §5. Structured as notes and
analysis rather than prose to lift — the intent is that you can write each
report section from the corresponding section here without needing the Lean open
beside you.

**Method.** I read all six files in `Pollux/Proto/` plus `lean/proto-design.org`
in full. I checked for `sorry`/`admit` (none). I did **not** run `lake build`,
so claims about the axiom set (`propext`, `Classical.choice`, `Quot.sound`) come
from `proto-design.org` §"Status and verification", not from my own
`#print axioms`. Design rationale marked *(design.org)* is the project's own
argument, restated; items marked **(finding)** are mine and are not recorded
anywhere in the repo.

---

## 1. The Layer at a Glance

| File | Lines | Holds |
| --- | ---: | --- |
| `SortedMap.lean` | 143 | Payload-parameterized sorted sigma-list map theory, shared by `Desc` and `Value` |
| `Descriptor.lean` | 438 | `Desc`/`Field`/`FieldType`/`ScalarType`/`Cardinality`, the seal, sizes, `AllWF` |
| `Value.lean` | 316 | `Value`/`Val`/`Payload`, the unsealed map interface, `Field.init`/`Value.init`, `Value.Total` |
| `Validity.lean` | 340 | `Desc.Legal` (protoc's schema rules), `Value.OneofOk`, `Value.Valid`/`Val.Matches` |
| `Transform.lean` | 694 | `Value.reinterpret` and its four theorems, `Desc.OneofPreserved{,All}` |
| `OneofCounterexample.lean` | 297 | Explicit witness refuting the one-layer oneof hypothesis |

Import order is exactly that chain. Everything compiles; nothing is `sorry`ed.

**The single most important thing for the report to absorb:** there is
*no compatibility relation in Lean at all*. What exists instead is a
**function**, `Value.reinterpret d₁ d₂ v`, that computes the value a reader with
descriptor `d₂` obtains from a writer's value written against `d₁`, plus
theorems that it preserves validity and is the identity at `d₁ = d₂`. Report §5
is currently designing the relation; the Lean layer has committed to the
function. Those are not in conflict — the plan is "compute the transform, then
prove the relation characterizes it" — but the report presents the relation as
primary, and the Lean development has made the function primary. That inversion
is the core of the refactor.

---

## 2. The Descriptor Kernel (`Descriptor.lean`)

### 2.1 the Types

```lean
inductive ScalarType where
  | double | float | int32 | int64 | uint32 | uint64
  | sint32 | sint64 | fixed32 | fixed64 | sfixed32 | sfixed64
  | bool | string | bytes

inductive Cardinality where
  | singular | optional | repeated | oneof (group : Nat)

mutual
inductive Desc      where | mk (es : List ((_ : Int) × Field))
inductive Field     where | mk (card : Cardinality) (ty : FieldType)
inductive FieldType where | scalar (s : ScalarType) | msg (d : Desc)
end
```

Fifteen scalar types (no enums, no groups). Four cardinalities — protobuf's own
field-presence taxonomy. `Field` is a *pair*: cardinality and type, **no name**.
Field numbers are `Int`.

### 2.2 Why a Key-Sorted Sigma List

*(design.org §Experiment)* The container must (a) be accepted by Lean's
nested-inductive translation, (b) support "same lookups ⇒ equal", (c) admit a
structural size, (d) minimize bespoke proof surface. The experiment table is
worth reproducing in the report verbatim — it is a genuine negative result:

| Container | Accepted? |
| --- | --- |
| `List (Int × Field)`, `List ((_ : Int) × Field)`, `Array`, `Std.TreeMap.Raw`, `Int → Option Field` | yes |
| `AList`, `Finmap`, `{l : List _ // l.Pairwise _}`, any `abbrev`/`def` synonym | **no** |

The three bundled-map failures share a cause: the nested-inductive translation
rewrites `List ((_ : Int) × Field)` to an internal `_nested.List` type, and any
structure carrying a *proof about* that list then fails to typecheck. The
synonym failure is separate and sharper: the translation only recognizes
*literal* applications of already-declared inductives, so `SortedList Field` is
rejected for both `abbrev` and `def`. That is why the list type is written out
in full in each of `Desc` and `Value` while the *theory* lives once in
`SortedMap.lean`.

`TreeMap.Raw` was accepted and rejected anyway: its recursor drags balanced-tree
internals into every structural recursion, and equal contents can have different
tree shapes, so extensionality would hold only up to `Equiv` — while the
project's round-trip theorems conclude genuine equalities.

Sigma pairs rather than `Int × Field` because mathlib's association-list theory
(`dlookup`, `kerase`, `lookup_ext`, …) is stated for `List (Sigma β)`. That is
`AList`'s internals, available unbundled — the workaround for the kernel
limitation is to use the contents of the bundled type without the bundle.

`WF` is *sortedness alone* — a single `Pairwise (· .1 < · .1)` — with
no-duplicate-keys derived in one line. `sortedInsert` is hand-rolled as a single
pass with replace-on-collision, specifically so that the lookup-after-insert
lemmas hold with **no** well-formedness hypothesis.

### 2.3 the Seal

The representation is kernel-internal *by convention* (Lean's `private` is
file-scoped, so this is a spec boundary enforced by review, not a language
mechanism). The public interface is:

```lean
def explode (d : Desc) : Finmap (fun _ : Int => Field) := d.entries.toFinmap
def get?    (d : Desc) (k : Int) : Option Field := d.explode.lookup k
```

`explode` unwraps **one layer** into a genuine mathlib map; nested `.msg`
descriptors stay sealed `Desc` handles. The realization that makes this work:
the kernel restriction constrains *constructor arguments*, not
*functions out of the type* — so the very map types that cannot appear inside
the inductive are available as its views.

Because `Finmap` is a quotient by permutation, the sorted-list invariant is
invisible at the interface. This is the payoff table:

| Interface law | Needs `WF`? |
| --- | --- |
| `explode_insert`, `get?_insert_same`, `get?_insert_ne`, `get?_erase_ne` | **no** |
| `explode_ext` (it *is* `Finmap.ext_lookup`) | **no** |
| `explode_erase`, `get?_erase_same` | yes (`kerase` removes only the first hit) |
| `eq_of_explode_eq` (WF descriptors are canonical representatives) | yes, both sides |

Values, by contrast, are **not** sealed (`Value.entries` is public, `get?` is
plain `dlookup`). The asymmetry is principled and worth a sentence in the
report: *descriptors are observed, values are traversed*. Descriptors are only
ever consumed one layer at a time — the serializer walks the value's entry list
and consults the descriptor by lookup — whereas values are the induction
skeleton of every round-trip proof.

### 2.4 Recursion Through the Interface

Structural recursion on the representation is replaced by well-founded recursion
on `descSize` through `get?`, with one public termination lemma:

```lean
theorem descSize_lt_of_get?_msg {d k c d'} (h : d.get? k = some (.mk c (.msg d'))) :
    descSize d' < descSize d
```

Three predicates are *defined* this way, all in one-layer form: `Desc.AllWF`,
`Desc.Legal`, and `Desc.OneofPreservedAll`. This eliminates InterParse's
parallel structural `fieldListAllWF`/`fieldAllWF` mutual block and its
synchronization lemmas.

There are consequently **two orthogonal descriptor predicates** plus a third
from `Validity.lean`, and the report should keep them distinct:

- `Desc.WF` — the entry list is strictly sorted. Representation hygiene.
- `Desc.AllWF` — `WF` at this layer and at every nested descriptor reachable by
  `get?`. Recursive representation hygiene.
- `Desc.Legal` — protoc's rules (§4.1). Recursive *semantic* legality.

### 2.5 Cardinality: Oneof as an Annotation, Not Structure

`Cardinality.oneof (group : Nat)` transcribes `FieldDescriptorProto.oneof_index`
verbatim. The tag is meaningful only within one descriptor — tag-equality *is*
the grouping — and nothing ever compares tags across descriptors.

The rejected alternative (a oneof that *contains* its members, matching `.proto`
surface syntax) is argued down in four steps
*(design.org §The rejected alternative)*, and the report's current set-keyed
field map is exactly the rejected design. The strongest two arguments:

1. **Descriptor form is already flat.** Members sit in `DescriptorProto.field`
   alongside ordinary fields carrying `oneof_index`; `oneof_decl` holds only
   names and options. The import path parses descriptors, never source.
2. **Oneofs have no field number.** Members share the message's tag space and
   the wire tag names the member directly, so a nested oneof entry has no key to
   live under in a sorted map. `get?` (tag dispatch — the parser's central move)
   would become a two-level search and `WF` would need cross-group
   number-disjointness.

A fourth argument bears directly on report §5's `Oneof-*` rules:
*"matching tags" never happens*. Within one descriptor there is nothing to
match; across descriptors the side condition is **partition preservation** — for
shared numbers `k₁, k₂`, same-group-in-`d₁` ↔ same-group-in-`d₂`, each side
stated with its own tags. Raw `oneof_index` is not evolution-stable (adding a
oneof shifts every later index), so that phrasing is forced in *any*
representation.

Because a field carries exactly one `Cardinality`, membership in two groups,
repeated oneof members, and empty groups are all unrepresentable. Report §5's
`Oneof-Add-F`/`Oneof-Elim` bugs (stale entries under set-valued keys) are
artifacts of the rejected representation and simply do not arise here.

### 2.6 What the Descriptor Deliberately Does Not Have

This list matters more than it looks, because report §5 currently uses several
of these:

| Absent | Status | Report impact |
| --- | --- | --- |
| **Reserved field sets** | Not modeled at all | §5 threads `⟨r, f⟩` through *every* judgement. There is no `r` in `Desc`. |
| **Field names** | Not modeled | §5's `f(i) = (s, τ)` has no counterpart; `Field` is `(card, ty)`. |
| **Enums** | Deferred (need a name table) | §5 has `Enum`, `Enum-T`, `Enum-Width`, `≼ₑ`. No Lean support. |
| **Groups** | Deprecated upstream, deliberately absent | Wire types 3/4 are a parse error, not a skippable hole. |
| **Map fields** | No support *needed* | The wire format *defines* `map<K,V>` as `repeated MapEntry`; maps arrive pre-desugared. §5's `Map-Type-F` should become a derived remark, not a rule. |
| **Recursive message types** | Tree-shaped `Desc` cannot express them | Planned fix is a flat symbol table; `explode` is the interface that makes that swap non-breaking. |
| **Packedness** | An encoding-layer concern | Not a descriptor fact here. See §7.3 — this has teeth. |

The reserved-set gap is the sharpest divergence. Report §5's `Reserved-Add`/
`Reserved-Rm` rules and the `⟨r, f⟩` pairing are pure report-side invention with
no formalization behind them, and (per the earlier §5 review, B7) they are inert
even on their own terms.

---

## 3. The Value Layer (`Value.lean`)

### 3.1 the Types

```lean
mutual
inductive Value   where | mk (es : List ((_ : Int) × Val))
inductive Val     where | implicit (p : Payload)
                        | optional (p : Option Payload)
                        | repeated (ps : List Payload)
inductive Payload where | int (z : Int) | bool (b : Bool) | string (s : String)
                        | bytes (bs : List UInt8) | float (bits : UInt32)
                        | double (bits : UInt64) | msg (v : Value)
end
```

Three levels, mirroring the descriptor's three: `Value` ↔ `Desc`, `Val` ↔
`Field`, `Payload` ↔ `FieldType`.
**The presence wrapper sits outside the payload**, so it is written once rather
than duplicated across every payload constructor, and a repeated message field
is a genuine `List Payload`. (The Rocq development duplicated its `DecoVal`
across all six `ValVal` constructors.)

Measured cost: `Value.rec` carries 7 motives against `Desc.rec`'s 5, the extras
being `Option Payload` and `List Payload` — trivial helper motives, not the
`TreeMap.Raw` problem.

### 3.2 Totality — the Pivotal Decision

```lean
def Value.Total (d : Desc) (v : Value) : Prop :=
  ∀ k, (v.get? k).isSome ↔ (d.get? k).isSome
```

Exact domain equality, in both directions. A well-formed value carries an entry
for **every** declared field, with absence expressed *inside* the presence
wrapper (`optional none`, `repeated []`, or the scalar default).

The argument *(design.org §Totality is protobuf's data model)*: on the wire
every field is optional, so why should a value carry an entry the encoding never
mentions? Because those are two different levels. Implicit presence means
precisely that the default is *indistinguishable from unset* — `msg.x` always
denotes something, and no haser is generated. Protobuf's own data model assigns
every implicit field a value at all times; what is optional is only whether that
value costs bytes, which is the serializer's skip-defaults rule.

The payoff table is the single best figure to lift into the report:

| Declared | `init` gives | Serializer | Parser re-injects |
| --- | --- | --- | --- |
| `singular` at default | `implicit 0` | emits nothing | `implicit 0` |
| `optional` unset | `optional none` | emits nothing | `optional none` |
| `optional` **at default** | `optional (some 0)` | **emits it** | `optional (some 0)` |
| `repeated` empty | `repeated []` | emits nothing | `repeated []` |
| `oneof` member unset | `optional none` | emits nothing | `optional none` |

Row 3 is what justifies the design: explicit presence exists to separate "set to
0" from "unset", and totality preserves that distinction instead of collapsing
it. This is why `reinterpret_self` can conclude a genuine **equality** rather
than the looser `IdCompatible`-style relation InterParse needed.

Totality being *descriptor-relative* is what stops it conflicting with schema
evolution: `Total d₁ v` is a hypothesis on the writer's value,
`Total d₂ (reinterpret d₁ d₂ v)` is a lemma about the reader's. There is no
intermediate state in which a value is "not yet total".

#### Why *Exact* Domain Equality, and Not `dom(d) ⊆ dom(v)`

The design notes justify the exactness with one sentence — "unknown-field junk
is unrepresentable in a valid value, so the drop rule fires only across
descriptors, never on our own serializer's output"
*(design.org §Totality is descriptor-relative)*. It is doing more work than it
looks, and the report should unpack it, because the consequence is load-bearing
for §5's entire premise.

The iff has two directions doing different jobs:

- **declared ⇒ present** (`.mpr`) — *no omission*. This is what makes
  `M-Declare` disappear (§6.4) and what means nothing has to be injected at
  `d₁ = d₂`.
- **present ⇒ declared** (`.mp`) — *no junk*. A valid value carries no entry at
  a key its descriptor does not declare.

*(Nit for anyone quoting the source: the docstring at `Value.lean:299–303`
labels these "forward" and "backward", but relative to the `↔` as written the
labels are swapped — `.mp` is the no-junk half. Worth fixing before the report
quotes it.)*

The no-junk half does three things.

**1. It makes the transform's case analysis three-way rather than five-way.**
`Value.reinterpretAt` (`Transform.lean:100`) matches on `d₁.get? k, v.get? k` —
four combinations. Under `Value.Valid d₁ v` only two are reachable:
`(some, some)` is *shared* and `(none, none)` is *reader-only*. `(some, none)`
is omission; `(none, some)` is junk. The Lean records this in situ — the
docstring on `reinterpretAt_of_value_missing` (`Transform.lean:317–319`) says
the case is "unreachable when the writer's value is total over `d₁`, but the
transform is total, so the case has to be discharged". So §5.2's "three cases
per key" is exact rather than an undercount; without exact totality it would be
five.

**2. It makes the drop set a schema fact rather than a data fact.** This is the
real content. `reinterpret`'s output has domain exactly `dom(d₂)` (by
`get?_reinterpret`), so the keys it loses are `dom(v) \ dom(d₂)`. The no-junk
half rewrites that to `dom(d₁) \ dom(d₂)` — a set computable from the two
descriptors alone, with no dependence on the runtime value. That substitution is
what makes a descriptor-level relation `≼` capable of characterizing a
value-level transform at all: if junk were representable the drop set would
depend on `v` and be unbounded, and no relation on `⟨d₁, d₂⟩` could pin down
what happens to values. Report §5 assumes throughout that it can reason about
compatibility at the schema level; this is the property that licenses it.

**3. It is what makes `reinterpret_self` conclude an equality.**
`reinterpret_self` is *false* without it, and the failing branch is precisely
the drop branch. In `reinterpret_self_aux` (`Transform.lean:277–283`):

```lean
cases hget : d.get? k with
| none =>
  have : v.get? k = none := by
    have h2 := hv.total k
    rw [hget] at h2
    simpa using h2      -- present ⇒ declared, contrapositive
  simp [this]
```

The goal is `none = v.get? k`. Weaken `Total` to `dom(d) ⊆ dom(v)` and a value
with one extra entry at `k ∉ dom(d)` still satisfies it, `reinterpret d d v`
drops `k`, and the equality fails. So the equality-concluding same-descriptor
theorem — and with it the claim that Proto needs no `IdCompatible` at all (§6.4,
last row) — rests on this half of `Total`.

**At the byte level**, "never on our own serializer's output" means: the
serializer walks the *value's* entry list and consults the descriptor by lookup,
so the tag set it emits is a subset of `dom(v) = dom(d₁)`. Bytes we produce
therefore contain no tag a same-descriptor reader fails to recognize; an unknown
tag on the wire can only come from a genuine schema difference or a foreign
encoder. The report should mark this half as **prospective** — there is no Proto
serializer yet (§7.7), so it is inherited from InterParse's `serialValue` shape,
whereas the value-level statement is proved.

Finally, a phrasing correction the report should carry: "fires only across
descriptors" is loose. Drop fires only at *writer-only keys* — only when
`dom(d₁) ⊄ dom(d₂)`, which is strictly stronger than `d₁ ≠ d₂`. Two different
descriptors with equal domains (a retyping, an `optional → oneof` move) cause no
drop at all.

### 3.3 Presence Is Three-Valued Though `Cardinality` Is Four-Valued

Oneof members are `optional`-shaped. Oneof's fourth-ness is a
*cross-field constraint* (at most one member set), not a shape — so it lives in
`Value.OneofOk`, quantified over pairs of keys. This is the one protobuf rule
that is not pointwise, which is also why cross-descriptor oneof compatibility
cannot live in a pointwise field relation.

### 3.4 Scalar Carriers

Twelve of the fifteen scalar types differ only in *encoding* and *range*, both
of which the descriptor already records, so they share one `Int` carrier; ranges
go to the validity predicate. This follows the Rocq development's
`V_INT (DecoVal Z)`.

`float`/`double` carry IEEE-754 **bit patterns** (`UInt32`/`UInt64`), not
`Float`. Three reasons in decreasing force: it is literally what the wire
stores; it makes the round trip an honest bit equality; and Lean's `Float` is
opaque with essentially no equational theory and non-reflexive equality (NaN),
so an equality-concluding round-trip theorem over it would be unprovable or
false. Interpreting bits as `Float` is a derived view — the same "functions out
of the type are free" move as `explode`.

Report Table 5.1 (`tab:val-spec`) needs updating against this: it lists "Bounded
Integer" for `float`/`double`, which is not what the model does.

### 3.5 `init` — the Value Denoted by Silence

```lean
def Field.init : Field → Val
  | .mk .singular (.scalar s) => .implicit (ScalarType.defaultPayload s)
  | .mk .singular (.msg _)    => .optional none   -- unreachable when Legal
  | .mk .optional _           => .optional none
  | .mk .repeated _           => .repeated []
  | .mk (.oneof _) _          => .optional none

def Value.init (d : Desc) : Value := ⟨d.entries.map (fun e => ⟨e.1, Field.init e.2⟩)⟩

theorem Value.get?_init (d : Desc) (k : Int) :
    (Value.init d).get? k = (d.get? k).map Field.init
```

**Note the signature**: `init` takes a whole `Field` — cardinality *and* type —
not a type. Report §5's `default(\mathtt{snd}\ f_2(i))` projects the type out
and loses the cardinality, which cannot then distinguish `optional none` from
`repeated []` from the scalar zero. That is a straightforward bug in the current
`Msg` rule, independent of the vacuity problem.

`Value.init` is one of only two places that legitimately reach through the
descriptor seal (the other is the parser's missing-field injection), because it
is the one descriptor-order-dependent step. Everything downstream consumes
`get?_init` instead. This "implementation reaches, specification doesn't"
pattern recurs and is worth naming in the report.

---

## 4. Validity (`Validity.lean`)

### 4.1 `Desc.Legal` Vs `Value.Valid` — Split Along the Line Protobuf Draws

```lean
def FieldNumber.Valid (k : Int) : Prop :=
  1 ≤ k ∧ k ≤ 2^29 - 1 ∧ ¬(19000 ≤ k ∧ k ≤ 19999)

def Desc.FieldOk (k : Int) (f : Field) : Prop :=
  FieldNumber.Valid k ∧ (f.card = .singular → ∃ s, f.ty = .scalar s)

def Desc.Legal (d : Desc) : Prop :=          -- WF recursion on descSize
  (∀ k f, d.get? k = some f → Desc.FieldOk k f) ∧
  (∀ k c d', d.get? k = some (.mk c (.msg d')) → Desc.Legal d')
```

`Desc.Legal` collects what **protoc enforces on a schema**; `Value.Valid` is
what the design notes call "the serializer's phantom well-formedness"
(`Validity.lean:13`, `:128`; design.org §Where the rules live). InterParse
folded its `0 ≤ k < 256` bound into `valWfFold` only because it had no
descriptor-side predicate beyond sortedness; with one available, re-checking a
schema fact at every value is redundant.

#### "Phantom Well-Formedness" — Definition, and a Caveat

The term is not loose language; it is a term of art from the parser framework
and the report should either define it on first use or drop it.
`Parse/Serializer.lean:19`:

```lean
abbrev Serializer (ι α : Type) (_wf : α → Prop) := α → Result ι Unit
```

The `wf` parameter is unused in the body — a phantom type parameter in the
standard sense. Three consequences *(Serializer.lean:7–10, CLAUDE.md:125)*:

1. **Computationally inert.** A serializer is a total function; it never
   inspects `wf`. On a non-well-formed input it still emits *something*. The
   predicate does not gate execution, it gates what the theorems claim.
2. **It is the domain of the correctness statement** — which values the
   serializer is *allowed* to encode, i.e. the precondition of the `ParseOk`
   family.
3. **It composes with the combinators** —
   `concatWf wfα wfβ = fun (a,b) => wfα a ∧ wfβ b`, `bindWf`, `repWf` — so a
   combinator-built serializer has an *intrinsic* wf fixed by its construction.

InterParse makes it literal:
`serialValue (d : Desc) : Serializer (List UInt8) Value (valueWf d)`
(`InterParse/Serializer.lean:105`).

**"Phantom" means computationally erased, not proof-theoretically cheap**, and
that is the misreading to guard against. `CLAUDE.md:192` is the counterevidence:
relaxing one arm of `valueWf` "also touches `schemaCorrectInterParseOk` and the
`Serialization.lean` inversion lemmas". Only the *code* ignores it.

**Caveat: in Proto the role is prospective.** There is no Proto serializer
(§7.7). `Value.Valid` is consumed today only as a hypothesis of
`reinterpret_self` and `reinterpret_valid`. The phrase describes an intended
role inherited from InterParse, where it was true by construction — the same
status as the byte-level half of the §3.2 claim, and it should be marked as such
in the report.

#### **(Finding)** the Phrase Mislocates the Predicate

InterParse's `valueWf` (`InterParse/Descriptor.lean:728`) is a
*fold over the value's entry list*: one conjunct per entry present, vacuous
(`none, _ => acc`) on keys outside the descriptor, with sortedness deliberately
kept **outside** it and carried by callers. That is exactly the shape a
combinator-composed wf has, which is why it could be the wf slot.

`Value.Valid` is a four-way conjunction and only one conjunct has that
character:

| Conjunct | Whose precondition, really |
| --- | --- |
| `Value.ValidEntries d es` | **the serializer's** — the direct successor of `valWfFold` |
| `SortedMap.WF es` | the *round trip's* — needed for `Value.ext_lookup`, i.e. to conclude an equality rather than lookup-agreement |
| `Value.Total d` | the *round trip's* — the parser re-injects declared-but-unmentioned fields, so `v` must already carry them. A per-entry fold cannot even state the "declared ⇒ present" direction: it visits only entries that are there |
| `Value.OneofOk d` | the *transform's* — quantified over pairs of keys (§4.2), used to trace an output group conflict back to a writer group conflict |

So `Value.Valid` is the **round trip's** precondition, of which the serializer's
phantom wf is one quarter. The wording was accurate for `valueWf` and no longer
is. Suggested restatement for the report: *"`Value.Valid` is the round trip's
precondition; its entrywise conjunct is what the serializer carries as its
phantom well-formedness."*

The practical cost is mild and worth saying so: because `_wf` is phantom,
nothing forces the annotation to be the composed predicate, so Proto's
`serialValue` can still be declared at `Value.Valid d`. What is owed is proof
plumbing at each combinator-lemma application —
`Value.Valid d v → ⟨composed wf⟩ v` — which is the weakening direction and so
goes through. `Parse/Theorems.lean:398–401` already anticipates the friction:
`repCorrectWeakFull` takes `wfα` explicitly "so it can differ from the
serializer's intrinsic phantom wf", and takes the serializer as a raw function
"to avoid the phantom wfα mismatch".

`FieldOk`'s second conjunct is load-bearing:
**implicit presence applies only to scalars.** In proto3 a singular *message*
field has explicit presence (`has_foo()` is generated). It pays for itself twice
— `Payload.isDefault` (the serializer's skip test) never has to recurse into a
nested `Value`, so it is a direct match on scalar constructors and needs **no**
`DecidableEq` (which `Desc`/`Field`/`FieldType` do not derive); and
`Field.init`'s `singular`/`msg` arm becomes unreachable.

This is also the answer to the recursion worry about totality: `default` on a
recursive message type would not terminate, but singular message fields are
`optional`-shaped, so `Field.init` returns `optional none` and the recursion
stops. The report should state this as an explicit modeling commitment.

Note the report's §5 "Valid Descriptors" definition (validity-as-reachability,
`⟨∅,∅⟩ ≼ ⟨r,f⟩`) has no Lean counterpart and is weaker than what is actually
used: `Desc.Legal` is a direct predicate, and every theorem takes it as a
hypothesis. Reachability is at best a theorem *about* `Legal`, not its
definition.

### 4.2 `Value.OneofOk` — the Only Non-Pointwise Rule

```lean
def Value.OneofOk (d : Desc) (v : Value) : Prop :=
  ∀ k₁ k₂ f₁ f₂ g p₁ p₂,
    k₁ ≠ k₂ →
    d.get? k₁ = some f₁ → d.get? k₂ = some f₂ →
    f₁.card = .oneof g → f₂.card = .oneof g →
    v.get? k₁ = some (.optional (some p₁)) →
    v.get? k₂ = some (.optional (some p₂)) → False
```

Quantified over *pairs* of keys, one layer at a time. Group tags are compared
only within a single descriptor.

### 4.3 Type and Range Matching

```lean
def Value.Valid (d : Desc) : Value → Prop
  | .mk es => SortedMap.WF es ∧ Value.Total d ⟨es⟩ ∧ Value.OneofOk d ⟨es⟩ ∧
              Value.ValidEntries d es
```

with `Val.Matches` pairing the value's presence shape against the declared
cardinality (oneof members share the `optional` arms; `implicit`/`msg` is absent
because `FieldOk` rules it out), `Payload.Matches` recursing at nested messages,
and `Payload.MatchesScalar` doing type *and range* in one match — one arm per
scalar type. `float`/`double` need no range condition at all, since their bit
carriers are width-exact: a second dividend of the bits representation.

The recursion is **structural on the value**, with the descriptor consulted by
`get?` — a function call, not a recursive argument — so no termination measure
is needed even though the descriptor changes at nested messages. This is
InterParse's `valueWf` pattern restated through the seal.

### 4.4 the Introduction Rule, and Why Its Shape Is Evidence

```lean
theorem Value.valid_of_get? (hwf : v.WF) (htot : Value.Total d v)
    (hone : Value.OneofOk d v)
    (hm : ∀ k x f, v.get? k = some x → d.get? k = some f → Val.Matches x f) :
    Value.Valid d v
```

The natural entrywise form quantifies over `v.entries`, and since both
`Value.init` and `Value.reinterpret` are *defined* by mapping over the
descriptor's entry list, discharging it drags the proof through
`Desc.get?_eq_dlookup` — representation contact in a file whose business is
statements. Stating the payload condition through `get?` on both sides removes
it. *(design.org notes: "the seal paid for itself here: the awkwardness was the
signal that the proof was reaching somewhere it should not.")* Good anecdote for
a methodology section.

`Value.init_valid (hwf : d.WF) (hleg : d.Legal) : Value.Valid d (Value.init d)`
is the base case of the round-trip story. Its oneof conjunct is free, via
`Field.init_ne_optional_some`: `init` never produces an explicitly-set optional
payload, so no two members of a group can both be set.

---

## 5. The Transform (`Transform.lean`)

### 5.0 Provenance: Where the Transform Came From

Not recorded anywhere in the repo; traced through git history for this document.
Worth a paragraph in the report, because the transform is the layer's central
design choice and it arrived as the answer to a **proof obstruction**, not as an
aesthetic preference.

| Commit | Date | What appeared |
| --- | --- | --- |
| `463d4da` | 2026-05-20 | `IdCompatible` relation **and** `idCompatTransform d v`, in the same commit; `idCompatRoundTrip` stated `sorry` |
| `58955e3` → `8cc70c9` | 2026-05-22 → 05-27 | Transform rewritten as an explicit structural recursion; round-trip proof closed |
| `4a721a2` | 2026-08-21 | `compatTransform d₁ d₂ v` — the cross-descriptor generalization |
| `78d41a0` | 2026-09-04 | `Value.reinterpret d₁ d₂ v` in the Proto layer |

**Theorem 1 (`schemaCorrectInterParseOk`) needed no transform.** The relation
`SchemaCorrectCompatible`, plus the squeeze lemma `schemaCorrectCompatibleEqual`
(`d₁ = d₂ → v₁ = v₂`), delivers a genuine round-trip equality directly. The
relation was tight enough to be functional in its output, so naming that output
was unnecessary.

**Theorem 2 (`idInterParseOk`) is where it broke.** Dropping schema-correctness
in favour of `AllWF` loosened the relation: `IdCompatible` admits `drop` (a key
outside the descriptor, with *no constraint at all on the dropped value*) and
`addMissing`. The relation is then no longer functional in `v₂`, the squeeze
lemma dies, and `∃ v₂, parse … = v₂ ∧ v₁ ≼ v₂` cannot be proved by induction —
the induction hypothesis never says *which* `v₂` to hand to the next step. The
fix is the textbook strengthen-the-induction-hypothesis move:
**name the witness.** Prove the strong statement "parsing yields *exactly*
`T(v)`", then compose with "`T(v)` always lands in the relation".

The first version of `T` was deliberately unglamorous — not a new construction
at all, but the parser's own missing-field injection lifted to the value level:

```lean
def idCompatTransform (d : Desc) (v : Value) : Value := listToValue d (valList d v)
```

It landed in the same commit as the relation, with the round-trip leg stated
`sorry`, so the two-leg strategy was committed to before either leg was proved.
The explicit structural recursion came later, during the proof work.

**Theorem 3 (`compatInterParseOk`) fixed the shape.** The cross-descriptor
generalization is "proven by the same two-step strategy", and here
`compatTransform` acquires the form `Value.reinterpret` inherits verbatim: *a
structural recursion over the reader's field list, reading the writer's
descriptor and value by key lookup.* Proto adds a second, better justification
for the same walk — the reader must produce a value
**total over its own descriptor**, so its domain is what the walk has to
enumerate.

Two plausible alternative origins, both checked and both **wrong**:

- *Not from the Rocq development.* The only `transform` in `rocq/` is an
  unrelated `FilterByte (filter) (transform)` parser-combinator argument in
  `ProtoParse.v`. Rocq contributed `init_deco` (ancestor of `Field.init`) and
  the collapsed `V_INT (DecoVal Z)` carrier, not this.
- *Not from Narcissus/EverParse.* Those are cited in `proto-design.org`, but for
  the *other* half — the planned relational `Encodes` spec and its
  soundness/completeness split. The transform predates that citation by three
  months.

**Why this bears on report §5.** The composition "parsing produces exactly `T`"

- "`T` lands in `≺`" only says something if `≺` is tight enough that `T` is
essentially its unique witness. A relation admitting `v₂ = ∅` against every `v₁`
still composes — and the conclusion is worthless. So the vacuity of the current
`Msg` rule (A3 in the §5 review) is not a cosmetic defect: it is precisely the
failure mode this strategy is vulnerable to, and InterParse's own history is the
evidence, since the strategy is what you get
*when the relation stops pinning the output down*. The strengthening that made
Theorem 2 provable is the same strengthening §5's `Msg` rule needs.

### 5.1 Four Mutually Recursive Functions

```lean
Value.reinterpret        (d₁ d₂ : Desc) (v : Value) : Value
Value.reinterpretEntries (d₁ : Desc) (v : Value) : List ((_:Int) × Field) → List ((_:Int) × Val)
Value.reinterpretAt      (d₁ : Desc) (v : Value) (k : Int) (f₂ : Field) : Val
Val.reinterpret          (f₁ f₂ : Field) (x : Val) : Option Val
Payload.reinterpret      (t₁ t₂ : FieldType) (p : Payload) : Option Payload
```

The `Option` in the bottom two is **not** a value-level bottom: it means "not
carryable", and the caller falls back to `Field.init`, which is exactly what a
reader sees when the writer's bytes do not populate the field.

### 5.2 Three Cases per Key

```lean
def Value.reinterpretAt (d₁ v k f₂) : Val :=
  match d₁.get? k, v.get? k with
  | some f₁, some x => (Val.reinterpret f₁ f₂ x).getD f₂.init
  | _, _            => f₂.init
```

- **shared** — both descriptors declare it: carry the payload across, recursing
  at nested messages;
- **reader-only** — `d₂` declares it, `d₁` does not: inject `Field.init`;
- **writer-only** — `d₁` declares it, `d₂` does not: **dropped**, and not as a
  case at all — the walk enumerates the *reader's* domain, so writer-only keys
  simply never come up.

Three cases, not five: the `match` has four combinations and the two remaining
corners — declared-but-absent, and present-but-undeclared ("junk") — are
unreachable under `Value.Valid d₁ v`. That exhaustiveness is exactly what the
no-junk half of `Value.Total` buys, and §3.2 is where the argument lives.

The recursion is driven by the reader's field list because the reader must
produce a value total over its own descriptor. Termination is therefore on
`descSize d₂`; nothing recurses on the value.

**The drop rule is the headline structural improvement over InterParse.**
InterParse's `≪` deliberately had no drop rule: `parseVal`'s `none` branch
consumed the tag byte but not the payload, so a reader missing a key
desynchronized the stream. Real protobuf tags carry a wire type, so unknown
fields are skippable and dropping is sound. (Protobuf ≥ 3.5 *preserves* unknown
fields; not adopted, because it requires an unparsed-bytes region in `Value`,
which would put raw bytes into the induction skeleton of every proof.)

Note what "drop" is scoped to. It fires at writer-only keys — when
`dom(d₁) ⊄ dom(d₂)` — which is strictly stronger than `d₁ ≠ d₂`: descriptors
that differ only in a field's type or in `optional`/`oneof` membership have
equal domains and drop nothing. The design notes' "only across descriptors"
should be restated this way in the report.

Two mechanical notes worth a footnote in the report: the measure chain
`descSize → entryListSize → fieldSize → fieldTypeSize → descSize` only *weakly*
decreases within one layer, so the measures are scaled by 4 with per-step
offsets — a lexicographic `(size, rank)` pair fails. And the entry walk is a
separate function rather than a `List.map` over `attach`, which keeps the size
component honest instead of forcing the obligation to be discharged from a
membership proof.

### 5.3 the Specification

```lean
theorem Value.get?_reinterpret (d₁ d₂ : Desc) (v : Value) (k : Int) :
    (Value.reinterpret d₁ d₂ v).get? k =
      (d₂.get? k).map (fun f₂ => Value.reinterpretAt d₁ v k f₂)
```

This is the interface-level specification, and it is *exactly* the
characterization report §5's `Msg` rule is missing (A3 in the earlier review):
the output's domain is the reader's descriptor's domain, and the value at each
key is determined. Anything in the report that says "`dom(v₂)`" should be
deriving it from here.

### 5.4 What Actually Carries Across Today

This table is not in `proto-design.org` and is the practical answer to "what
does the transform support". Read off `Val.reinterpret`'s match:

| Writer card → reader card | Carried? |
| --- | --- |
| `singular → singular` | yes, via `Payload.reinterpret` |
| `optional/oneof → optional/oneof` (any combination) | yes |
| `repeated → repeated` | yes, elementwise `filterMap` |
| `singular ↔ optional`, `singular ↔ repeated`, `optional ↔ repeated`, `oneof ↔ repeated`, `oneof ↔ singular` | **no** → `Field.init` |

| Writer type → reader type | Carried? |
| --- | --- |
| `msg d₁' → msg d₂'` | yes, recursing |
| `scalar s → scalar s` (equal) | yes |
| `scalar s₁ → scalar s₂` (s₁ ≠ s₂) | **no** → `Field.init` |
| `scalar ↔ msg` | **no** → `Field.init` |

So the transform today supports exactly: **width changes** (add/remove fields),
**depth changes at nested messages**, and
**moving fields between `optional` and `oneof`**. Scalar retyping is booked as
deferred in the file header. The cardinality gaps are *not* booked anywhere —
see §7.2.

Note the one cardinality change that *is* supported is the interesting one:
`optional ↔ oneof` is precisely field-joins-a-oneof, and it is unguarded at this
level — the group discipline is enforced separately by `OneofPreserved`.

### 5.5 the Four Theorems

```lean
theorem Value.reinterpret_wf    (v) (h : d₂.WF)  : (Value.reinterpret d₁ d₂ v).WF
theorem Value.reinterpret_total (d₁ d₂ v)        : Value.Total d₂ (Value.reinterpret d₁ d₂ v)
theorem Value.reinterpret_self  (hd : d.AllWF) (h : Value.Valid d v) :
    Value.reinterpret d d v = v
theorem Value.reinterpret_valid (h₁ : Value.Valid d₁ v) (hwf : d₂.AllWF)
    (hleg : d₂.Legal) (hone : Desc.OneofPreservedAll d₁ d₂) :
    Value.Valid d₂ (Value.reinterpret d₁ d₂ v)
```

`reinterpret_self` is the identity round trip — the payoff of totality plus
`init`, and the reason the same-descriptor theorem concludes a genuine equality.

In `reinterpret_valid`, note that `d₂`'s invariants are
**explicit hypotheses rather than recovered from `d₁`**, for the same reason
`AllWF` was in InterParse: descriptor-side invariants do not lift along a
compatibility relation, which may add unconstrained fields. This is the
`not_descCompat_allWF` lesson, and it means the report's §5 theorem correctly
needs its `d₂` well-formedness hypothesis — but it needs *three* of them
(`AllWF`, `Legal`, `OneofPreservedAll`), not one.

Both round-trip proofs are strong induction on `descSize` with payload-, list-
and field-level steps split out as local `have`s.

### 5.6 the Oneof Side Condition, and the Counterexample

This is the most report-worthy result in the layer.

`proto-design.org` predicted (before the value layer existed) that oneof
compatibility would be "the one place to expect trouble", because moving fields
in or out of a oneof is wire-compatible but changes the reader's transform. The
prediction was confirmed **twice**.

First, `reinterpret_valid` is simply false without a side condition: a writer
that legitimately sets two ungrouped fields hands a reader that groups them a
value violating `OneofOk`. Hence:

```lean
def Desc.OneofPreserved (d₁ d₂ : Desc) : Prop :=
  ∀ k₁ k₂ f₁ f₂ f₁' f₂' g,
    d₁.get? k₁ = some f₁ → d₁.get? k₂ = some f₂ →
    d₂.get? k₁ = some f₁' → d₂.get? k₂ = some f₂' →
    f₁'.card = .oneof g → f₂'.card = .oneof g →
    ∃ g₀, f₁.card = .oneof g₀ ∧ f₂.card = .oneof g₀
```

"Two of the reader's keys sharing a group tag were already in one group for the
writer" — stated in the direction that preserves validity. Note it is vacuous
when either key is reader-only, so
**adding a new field to an existing oneof is permitted**, while **moving an
existing field into a group another existing field inhabits is forbidden**. That
is exactly the official guidance, and exactly the instinct recorded in the
report's source comment ("introduce a new field, but not move an existing one")
— now with a formal justification rather than a hunch.

Second, and sharper: **the one-layer condition is itself not enough.** The
transform recurses into nested message fields, where the descriptors under
consideration are a pair of *nested* ones, about which a one-layer hypothesis
says nothing. `OneofCounterexample.lean` builds the witness — two `bool` fields,
independent for the writer and grouped for the reader, one layer down inside a
message field — discharges every hypothesis of the originally stated theorem for
it, and proves the negation of that statement's universal closure:

```lean
theorem not_reinterpret_valid_one_layer :
    ¬ ∀ (d₁ d₂ : Desc) (v : Value), Value.Valid d₁ v → d₂.AllWF → d₂.Legal →
        Desc.OneofPreserved d₁ d₂ → Value.Valid d₂ (Value.reinterpret d₁ d₂ v)
```

The hypothesis actually in force is `Desc.OneofPreservedAll`, the recursive
closure, defined by well-founded recursion on `descSize d₂` and recursing at
shared keys where *both* sides declare `.msg` — precisely the transform's
recursion sites. Where the two disagree on a key's shape the reader receives
`Field.init`, which is never `optional (some _)`, so no oneof obligation arises
there.

Two observations the design notes flag for the report, both of which I'd
endorse:

1. It is the same lesson as `WF` versus `AllWF`, arriving for a different
   reason: **a one-layer predicate on a one-layer-observable type is never
   automatically the predicate a recursive traversal needs, and the gap is
   invisible until something recurses.**
2. Its *shape* differs from its neighbours: `AllWF` and `Legal` recurse on a
   single descriptor, this recurses on a **pair**. That is the shape of a
   compatibility relation — `OneofPreservedAll` is a first fragment of the Proto
   analogue of `≼`, and when that relation is built it should *absorb* this
   rather than sit beside it.

---

## 6. What This Means for Report §5

### 6.1 Judgement-by-Judgement

| Report §5 | Lean status | Verdict |
| --- | --- | --- |
| `≺` value relation (definition via `E_τ`) | No relation; `Val.reinterpret`/`Payload.reinterpret` are the functional core | Restate as characterizing the transform |
| `Refl` | `reinterpret_self` (needs `AllWF` + `Valid`) | Survives as a theorem, not a rule |
| `Varint` schema + both tables | **No counterpart** — `Payload.reinterpret` requires `s₁ = s₂` | Report is *ahead* of Lean; keep it, mark as the spec for future work |
| `Str-Byte`/`Byte-Str` | Same — not implemented | Ditto |
| `Msg` value rule | `get?_reinterpret` + `reinterpretAt` | Replace wholesale |
| `Enum` | No enums in Lean | Keep as designed-not-formalized, flag clearly |
| `Opt-Intro`/`Rep-Intro`/`Missing-Imp` and the decorator rules | Cardinality changes not carried (§5.4 table) | Report is ahead; note the gap |
| `∝` type relation | Implicitly "`Payload.reinterpret` succeeds"; today ≈ type equality plus nested-msg recursion | Reframe as the spec that will force `∝` to be more than equality |
| `≼` message relation | **Does not exist.** Nearest thing: the hypothesis bundle `d₂.AllWF ∧ d₂.Legal ∧ OneofPreservedAll d₁ d₂` | This is the biggest rewrite |
| `Refl-M`/`Trans-M` | Nothing | Trans is the one to be suspicious of (see the §5 review, A2) |
| `Field-Add`/`Field-Type` | `reinterpretAt`'s reader-only and shared cases | Survive in spirit |
| `Oneof-*` (five rules, set-keyed) | Flat `Cardinality.oneof g` + `OneofPreservedAll` | Rewrite; the set-key bugs vanish |
| `Reserved-Add`/`Reserved-Rm` | **Nothing in Lean** | Either drop, or state as report-only future work |
| `Map-Type-F` | Maps are pre-desugared | Demote to a remark |
| Valid descriptors (reachability) | `Desc.Legal`, a direct predicate | Replace definition; reachability becomes a theorem at best |
| Compatibility theorem | `reinterpret_self` + `reinterpret_valid`; the parsing leg awaits the parser | Restate as a two-leg plan |

### 6.2 the Theorem, Restated

The current statement —

> If `d₁ ≼ d₂` and `d₂` is well-formed, then for all `bs` with
> `parse_{d₁} bs = Some v₁`, `parse_{d₂} bs = Some v₂` and `v₁ ≺ v₂`

— should become the two-leg structure the Lean layer has committed to:

1. **Transform totality/validity** (proved): `Value.reinterpret d₁ d₂ v` is
   total over `d₂` and satisfies `Value.Valid d₂`, given `Value.Valid d₁ v`,
   `d₂.AllWF`, `d₂.Legal`, `Desc.OneofPreservedAll d₁ d₂`.
2. **Parser completeness** (awaiting the parser):
   `Encodes d₁ v bs → parseValue d₂ bs ≡ success (Value.reinterpret d₁ d₂ v) rest`.

   *Caveat:* `proto-design.org` states this leg only in its same-descriptor
   form, `Encodes d v bytes → parseValue d bytes ≡ success (transform v) rest`.
   The cross-descriptor generalization above is my extrapolation — it is the
   obvious one and is what `reinterpret d₁ d₂` exists for, but it is not written
   down anywhere yet, and §7.3 below is a reason it cannot hold unrestrictedly.

with the same-descriptor case (`reinterpret_self`) as a corollary of (2) at
`d₁ = d₂`. The `Encodes` relation is the planned relational spec —
Narcissus/EverParse style — closed under the wire format's nondeterminism (field
order, duplicate merge, over-long varints, packed vs unpacked). The existing
functional round-trip theorems become the *soundness* leg
(`Encodes d v (serialValue d v)`).

### 6.3 Suggested Section Skeleton

Roughly what the Lean layer's own structure suggests:

1. **The representation problem** — kernel acceptance, the experiment table, the
   negative results. This is genuine research content the report currently has
   none of.
2. **The seal** — `explode`, the WF-hypothesis table, descriptors-observed vs
   values-traversed, recursion via `descSize_lt_of_get?_msg`.
3. **The descriptor** — types, `Cardinality`, the flat-vs-folded oneof argument,
   what's deliberately absent.
4. **The value layer** — totality, the five-row round-trip table, presence
   three-valued vs cardinality four-valued, scalar carriers, `init`.
5. **Legality and validity** — `Desc.Legal` vs `Value.Valid`, the split, ranges,
   `OneofOk`.
6. **The transform** — three cases per key, reader-driven, the drop rule's
   return, `get?_reinterpret`. Open it with the provenance argument (§5.0): the
   transform exists because a relation that stops being functional cannot carry
   its own induction. That framing makes the two-leg architecture look forced
   rather than chosen, which is the stronger claim.
7. **The oneof side condition** — the prediction, the two confirmations, the
   counterexample. Present this as a *result*, with the "one-layer predicates
   don't survive recursion" moral.
8. **The compatibility relations** — what §5 currently is, now positioned as the
   *design target* the transform must be widened to meet, with the coverage
   table from §5.4 as the honest status report.
9. **Comparison with InterParse** — see below; this is a strong narrative spine.

### 6.4 the InterParse → Proto Delta

*(design.org §Consequences for the compatibility relations, all
simplifications)*

| InterParse | Proto | Why |
| --- | --- | --- |
| `M-Declare` | **gone** | Existed only because `valueWf` permitted omitting a declared key; totality makes that unrepresentable |
| `M-Add` (removed as "no round trip produces it") | **returns, pinned** as reader-only ↦ `Field.init` | Here a round trip *does* produce it, but determinately |
| `≪` has no drop rule | **drop rule returns** | Protobuf tags carry wire types, so unknown fields are skippable |
| eight `≼` rules | **three cases per key** | Reader-driven walk |
| `IdCompatible` needed (junk at unknown keys + omission both possible) | possibly unnecessary — `reinterpret_self` concludes equality | Exact totality kills both |

#### What `M-Declare` Was

From `sections/09-inter-parse.tex:333`:

```text
  m₁ : d₁ ≼ m₂ : d₂    k ∉ dom(d₁)    k ∉ dom(m₁)    f₁ ∝ f₂
  ──────────────────────────────────────────────────────────────
     m₁ : d₁[k ↦ f₁]  ≼  m₂[k ↦ M_MISSING] : d₂[k ↦ f₂]
```

The writer's *descriptor* declares `k`; the writer's *value* has no entry at it;
the reader receives `M_MISSING`. In Lean it is `MsgCompat.declare`
(`Compatible.lean:169`), and its docstring (`Compatible.lean:145–168`) is the
most complete statement of the argument anywhere in the repo — worth quoting in
the report rather than paraphrasing. The load-bearing sentence:

> Not optional: without it `≼` cannot follow `IdCompatible.addMissing`, and the
> cross-descriptor round-trip theorem is *false* already at `d₁ = d₂`.
> `serialValue` emits nothing for a declared-but-absent key and `parseValue`
> reads it back as `.missing`; `valueWf` permits exactly that (it constrains
> only the keys the value actually carries), so the configuration is reachable
> from the top-level theorem's hypotheses and no other rule produces it.

That is the whole provenance: the rule exists because `valueWf` "constrains only
the keys the value actually carries." Under `Value.Total` the premise pair
`k ∈ dom(d₁)`, `k ∉ dom(m₁)` is unsatisfiable for any `Valid d₁ v`, so the rule
is vacuous and goes.

#### Why Deleting It Is a Gain and Not Just a Saving

Four reasons, in increasing order of force.

**1. It is the relation paying for the invariant's weakness.** The state it
covers is not exotic — it is reachable from the theorem's own hypotheses — but
it has no protobuf meaning. Protobuf's data model assigns every implicit field a
value at all times (§3.2), so a value omitting a declared key is not a value
that any protobuf implementation can hand you; it is an artifact of a `valueWf`
too weak to say so. Every rule of this kind is a permanent tax: it must be
stated, threaded through `M-Trans`, and discharged as a case in every induction
over `≼`, forever, in exchange for describing inputs nobody can produce.
Strengthening the invariant deletes the state and the rule together.

**2. It doubles a case that has one semantics.** `M-Declare` and `M-Missing`
agree on the reader's side — `M_MISSING` at `k` — and differ only in whether
`d₁` gains `k`. Nothing observable separates them; the reader's value is
identical either way. Under totality they merge, and together with the
already-deleted `M-Add` they collapse into a *single* Proto case: reader-only ↦
`Field.init`. Three InterParse rules become one, which is a concrete piece of
the "eight `≼` rules → three cases per key" row above. `Field.init` is also the
cardinality-aware successor of `M_MISSING`: one marker for all shapes was
adequate only because InterParse had no repeated fields.

**3. It needed a premise that had to be *discovered*, and is silently wrong
without it.** `f₁ ∝ f₂` is not decoration. `Compatible.lean:157–168` records the
forcing example: `d₁ = {0 ↦ bool}`, `d₂ = {0 ↦ int}` (a legal `D-Chg` at
`F-Bool-Int`), `m₁ = ∅`. The writer emits nothing, the reader injects `.missing`
typed by *its own* descriptor, and so the round trip demands

```text
⟨ ∅ ∷ {0 ↦ bool} ⟩ ⪯ ⟨ {0 ↦ missing} ∷ {0 ↦ int} ⟩
```

which is underivable with `f₁ = f₂` — `M-Update` needs `m₁.get? 0` populated,
and `M-Trans` stalls on a `.missing` left-hand side that `≺` cannot retype. So
the rule is *both* an artifact of a weak invariant *and* a rule with a
non-obvious side condition standing between it and unsoundness: two chances to
get it wrong, for a case that should not exist. The report is currently taking
the second chance — `Missing-Imp` relates any `τ₁` to any `τ₂` (§5 review B9),
which is exactly the defect `∝` was added to fix.

**4. It is one of the two rules that cost InterParse its equality.**
`IdCompatible` exists because `valueWf` permitted *both* junk at undeclared keys
(`IdCompatible.drop`, surfacing as `M-Drop-Unknown`) and omission of declared
ones (`IdCompatible.addMissing`, surfacing as `M-Declare`). Those are precisely
the two halves of exact totality (§3.2). Killing both is what lets
`reinterpret_self` conclude `reinterpret d d v = v` instead of a relation, and
it is the difference between InterParse's three top-level theorems and Proto's
projected two.

#### The Report-Side Consequence

The §5 review's A3 asks for a "`i ∈ dom(f₂)`, absent from the writer's value →
missing/default" case, calling it *"the `M-Declare` lesson: without this case
the theorem is false already at `d₁ = d₂`."* That is correct for a §5 that has
no totality invariant — but there are **two** fixes, not one: add the case, or
adopt `Value.Total` and delete it. The Lean took the second. A §5 rewritten
against the Lean model should therefore state totality and note the case as
unreachable, **not** add it. Doing both would reintroduce the exact rule the
value model was designed to remove, and would drag the `∝` premise back in with
it.

#### The Moral

The mirror image with `M-Add` is the point worth making explicitly. `M-Add` was
*deleted* from InterParse because no round trip produces it — keeping it "would
let a derivation conjure values out of thin air, so `≼` could not be read as a
specification of what parsing produces" (`Compatible.lean:58–65`). `M-Declare`
*survived* there because a round trip does produce it. Totality changes what a
round trip can produce, so in Proto `M-Declare` goes and `M-Add` returns pinned
to `Field.init`. In both layers, and in both directions, the rule set is a
readout of the transform rather than an independent design — which is the same
framing §5.0 recommends for opening the transform section.

---

## 7. Gaps, Findings, Open Questions

Ordered by how much they should affect the rewrite.

### 7.1 the Report Models Three Things Lean Does Not

**Reserved field sets, field names, and enums.** All three appear throughout §5;
none exist in `Desc`. For reserved sets in particular the earlier §5 review
found the machinery inert even on the report's own terms (no rule consults `r`;
no rule puts a number *into* `r`; validity doesn't force `dom(f) ∩ r = ∅`).
Decide explicitly whether these are (a) future formalization work, stated as
such, or (b) dropped. Threading `⟨r, f⟩` through every judgement for a component
nothing reads is the worst of both.

### 7.2 **(Finding)** `Val.reinterpret` Covers No Cardinality Changes Except `optional ↔ oneof`

Five classes fall through to `Field.init`: `singular ↔ optional`,
`singular ↔ repeated`, `optional ↔ repeated`, `oneof ↔ repeated`,
`oneof ↔ singular`. The file header books only *scalar retyping* as deferred, so
this looks like an unnoticed omission rather than a decision. It matters because
`Opt-Add-T`, `Opt-Rm-T` and `Rep-Add-T` in report §5 all promise conversions the
transform discards.

Concretely, `singular → optional` should read: if the writer's payload
`isDefault` then `optional none` (the writer emitted nothing), else
`optional (some q)`. That guard is precisely the `v ≠ default(τ)` premise the §5
review's A4 asked for, showing up in the code — which is decent evidence for
both.

### 7.3 **(Finding)** `repeated → non-repeated` Cannot Be a Function of the Value

`Value.reinterpret` takes `(d₁, d₂, v)` — no bytes. But a repeated field of a
*packed-eligible* scalar type (the varint and fixed-width numerics; not
`string`/`bytes`/`msg`) has two legal encodings, and a non-repeated reader gets
different results from them:

- **packed** arrives as one LEN record → wire-type mismatch against the reader's
  expected VARINT/I32/I64 → routed to unknown fields → the field keeps
  `Field.init`;
- **unpacked** arrives as several records at the same tag → last-wins.

Same writer value, two `bs` both satisfying `Encodes d₁ v bs`, two different
reader values. So parser completeness —
`Encodes d₁ v bs → parse d₂ bs = reinterpret d₁ d₂ v` — is *unsatisfiable* the
moment compatibility admits repeated → singular/optional on a packable scalar.

Current Lean behaviour (fall through to `Field.init`) happens to match the
**packed** case, so it is correct-for-proto3-defaults and wrong for unpacked
input. Two ways out:

- **cheap**: never admit `repeated → non-repeated` in the compatibility
  relation, and say so in the report with the packed argument as the
  justification. This also answers the red note at
  `sections/05-proto-relations.tex:250` directly: you cannot eliminate a packed
  repeated field to a singular one and get last-wins.
- **expensive**: make the theorem's conclusion relational rather than
  functional, which gives up the whole `compatTransform` strategy.

Note the asymmetry: `singular → repeated` *is* deterministic (a singular field's
encoding is unambiguous), as is `repeated string → optional string` (strings are
never packed). Only packable scalars going *out* of `repeated` are affected.

### 7.4 **(Finding)** `Desc.OneofPreserved` Is Stronger Than the Proof Needs

It omits `k₁ ≠ k₂`. Instantiating at `k₁ = k₂ = k` forces: if the reader
declares `k` as a oneof member, the *writer* must already have declared `k` as a
oneof member. So moving a lone `optional` field into a fresh singleton oneof
group is forbidden — even though it is wire-compatible and violates no `OneofOk`
(a group with one member can never have two members set).

The proof does not use this strength: `reinterpret_valid`'s `honeok` step has
`hne : k₁ ≠ k₂` in scope from `Value.OneofOk` and simply doesn't pass it. Adding
`k₁ ≠ k₂` as a hypothesis to `Desc.OneofPreserved` weakens the assumption
(strengthening the theorem) at, as far as I can see, zero proof cost, and the
counterexample still goes through since it only weakens what
`outer_oneofPreserved` has to prove. Worth checking in Lean before relying on
it, but if it holds it's a free improvement and removes an otherwise-puzzling
restriction from the report's oneof story.

### 7.5 **(Finding)** Nothing Requires a Serializer to Respect Its Type-Level `wf`

The `wf` index is unenforced at two independent levels. The consequence for the
report is that the round-trip theorems are **partial** correctness statements,
and should be named as such rather than left to imply more than they prove.

**The type imposes nothing.** `Serializer ι α wf` is an `abbrev` whose body
drops `wf` (§4.1), so `Serializer ι α P` and `Serializer ι α Q` are
*the same type* for every `P`, `Q`. The annotation on `serialValue`
(`InterParse/Serializer.lean:105`) therefore carries zero proof obligation —
`fun _ => False` in that slot typechecks identically. Nor can `wf` be inferred
*from* a serializer; it travels purely by ascription, which is why `ParseOk'''`
takes it as an implicit `{wf : α → Prop}` recovered at the use site.

**The consuming theorems use it only as an antecedent**
(`Parse/Theorems.lean:23`):

```lean
def ParseOk''' {wf : α → Prop} (par : Parser ι α) (ser : Serializer ι α wf)
    (x : α) (enc rest : ι) : Prop :=
  wf x → ser x = .success () enc → par (Input.app enc rest) = .success x rest
```

Both `wf x` **and serializer success** are hypotheses, so neither reading of
"respects" is demanded:

- **progress** ("succeeds on every wf value") — not required; a serializer that
  always fails satisfies `ParseOk` vacuously;
- **domain soundness** ("fails outside the wf set") — not required either; the
  theorem simply says nothing there.

This is not hypothetical: these serializers really can fail —
`Serializer.recursiveProgressError` (`Serializer.lean:254`) is what the
recursion guard emits when the depth measure does not decrease. I searched
`Pollux/Parse/` and `Pollux/InterParse/` and found **no** progress lemma:
nothing of the form `valueWf d v → ∃ enc, serialValue d v = .success () enc`.
All three top-level theorems (`idInterParseOk:381`, `compatInterParseOk:989`,
`schemaCorrectInterParseOk:521`) unfold to `intro enc hwf hser`, and even the
length lemmas are conditional — "when each *succeeds* with a length given by
`lenFn`" (`Serialization.lean:305`).

**What keeps the annotation honest** is the round-trip proof, and only from one
side: too weak a `wf` and the proof fails for want of facts about `x`; too
strong and everything still goes through, with a theorem covering fewer values.
The wf is pinned from below and not at all from above, and there is no separate
check.

The theorems are *not* vacuous for the actual `serialValue` — it does succeed on
well-formed values — but **that is not among the things proved**, and the
distinction belongs in the report.

**Recommendation.** The gap closes cheaply inside work already planned.
`proto-design.org` states the soundness leg informally as
`Encodes d v (serialValue d v)`, as though `serialValue d v` were bytes. Written
literally against `Result` that forces a choice: `.getEnc`, which silently
returns `d.remaining` on failure (`Result.lean:57`), or success as an antecedent
again. State it instead as

```lean
Value.Valid d v → ∃ bs, serialValue d v = .success () bs ∧ Encodes d v bs
```

and progress falls out of the soundness leg rather than becoming a separate
chore. Since the only failure mode is the recursion guard, and Proto's guard is
on `valueDepth`, which decreases structurally at nested messages, the
existential should be routine.

This is also a third reason the §4.1 phrase undersells `Value.Valid`: nothing
about the serializer's *type* is ever at stake, so the predicate's entire job is
in theorem statements.

### 7.6 Booked Deferrals (Theirs, Not Findings)

- **Scalar type changes.** `Payload.reinterpret` requires `s₁ = s₂`. Widening to
  the compatible-retyping table "is what will force the field relation `∝` to be
  more than equality". Report §5's varint tables are the specification for this
  work — worth saying so explicitly, since it reframes them from "rules awaiting
  formalization" to "the design document for the next Lean pass".
- **Cross-member last-wins.** The transform does not implement it; instead it
  *assumes* `OneofPreservedAll`. The alternative — clear all but one member — is
  what a spec-faithful parser does, and is "the honest fix", deferred with the
  `Encodes` work since last-wins is only observable against foreign encoders.
  Which of the two survives is a decision the parser will force.
- **Unknown-field preservation** (protobuf ≥ 3.5). Requires an unparsed-bytes
  region in `Value`. Recorded as a choice rather than defaulted into; should be
  revisited with the `FileDescriptorSet` import path. **(Finding)** The no-junk
  half of `Value.Total` (§3.2) is the formal content of "we do not preserve
  unknown fields", but the two are *separable* and the report should not present
  them as one decision: preservation would put unknowns in a
  **separate `Value` component**, which is what real implementations do, leaving
  the entry map — and hence `Total`'s exactness and everything §3.2 derives from
  it — untouched. What preservation actually costs is raw bytes in the induction
  skeleton, and a transform that is the identity on the unknowns region; it does
  not cost the totality invariant.
- **Recursive message types.** Plan is the flat symbol table. The real casualty
  is the compatibility relations: an inductive `DescCompat` recursing
  structurally cannot have finite derivations relating cyclic descriptors, and
  would restate as pointwise one-layer compatibility over the name graph. That
  cost is intrinsic to recursive schemas, not to the representation — a good
  point for the report, since it is the kind of thing that looks like a modeling
  failure and isn't.
- **Enums**, **groups**, **`String` vs UTF-8 bytes carrier** (the round trip
  will need `String.fromUTF8? (toUTF8 s) = some s`; fallback is a byte carrier
  with validity in the predicate).

### 7.7 Not yet Written at All

No Proto-layer parser, serializer, `Encodes` relation, or compatibility
relation. `Pollux/Parse/` and `Pollux/InterParse/` are the frozen predecessors.
So report §5, once rewritten, is genuinely
*the design document for unwritten Lean* — which is a legitimate and
worth-stating position, but the report should say which side of the line each
rule is on. The §5.4 coverage table is the honest way to do it.

---

## 8. Vocabulary Map

For translating between report notation and Lean names while writing.

| Report §5 | Lean |
| --- | --- |
| `v₁ : τ₁ ≺ v₂ : τ₂` | no relation; `Val.reinterpret f₁ f₂ x = some y`, `Payload.reinterpret t₁ t₂ p = some q` |
| `τ₁ ∝ τ₂` | no relation; today ≈ `t₁ = t₂` or both `.msg` |
| `m₁ ≼ m₂` | no relation; nearest is `d₂.AllWF ∧ d₂.Legal ∧ Desc.OneofPreservedAll d₁ d₂` |
| `⟨r, f⟩` | `Desc` — **no reserved component** |
| `f(id) = (s, τ)` | `d.get? k = some ⟨card, ty⟩` — **no name** |
| `IMP` / `OPT` / `REP` | `Cardinality.singular` / `.optional` / `.repeated` (+ `.oneof g`) |
| `MSG m` | `FieldType.msg d` |
| `default(τ)` | `Field.init : Field → Val` (takes the **whole field**) |
| `v(i)` | `v.get? k : Option Val` |
| `dom(f)`, `dom(v)` | `(d.get? k).isSome`, `(v.get? k).isSome` |
| valid descriptor `v(d)` | `Desc.AllWF d ∧ Desc.Legal d` |
| — | `Value.Total d v` (no report counterpart yet — needs one) |
| `E_τ(v, bs)` | `Encodes d v bytes` (planned, not written) |
| `parse_{d₂}(bs)` | `parseValue d₂ bs` (planned for Proto; exists for InterParse) |
| — | `Value.reinterpret d₁ d₂ v` (no report counterpart yet — needs one) |
