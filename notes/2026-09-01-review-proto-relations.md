# Review: Section 5 — Protobuf Compatibility Relations

Reviewed 2026-09-01 against `sections/05-proto-relations.tex`, the wire-format
semantics, and the InterParse compatibility experience (`Compatible.lean`,
`CompatTransform.lean`). Organized by severity: first the things that break it
as a *compatibility relation* (i.e., as a sound description of "parse the
writer's bytes under the reader's descriptor"), then rules that are wrong as
stated, then modeling recommendations, then nits.

## A. Foundational Problems

**DONE A1. The definition, the rules, and the theorem describe three different
relations.** The value relation is *defined* as
`parse_τ₂(serialize_τ₁(v₁)) = v₂` — a round trip from a value. But the final
theorem quantifies over arbitrary `bs` parsed under both descriptors. These
coincide only for canonical encodings, and protobuf encodings aren't canonical:
field order is free, duplicated singular fields merge/last-wins, varints may be
over-long, packed and unpacked repeated encodings are both legal. A `bs` in the
image of no serializer still parses, and `parse_{d₂}(bs)` need not equal
`parse_{d₂}(serialize_{d₁}(parse_{d₁}(bs)))`. Given the goal — characterize how
a value changes under the reader's descriptor — the right foundation is the
relational `Encodes` spec already planned for the Proto layer: define
`v₁:τ₁ ≺ v₂:τ₂` as (∀ or ∃)
`bs, Encodes_{τ₁}(v₁, bs) → parse_{τ₂}(bs) = some v₂`. The ∀-form is the one the
theorem needs.

**DONE A2. Trans is false under the stated definition.** Counterexample:
`2^40 : uint64 ≺ 0 : uint32` (Uint-Chg-W) and `0 : uint32 ≺ 0 : uint64`, so
Trans gives `2^40 : uint64 ≺ 0 : uint64`. But the definition is functional in
`v₂`, and `parse_{uint64}(ser_{uint64}(2^40)) = 2^40 ≠ 0`. Trans only holds when
the intermediate step is byte-faithful, which narrowing isn't. Note this is also
*unnecessary*: under the A1 parse-parse reading, "transitivity" of the
end-to-end guarantee falls out of composing the theorem (same `bs`, three
descriptors) with no syntactic Trans rule at all. Recommendation: cut Trans, and
cover the cross-width-cross-encoding pairs directly (see B1's rule schema, which
makes them all one rule). This matches the InterParse relations, none of which
have a Trans rule.

**A3. The Msg value rule is vacuously satisfiable — it doesn't pin down the
transform.** The rule constrains only `i ∈ dom(v₂)`, so `v₂ = ∅` is related to
*every* `v₁` at any pair of ≼-related descriptors. Consequences: the theorem's
conclusion `v₁ ≺ v₂` carries almost no information; `Msg-T`'s semantic
obligation ("∀v₁ ∃v₂") is discharged trivially; and read as a lemma about the
functional definition, the rule is simply unsound (many `v₂` satisfy the
premises; parse produces one). The rule needs to characterize `dom(v₂)` and be
driven by the reader's descriptor, exactly like `compatTransform` in the Lean
InterParse layer:

- `i ∈ dom(f₂) ∩ dom(v₁)`, types related → present with
  `v₁(i) : τ₁ ≺ v₂(i) : τ₂` (the current premise binds `τ₁` and then never uses
  it — the recursive premise is untyped);
- `i ∈ dom(f₂)`, absent from the writer's value → missing/default (the
  `M-Declare` lesson: without this case the theorem is false already at
  `d₁ = d₂`);
- `i ∈ dom(v₁) \ dom(f₂)` → dropped (see C4 — unlike the intermediate format,
  this *is* sound for protobuf).

The unguarded `∨ v₂(i) = default(…)` disjunct also lets a field be defaulted
even when the writer sent a perfectly compatible value; it should be reachable
only when the writer's field is absent or wire-incompatible.

**A4. No range/presence premises anywhere.** Every integer rule implicitly
assumes `v₁` is in `τ₁`'s range (`(−5) : uint32` derives nonsense otherwise) —
either state a global convention that `v : τ` implies range-wf (the serializer's
phantom-wf move), or add premises. More importantly:
**implicit-presence fields don't serialize default values.** So `Opt-Intro` is
wrong at `v = default(τ)` (the reader sees `none`, not `some default`),
`Rep-Intro` is wrong at default (`[]`, not `[v]`), and the same wrinkle hits
`bool false` and enum `0`. The red note about needing a `None`-intro and a
`MISSING` value is exactly right — the InterParse `.missing` modeling is the
proven approach; take that option, plus guard the intro rules with
`v ≠ default(τ)`.

## B. Rules That Are Wrong as Stated

**DONE B1. Three of the integer formulas have bugs.** (Verified against the wire
format; the others — Uint-Chg-W, Uint-Int, Int-Uint, Uint-Sint, Sint-Uint,
Sint-Int, and all bool rules — check out, including the cute `Bool-Sint`
`−𝟙[v]`.)

- **Int-Chg-W**: the `× 𝟙[v₁ < 0]` multiplies the whole expression, so every
  non-negative `v₁` maps to 0. And for negatives it's wrong whenever the low `m`
  bits have the sign bit clear: `v₁ = −2^31 − 1 : int64 → int32` truncates to
  `0x7FFFFFFF = 2^31 − 1`, but the formula gives `−1`. Correct closed form:
  `v₂ = ((v₁ + 2^{m−1}) mod 2^m) − 2^{m−1}`.
- **Sint-Chg-W**: `−1 : sint64 → sint32` should be `−1` (zigzag 1 truncates to
  1), but the formula gives `2^31 − 1`. Truncating a zigzag preserves the low
  bit, hence the *sign* — so: `v₂ = v₁ mod 2^{m−1}` if `v₁ ≥ 0`, else
  `−1 − ((−1 − v₁) mod 2^{m−1})`.
- **Int-Sint**, negative branch: off by one. `−1 : int32` serializes as ten
  bytes = `2^64 − 1`; truncate to 32 bits: `2^32 − 1`, unzigzag: `−2^31`. The
  formula gives `−2^31 + 1`.

Rather than patching, restructure: every varint-family pair is
`decode_{τ₂}(encode_{τ₁}(v₁))` for `encode_{uint} = id`,
`encode_{int_n} = (· mod 2^64)` (the 10-byte sign extension the text correctly
identifies), `encode_{sint} = zigzag`, and `decode_{uint_m} = (· mod 2^m)`,
`decode_{int_m} = toSigned_m`, `decode_{sint_m} = unzigzag ∘ (· mod 2^m)`. One
rule schema plus a six-row table replaces ~12 rules, eliminates all three bugs
by construction, and is what the Lean proofs will factor through anyway. It also
kills the `%`-floored-but-division-truncated convention (line 125–126), which is
precisely the sort of thing that produced these off-by-ones.

**DONE B2. Two ∝ directions are reversed.** The writer's type goes on the left:
`τ_writer ∝ τ_reader`. `Field-Type` has this right (`f(id) = τ₁`, `τ₁ ∝ τ₂`).
But **Msg-Width-Depth** (`f(id) = τ, τ' ∝ τ` updating to `τ'`) and
**Oneof-Feild-Update** (same shape) point backwards — as written they say the
*new* type must convert into the *old* one. Also Msg-Width-Field is verbatim
Field-Add, and Msg-Width-Depth is (modulo the bug) Field-Type — deduplicate.

**B3. ∝ is not reflexive, violating its own definition.** By Refl, `v :τ ≺ v :τ`
always, so semantically `τ ∝ τ` for every τ. But syntactically: `str ∝ str` is
underivable (only the two cross rules exist), and `ENUM e ∝ ENUM e` is
underivable because Enum-T requires *strict* `⊂`. Add `Refl-T`, and change `⊂`
to `⊆` in Enum-T and Enum-Width (and `r ⊂ r'` in Reserved-Add).

**B4. The set-keyed oneof map update rules leave stale entries.** `f[{id} ↦ …]`
in Oneof-Intro-Field inserts at a *new* key without deleting the old key `id`,
so the field number now lives in two entries. Same bug in Oneof-Add-F and
Oneof-Elim (`f[id_n∖id ↦ …]` leaves `id_n` in place). Relatedly, freshness
premises are unenforceable: `id ∉ dom(f)` doesn't check membership *inside*
set-valued keys, and Oneof-Add-F's `id_n ∉ id_s` doesn't require `id_n` fresh in
`f` globally. This matters beyond hygiene: via that hole you can derive a `d₂`
where two fields the `d₁`-writer can independently set share a oneof — and then
the reader applies cross-member last-wins, which the Msg value rule cannot
express, making the theorem false. With proper global freshness, only *one*
pre-existing field can ever enter a oneof (the source comment "introduce a new
field, but not move an existing one" is the right instinct and matches the
official guidance), and the last-wins case becomes unreachable.

**DONE B5. Byt-Str needs a UTF-8 premise.** Proto3 conformant parsers reject
invalid UTF-8 in `string` fields, so `Byte-Str` needs `validUtf8(v)` — and
`Byt-Str-T` is then false as a type-level rule (an invalid-UTF-8 bytes value has
no image). The official compat docs say the same: bytes → string only "if the
bytes are valid UTF-8". This also means `parse_{d₂} bs = Some v₂` in the
theorem's conclusion is *not* free once bytes→string retyping is allowed.

**B6. The Enum value rule contradicts the section's own open-enum stance.** The
premise `v ∈ e₂` models *closed* enums, but the prose (correctly) commits to
proto3 open enums, under which an unknown value is preserved, not rejected — so
the rule should have no membership premise (or the closed case should be modeled
separately). As written, the theorem's `parse_{d₂}` conclusion is fine but the
relation can't derive the pair that parsing actually produces when `v ∉ e₂`.

**B7. The reserved machinery is inert.** No rule consults `r`: Field-Add doesn't
require `id ∉ r`, there's no Field-Remove rule that *puts* a number into `r`,
and validity doesn't force `dom(f) ∩ r = ∅`. So reserved sets can grow and
shrink without ever affecting anything. The point of `reserved` is exactly the
chain: remove field → reserve number → adding at that number is forbidden. And
the red-flagged **Reserved-Rm** defeats it under Trans-M: reserve 5, unreserve
5, re-add 5 at a new type gives the stale-number retype that reserved exists to
prevent. Drop Reserved-Rm, add `id ∉ r` to Field-Add (and the oneof add rules),
and add Field-Remove with `r' = r ∪ {id}`.

**B8. Rules the prose promises but doesn't deliver.** "We can introduce,
eliminate or change" — but there is no `Rep-Elim` and no `Opt-Elim-Some`
(`some v : opt τ ≺ v : τ`), and without the latter `Opt-Rm-T` has no value-level
backing for the `some` case. On the red question about eliminating a *packed*
field: a packed run is a single LEN record; a singular varint-typed reader sees
a wire-type mismatch, which conformant parsers route to unknown fields — so the
reader gets *absent/default*, not the last element. Last-wins only happens for
unpacked encodings. Since proto3 packs by default and the theorem quantifies
over all `bs`, an unconditional last-wins Rep-Elim is unsound; the rule has to
either yield both outcomes or the relation must be parameterized by the encoding
(another argument for the `Encodes`-based ∀-form, which handles this naturally).

**B9. Missing-Imp relates *any* τ₁ to *any* τ₂.** No premise connects them, so
an absent message-typed field can "become" an int default, etc. Harmless in
isolation but it makes ≺ uselessly coarse at exactly the M-Declare-shaped case;
require `τ₁ ∝ τ₂` (the same fix InterParse's `M-Declare` needed, for the same
reason — a D-Chg on a declared-but-unset key retypes the injected missing
value).

## C. Modeling Recommendations

**C1. Make the transform explicit.** Given the stated goal — "how would this
value change if parsed under the updated descriptor" — the load-bearing artifact
is a *function*, not a relation: the Proto analogue of
`idCompatTransform`/`compatTransform`. Define `transform_{d₁→d₂}(v)`
(reader-descriptor-driven, per-field `decode_{τ₂} ∘ encode_{τ₁}`), state ≺ as
characterizing it, and prove "parsing produces exactly the transform" then "the
transform lands in ≺". That two-step strategy is already proven out three times
in InterParse, and it fixes A3's vacuity for free.

**C2. Align the oneof model with the Lean kernel.** The report keys the field
map by *sets* of field numbers; `Proto/Descriptor.lean` and proto-design.org
deliberately chose the flat map with `Cardinality.oneof (group : Nat)` — because
descriptor form is flat, the wire names members directly, and cross-descriptor
comparison should compare *induced partitions*, never structural keys. The
set-key choice is the direct cause of B4's bugs and the FIXME in the source.
Rewriting the oneof rules as flat rules plus side conditions on the group
partition ("id joins a group no other writer-settable field inhabits") would
shrink five awkward rules to about two.

**C3. Desugar maps.** `MAP` appears in the type relation but has no
value-relation rules at all, so `Map-Type-F` has no semantic backing. The wire
format defines `map<K,V>` as `repeated MapEntry` — the Lean kernel already
relies on this — so map compatibility should *follow from* the Msg + Rep rules
rather than be primitive. One real semantic point deserves a remark: narrowing a
key type (`uint64 → uint32`) can collide distinct entries, and the reader's map
keeps the last one. (Also: `\impt` vs `\imp` are inconsistently used in that
rule's premise/conclusion.)

**C4. Say why field *removal* is allowed — it's the payoff of the real wire
format.** InterParse's `≪` famously could not have a drop rule (unknown tags
desync the toy stream). Protobuf tags carry wire types, so unknown fields are
always skippable and dropping is sound. That's the key structural improvement of
the Proto layer over InterParse and the reason `parse_{d₂}` totality in the
theorem is even provable — worth stating explicitly, and worth an explicit
Field-Remove rule (per B7) rather than leaving removal representable only
through Oneof-Elim.

**C5. The three relations are mutually recursive — say so.** Msg (≺) references
≼; Msg-T (∝) references ≼; Field-Type (≼) references ∝. That's fine, but the
report presents them as three sequential definitions. In Lean this becomes one
`mutual` block (as `Compatible.lean` already forced for the InterParse
versions); the text should present them as a simultaneous inductive definition.

**C6. Validity-as-reachability is weaker than a WF predicate.** `v(d) := ∅ ≼ d`
is elegant but (a) the definition has a binding slip (`d` on the left, unbound
`r`,`f` on the right), (b) given B4/B7, reachability doesn't actually enforce
the static rules (reserved-disjointness, no duplicate numbers, oneof
constraints, map-key restrictions — Field-Add can introduce anything, including
`map<bytes,…>`), and (c) every proof about valid descriptors becomes an
induction over evolution paths. The Lean kernel's direct `WF` is the right
primary definition; reachability is then a nice theorem, not the definition.

## D. Smaller Items

- **DONE Metavariable table**: `s : "I don't actually know…"` is still in the
  text (it's the field name, from `f(i) = (s, τ)`); `d` is booked as "decorator"
  but used as descriptor in the theorem; `m` is message, bit width, *and* the
  oneof submap in Oneof-Add-F. Also the field-map codomain shifts between rules:
  `f(id) = τ` (Field-Type), `(s, τ)` (Msg value rule), `d τ`
  (Oneof-Intro-Field).
- DONE Line 366: "since names **are** recorded in the encoded message" — should
  be "are **not**"; as written it says the opposite of the justification for
  free renaming.
- DONE Line 136: `\sintn[m]` — the macro takes `{...}` (see `pollux.tex:105`),
  so this typesets as literal `[m]`.
- DONE "Oneof-Feild-Update" typo; also its inner/outer `id` collide (premise
  `f_o(id) = τ` vs conclusion key `f[id ↦ f_o]`).
- `(−1)^{v₁}` with negative `v₁` should be defined via parity.
- DONE ≼ was declared as the *message* relation but Refl-E/Trans-E/Enum-Width
  apply it to enums — declare it for both or use a separate symbol.
- DONE Line 8 grammar: "relates two protobuf type is any value" → "types if any
  value".
- DONE The theorem is titled "Field Compatibility" but is the
  message/descriptor-level statement; and per the InterParse experience
  (`not_descCompat_allWF`), expect to need a `d₂`-well-formedness hypothesis
  explicitly — it won't be recoverable from `d₁ ≼ d₂`.
- DONE Int-Int-T deliberately exceeds the official compat list (officially
  `sint*` is not interchangeable with `int*`/`uint*`); since documenting the
  value mangling is the point of the project, keep it — but add a sentence
  acknowledging the deliberate divergence from the protobuf documentation's
  notion of "compatible".

## What's Solid

The overall three-tier architecture (value / type / message) is right and
mirrors what worked in `Compatible.lean` (≺/∝/⋘ /≼). The 10-byte negative-int
observation (line 116) is correct and is exactly why Int-Uint/Uint-Int work
cross-width. Six of the nine integer formulas and all six bool rules are exactly
right. The "new fields may join oneofs, existing ones may not move" instinct
matches both the official guidance and what soundness requires. And both red
notes — the MISSING/None modeling and the packed-elimination question — identify
real problems whose resolutions (InterParse-style `.missing`; wire-type mismatch
→ default) are within reach.
