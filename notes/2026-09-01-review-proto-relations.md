Status: open
Report: sec:proto-relations, sec:framework (def:well-behaved, def:sem-compat, def:sem-compat-fld, def:sem-assum, def:soundness, lem:msg-from-fields), def:dlegal, thm:trans-valid @ 6aa5da8 (+ uncommitted D-Add reserved premise)
Lean:   Pollux/Proto/Value.lean (`Payload.string`/`.bytes`) @ 6aa5da8; the relations themselves are not yet formalized

# Review: Protobuf Compatibility Relations

Reviewed 2026-09-01 against `sections/05-proto-relations.tex`, the wire-format
semantics, and the InterParse compatibility experience (`Compatible.lean`,
`CompatTransform.lean`).

**Re-reviewed 2026-10-28** against the rewritten `sec:framework`
(`04-pollux-framework.tex`) and `sec:proto-relations`
(`09-proto-relations.tex`), which now use the coercion framing: a derivation
`Γ ⊢ d₁ ≪ d₂ ⇝ f` builds the coercion `f`, judged by `def:well-behaved`. The
rewrite resolves most of sections A–D. Each item's status is updated in place,
with a one-line reason. New problems are in **section E**, ordered by severity.
E1 and E2 are soundness bugs. E1 has a concrete counterexample.

Original line numbers in A–D refer to the old §5 file and are stale.

## Status at a Glance (2026-10-28)

| Item | Status |
|------|--------|
| A1, A2, B1, B2, D (most) | done before this re-review |
| A3, A4, B3, B9, C1, C2, C4, C6 | done by the rewrite |
| B6, C3 | moot: enums and maps are now listed as omitted features (`sec:proto-desc`) |
| B4 | done for the oneof model, but the hazard returns through D-Add (E1) |
| B5 | partly done; see E4 |
| B7 | partly done; reserved sets are now consulted, but D-Update bypasses them (E1) |
| B8 | partly done; see E2 and E6 |
| C5 | still open (the text now says "stratified") |
| B1 | regression in the encoding table (E7) |

## A. Foundational Problems

**DONE A1. The definition, the rules, and the theorem describe three different
relations.** The value relation is *defined* as
`parse_τ₂(serialize_τ₁(v₁)) = v₂`, a round trip from a value. But the final
theorem quantifies over arbitrary `bs` parsed under both descriptors. These
coincide only for canonical encodings, and protobuf encodings aren't canonical:
field order is free, duplicated singular fields merge/last-wins, varints may be
over-long, packed and unpacked repeated encodings are both legal. A `bs` in the
image of no serializer still parses, and `parse_{d₂}(bs)` need not equal
`parse_{d₂}(serialize_{d₁}(parse_{d₁}(bs)))`. Given the goal (characterize how
a value changes under the reader's descriptor), the right foundation is the
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

> 2026-10-28: Still fine. The `sec:proto-relations` type-level example still
> uses the retired value-relation notation (`2^40 : uint64 ≺ 0 : uint32`). In the
> coercion framing the same point reads more sharply: a Trans rule would give
> `uint64 ≺ uint64` a second derivation whose coercion is
> `(dec_u64 ∘ enc_u32) ∘ (dec_u32 ∘ enc_u64) ≠ id`, so coherence (which
> `sec:framework` says is "free") would fail. See E8.

**DONE A3. The Msg value rule is vacuously satisfiable, so it doesn't pin down
the transform.** *(2026-10-28: resolved. D-Update now builds the coercion
explicitly, with shared keys coerced, reader-only keys `init`, and writer-only
keys dropped, and `def:well-behaved`'s `U ⊆ dom(d₁) ∖ dom(d₂)` clause rules out
the "default everything" coercion.)* The rule constrained only `i ∈ dom(v₂)`,
so `v₂ = ∅` was related to every `v₁`. The fix was to drive it by the reader's
descriptor, like `compatTransform`. That is what D-Update now does.

**DONE A4. No range/presence premises anywhere.** *(2026-10-28: resolved.
Ranges come from `def:vvalid`, whose legality part enforces integer ranges, and
every semantic definition quantifies over valid messages. The implicit-default
problem is now stated correctly in the red-rule discussion, which says
K-ImpOpt and K-ImpRep can't be wire-sound because an encoding may or may not
write an implicit default. MISSING has given way to totality plus `init`.)* One
consequence of the "may or may not write the default" reading has not been
followed through. It breaks the message-merge plan. See E2.

## B. Rules That Are Wrong as Stated

**DONE B1. Three of the integer formulas have bugs.** (Verified against the wire
format; the others, Uint-Chg-W, Uint-Int, Int-Uint, Uint-Sint, Sint-Uint,
Sint-Int, and all bool rules, check out, including the cute `Bool-Sint`
`−𝟙[v]`.)

- **Int-Chg-W**: the `× 𝟙[v₁ < 0]` multiplies the whole expression, so every
  non-negative `v₁` maps to 0. And for negatives it's wrong whenever the low `m`
  bits have the sign bit clear: `v₁ = −2^31 − 1 : int64 → int32` truncates to
  `0x7FFFFFFF = 2^31 − 1`, but the formula gives `−1`. Correct closed form:
  `v₂ = ((v₁ + 2^{m−1}) mod 2^m) − 2^{m−1}`.
- **Sint-Chg-W**: `−1 : sint64 → sint32` should be `−1` (zigzag 1 truncates to
  1), but the formula gives `2^31 − 1`. Truncating a zigzag preserves the low
  bit, hence the *sign*. So `v₂ = v₁ mod 2^{m−1}` if `v₁ ≥ 0`, else
  `−1 − ((−1 − v₁) mod 2^{m−1})`.
- **Int-Sint**, negative branch: off by one. `−1 : int32` serializes as ten
  bytes = `2^64 − 1`; truncate to 32 bits: `2^32 − 1`, unzigzag: `−2^31`. The
  formula gives `−2^31 + 1`.

Rather than patching, restructure: every varint-family pair is
`decode_{τ₂}(encode_{τ₁}(v₁))`, with one rule schema plus a table.

> 2026-10-28: The schema (T-Varint, `tab:varint-conversion`,
> `tab:varint-derived`) is in. I re-checked all 49 cells of `tab:varint-derived`
> and they are correct. One cell of `tab:varint-conversion` regressed, though.
> See E7.

**DONE B2. Two ∝ directions are reversed.** The writer's type goes on the left:
`τ_writer ∝ τ_reader`. `Field-Type` has this right (`f(id) = τ₁`, `τ₁ ∝ τ₂`).  But
**Msg-Width-Depth** (`f(id) = τ, τ' ∝ τ` updating to `τ'`) and **Oneof-Feild-Update** (same
shape) point backwards. As written they say the *new* type must convert into the
*old* one. Also Msg-Width-Field is verbatim Field-Add, and Msg-Width-Depth is
(modulo the bug) Field-Type. Deduplicate.

**DONE B3. ∝ is not reflexive, violating its own definition.** *(2026-10-28:
resolved. T-Refl and D-Refl exist, and enums are no longer modeled.)* One
remaining gap is that reflexivity fails for any descriptor containing a oneof
except through D-Refl, because no cardinality rule covers `ONE g`. See E3.

**DONE B4. The set-keyed oneof map update rules leave stale entries.** (2026-10-28:
*resolved for the model. Oneofs are now the flat `ONE g` cardinality, and
*D-Update carries `OneofPreserved`, which matches C2.)* The underlying hazard, a
*reader putting two independently set writer fields into one oneof so that
*cross-member last-wins applies, is reachable again through D-Add, which never
*checks `OneofPreserved` and doesn't require the added key to be reader-only. See
*E1.

**DONE B5. Byt-Str needs a UTF-8 premise.** *(2026-10-28: partly done.)* The premise
is there, in red in `sec:proto-relations` and in black in `sec:framework`. But
it's a premise about values in a type-level rule, as the source's TODO comment
notes, and `id` is not a well-typed coercion between Lean's `String` and
`List UInt8`. See E4.

**DONE B6. The Enum value rule contradicts the section's own open-enum stance.**
*(2026-10-28: moot. Enums are listed under omitted features in
`sec:proto-desc`.)* When enums come back, model them as open (proto3). The
natural encoding is `enum ∈ 𝒱` with `enc`/`dec` equal to the `int32` row, which
gives `enum ↔ int32/int64/uint*` for free and matches the protobuf docs.

**DONE B7. The reserved machinery is inert.** *(2026-10-28: partly done.)* D-Add now
requires `id ∉ r₁ ∪ r₂` (uncommitted edit), D-Rm moves the removed number into
`r`, D-ResAdd grows `r`, and Reserved-Rm is gone. That was the requested chain.
But D-Update can add and drop keys without consulting `r` at all, so every
reserved premise can be routed around. That loophole is also what makes D-Add
unsound. See E1.

**DONE B8. Rules the prose promises but doesn't deliver.** *(2026-10-28: partly
done.)* Rep-Elim now exists as K-RepOpt/K-RepImp with `¬Packable(τ₁)`, which is
the right resolution of the packed-elimination question. Opt-Elim exists as
K-OptImp. But all of them are red, and the explanations don't match the colours.
K-OptImp looks sound, and K-RepOpt is sound for `string`/`bytes` but unsound for
messages. See E2 and E6.

**DONE B9. Missing-Imp relates *any* τ₁ to *any* τ₂.** *(2026-10-28: resolved.
There is no Missing rule any more. Reader-only keys get `init(d₂[id])` in
D-Update.)*

## C. Modeling Recommendations

**DONE C1. Make the transform explicit.** *(2026-10-28: resolved, and more
thoroughly than proposed. The derivation is the program.)* The Lean section
offers two routes: put the derivation in `Type`, or keep
`Value.reinterpret` and prove agreement. The text uses both. See E5.

**DONE C2. Align the oneof model with the Lean kernel.** *(2026-10-28: resolved
by the flat `ONE g` cardinality plus `OneofPreserved`.)* See E3 for the missing
cardinality rule.

**DONE C3. Desugar maps.** *(2026-10-28: moot. "Explicit Maps" is an omitted feature
with desugaring as the stated plan.)* Keep the key-narrowing remark for when
maps arrive: `map<uint64,V> → map<uint32,V>` can collide distinct keys, and the
reader keeps the last entry, so the coercion is not `map` of a key coercion.

**DONE C4. Say why field *removal* is allowed.** *(2026-10-28: resolved. The
D-Update prose says writer-only keys are skipped "using the wire type in the
tag", and D-Rm exists.)*

**DONE C5. The three relations are mutually recursive, so say so.** *(2026-10-28:
still open.)* `sec:framework` now calls the definition "stratified", which
usually means the opposite: each level defined before the next. The levels here
are mutually inductive. D-Update uses `⊑` on fields, K-Field uses `≺` on
payloads, and T-Msg/F-Msg reaches `≪` on names, then N-Unfold, then D-Update
again. Suggested wording: "This is a single mutually inductive definition,
with one judgment form for each level:".

**DONE C6. Validity-as-reachability is weaker than a WF predicate.**
*(2026-10-28: resolved. `def:dwf`/`def:dlegal` are direct, and soundness takes
them as hypotheses.)*

## D. Smaller Items

- **DONE Metavariable table**: `s : "I don't actually know…"` is still in the
  text (it's the field name, from `f(i) = (s, τ)`); `d` is booked as "decorator"
  but used as descriptor in the theorem; `m` is message, bit width, *and* the
  oneof submap in Oneof-Add-F. Also the field-map codomain shifts between rules:
  `f(id) = τ` (Field-Type), `(s, τ)` (Msg value rule), `d τ`
  (Oneof-Intro-Field). *(2026-10-28: the new table has its own issues. See E8.)*
- DONE Line 366: "since names **are** recorded in the encoded message" should
  be "are **not**"; as written it says the opposite of the justification for
  free renaming.
- DONE Line 136: `\sintn[m]`: the macro takes `{...}` (see `pollux.tex:105`),
  so this typesets as literal `[m]`.
- DONE "Oneof-Feild-Update" typo; also its inner/outer `id` collide (premise
  `f_o(id) = τ` vs conclusion key `f[id ↦ f_o]`).
- DONE `(−1)^{v₁}` with negative `v₁` should be defined via parity.
  *(2026-10-28: gone with the table rewrite.)*
- DONE ≼ was declared as the *message* relation but Refl-E/Trans-E/Enum-Width
  apply it to enums. Declare it for both or use a separate symbol.
- DONE Line 8 grammar: "relates two protobuf type is any value" → "types if any
  value".
- DONE The theorem is titled "Field Compatibility" but is the
  message/descriptor-level statement; and per the InterParse experience
  (`not_descCompat_allWF`), expect to need a `d₂`-well-formedness hypothesis
  explicitly, since it won't be recoverable from `d₁ ≼ d₂`.
- DONE Int-Int-T deliberately exceeds the official compat list (officially
  `sint*` is not interchangeable with `int*`/`uint*`); since documenting the
  value mangling is the point of the project, keep it, but add a sentence
  acknowledging the deliberate divergence from the protobuf documentation's
  notion of "compatible".

## E. New Issues (2026-10-28)

**DONE E1. D-Add is unsound, because D-Update drops and adds keys without consulting
the reserved sets.** D-Update quantifies only over shared keys, so on its own it
derives `d₁ ≪ d₂` for *any* `d₂` whose shared keys are related. A writer key can
be dropped without being reserved. D-Add then re-adds that key with a new type.
Its premises check `id ∉ dom(d₂)` and `id ∉ r₁ ∪ r₂`, but never `id ∉ dom(d₁)`.

Counterexample (both descriptors are well-formed and legal):

```
d₁  = ⟪r, [(1, ⟨IMP, int32⟩)]⟫        r = {19000..19999}
d₂  = ⟪r, []⟫
D-Update (no shared keys; OneofPreserved vacuous):  ∅ ⊢ d₁ ≪ d₂ ⇝ λm. {}
D-Add 1 ↦ ⟨IMP, sint32⟩  (1 ∉ dom d₂, 1 ∉ r ∪ r):  ∅ ⊢ d₁ ≪ d₂' ⇝ λm. {1 ↦ 0}

m  = {1 ↦ IMP 5},   bs = 08 05
parse_{d₂'}(bs) = ({1 ↦ unzz(5)}, ∅) = ({1 ↦ −3}, ∅)   but   f(m) = {1 ↦ 0}
```

So `def:soundness` is false. The same path gives two more failures:

- **Wire-incompatible retype.** D-Add `1 ↦ ⟨IMP, string⟩` makes the reader
  skip the varint record for key 1. Then `U = {1}`, but `1 ∈ dom(d₂')`, which
  violates `U ⊆ dom(d₁) ∖ dom(d₂')`.
- **Moving a writer field into a oneof.** D-Add never checks `OneofPreserved`,
  and `thm:trans-valid`'s argument that `OneofPreserved` is "vacuous if either
  key is reader-only" assumes the added key really is reader-only. Take writer
  fields 1 and 2 (both `OPT`). D-Update drops 2, D-Update or D-Refl keeps 1 in a
  group `g`, and D-Add re-adds 2 as `ONE g`. The reader now applies cross-member
  last-wins to two fields the writer sets independently (old B4).

Even with D-Add patched, D-Update makes the reserved rules toothless. Every
derivation through D-Add/D-Rm/D-ResAdd can be replaced by one D-Update with
fewer premises. Single-step soundness doesn't need reserved sets (there's no
Trans), but `sec:proto-relations` "Basic Rules" says reserved numbers "restore
our ability to compose updates", and with this relation they don't. Its own
`Msg → Msg' → Msg''` example goes through two D-Updates with nothing reserved.

Options:

1. **(Recommended)** Make D-Update the only structural rule and give it the
   reserved premises:
   ```
   r₁ ⊆ r₂        dom(d₁) ∖ dom(d₂) ⊆ r₂
   ```
   (`sec:framework` already has a TODO for `r₁ ⊆ r₂`.) Reader-only keys then
   can't have been reserved by the writer, by legality. D-Add, D-Rm and
   D-ResAdd become special cases and can be deleted, and E1 is closed. The
   payoff is a clean transitivity lemma for the plain relation. If
   `d₁ ≪ d₂ ≪ d₃` with all three legal, then `dom(d₁) ∩ dom(d₃) ⊆ dom(d₂)`: a
   key dropped at step 1 is in `r₂ ⊆ r₃` and so can't be in `dom(d₃)`. So
   transitivity reduces to per-field transitivity of `⊑`. The cost is that a
   removal that isn't reserved is no longer derivable. Protobuf permits one on
   the wire. Reserving is a lint (buf's
   `FIELD_NO_DELETE_UNLESS_NUMBER_RESERVED`).
2. Keep D-Update free of reserved premises, so single-step compatibility
   matches the wire exactly. Patch D-Add with `id ∉ dom(d₁)`, which makes it
   redundant with D-Update's reader-only case. Then state the reserved
   discipline as a separate evolution predicate that a transitivity theorem
   assumes. This is more faithful to what protobuf accepts, but the reserved set
   leaves the relation entirely.

Note that the transitivity lemma in option 1 needs `✓_l` (`dom ∩ r = ∅` lives in
`def:dlegal`), but `def:soundness` assumes only `✓_w`. See E5.

**E2. The message-merge plan doesn't work under the report's own `Encodes`, and
`assemble` is wrong for message slots.** The red-rule discussion kills K-ImpOpt
because "an encoding can write an implicit field that holds its default". Under
that reading, the parse of a concatenation is not a function of the two
messages. Take the payload message `P = ⟪r, [(1, ⟨IMP, int32⟩)]⟫`:

```
m  = {1 ↦ IMP 5}   bs  = [1:5]
m' = {1 ↦ IMP 0}   bs' = []   or   bs' = [1:0]     (both satisfy Encodes_P(m', ·))
parse_P(bs ++ bs') = {1 ↦ 5}  or  {1 ↦ 0}
```

Three consequences:

- **No `merge` function satisfies the concatenation property** in
  `sec:framework` ("if `bs` encodes `m` and `bs'` encodes `m'` then `bs ++ bs'`
  encodes `merge(m, m')`"). So the merge-homomorphism lemma has nothing to be
  about, and it does not "come for free like coherence".
- **K-RepOpt/K-RepImp are unsound for message payloads that have any implicit
  field**, whatever the coercion. A writer `REP [m, m']` read as `OPT P` gives
  either result, depending on the encoding.
- **`assemble` for a singular message slot can't be "combine the records'
  values with `⊕`"** (`sec:framework`, after `def:sem-compat-fld`). The two
  `bs'` above parse to the same value `{1 ↦ 0}`, yet the reader's results
  differ. The protobuf spec defines merging singular message records as parsing
  the *concatenation of their payloads*, and that is what `assemble` must do.

There is good news too. If `assemble` parses the concatenated payloads, and
`Encodes` for a singular message slot is "records whose concatenated payloads
encode `m`", then K-Opt on messages needs no merge-homomorphism. The reader
parses one byte string that encodes `m` (a strictly smaller message), and the
outer induction hypothesis gives `f(m)`. Oneof last-wins inside the payload is
handled by the same argument. Recommendation:

- restate `assemble` and the message case of `Encodes` that way;
- drop the merge-homomorphism paragraph and the concatenation-closure
  paragraph;
- restrict K-RepOpt/K-RepImp to `¬Packable(τ₁) ∧ τ₁` not a message, which
  leaves `string`/`bytes`.

(K-RepImp on messages is already excluded, since message fields are never
`IMP`.)

**DONE E3. No cardinality rule covers `ONE g`.** The descriptor grammar
(`fig:proto-desc-syn`) has `ONE g` as its own cardinality, and the last bullet
of `sec:proto-relations` says a oneof field "is represented here as an `OPT`
and [doesn't] have explicit rules". But K-Imp/K-Opt/K-Rep match `IMP`/`OPT`/`REP`
syntactically. As written, no descriptor that contains a oneof can be related by
D-Update, not even to itself, so changing any other field of such a message is
underivable. Fix: let K-Opt (and K-OptImp, K-RepOpt, … as appropriate) range
over `κ ∈ {OPT} ∪ {ONE g}`, either by a sentence or by an erasure
`⌊ONE g⌋ = OPT` in K-Field, and leave group membership entirely to
`OneofPreserved`.

One related point is optional. `OneofPreserved` (`thm:trans-valid`) quantifies
over `id₁ = id₂` too, so it forbids moving even a *single* existing field into a
new oneof. The protobuf language guide lists that move as safe. Requiring only
that the shared members of each reader group come from one writer group *or*
are a single writer field would admit it. That's a weakening of a stated
definition, so it is the author's call.

**DONE E4. `bytes → string` (old B5, continued).** Lean's `Payload.string` holds a
Lean `String`, which is valid UTF-8 by construction, and `Payload.bytes` holds a
`List UInt8` (`Value.lean:92-93`, matching `tab:val-spec`). So:

- T-Str-Byte's coercion is `String.toUTF8`, not `id`. It's total, so this is a
  notation fix.
- T-Byte-Str has no total coercion at all, because invalid bytes have no
  `String` image. `def:well-behaved` quantifies over *all* valid writer
  messages, so no premise at the type level can make the rule sound. That is
  what the source TODO senses.

Options:

1. **(Recommended)** Drop T-Byte-Str and say why in one sentence. The protobuf
   docs make it conditional on the data ("if the bytes are valid UTF-8"), and
   Pollux already claims soundness, not completeness. The `sec:framework`
   listing (T-BytStr, black premise) needs the same change.
2. Make judgments relative to a writer-side predicate `P` (`⊨ f : d₁ ≪ d₂ | P`,
   quantifying over valid `m` with `P m`). This is general, and it also covers
   the "moved into an existing oneof" weakening in `thm:trans-valid`'s prose.
   But it's a real extension of `def:well-behaved` and threads through every
   rule.
3. Model `⟦string⟧` as bytes plus a validity predicate. This doesn't help:
   conformant parsers still reject invalid UTF-8, so the rule stays unsound.

**E5. The framework definitions disagree with each other.**

- `def:well-behaved` allows skipped records `U ⊆ dom(d₁) ∖ dom(d₂)`, but
  `def:sem-compat` (and so `cor:compat-sound`) has `parse = some(f(m))` with no
  `U`. The paragraph after `def:compat` says "faithfulness states that there are
  no skipped fields during parsing", which contradicts `def:well-behaved`. As
  written, the corollary doesn't deliver `def:soundness`. Suggest:
  `def:sem-compat` carries the `U` clause, and faithfulness is described as
  "only writer-only records are skipped". (The field-level
  `def:sem-compat-fld` is right to demand *no* skips, since it is only applied
  at shared keys.)
- `def:sem-assum` and `cor:compat-sound` read Γ through the fixed function
  `transform{Σ(n₁)}{·}{Σ(n₂)}`, but Γ now binds assumption variables `x`, and
  D-Update's coercion is built from the derivation. Pick one of the two routes in
  `sec:log-rel-lean`. Under "derivation is the program", `⊨ₙ Γ` needs an
  environment `ρ` with each `ρ(x)` carrying `Σ(n₁)` into `Σ(n₂)` below depth
  `n`. Under "keep `reinterpret`", state the agreement lemma and use
  `reinterpret` in the corollary explicitly. Right now the two are mixed.
- `def:soundness` assumes `✓_w` only. But `sec:proto-relations` (field
  relation) says implicit message fields are excluded by "descriptor
  well-formedness (`def:dwf`)", and since the uncommitted `sec:proto-desc` edit
  that exclusion is in `def:dlegal`. E1's transitivity lemma also needs
  `def:dlegal`. Either add `✓_l` to `def:soundness`, or give K-Imp a premise
  that `τ` is not a message, and fix the reference.
- N-Assum and N-Unfold are each stated twice in `sec:framework`, differently.
  The first N-Unfold concludes `⟨κ, n₁⟩ ≪ ⟨κ, n₂⟩`, which puts `≪` on fields and
  mixes levels. The second concludes `n₁ ≪ n₂`. The second N-Assum has no
  coercion. Keep the first N-Assum and the second N-Unfold. The guardedness
  argument for `fix` ("`x` is only applied to strictly smaller messages") is
  then a property of F-Msg/T-Msg plus the K-rules (`map`, `foldl`), and it's
  worth saying so there.
- Notation drift: `depth`, `depth_f` and `depth_v` all appear;
  `def:sem-compat-fld` writes `g : st₁ ≪ st₂` where it means `⊑` on fields; the
  "Not a Logical Relation" subsection uses `A` for Γ and ends with a dangling
  "we can define a logical relation as such:".

**E6. The red cardinality rules don't match their explanations.** The text says
"the red rules are unsound", but the bullets below it only argue that K-ImpOpt,
K-ImpRep and K-OptRep are unsound, plus K-RepImp *for packable types*.

- **K-OptImp** gets no bullet, and it looks sound. `None` writes nothing, so
  the reader gets `init`. `Some p` writes one or more records whose last value is
  `p` (scalars; messages can't be `IMP`), so the reader gets `f(p)`. Protobuf's
  docs also list `optional ↔ implicit` as wire-compatible. Either it should be
  black, or the reason for red belongs in the list.
- **K-RepOpt/K-RepImp** with `¬Packable` are sound for `string`/`bytes`
  (last-wins equals the last element). Restricted per E2, they can be black.
- "K-ImpRep and K-RepImp are composite rules which can be derived". There is no
  composition rule at the cardinality level, so say "they agree with the
  composites K-ImpOpt;K-OptRep and K-RepOpt;K-OptImp". Note that K-ImpRep is
  then a composite of two unsound rules.
- K-Field's conclusion uses `≺` (`\typrel`). It should be `⊑` (`\fieldrel`).
  K-Imp etc. use `\imp` as a cardinality, but the grammar's cardinality is
  `\sig` (`IMP` is the slot constructor `\impslot`).

 **DONE E7. Encoding table regression (old B1).** In `tab:varint-conversion` the
`int_n` row has `enc(v) = v % 2^w`, with the writer's width. The caption
correctly says the encoding is the 10-byte sign extension, `v % 2^64`. They
differ for a negative `int32`. For example, `−1 : int32` read as `uint64` is
`2^64 − 1` on the wire, but the table's `enc` gives `2^32 − 1`.
`tab:varint-derived` is right, because `(v % 2^64) % 2^m = v % 2^m` for
`m ≤ 64`, so only the `enc` cell needs changing, to `v % 2^{64}`.

**DONE E8. Smaller items.**

- `tab:varint-derived`'s caption and the preceding prose say "thirty"
  conversions. With `bool` in `𝒱` there are 7 types, so 42 non-identity pairs
  (30 was the count without `bool`).
- The varint prose writes `uint[n]` "into `w` bits", and the tables use `n`, `m`
  and `w`. `n` is now also a reserved-interval bound (`fig:proto-desc-syn`) and
  the depth index. The metavariable table lists `𝑓𝑑` twice and omits `d`, `f`,
  `a`, `Γ`, `κ`, `g`.
- D-Update's coercion writes `λm. ∀ id ∈ d₂. {…}`. A map comprehension
  `λm. {id ↦ … | id ∈ dom(d₂)}` says what's meant. D-Add uses `default(fd)`
  where D-Update uses `init(d₂[id])`.
- D-Rm writes `r ⊎ id`. Now that `r` is a list of intervals with set notation
  (`sec:proto-desc`, "Reserved Field Numbers"), `r ∪ {id}` is consistent.
  D-ResAdd has `r₁ ⊆ r₂` as a premise of one rule, but it's an invariant every
  structural rule should keep (E1, option 1).
- Rule names differ between the sections: T-StrByt/T-BytStr/F-Msg in
  `sec:framework` versus T-Str-Byte/T-Byte-Str/T-Msg in `sec:proto-relations`,
  and `sec:framework` mentions an "F-Field" case that is K-Field.
- Possible addition: `fixed32 ↔ sfixed32` and `fixed64 ↔ sfixed64` are
  officially compatible, and they are a meaningful two's-complement
  reinterpretation. A T-Fixed rule (`toSigned_w`/`· % 2^w`) would cover them in
  the same way as T-Varint.

## What's Solid

The overall three-tier architecture (value / type / message) is right and
mirrors what worked in `Compatible.lean` (≺/∝/⋘ /≼). The 10-byte negative-int
observation is correct and is exactly why Int-Uint/Uint-Int work cross-width.
The "new fields may join oneofs, existing ones may not move" instinct matches
both the official guidance and what soundness requires.

*(2026-10-28)* The rewrite is a large improvement. The coercion framing with
the `U ⊆ dom(d₁) ∖ dom(d₂)` faithfulness clause is the right definition, and it
neatly kills the "skip and default" trivial coercion. T-Varint plus the two
tables replaces about 30 rules, and every derived cell checks out. The
`¬Packable` premise on rep→singular is exactly the right packed-encoding
condition. The symbol table with N-Unfold/`fix` is a clean way to handle
recursion, and the nested strong induction (depth outside, derivation inside)
in `sec:framework` is the right proof shape for it.
