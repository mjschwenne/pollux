# CLAUDE.md: InterParse (Frozen)

`Pollux.InterParse` is the intermediate tagged key-value format, the v1 artifact documented in the report's `sec:inter-parse`. It is **complete and frozen**: `schemaCorrectInterParseOk`, `idInterParseOk`, and `compatInterParseOk` are fully proven and sorry-free. Don't refactor it. New correctness work belongs in `Pollux.Proto` (see `lean/CLAUDE.md`).

Come here for reference, e.g. when the Proto layer reuses the transform-then-relate strategy proven here, or when the author asks for a change. Any change needs the author's go-ahead, and the root rules still apply: the report is the source of truth.

## Report ↔ Lean

| Report (`\label`)                                                        | Lean                                                                                  |
|--------------------------------------------------------------------------|---------------------------------------------------------------------------------------|
| `def:ip-desc`, `def:ip-msg`                                              | `Desc`/`Field`, `Value`/`Val` (`Descriptor.lean`)                                     |
| `def:inter-dwf` (`d ✓`)                                                   | `Desc.WF` (recursive: `Desc.AllWF`)                                                   |
| `def:inter-vwf` (`m ✓`)                                                   | `valueWf d v`, `serialValue`'s phantom wf                                             |
| `def:base-pc`, `def:simp-pc`, `def:rpc`                                  | the `ParseOk` family and `LimitParseOkCompat''` (`Parse/Theorems.lean`)               |
| `sec:sc-id-compat`: Schema Correct, `lem:inter-sc-eq`, `thm:inter-schema-correct` | `SchemaCorrect` (`⟨ v ∷ d ⟩`), `schemaCorrectCompatibleEqual`, `schemaCorrectInterParseOk` |
| `sec:full-id-compat`, `thm:inter-id-compat`                              | `IdCompatible`, `idInterParseOk`                                                      |
| `sec:ip-compat-rel` (`≺`, `∝`, `≪`, `≼`), `thm:inter-compat`              | `ValCompat`, `FieldCompat`, `DescCompat` (`⋘`), `MsgCompat` (`⪯`); `compatInterParseOk` |

## Layout

```
lean/Pollux/
├── InterParse.lean                  -- umbrella for the intermediate format
└── InterParse/
    ├── Descriptor.lean              -- Desc/Field, Value/Val, sorted-map ops, valid/wf, sizes
    ├── Parser.lean                  -- byte parsers, `parseValue`
    ├── Serializer.lean              -- byte serializers, `serialValue`
    ├── Theorems.lean                -- re-exports Theorems/
    └── Theorems/
        ├── Primitives.lean          -- byte/unsigned/nat/z32/bool roundtrips
        ├── SortedHelpers.lean       -- sortedInsert/sortedErase commutativity
        ├── Validity.lean            -- validDropFirst, validInsert, depth/length,
        │                               `valid'` + `valueWf` decomposition lemmas
        ├── SchemaCorrect.lean       -- `SchemaCorrect` relation + sc_* lemmas
        ├── SchemaCorrectCompatible.lean  -- `SchemaCorrectCompatible` + schemaCorrectCompatibleEqual
        ├── ValList.lean             -- valList filter + listToValue roundtrip
        ├── IdCompatible.lean        -- `IdCompatible` relation + `idCompatTransform`
        ├── IdCompatibleHelpers.lean -- sorted-cons smart constructors + transform lemmas
        ├── IdCompatibleRoundTrip.lean -- `idCompatRoundTrip`
        ├── Serialization.lean       -- willEncode + weakening + serializer inversion
        ├── Compatible.lean          -- full cross-descriptor ≺/∝/≪/≼, `≪` structure,
        │                               `msgCompat_of_idCompatible`
        ├── CompatTransform.lean     -- `compatTransform d₁ d₂ v` (cross-descriptor
        │                               analogue of `idCompatTransform`) + lookup/WF lemmas
        ├── CompatRoundTrip.lean     -- `compatRoundTrip`: the transform lands in `≼`
        └── InterParseOk.lean        -- `parseOk_wf` + `schemaCorrectInterParseOk` +
                                        --   `idInterParseOk` + `compatInterParseOk`
```

## `Desc`/`Field` and `Value`/`Val` (`InterParse/Descriptor.lean`)

The intermediate format. Schemas (`Desc`) map integer field numbers to types (`Field`); values (`Value`) map integer field numbers to typed payloads (`Val`). Both are mutually inductive so they can contain nested messages:

```
mutual
  inductive Desc  | mk (fs : List (Int × Field))
  inductive Field | msg (d : Desc) | bool | int
end
mutual
  inductive Value | mk (vs : List (Int × Val))
  inductive Val   | msg (v : Value) | bool (b : Bool) | int (z : Int) | missing
end
```

**Why `List (Int × _)` and not a proper map?** Lean's positivity checker rejects mutual inductives that go through `AList`/`Finmap`/`TreeMap`. The fix: store the fields as a list and impose a **sorted, no-duplicate-keys** invariant via `WF`:

- `Desc.Sorted` / `Desc.NodupKeys` / `Desc.WF = Sorted ∧ NodupKeys` (and the same for `Value`)
- `sortedInsert` / `sortedErase` preserve `WF`
- `ext_lookup` is the payoff: well-formed descriptors (resp. values) with the same `get?` are equal

Every constructor in the codebase (`∅`, `insert`, `erase`) preserves `WF`; lemmas use this throughout.

**Lookup after insert carries no `WF` side condition.** `Desc.get?_insert_same` / `get?_insert_ne` and their `Value` analogues (plus `isSome_get?_insert`) hold for *any* underlying list, because `sortedInsert k x` only ever adds or replaces an entry whose key is `k` and leaves every other lookup alone. They are proved from `lookup_sortedInsert_self` / `lookup_sortedInsert_ne`. Prefer them over threading `WF` — several relations (`MsgCompat` especially) carry no well-formedness premises at all, and needing one used to be the only reason `descCompat_isSome` / `descCompat_field` / `descCompat_msg` took a `d₁.WF` argument. Lookup after *erase* still requires `WF`.

The file also defines several derived metrics and predicates that downstream proofs depend on:

- `descSize` / `fieldSize` / `valueSize` / `valSize` — for well-founded recursion
- `valueDepth` — strictly decreases at nested messages, used as the serializer termination measure
- `valueEncLen`, `valueEncLen'` — encoding-length bounds
- `valid d v` / `valid'` — "every field in the descriptor exists in the value (resp. vice-versa)"
- `valueWf d v` — bound-respecting well-formedness used by `serialValue`
- `willEncode d kv` — per-entry condition: the field exists in `d` and the pair is `valWf`
- `valList d v` / `listToValue d vs` — filter and merge between values and their key-list view

## Compatibility relations

These are the heart of the schema-evolution story; understanding them is essential before touching anything in `InterParse/Theorems/`.

**`SchemaCorrect d v`** (`Theorems/SchemaCorrect.lean`, notation `⟨ v ∷ d ⟩`)

A value is *schema-correct* against a descriptor when every entry in `v` exactly matches the type declared in `d`, there are no `V_MISSING` entries, and there are no extra entries. The inductive presentation builds this up by repeated `insert` on disjoint keys with matching field-value types (`fieldValMatch`), recursing structurally on `.msg` fields.

This is the strict relation. The top-level `parseValue`/`serialValue` roundtrip is stated for schema-correct values.

**`SchemaCorrectCompatible d₁ d₂ v₁ v₂`** (`Theorems/SchemaCorrectCompatible.lean`, notation `⟨ v₁ ∷ d₁ ⟩≼⟨ v₂ ∷ d₂ ⟩`)

The schema-evolution relation: when two `(descriptor, value)` pairs both correspond to the "same" message under potentially different schemas. Two constructors:

- `refl` — both pairs are identical and both are schema-correct
- `add` — extend both pairs symmetrically with a new field at the same key, same value, same type

`schemaCorrectCompatibleEqual` is the load-bearing lemma: if `d₁ = d₂` then `v₁ = v₂`. This is what lets the top-level theorem squeeze a `Compatible`-flavored conclusion down to a true roundtrip equality.

**`IdCompatible d v₁ v₂`** (`Theorems/IdCompatible.lean`, notation `⟨ v₁ ≼ v₂ ⟩∷ d`)

Two values compatible under the *same* descriptor, dropping the schema-correct requirement that `SchemaCorrectCompatible` imposes on both sides. The input value may carry fields outside the descriptor (dropped on parse) or omit declared fields (re-injected as `.missing` on parse). Seven constructors: `emp`, `insertInt` / `insertBool` / `insertMsg` (type-matched entries, recursing at nested messages), `drop` (key absent from the descriptor — no constraint on the dropped value), `addMissing` (key declared but absent from the input), and `inputMissing` (`.missing` on both sides at a declared key).

Alongside the relation, `idCompatTransform d v` computes the value a round trip actually yields — drop unknown keys, `.missing` for unmatched declared keys, recurse into nested messages. `idCompatRoundTrip` (`Theorems/IdCompatibleRoundTrip.lean`) proves the transform always lands in the relation; the top-level theorem proves parsing *produces* the transform, then composes. `IdCompatibleWrapper` is the `δ → δ → α → α → Prop` shim that lets it slot into `LimitParseOkCompat''`.

Two caveats worth knowing before extending this:

- `idInterParseOk` is stated under `valueWf d v` alone (it used to also require `valid' d v`, which forbade real values at unknown keys and so left the drop case only half-proven). `valueWf` is vacuous on keys outside the descriptor, which is exactly what makes `drop` reachable.
- `valueWf` still sends `some f, .missing` to `False`, so **`inputMissing` is unreachable from `idInterParseOk`** — `IdCompatible.inputMissing_cons` is currently dead code, and `roundTrip_case4b`'s `.missing` branch is discharged by `valWfFold_missing_elim`. Relaxing that arm of `valueWf` (the serializer already handles the case: `valListFilterP` drops it, `mergeFieldVal` re-injects it) would make the constructor live, but `valueWf` is `serialValue`'s phantom wf, so the change also touches `schemaCorrectInterParseOk` and the `Serialization.lean` inversion lemmas.

The `≼` in both notations is suggestive: these are partial orders on the schema-extension lattice. Neither is the cross-descriptor "full compatibility relation" from the report (`sec:ip-compat-rel`); that one lives in `Theorems/Compatible.lean`, below.

**The full compatibility relation** (`Theorems/Compatible.lean`)

Four mutually-recursive relations transcribing `sec:ip-compat-rel` of the report: `ValCompat v₁ f₁ v₂ f₂` (`≺`, notation `⟨ v₁ ∷ f₁ ⟩≺⟨ v₂ ∷ f₂ ⟩`), `FieldCompat f₁ f₂` (`∝`), `DescCompat d₁ d₂` (`⋘`, the report's `≪`), and `MsgCompat m₁ d₁ m₂ d₂` (notation `⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩`, the report's `≼`). They must share one `mutual` block: `V-Msg → ≼`, `F-Msg → ≪`, `D-Chg → ∝`, `M-Update → ≺` and `∝`. `MsgCompatWrapper` is the shim into `LimitParseOkCompat''`.

The round-trip theorem is **not** here — only the relations plus the `DescCompat` structure lemmas that `limitRecursiveStateCompat_correct` consumes (`descCompat_isSome`, `descCompat_field`, `descCompat_msg`, `fieldCompat_msg_inv`, `fieldCompat_scalar_inv`). The theorem itself is proven as `compatInterParseOk` in `InterParseOk.lean` (via `Theorems/CompatTransform.lean` and `Theorems/CompatRoundTrip.lean`), which is where it consumes them: `LimitParseOkCompat''` already takes two descriptors, and `limitRecursiveStateCompat_correct` takes a `linkedState : σ → σ → Prop` that the two same-descriptor theorems instantiate with `(· = ·)` and that `≪` fills.

Things to know before touching this file:

- **`≼` has eight rules.** They are `sec:ip-msg-rel`'s rules minus `M-Add`, which the report still shows in red: `emp`, `missing`, `declare`, `update`, `drop`, `dropUnknown`, `refl`, `trans`. They differ from the report's *original* eight. `M-Declare` (writer declares a field its own value leaves unset; reader gets `.missing`) was added — without it `≼` cannot follow `IdCompatible.addMissing`, and the cross-descriptor round-trip theorem is false already at `d₁ = d₂`, since `valueWf` permits a value that omits a declared key. It relates the two field types by `f₁ ∝ f₂` rather than equating them, which is also forced: a `D-Chg` on a declared-but-unset key retypes the `V_MISSING` the reader injects, and with `f₁ = f₂` the resulting judgment is underivable (`≺` cannot carry a `.missing` across a type change, and `M-Update` needs the writer's key populated). `F-Refl` recovers the equal-type rule. `M-Add` (reader gains an arbitrary type-matching value at a key the writer never declared) was removed — no round trip produces it, `M-Missing` covers the real case, and keeping it would stop `≼` being readable as a specification of what parsing produces. Both changes are safe in the same direction: `≼` occurs only *positively* in `LimitParseOkCompat''`.
- **`≪` is the asymmetric one.** It occurs *negatively*, as the `linkedState` hypothesis, and has no drop rule. Adding one would make the top-level theorem false: `parseVal`'s `none` branch consumes the tag byte but not the payload, so a reader whose descriptor lacks a key the writer encoded desynchronizes the stream. Consequently `⟨ m₁ ∷ d₁ ⟩⪯⟨ m₂ ∷ d₂ ⟩` does *not* imply `d₁ ⋘ d₂`.
- **`≼` constrains no domains.** `not_msgCompat_dom` proves the natural domain invariant false: composing `M-Declare` with `M-Drop` yields `⟨ ∅ ∷ {0 ↦ int} ⟩⪯⟨ ∅ ∷ ∅ ⟩`. Don't try to recover facts about `dom(m₂)` or `dom(d₁)` from a `≼` derivation.
- **Induction needs the hand-rolled eliminators.** Lean's `induction` tactic refuses mutually inductive types, so use `MsgCompat.ind` / `DescCompat.ind` / `FieldCompat.ind`, which specialize the joint recursor with `True` motives for the other three relations. This works for any motive that doesn't need to *inspect* the sibling relations. All three feed `.rec` one `?_` per constructor across the whole block — currently 5 + 5 + 5 + 8 = 23; adding a rule anywhere breaks all three with a confusing "application type mismatch", and the fix is one more `?_`, not a motive change.
- `msgCompat_of_idCompatible` is the sanity check that `≼` generalizes `IdCompatible` at `d₁ = d₂`. `idCompatible_eq_of_schemaCorrect` records why that check is weak on schema-correct writers: `SchemaCorrect` makes `IdCompatible` degenerate to equality, so the subsumption there is just `M-Refl`.
- `descCompat_wf` lifts `Desc.WF` along `≪`; `not_descCompat_allWF` shows the recursive `AllWF` does *not* lift, because `D-Add` inserts an unconstrained field. So `d₂.AllWF` has to be an explicit hypothesis of the eventual top-level theorem rather than something recovered from `d₁`.

## Top-level theorems (`Theorems/InterParseOk.lean`)

```
theorem schemaCorrectInterParseOk (v : Value) (d : Desc) :
  ⟨ v ∷ d ⟩ →
  LimitParseOkCompat'' SchemaCorrectCompatible parseValue serialValue d d v

theorem idInterParseOk (v : Value) (d : Desc) :
  d.AllWF → v.AllWF →
  LimitParseOkCompat'' IdCompatibleWrapper parseValue serialValue d d v

theorem compatInterParseOk (v : Value) (d₁ d₂ : Desc) :
  d₁.AllWF → v.AllWF → d₂.AllWF → d₁ ⋘ d₂ →
  LimitParseOkCompat'' MsgCompatWrapper parseValue serialValue d₁ d₂ v
```

The first: for any schema-correct value, `serialValue` followed by `parseValue` recovers a value that is `SchemaCorrectCompatible` with the original under the same descriptor — which, by `schemaCorrectCompatibleEqual`, equals the original.

The second drops schema correctness for `AllWF` (recursive sortedness/no-dups) plus the `valueWf` already carried by `serialValue`, and concludes with the looser `IdCompatible`. It goes through `idCompatTransform`: prove the strengthened statement "parsing yields exactly `idCompatTransform d v`", then compose with `idCompatRoundTrip`.

Both reduce to `limitRecursiveStateCompat_correct` plus per-step correctness; the per-step arguments (`parseVal_serialVal_correct` and `parseVal_serialVal_transform`) are the bulk of the file and use `repCorrectWeakFull` / `repCorrectWeakFullMap` to lift per-entry correctness through `Parser.rep`.

The third is the cross-descriptor generalization, proven by the same two-step strategy as `idInterParseOk`: `Theorems/CompatTransform.lean` defines `compatTransform d₁ d₂ v` — the value a cross-descriptor round trip actually yields, a structural recursion over the *reader's* field list reading the writer's descriptor and value by key lookup — the strengthened statement "parsing produces exactly `compatTransform d₁ d₂ v`" goes through `limitRecursiveStateCompat_correct` with `linkedState := fun a b => a ⋘ b ∧ b.AllWF`, and `compatRoundTrip` (`Theorems/CompatRoundTrip.lean`) shows the transform always lands in `≼`, assembling the derivation key by key in increasing key order (the reader's field list drives the walk, since `≪` never removes a key). `d₂.AllWF` is carried in `linkedState` because `validState` is threaded on the writer's descriptor only and `AllWF` does not lift along `≪` (`not_descCompat_allWF`).

## Extending (With the Author's Go-Ahead)

- The InterParse `Theorems/` subdirectory is **layered** for incremental compilation; respect the dependency order (`Primitives → SortedHelpers → Validity → SchemaCorrect → SchemaCorrectCompatible → ValList → IdCompatible → IdCompatibleHelpers → IdCompatibleRoundTrip → Serialization → Compatible → CompatTransform → CompatRoundTrip → InterParseOk`). Note `IdCompatibleHelpers` imports `ValList`, so `ValList` precedes the `IdCompatible*` group; `Serialization` needs only `Primitives`/`Validity`/`SchemaCorrect` and `Compatible` only those plus `IdCompatible`, so both are otherwise free-floating. `CompatTransform` needs the `IdCompatible*` group, `ValList`, and `Compatible`; `CompatRoundTrip` needs `CompatTransform` and `IdCompatibleRoundTrip`.
- Anything that needs schema correctness should go through `⟨ v ∷ d ⟩`. Anything about same-descriptor evolution should go through `IdCompatible`; `SchemaCorrectCompatible` is the stricter schema-correct variant. Anything genuinely cross-descriptor goes through `MsgCompat`/`DescCompat`. Don't reach into the underlying lists if you can use `get?` / `ext_lookup` / `get?_insert_same` / `get?_insert_ne` / `insert_wf` / `erase_wf` instead — those abstractions exist precisely so callers can ignore the sorted-list encoding.
- `valid'` and `valueWf` overlap: on keys *in* the descriptor `valueWf` is strictly stronger (type match plus bounds plus recursive `valueWf`); on keys *outside* it `valid'` demands `.missing` while `valueWf` demands nothing. Prefer `valueWf` in new statements — it comes for free as `serialValue`'s phantom wf. `Validity.lean` carries parallel decomposition lemmas for both (`valid'_cons` / `valueWf_cons`, `valid'_entry_head` / `valueWf_entry_head`, …), plus `valWfFold_{bool,int,msg}_field` and `valWfFold_missing_elim` for reading a field type off `valWfFold` once the key is known to be in the descriptor. `valid'` survives mainly for `valueEncLength_length` and as the Rocq `Valid'` counterpart; several of its helpers in `IdCompatibleHelpers.lean` are now unused.
- New mutually-recursive functions on `Desc`/`Value` should follow the existing pattern: define the structural size or depth, then prove the relevant `*_smaller` lemma so they can be used as termination measures.
