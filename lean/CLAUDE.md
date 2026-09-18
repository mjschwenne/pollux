# CLAUDE.md: Lean Formalization

This file covers work under `lean/`. The repository-wide rules in the root `CLAUDE.md` apply here too, above all this one: **the report in `latex/` is the single source of truth, and this formalization implements its setup and techniques.** This file covers how the Lean is built, organized, and extended.

The development has three layers:

- `Pollux.Parse`: the abstract parser/serializer framework.
- `Pollux.InterParse`: the intermediate tagged key-value format. It is **complete and frozen**. `schemaCorrectInterParseOk`, `idInterParseOk`, and the cross-descriptor `compatInterParseOk` are fully proven, and the layer is the artifact documented in the report's `sec:inter-parse`. Don't refactor it. Its details (relations, top-level theorems, conventions) are in `Pollux/InterParse/CLAUDE.md`, which loads when you work in that directory.
- `Pollux.Proto`: the real protobuf layer. It is **in progress**, and new correctness work goes here. The sealed descriptor kernel and the value layer (validity, the `reinterpret` transform) exist; the wire format, parser, serializer, and compatibility relations do not. It succeeds Rocq's `ProtoParse`/`Varint`/`SimplParse` rather than porting them.

## Relationship to the Report

### Where each part of the report lands

| Report (`\label`)                                                                                    | Lean                                                                                   | Status (2026-09-18)                                                                                     |
|------------------------------------------------------------------------------------------------------|----------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------|
| `sec:philosophy`, `def:compat`                                                                       | `Parse/Theorems.lean`: the `ParseOk` family, `LimitParseOkCompat''`                    | in place                                                                                                |
| `sec:proto-desc` (`def:dwf`, `def:dlegal`, `def:dsize`)                                              | `Proto/Descriptor.lean`, `Proto/SortedMap.lean`, `Desc.Legal` in `Proto/Validity.lean` | in place, except the reserved set `r` of `fig:proto-desc-syn`, which is not modeled                     |
| `sec:proto-msg` (`sec:value-totality`, `def:vvalid`, `def:vwf`, `def:vlegal`, `def:vsize`)           | `Proto/Value.lean`, `Proto/Validity.lean`                                              | in place                                                                                                |
| `sec:proto-transform` (`thm:trans-wf`, `thm:trans-total`, `thm:trans-self`, `thm:trans-valid`)       | `Proto/Transform.lean`, `Proto/OneofCounterexample.lean`                               | in place; scalar retyping deferred                                                                      |
| `sec:proto-transform` (`thm:faith`, `thm:pointwise-compat`)                                          | none yet                                                                               | waits on the descriptor relation `≪` and type relation `∝`                                              |
| `sec:comp-rel` (value `≺`, type `∝`, message `≼`, varint rules `sec:proto-compat-ints`)              | none yet                                                                               | not started                                                                                             |
| `sec:type-theory`                                                                                    | none                                                                                   | discussion only                                                                                         |
| `sec:simpl-parse`                                                                                    | Rocq only (`SimplParse.v`)                                                             | not ported                                                                                              |
| `sec:inter-parse` (`thm:inter-schema-correct`, `thm:inter-id-compat`, `thm:inter-compat`)            | `Pollux/InterParse/` (label map in its `CLAUDE.md`)                                    | complete, frozen                                                                                        |
| `sec:TODO`                                                                                           | the backlog                                                                            |                                                                                                         |

The status column is a snapshot; run `/report-drift` for a current comparison. Refer to the report by `\label`, never by section number: sections get renumbered (the relations section has been both §5 and §8).

### Citing the report in Lean

When a declaration implements a report item, its docstring says so, e.g. `Report: thm:trans-valid.` For an unlabeled item, give the enclosing section's label and the item's title: `Report: sec:proto-transform, "Transformation Specification".` Existing files predate this convention, so add citations to declarations as you touch them.

### `proto-design.org` is frozen

`lean/proto-design.org` is the record of how the Proto design was reached: the container experiments, the seal, the recursion survey, and the oneof and totality decisions. Read it for context, but don't update it. Where it and the report disagree, the report wins. New rationale goes in a `notes/` finding for the author to carry into the report.

The operative rules in "The Proto layer" below are the Lean-side consequences of the report's design, i.e. how to write Lean that stays within it. If one of them conflicts with the current report, that's drift: record it and don't pick a side.

## Build and Toolchain

```bash
cd lean && lake build      # incremental build
nix build .#lean-build     # hermetic build, from the repo root (also the flake default)
```

Toolchain: `leanprover/lean4:v4.28.0`. The single dependency is mathlib `v4.28.0` (see `lean-toolchain` and `lakefile.toml`). `lean/flake-module.nix` reads the toolchain file through `lean4-nix` and provides the `.#lean` dev shell.

The Nix build (`lean/package.nix`) is non-trivial. It uses an FOD to fetch mathlib's pre-compiled `.olean` cache (`lake exe cache get`), reconstructs minimal git stubs so Lake's cache validity checks pass, and pre-fetches the ProofWidgets npm tarball. Update the `outputHash` whenever `lake-manifest.json` changes.

CI (`.github/workflows/lean.yml`) runs `leanprover/lean-action` on Linux and macOS with `lake-package-directory: lean/`; it does not go through Nix.

`lake build` reports `sorry` only as a warning, so a green build does not mean the code is sorry-free. `/lean-check` checks for `sorry` and also checks axioms.

## Repository Layout

```
lean/
├── lakefile.toml, lean-toolchain, lake-manifest.json
├── flake-module.nix, package.nix        -- dev shell + hermetic `lean-build` package
├── aristotle.nix                        -- packages the Aristotle Python client
├── proto-design.org                     -- FROZEN record of how the Proto design was reached
├── README.org, rocq-to-lean-guide.org   -- Rocq ↔ Lean file map, porting guide
├── Pollux.lean                          -- root (imports Parse + InterParse + Proto)
└── Pollux/
    ├── Parse.lean                       -- umbrella for the abstract framework
    ├── Parse/
    │   ├── Input.lean                   -- `Input` typeclass + `List UInt8` instance
    │   ├── Result.lean                  -- `Level`, `Data`, `Result`, `resultEquiv`
    │   ├── Parser.lean                  -- parser combinators
    │   ├── Serializer.lean              -- dual serializer combinators (phantom `wf`)
    │   └── Theorems.lean                -- `ParseOk` family + combinator correctness
    ├── InterParse.lean, InterParse/     -- FROZEN intermediate format; see InterParse/CLAUDE.md
    ├── Proto.lean                       -- umbrella for the protobuf layer (in progress)
    └── Proto/
        ├── Descriptor.lean              -- sealed descriptor kernel: Desc/Field/FieldType,
        │                                   --   `explode` interface, WF/AllWF, sizes
        ├── SortedMap.lean               -- payload-parameterized sorted sigma-list theory,
        │                                   --   shared by Desc and Value
        ├── Value.lean                   -- Value/Slot/Payload, unsealed map interface, sizes,
        │                                   --   defaults, Field.init/Value.init, Value.Total
        ├── Validity.lean                -- Desc.Legal, Value.OneofOk, Payload.MatchesScalar,
        │                                   --   Value.Valid/Slot.Matches/Payload.Matches,
        │                                   --   Value.valid_of_get?, Value.init_valid
        ├── Transform.lean               -- Value.reinterpret: the value a cross-descriptor
        │                                   --   round trip yields, plus its `get?` spec,
        │                                   --   Desc.OneofPreserved{,All}, reinterpret_self,
        │                                   --   reinterpret_valid
        └── OneofCounterexample.lean     -- why reinterpret_valid needs the *recursive*
                                            --   oneof condition: an explicit witness
```

## Core Abstractions

### `Input` typeclass (`Parse/Input.lean`)

Lean's replacement for the Rocq module functors. Abstracts over the concrete byte-sequence representation by bundling:

- An element type `C` and operations (`length`, `view`, `toInput`, `charAt`, `app`, `drop`, `slice`)
- Algebraic laws relating them (`app_assoc`, `drop_app`, `slice_app`, `view_length`, …)
- `IsRemaining input remaining` — the suffix relation used everywhere a parser threads input

The single concrete instance is `Input (List UInt8)` (the project's `ByteInput`). Everything in `Parse` and `InterParse` is written generically against `[Input ι]` until the InterParse layer fixes `ι := List UInt8`.

### `Result ι α` (`Parse/Result.lean`)

The unified return type for parsers and serializers:

- `success result enc` — `result : α`, `enc : ι` is the remaining input (parser) or produced encoding (serializer)
- `failure level data` — `level : Level` is `fatal` or `recoverable`; `data : Data ι` is a linked error chain

`resultEquiv` (`≡ᵣ`) is the equivalence used in correctness proofs — it ignores error messages so that proofs aren't coupled to specific error strings.

### `Parser ι α` and `Serializer ι α wf` (`Parse/Parser.lean`, `Parse/Serializer.lean`)

```
abbrev Parser ι α            := ι → Result ι α
abbrev Serializer ι α (_wf)  := α → Result ι Unit
```

Serializers carry a **phantom well-formedness predicate** `wf : α → Prop`. Computationally it does nothing; in theorem statements it specifies which values the serializer is allowed to encode. Combinators compose these predicates (e.g. `concatWf wfα wfβ = fun (a, b) => wfα a ∧ wfβ b`, `bindWf`, `repWf`, …).

The combinator set includes the usual suspects: `bind`/`bindSucceeds`/`bindResult`, `concat`/`depConcat`/`concatMap`, `or`, `opt`, `rep`/`repN`, `map`/`partMap`, `len`/`len'`, `recursiveState`/`recurSt` (recursion threading state, with a measure for termination).

### `ParseOk` family (`Parse/Theorems.lean`)

The correctness statements for parser/serializer pairs, parameterized over the phantom `wf`:

```
ParseOk''' par ser x enc rest := wf x → ser x = success () enc
                                  → par (app enc rest) = success x rest
ParseOk''  par ser x enc      := ∀ rest, ParseOk''' …          -- fix x, enc
ParseOk'   par ser x          := ∀ enc rest, …                 -- fix x
ParseOk    par ser            := ∀ x enc rest, …               -- full
```

`LimitParseOkCompat'' R par ser d₁ d₂ x` is the cross-descriptor, relational form every top-level round-trip theorem instantiates, and the Lean reading of the report's `def:compat`: if the serializer encodes `x` under `d₁` (and `wf d₁ x`), the parser under `d₂` consumes all of it and returns some `x'` with `R d₁ d₂ x x'`. `limitRecursiveStateCompat_correct` is the combinator lemma that proves it for recursive-stateful parsers, taking a `linkedState` hypothesis that relates the two descriptors (InterParse fills it with `(· = ·)` or `⋘`).

`LimitParseOk*` are the no-trailing-data variants. `LenOk` says the declared length function matches the actual encoding size. These compose: most combinator lemmas (`bind_correct`, `concat_correct`, `rep_correct`, …) take `ParseOk`s on subparts and produce a `ParseOk` on the whole.

## The Proto layer (`Pollux/Proto/`) — in progress

`Pollux.Proto` is the real-protobuf successor to `InterParse`. Two pieces exist: the **sealed descriptor kernel** (`Proto/Descriptor.lean`) and the **value layer** (`SortedMap.lean`, `Value.lean`, `Validity.lean`, `Transform.lean`), both `sorry`-free. The parser, serializer and compatibility relations are still absent. The specification is the report (`sec:proto-desc`, `sec:proto-msg`, `sec:proto-transform`, `sec:comp-rel`); `lean/proto-design.org` is the frozen record of the experiments behind it. Operative rules (the Lean-side consequences of that design; if one conflicts with the current report, record the drift rather than follow either blindly):

- **The list encoding is sealed by convention.** `Desc` stores its field map as a sorted sigma list, but outside `Proto/Descriptor.lean` nothing may mention `Desc.entries`, `sortedInsert`, or any list lemma. The public interface is `explode : Desc → Finmap (fun _ : Int => Field)` — a one-layer unwrap into a genuine mathlib map with nested message descriptors staying sealed `Desc` handles — plus `get?`/`insert`/`erase`/`ofList`/`∅`. This is possible because positivity constrains constructor arguments, not functions out of the type. Lean's `private` is file-scoped, so the seal is enforced by review, not the language; the parser/serializer implementation files may reach the representation, theorem *statements* may not.
- **WF discipline**: `Desc.WF` is a single `Pairwise` (sortedness; no-dup keys is derived, `WF.nodupKeys`). Interface lemmas are WF-free wherever possible — `explode_insert` and both `get?_insert` lemmas hold unconditionally because the `Finmap` quotient absorbs the invariant; only the `erase` laws at the erased key and `eq_of_explode_eq` (WF descriptors are canonical representatives) need `WF`.
- **Recursion through descriptors goes through the interface**: `descSize_lt_of_get?_msg` is the termination lemma — anything recursing into a nested message obtained via `get?` uses well-founded recursion on `descSize`. `Desc.AllWF` is *defined* this way, directly in its one-layer form; there is no structural `fieldListAllWF` analogue to keep in sync.
- Field numbers are `Int` (continuity with the InterParse relations); the protobuf range bounds (1 to 2^29−1, reserved 19000–19999) belong in the serializer-layer validity predicate, like `valueWf`'s bounds in InterParse.
- Oneof membership is a **presence mode**, not structure: `Cardinality.oneof (group : Nat)` transcribes `FieldDescriptorProto.oneof_index` (descriptor form is flat; the folded `.proto` block is surface syntax protoc desugars). Group tags are only ever compared *within* one descriptor — tag-equality is the grouping; cross-descriptor compatibility will compare induced partitions, never raw tags. At-most-one-member-set belongs to the serializer validity predicate, cross-member last-wins to the future `Encodes` spec; the tag is dormant until those exist. Synthetic proto3-`optional` oneofs import as `.optional`. Map fields need no descriptor support: the wire format defines `map<K,V>` as `repeated MapEntry`, so they arrive pre-desugared (key-type restrictions go to the validity predicate).
- Values are **unsealed** — they are the induction skeleton of the round-trip proofs. The seal asymmetry is deliberate: descriptors are observed one layer at a time; values are traversed. `Value.entries` is public and `Value.get?` is plain `dlookup`, with no `Finmap` in between.
- **The container type cannot be shared, but the theory can.** A parameterized synonym (`abbrev SortedList (β : Type) := List ((_ : Int) × β)`) used as a constructor argument is rejected by the kernel — for `abbrev` as well as `def`, since the declaration reaching the kernel still names the synonym. Each inductive writes `List ((_ : Int) × _)` out in full; `Proto/SortedMap.lean` carries `sortedInsert`/`WF`/lookup laws/extensionality for a general payload and both instantiate it.
- **Values are total over their descriptor.** `Value.Total d v` is exact domain equality: a valid value has an entry for every declared field, with absence expressed *inside* the presence wrapper (`optional none`, `repeated []`). This is protobuf's data model, not an artifact — implicit presence means the default is indistinguishable from unset. `Value.init d` is the value denoted by silence, and totality is what makes the same-descriptor round trip an identity rather than a transform. Totality is **descriptor-relative**, so evolution is fine: `Total d₁ v` is a hypothesis, `Total d₂ (reinterpret d₁ d₂ v)` a lemma. Do not look for a state in which a value is "not yet total".
- The value shape is **three-valued** though `Cardinality` is four-valued: oneof members are `optional`-shaped, and at-most-one-member-set is the cross-field `Value.OneofOk`, quantified over *pairs* of keys.
- **Scalar carriers**: the twelve integer types share one `Int` carrier (they differ only in encoding and range, both recorded by the descriptor; ranges go to `Payload.MatchesScalar`), and `float`/`double` carry IEEE-754 **bits** (`UInt32`/`UInt64`), never Lean's `Float` — it is opaque, has no equational theory, and IEEE equality is not reflexive. Bit carriers are width-exact, so they need no range condition. `string` is `String` provisionally; the fallback is bytes plus a UTF-8 conjunct.
- **Implicit presence applies only to scalars** (proto3 singular message fields have explicit presence). Recorded in `Desc.FieldOk`; it is why `Payload.isDefault` needs no `DecidableEq` and why `Field.init`'s `singular`/`msg` arm is unreachable.
- Schema rules live descriptor-side (`Desc.Legal`: field-number range, the presence rule, recursive via `descSize`), value well-formedness value-side (`Value.Valid`, structural on the value with the descriptor consulted by `get?` — InterParse's `valueWf` pattern, so no termination measure needed).
- **The drop rule is back.** Real tags carry a wire type, so unknown fields are skippable and `Value.reinterpret` drops writer-only keys by construction — unlike InterParse's `≪`, which had no drop rule because `parseVal` desynchronized. Unknown-field *preservation* (protobuf ≥ 3.5) is deliberately not implemented; it would put unparsed bytes in the induction skeleton.
- `Value.reinterpret` is driven by the **reader's** field list (it must produce a value total over `d₂`), terminating on `descSize d₂` via `fieldSize_lt_of_mem` — the first real consumer of the kernel's termination interface. Measures are scaled by 4 with per-step offsets; a lexicographic pair does not work. Scalar *retyping* is deferred: only equal scalar types carry across today.
- **The oneof side condition on `reinterpret_valid` must be recursive.** `Desc.OneofPreserved d₁ d₂` is one-layer — it quantifies over pairs of keys of `d₁` and `d₂` themselves — but the transform recurses into nested message fields, where the reader may group fields the writer left independent. With only the one-layer hypothesis the theorem is **false**, and `Proto/OneofCounterexample.lean` proves it so: a witness with no oneof at the top layer and two `bool` fields grouped only by the reader one layer down, satisfying every hypothesis while the transform's output violates `Value.OneofOk` inside the nested message. Strengthening the *writer* side does not help — the same witness has `d₁.AllWF` and `d₁.Legal`. The hypothesis in force is `Desc.OneofPreservedAll`, the recursive closure, defined by well-founded recursion on `descSize d₂` in the `AllWF`/`Legal` style and recursing exactly at shared keys where **both** sides declare `.msg`, which is exactly where the transform recurses. Where writer and reader disagree on a key's shape the reader gets `Field.init`, which is never `optional (some _)` (`Field.init_ne_optional_some`), so no oneof obligation arises there. The one-layer form is kept because the counterexample needs it to state the refutation; use `OneofPreservedAll.oneLayer` to get from one to the other.
- **Build values with `Value.valid_of_get?`, not `valid_of_mem`.** Both are introduction rules for `Value.Valid`, but `valid_of_mem`'s payload hypothesis ranges over `v.entries`, and since both `Value.init` and `Value.reinterpret` are *defined* by mapping over the descriptor's entry list, discharging it drags the proof through `Desc.get?_eq_dlookup` — a seal breach in a file whose business is statements. `valid_of_get?` states the same condition through `get?` on both sides (totality supplies the declaration per entry, `v.WF` turns membership into a lookup), which lines up with the `get?`-form specs the callers already have (`Value.get?_init`, `Value.get?_reinterpret`). Both consumers are shorter for it.
- Planned but not yet present (the report's `sec:TODO` and the "Omitted Protobuf Features" list in `sec:proto-desc` are the authority on scope and order; `proto-design.org` has the history): reserved field numbers, varint primitives and the rest of the wire format, a *relational* encoding spec `Encodes` (spec-compliant parsers must accept arbitrary field order — the functional serializer becomes its soundness leg), enums (they need a name table), and the flat symbol-table representation for recursive message types — the 2026-08 corpus survey (in `proto-design.org`) settled when it's needed: not for the current milestone (~93% of surveyed real-world messages are tree-representable), but unavoidably once the `FileDescriptorSet` import path arrives, since `descriptor.proto` is itself recursive (`explode` is the interface that makes that swap non-breaking).

## Working in This Project

### When extending proofs

- **New statements come from the report.** A definition or theorem you add to `Pollux.Proto` should be the Lean reading of a report item, with a `Report:` citation in its docstring. Supporting lemmas need no citation. If the Lean you need has no report counterpart, or contradicts one, apply the stop-and-write-a-finding rule from the root `CLAUDE.md`. `/formalize` walks through this.
- **`main` stays sorry-free.** A `sorry` may exist only transiently, as a target handed to Aristotle or as a step in a proof you are actively writing. Never leave one in a commit, and never "prove" a statement by weakening it.
- InterParse conventions (the `Theorems/` layering, which relation to reach for, `valid'` vs `valueWf`, termination measures) live in `Pollux/InterParse/CLAUDE.md`.
- **Keep the axiom set standard.** Every theorem in `lean/Pollux` depends only on `propext`, `Classical.choice` and `Quot.sound`; check with `#print axioms`. In particular don't reach for `native_decide` — it pulls in `Lean.ofReduceBool` and `Lean.trustCompiler`, and the one place that used it (`sc_dom_eq`'s base case) turned out to be `rfl`.

### Aristotle

Some proofs in this codebase were generated/completed with [Aristotle](https://aristotle.harmonic.fun), an automated theorem prover. Its style is heavy on `grind`, `aesop`, `simp_all +decide`, and `exact?`. The `lean/aristotle.nix` derivation packages the Python client (the `aristotle` CLI, in the default dev shell); `ARISTOTLE_API_KEY` is read from `../aristotle.txt` by the dev-shell hook.

The division of labor: Claude writes statements that match the report and leaves `sorry`s; Aristotle fills them; Claude integrates and verifies that **every statement and definition came back unchanged**. The procedure is in `/aristotle`. Submitting uploads the Lean project to Harmonic's service, so do it only when the author has asked for it.

When editing an Aristotle-generated proof, expect dense tactic blocks. They tend not to be very legible — feel free to rewrite for clarity if you understand what's going on, but the existing form is usually load-bearing.

### Rocq cross-reference

If a Rocq counterpart exists, each Lean file's header docstring names it. `lean/README.org` has the full mapping table, and `lean/rocq-to-lean-guide.org` is a longer porting guide for the syntax/tactic differences. `rocq/CLAUDE.md` documents the legacy Rocq tree.

