# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Pollux is a formally verified Protocol Buffers parser and serializer. Active development is now in **Lean 4** (`lean/`); the older Rocq development is retained for reference (`rocq/`) and documented separately in `CLAUDE-rocq.md`.

The Lean port covers:

- The abstract parser/serializer framework (`Pollux.Parse`)
- The intermediate tagged key-value format (`Pollux.InterParse`)

The full protobuf wire-format layer (`ProtoParse`, `Varint`, `SimplParse`, etc. from the Rocq side) has **not** been ported. All ported files are sorry-free; both top-level correctness theorems (`schemaCorrectInterParseOk` and `idInterParseOk`) are fully proven.

## Build System and Commands

The project uses `lake` for Lean and Nix for reproducible builds.

```bash
# Inside lean/: build everything
cd lean && lake build

# Nix entry point
nix build .#lean-build           # CI-style hermetic build
nix develop                      # dev shell (lean, mathlib cache, aristotle, etc.)
```

Toolchain: `leanprover/lean4:v4.28.0`, single dep is mathlib pinned to `v4.28.0` (see `lean/lean-toolchain` and `lean/lakefile.toml`).

The Nix build (`nix/pollux-lean/default.nix`) is non-trivial: it uses an FOD to fetch mathlib's pre-compiled `.olean` cache (`lake exe cache get`), reconstructs minimal git stubs so Lake's cache validity checks pass, and pre-fetches the ProofWidgets npm tarball. Update the `outputHash` whenever `lake-manifest.json` changes.

CI lives at `.github/workflows/lean.yml` (Linux + macOS, both run `nix build -L .#lean-build`).

## Repository Layout

```
lean/
├── lakefile.toml, lean-toolchain, lake-manifest.json
├── Pollux.lean                          -- root (imports Parse + InterParse)
└── Pollux/
    ├── Parse.lean                       -- umbrella for the abstract framework
    ├── Parse/
    │   ├── Input.lean                   -- `Input` typeclass + `List UInt8` instance
    │   ├── Result.lean                  -- `Level`, `Data`, `Result`, `resultEquiv`
    │   ├── Parser.lean                  -- parser combinators
    │   ├── Serializer.lean              -- dual serializer combinators (phantom `wf`)
    │   └── Theorems.lean                -- `ParseOk` family + combinator correctness
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
            ├── Compatible.lean          -- full cross-descriptor ≺/∝/≪/≼ + `≪` structure
            └── InterParseOk.lean        -- `parseOk_wf` + `schemaCorrectInterParseOk` + `idInterParseOk`
```

Outside `lean/`: `rocq/` (legacy proofs), `pollux-go/` (reference Go implementation), `proto/` (schema versions for evolution tests), `ocaml/` (Rocq extraction target — does not apply to Lean).

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

### `Desc`/`Field` and `Value`/`Val` (`InterParse/Descriptor.lean`)

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

The file also defines several derived metrics and predicates that downstream proofs depend on:

- `descSize` / `fieldSize` / `valueSize` / `valSize` — for well-founded recursion
- `valueDepth` — strictly decreases at nested messages, used as the serializer termination measure
- `valueEncLen`, `valueEncLen'` — encoding-length bounds
- `valid d v` / `valid'` — "every field in the descriptor exists in the value (resp. vice-versa)"
- `valueWf d v` — bound-respecting well-formedness used by `serialValue`
- `willEncode d kv` — per-entry condition: the field exists in `d` and the pair is `valWf`
- `valList d v` / `listToValue d vs` — filter and merge between values and their key-list view

### Compatibility relations

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

The `≼` in both notations is suggestive: these are partial orders on the schema-extension lattice. Neither is the cross-descriptor "full compatibility relation" (value `≺` / field-type `∝` / descriptor-type `≪` / message `≼`) from the written report — that is not implemented. The plumbing anticipates it: `LimitParseOkCompat''` already takes two descriptors, and `limitRecursiveStateCompat_correct` takes a `linkedState : σ → σ → Prop` that both current theorems instantiate with `(· = ·)`.

### `ParseOk` family (`Parse/Theorems.lean`)

The correctness statements for parser/serializer pairs, parameterized over the phantom `wf`:

```
ParseOk''' par ser x enc rest := wf x → ser x = success () enc
                                  → par (app enc rest) = success x rest
ParseOk''  par ser x enc      := ∀ rest, ParseOk''' …          -- fix x, enc
ParseOk'   par ser x          := ∀ enc rest, …                 -- fix x
ParseOk    par ser            := ∀ x enc rest, …               -- full
```

`LimitParseOk*` are the no-trailing-data variants. `LenOk` says the declared length function matches the actual encoding size. These compose: most combinator lemmas (`bind_correct`, `concat_correct`, `rep_correct`, …) take `ParseOk`s on subparts and produce a `ParseOk` on the whole.

### Top-level theorems (`Theorems/InterParseOk.lean`)

```
theorem schemaCorrectInterParseOk (v : Value) (d : Desc) :
  ⟨ v ∷ d ⟩ →
  LimitParseOkCompat'' SchemaCorrectCompatible parseValue serialValue d d v

theorem idInterParseOk (v : Value) (d : Desc) :
  d.AllWF → v.AllWF →
  LimitParseOkCompat'' IdCompatibleWrapper parseValue serialValue d d v
```

The first: for any schema-correct value, `serialValue` followed by `parseValue` recovers a value that is `SchemaCorrectCompatible` with the original under the same descriptor — which, by `schemaCorrectCompatibleEqual`, equals the original.

The second drops schema correctness for `AllWF` (recursive sortedness/no-dups) plus the `valueWf` already carried by `serialValue`, and concludes with the looser `IdCompatible`. It goes through `idCompatTransform`: prove the strengthened statement "parsing yields exactly `idCompatTransform d v`", then compose with `idCompatRoundTrip`.

Both reduce to `limitRecursiveStateCompat_correct` plus per-step correctness; the per-step arguments (`parseVal_serialVal_correct` and `parseVal_serialVal_transform`) are the bulk of the file and use `repCorrectWeakFull` / `repCorrectWeakFullMap` to lift per-entry correctness through `Parser.rep`.

## Working in This Project

### When extending proofs

- The `Theorems/` subdirectory is **layered** for incremental compilation; respect the dependency order (`Primitives → SortedHelpers → Validity → SchemaCorrect → SchemaCorrectCompatible → ValList → IdCompatible → IdCompatibleHelpers → IdCompatibleRoundTrip → Serialization → Compatible → InterParseOk`). Note `IdCompatibleHelpers` imports `ValList`, so `ValList` precedes the `IdCompatible*` group; `Serialization` and `Compatible` only need `Primitives`/`Validity`/`SchemaCorrect` and are otherwise free-floating.
- Anything that needs schema correctness should go through `⟨ v ∷ d ⟩`. Anything about same-descriptor evolution should go through `IdCompatible`; `SchemaCorrectCompatible` is the stricter schema-correct variant. Don't reach into the underlying lists if you can use `get?` / `ext_lookup` / `insert_wf` / `erase_wf` instead — those abstractions exist precisely so callers can ignore the sorted-list encoding.
- `valid'` and `valueWf` overlap: on keys *in* the descriptor `valueWf` is strictly stronger (type match plus bounds plus recursive `valueWf`); on keys *outside* it `valid'` demands `.missing` while `valueWf` demands nothing. Prefer `valueWf` in new statements — it comes for free as `serialValue`'s phantom wf. `Validity.lean` carries parallel decomposition lemmas for both (`valid'_cons` / `valueWf_cons`, `valid'_entry_head` / `valueWf_entry_head`, …), plus `valWfFold_{bool,int,msg}_field` and `valWfFold_missing_elim` for reading a field type off `valWfFold` once the key is known to be in the descriptor. `valid'` survives mainly for `valueEncLength_length` and as the Rocq `Valid'` counterpart; several of its helpers in `IdCompatibleHelpers.lean` are now unused.
- New mutually-recursive functions on `Desc`/`Value` should follow the existing pattern: define the structural size or depth, then prove the relevant `*_smaller` lemma so they can be used as termination measures.

### Aristotle

Some proofs in this codebase were generated/completed with [Aristotle](https://aristotle.harmonic.fun), an automated theorem prover. Its style is heavy on `grind`, `aesop`, `simp_all +decide`, and `exact?`. The `lean/aristotle.nix` derivation packages the Python client; `ARISTOTLE_API_KEY` is read from `../aristotle.txt` by the dev-shell hook.

When editing an Aristotle-generated proof, expect dense tactic blocks. They tend not to be very legible — feel free to rewrite for clarity if you understand what's going on, but the existing form is usually load-bearing.

### Rocq cross-reference

If a Rocq counterpart exists, each Lean file's header docstring names it. `lean/README.org` has the full mapping table, and `lean/rocq-to-lean-guide.org` is a longer porting guide for the syntax/tactic differences. `CLAUDE-rocq.md` (formerly the project CLAUDE.md) documents the legacy Rocq tree.

### Multi-language layout

- **Lean** (`lean/`) — formal specification, current focus of correctness work
- **Rocq** (`rocq/`) — legacy formal development, retained for reference
- **Go** (`pollux-go/`) — reference implementation for cross-checking wire format
- **Protobuf schemas** (`proto/`) — versioned schemas (v1–v5) for schema-evolution testing via `buf`

The OCaml extraction target (`ocaml/`) was for Rocq and is not part of the Lean workflow.
