# CLAUDE.md: The Report

`latex/` holds the Pollux report, **the single source of truth** for the project. The Lean formalization implements the setup and techniques described here.

## Read-Only for Claude

**Only the author modifies anything in this directory**, and that includes this file. Don't edit, create, move, or delete files here, whether through the edit tools or the shell. Don't build the report either (`make`, `latexmk`); builds write here and the author runs them. `.claude/settings.json` denies `Edit`/`Write` under `latex/`.

To propose a change to the report, or to this file, write a note in `notes/` (see `notes/README.md`). It can include replacement LaTeX.

Reading is expected. Before formalizing anything, read the whole relevant section, not just the definition: the prose around a definition often fixes its intent.

## Layout

`pollux.tex` is the root: preamble, notation macros, and the `\input` order below. The rendered `pollux.pdf` (if present) may be stale. Read the `.tex`.

| File                              | Label                 | Content                                                                                     |
|-----------------------------------|-----------------------|---------------------------------------------------------------------------------------------|
| `sections/01-intro.tex`           |                       | motivation, versioned formats, impact on verified systems                                   |
| `sections/02-proto-primer.tex`    | `sec:proto`           | the `.proto` language and the wire encoding (varints, tags, zigzag, packed, last-writer-wins) |
| `sections/03-philosophy.tex`      | `sec:philosophy`      | `def:compat`, the compatibility statement every theorem instantiates; parse vs. validate     |
| `sections/05-proto-desc.tex`      | `sec:proto-desc`      | descriptors: syntax, `def:dwf`, `def:dlegal`, `def:dsize`, the seal, omitted features, recursion survey |
| `sections/06-proto-msg.tex`       | `sec:proto-msg`       | values: syntax, totality, carriers, `init`, `def:vvalid`/`def:vwf`/`def:vlegal`, `def:vsize`  |
| `sections/07-proto-trans.tex`     | `sec:proto-transform` | the transform `⟦m⟧`, its theorems, `OneofPreservedAll`, faithfulness                       |
| `sections/08-proto-relations.tex` | `sec:comp-rel`        | value `≺`, type `∝`, and message `≼` relations; varint conversion rules                    |
| `sections/09-type-theoretic.tex`  | `sec:type-theory`     | a type-theoretic view (discussion)                                                          |
| `sections/10-eval.tex`            |                       | evaluation data sources (numbers come from `eval/`)                                         |
| `sections/11-simpl-parse.tex`     | `sec:simpl-parse`     | the simple format (Rocq only)                                                               |
| `sections/12-inter-parse.tex`     | `sec:inter-parse`     | the intermediate format: the frozen `Pollux.InterParse` layer                               |
| `sections/XX-todo.tex`            | `sec:TODO`            | the author's task list: the formalization backlog                                           |

Files named `XX-*` other than `XX-todo.tex` (CBOR, F\*, examples, older compatibility definitions) are **not** `\input` and are not part of the current specification. `tools/tools.tex` is a separate document. `latex-pl-syntax/` is a vendored style package for the syntax figures.

## Reading Conventions

- **Cite by `\label`**, never by section number, because sections get renumbered. Many theorems are unlabeled; cite those by section label and title.
- **Red text** (`{\color{red} …}`) marks open questions or likely changes. Treat it as unsettled: don't formalize against it without asking.
- **"UPDATE: What's implemented right now"** subsections are status snapshots, not specification.
- **`minted` Lean snippets are illustrations** the author maintains, and they lag the code. For example, `sec:proto-msg`'s `Field.init : Field → Val` predates the `Val` → `Slot` rename. A stale snippet is a low-severity drift item. Never rename Lean to match one; names are Lean's call.
- **Implicit side conditions.** The prose sometimes treats representation invariants as ambient. A Lean statement may carry the invariant the report names (`✓_w`), but any other hypothesis the report doesn't state is a finding.

## Notation → Lean

All Lean names are in namespace `Pollux.Proto` unless noted.

| Report                                                      | Lean                                                                                      |
|-------------------------------------------------------------|-------------------------------------------------------------------------------------------|
| descriptor `⟪r, l⟫`, field `⟨c, τ⟩`                           | `Desc` (no reserved set `r` yet), `Field.mk c τ`, `FieldType.scalar`/`.msg`                |
| `SIG`/`OPT`/`REP`/`ONE n` (`\sig`, `\opt`, `\rep`, `\oneof`) | `Cardinality.singular`/`.optional`/`.repeated`/`.oneof n`                                   |
| `IMP p`/`OPT p`/`OPT none`/`REP [...]` (`\impt`, `\optt`, `\rept`) | `Slot.implicit p`/`.optional (some p)`/`.optional none`/`.repeated ps`                    |
| `d[k]`, `m[k]`, `dom(d)`                                    | `d.get? k`, `v.get? k`, keys of `d.explode`                                               |
| `d ✓_w` (`def:dwf`)                                          | `Desc.AllWF` (one layer: `Desc.WF`)                                                       |
| `d ✓_l` (`def:dlegal`)                                       | `Desc.Legal` (per field: `Desc.FieldOk`, `FieldNumber.Valid`)                             |
| `size_d` (`def:dsize`)                                       | `descSize`, `fieldSize`, `fieldTypeSize`, `entryListSize`                                 |
| `m ✓^d` (`def:vvalid`)                                       | `Value.Valid d v` (WF ∧ `Value.Total` ∧ `Value.OneofOk` ∧ entrywise `Slot.Matches`, recursive) |
| `m ✓_w` (`def:vwf`)                                          | `Value.WF` (one layer; nested WF comes through `Value.Valid`)                              |
| `m ✓_l^d` (`def:vlegal`)                                     | no single predicate; its conjuncts are the non-WF parts of `Value.Valid`                   |
| `size_v` (`def:vsize`)                                       | `valueSize`, `slotSize`, `payloadSize`                                                    |
| `init(d)`                                                   | `Value.init d`, `Field.init`; the validity lemma is `Value.init_valid`                    |
| `⟦m⟧` from `d₁` to `d₂` (`\transform`)                        | `Value.reinterpret d₁ d₂ v`; field level `Slot.reinterpret f₁ f₂ x`                       |
| Transformation Specification, `thm:trans-wf/-total/-self/-valid` | `Value.get?_reinterpret`, `Value.reinterpret_wf`/`_total`/`_self`/`_valid`             |
| `OneofPreserved`, `OneofPreservedAll`                       | `Desc.OneofPreserved`, `Desc.OneofPreservedAll`                                           |
| `≺`, `∝`, `≼`, `≪` (`sec:comp-rel`, `thm:faith`)             | not yet in `Pollux.Proto`; the InterParse analogues are `ValCompat`, `FieldCompat`, `MsgCompat`, `DescCompat` (Lean notation `⋘` for the report's `≪`) |
| `E_τ(v, bs)` relational encoding                             | planned `Encodes`                                                                         |
| `enc`/`dec`/`zz`/`σ` varint pipeline (`sec:proto-compat-ints`) | planned varint layer                                                                    |

This table reflects the code as of 2026-09-18. `/report-drift` produces a current, verified comparison.
