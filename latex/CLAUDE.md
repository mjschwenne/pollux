# CLAUDE.md: The Report

`latex/` holds the Pollux report, **the single source of truth** for the project. The Lean formalization implements the setup and techniques described here.

## Read-Only for Claude

**Only the author modifies anything in this directory**, and that includes this file. Don't edit, create, move, or delete files here, whether through the edit tools or the shell. Don't build the report either (`make`, `just report`, `latexmk`); builds write here (`auto/`, `_minted/`, `pollux.*`) and the author runs them. `.claude/settings.json` denies `Edit`/`Write` under `latex/`.

To propose a change to the report, or to this file, write a note in `notes/` (see `notes/README.md`). It can include replacement LaTeX.

Reading is expected. Before formalizing anything, read the whole relevant section, not just the definition: the prose around a definition often fixes its intent.

## Layout

`pollux.tex` is the root: preamble, notation macros, and the `\input` order below. The rendered `pollux.pdf` (if present) may be stale. Read the `.tex`.

| File                                | Label                 | Content                                                                                     |
|-------------------------------------|-----------------------|---------------------------------------------------------------------------------------------|
| `sections/01-intro.tex`             |                       | motivation, versioned formats, impact on verified systems                                   |
| `sections/02-proto-primer.tex`      | `sec:proto`           | the `.proto` language and the wire encoding (varints, tags, zigzag, packed, last-writer-wins) |
| `sections/03-philosophy.tex`        | `sec:philosophy`      | parse vs. validate; the two-step parse (`records`, then `assemble` per field)               |
| `sections/04-pollux-framework.tex`  | `sec:framework`       | compatibility as coercion: `def:well-behaved`, `def:compat`, judgments `Σ; Γ ⊢ … ⇝ f`, recursion via the symbol table (`N-Assum`/`N-Unfold`), generic `D-Update`, semantic definitions and soundness (`def:sem-compat*`, `def:soundness`, `cor:compat-sound`), Lean strategy (`sec:log-rel-lean`) |
| `sections/05-proto-desc.tex`        | `sec:proto-desc`      | descriptors: syntax, `def:dwf`, `def:dlegal`, `def:dsize`, `def:ddepth`, reserved field numbers, the seal, omitted features, recursion survey |
| `sections/06-proto-msg.tex`         | `sec:proto-msg`       | values: syntax, totality, carriers, `init`, `def:vvalid`/`def:vwf`/`def:vlegal`, `def:vsize`  |
| `sections/07-proto-parse.tex`       | `sec:proto-parse`     | the Protobuf parser: wire records, wire types, combining records                            |
| `sections/08-proto-trans.tex`       | `sec:proto-transform` | the transform `_{d₁}⟦m⟧_{d₂}`, its theorems, `OneofPreservedAll`, faithfulness              |
| `sections/09-proto-relations.tex`   | `sec:proto-relations` | the Protobuf instance: descriptor `≪` (`sec:desc-rel`), type `≺` (`sec:typ-rel`, varint rules in `sec:proto-compat-ints`), field `∝` and cardinality `≼_{τ₁,τ₂}` rules, each with its coercion |
| `sections/10-eval.tex`              |                       | evaluation data sources (numbers come from `eval/`)                                         |
| `sections/11-simpl-parse.tex`       | `sec:simpl-parse`     | the simple format (Rocq only)                                                               |
| `sections/12-inter-parse.tex`       | `sec:inter-parse`     | the intermediate format: the frozen `Pollux.InterParse` layer                               |
| `sections/XX-todo.tex`              | `sec:TODO`            | the author's task list: the formalization backlog                                           |

Files named `XX-*` other than `XX-todo.tex` (CBOR, F\*, examples, older compatibility definitions) are **not** `\input` and are not part of the current specification. `tools/tools.tex` is a separate document. `latex-pl-syntax/` is a vendored style package for the syntax figures.

## Reading Conventions

- **Cite by `\label`**, never by section number, because sections get renumbered. Many theorems are unlabeled; cite those by section label and title.
- **Red text** (`{\color{red} …}`) marks open questions or likely changes. Treat it as unsettled: don't formalize against it without asking. One exception in meaning, not in handling: in `sec:proto-relations` the red cardinality rules (`K-OptImp`, `K-ImpOpt`, `K-OptRep`, `K-RepOpt`, `K-ImpRep`, `K-RepImp`) are ones the report calls unsound and kept only for reference. They are not part of the relation.
- **`% TODO` comments** in the source mark points the author hasn't settled (e.g. linking `def:soundness` to semantic compatibility). Treat them like red text.
- **`minted` Lean snippets are illustrations** the author maintains, and they lag the code. For example, `sec:proto-msg`'s `Field.init : Field → Val` and the signatures in `sec:proto-transform` predate the `Val` → `Slot` rename. A stale snippet is a low-severity drift item. Never rename Lean to match one; names are Lean's call.
- **Implicit side conditions.** The prose sometimes treats representation invariants as ambient. A Lean statement may carry the invariant the report names (`wfd(d)`, `wfm(m)`), but any other hypothesis the report doesn't state is a finding.

## Notation → Lean

All Lean names are in namespace `Pollux.Proto` unless noted.

| Report                                                      | Lean                                                                                      |
|-------------------------------------------------------------|-------------------------------------------------------------------------------------------|
| descriptor `⟪r, l⟫`, field `⟨c, τ⟩`                           | `Desc` (no reserved set `r` yet), `Field.mk c τ`, `FieldType.scalar`/`.msg`                |
| message name `a`, symbol table `Σ`                           | not yet: Lean nests descriptors directly (`FieldType.msg d`), so no recursive descriptors |
| `SIG`/`OPT`/`REP`/`ONE g` (`\sig`, `\opt`, `\rep`, `\oneof`) | `Cardinality.singular`/`.optional`/`.repeated`/`.oneof g`                                   |
| slots `IMP p`/`OPT p`/`OPT None`/`REP [...]` (`\impslot`, `\optslot`, `\repslot`) | `Slot.implicit p`/`.optional (some p)`/`.optional none`/`.repeated ps`      |
| `d[k]`, `m[k]`, `dom(d)`                                    | `d.get? k`, `v.get? k`, keys of `d.explode`                                               |
| `wfd(d)` (`def:dwf`)                                         | `Desc.AllWF` (one layer: `Desc.WF`)                                                       |
| `legal(d)` (`def:dlegal`)                                    | `Desc.Legal` (per field: `Desc.FieldOk`, `FieldNumber.Valid`)                             |
| `size_d` (`def:dsize`)                                       | `descSize`, `fieldSize`, `fieldTypeSize`, `entryListSize`                                 |
| `depth_d` (`def:ddepth`), message depth `depth_m`            | not yet                                                                                   |
| `m ∷ d` (`def:vvalid`)                                       | `Value.Valid d v` (WF ∧ `Value.Total` ∧ `Value.OneofOk` ∧ entrywise `Slot.Matches`, recursive) |
| `wfm(m)` (`def:vwf`)                                         | `Value.WF` (one layer; nested WF comes through `Value.Valid`)                              |
| `legal_d(m)` (`def:vlegal`)                                  | no single predicate; its conjuncts are the non-WF parts of `Value.Valid`                   |
| `size_m`/`size_s`/`size_p` (`def:vsize`)                     | `valueSize`, `slotSize`, `payloadSize`                                                    |
| `init(d)`                                                   | `Value.init d`, `Field.init`; the validity lemma is `Value.init_valid`                    |
| `_{d₁}⟦m⟧_{d₂}` (`\coercion`)                                | `Value.reinterpret d₁ d₂ v`; lower layers `Slot.reinterpret f₁ f₂ x`, `Payload.reinterpret` |
| Transformation Specification, `thm:trans-wf/-total/-self/-valid` | `Value.get?_reinterpret`, `Value.reinterpret_wf`/`_total`/`_self`/`_valid`             |
| `OneofPreserved`, `OneofPreservedAll`                       | `Desc.OneofPreserved`, `Desc.OneofPreservedAll`                                           |
| judgments `≪`, `∝`, `≺`, `≼_{τ₁,τ₂}` with coercion `⇝ f` (`sec:framework`, `sec:proto-relations`), `thm:faith` | not yet in `Pollux.Proto`; `sec:log-rel-lean` weighs two renderings (derivations in `Type` vs. a `Prop` relation plus agreement with `Value.reinterpret`). The InterParse analogues are `ValCompat`, `FieldCompat`, `DescCompat`, `MsgCompat` (Lean notation `⋘` for that section's `≪`) |
| `⊨_n` semantic compatibility (`def:sem-compat*`, `def:sem-assum`) | not yet                                                                              |
| `Encodes_d(m, bs)`, `records`, `assemble`, `parse_d`, `⊕_τ`   | not yet (planned relational encoding and parser)                                          |
| `enc`/`dec`/`zz`/`σ` varint pipeline (`sec:proto-compat-ints`) | planned varint layer                                                                    |

This table reflects the code as of 2026-10-28. `/report-drift` produces a current, verified comparison.
