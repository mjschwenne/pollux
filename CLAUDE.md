# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository. Each component has its own `CLAUDE.md`, loaded when you work in that directory; this one holds what applies everywhere.

## Project Overview

Pollux is a verification project on the compatibility of data descriptors: when can bytes written under one Protocol Buffers schema be read under another, and what does the reader get? It pairs a written report with a Lean 4 formalization, plus tooling that grounds both in real-world protobuf usage.

| Directory    | What it is                                                                      | Guide                 |
|--------------|---------------------------------------------------------------------------------|-----------------------|
| `latex/`     | The report: **the single source of truth**. Read-only for Claude               | `latex/CLAUDE.md` (author-maintained) |
| `lean/`      | Lean 4 formalization of the report                                              | `lean/CLAUDE.md`; the frozen InterParse layer has `lean/Pollux/InterParse/CLAUDE.md` |
| `pollux-go/` | Go `pollux` CLI: varint cross-checks, corpus statistics, recursion analysis     | `pollux-go/CLAUDE.md` |
| `eval/`      | Python pipeline that mines real-world `.proto` corpora for the report's numbers | `eval/CLAUDE.md`      |
| `notes/`     | Claude's write-ups for the author: findings, drift reports, reviews            | `notes/README.md`     |
| `rocq/`      | Legacy Rocq development, reference only                                         | `rocq/CLAUDE.md`      |

Also: `proto/` holds versioned schemas (v1–v5) for evolution tests via `buf`; `ocaml/` is the Rocq extraction target and not part of the Lean workflow.

## The Workflow: The Report Leads, Lean Follows

One principle governs this repository: **the LaTeX report in `latex/` is the single source of truth, and the Lean formalization is an implementation of the setup and techniques the report describes.** The author works in the report. Claude and Aristotle complete the formalization behind it.

### Only the author modifies the report

- Never create, edit, move, or delete anything under `latex/`. That covers the `.tex` sections, `pollux.bib`, `makefile`, `latexmkrc`, `flake-module.nix`, `latex-pl-syntax/`, and build outputs. It holds for shell commands too (`sed -i`, redirects, `mv`, `rm`, `git checkout -- latex/…`), not only the edit tools. `.claude/settings.json` denies `Edit`/`Write` under `latex/`; nothing mechanically stops a shell command, so that part is on you.
- Don't build the report (`make`, `latexmk`). Builds write into `latex/`, and the author runs them.
- Reading it is expected: read the relevant section before any formalization work.
- When the report should change, write that up in `notes/`. Suggested wording or LaTeX is welcome there. The author decides and edits. The same goes for `latex/CLAUDE.md`: it lives in the author's directory, so propose changes to it in a note.

### What "Lean follows the report" means

The report fixes the **mechanisms**: data representations, definitions, relations and their rules, theorem statements and their hypotheses, and proof strategies (e.g. transform-then-relate, a sealed descriptor observed through `explode`). Lean implements those. The report does **not** fix Lean's file layout, module structure, or declaration names.

- **Claude's call** (below the report's level of detail): helper lemmas, termination measures, tactics, file and module organization, naming, and refactors that leave every statement unchanged.
- **Needs the report first**: a new definition or a change in one's meaning, a theorem statement or its hypotheses, a relation rule, a change of data representation, and a proof strategy the report would describe differently.

### When they disagree: stop and write a finding

If the report's approach doesn't work in Lean (a theorem is false as stated, a definition doesn't typecheck or terminate as described, a hypothesis is missing), or Lean needs a decision the report doesn't make:

1. Stop work on the affected piece. Don't diverge from the report to get unblocked, and never quietly weaken or strengthen a statement.
2. Write a finding in `notes/` (format in `notes/README.md`). Say what the report says (cite its `\label`), what goes wrong, and the evidence, then lay out candidate fixes with their trade-offs. The best evidence is a Lean counterexample, as `lean/Pollux/Proto/OneofCounterexample.lean` is for the one-layer oneof condition.
3. Tell the author, and carry on with unaffected work.

Existing divergence is handled the same way. Parts of the report were written after the Lean, so they differ in places, and a mismatch alone doesn't tell you which side is stale. Record it (`/report-drift`) instead of "fixing" either side. Once the author settles it, either by revising the report or by confirming the report's version, bring Lean in line.

### Aristotle proves; it does not design

[Aristotle](https://aristotle.harmonic.fun) (Harmonic's automated prover) fills `sorry`s in statements Claude has already written to match the report. Integrating its output includes checking that no statement or definition changed. Use `/aristotle`.

### Skills

| Skill                         | Use it to                                                                 |
|-------------------------------|---------------------------------------------------------------------------|
| `/formalize <report item>`    | Implement a report definition, theorem, relation, or mechanism in Lean    |
| `/report-drift [section]`     | Compare a report section with the Lean and write a drift note             |
| `/aristotle <prepare\|status\|integrate>` | Hand `sorry`s to Aristotle and integrate the results          |
| `/lean-check`                 | Build, scan for `sorry`/`native_decide`, and check axioms                 |

## Build System

The flake uses `flake-parts`. Each component contributes a `flake-module.nix` (`lean/`, `eval/`, `pollux-go/`, `latex/`, `rocq/`), and the root `flake.nix` merges them.

```bash
nix develop               # everything (merges every component shell)
nix develop .#lean        # or .#eval, .#go, .#latex, .#rocq
nix build                 # = .#lean-build (hermetic Lean build)
nix build .#pollux-go     # Go CLI;  .#rocq-build for the legacy proofs
```

The default shell's hook exports `GITHUB_TOKEN` and `ARISTOTLE_API_KEY` from `../gh_pat.txt` and `../aristotle.txt`, files outside the repository. Never print, copy, or commit their contents.

CI: `.github/workflows/lean.yml` (`leanprover/lean-action` on Linux and macOS, on pushes touching `**/*.lean`) and `.github/workflows/rocq.yml` (`nix build -L`).
