---
name: report-drift
description: Compare a section of the LaTeX report with the Lean formalization, item by item, and write a drift note to notes/. Read-only for both report and Lean. Use when asked whether Lean matches the report, what's left to formalize, what changed after the author revised a section, or before starting work on a section.
argument-hint: "[section \\label or file, e.g. sec:proto-transform; default: the Proto sections]"
---

# Report ↔ Lean Drift

Scope: $ARGUMENTS. If empty, use `sec:proto-desc`, `sec:proto-msg`, `sec:proto-transform`, and `sec:comp-rel`.

This skill only observes. It edits neither the report nor the Lean. Its output is a note and a summary.

## 1. Inventory the report

Read the scoped section files in full (`latex/CLAUDE.md` maps labels to files). List every formal or checkable item:

- syntax figures (the fields and constructors each grammar category has)
- definitions, lemmas, and theorems, labeled or not
- relation rules (`\infer`/`mathpar` blocks)
- `minted` Lean snippets
- prose claims about the Lean ("the Lean formalization does X", "at the moment, Y is implemented")

Note red text and "UPDATE" subsections as such; they are not specification.

## 2. Find each item's counterpart

Use the notation table in `latex/CLAUDE.md` and grep `lean/Pollux/`. **Open the Lean statement and compare it clause by clause**: hypotheses, quantifier order, conclusion, and what a definition actually computes. A matching name proves nothing.

## 3. Classify

| Mark      | Meaning                                                                                             |
|-----------|-----------------------------------------------------------------------------------------------------|
| match     | Lean implements the item as stated.                                                                  |
| differs   | Both exist and disagree. Say exactly how.                                                            |
| report-only | Not in Lean yet: formalization backlog.                                                            |
| lean-only | Lean has it and the report doesn't describe it: a candidate for the report.                           |
| stale     | A snippet, name, or status claim in the report that lags the code (low severity).                     |

For `differs`, add evidence on which side looks newer (`git log -1 --format=%cs -- <lean file>` against the report's own claims and commit), but **don't pick a winner**. The author decides. If a difference means a report theorem is actually false, or not provable as stated, that belongs in a `finding` note instead (template in `notes/README.md`).

## 4. Write the note

Write `notes/YYYY-MM-DD-drift-<scope>.md` with the standard header (both commit shas) and:

1. a summary table: item, report location, Lean declaration (`file:line`), mark
2. a short section per `differs` item: the report says…, the Lean says…, which side looks newer and why
3. the `report-only` items grouped as a backlog, in the order the report's dependencies imply

If a drift note already exists for this scope, write a new dated one and mark the old one `superseded by`.

## 5. Summarize to the author

Give counts per mark, list the `differs` items that matter most, and link the note. Don't propose Lean changes for `differs` items until the author has settled them.
