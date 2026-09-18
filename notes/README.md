# notes/

This directory holds what Claude writes for the author. The report in `latex/` is the single source of truth and only the author edits it, so anything Claude has to say about the report ends up here. That includes Lean-side reasoning the report should absorb. Notes are tracked in git.

## Naming

`YYYY-MM-DD-<kind>-<slug>.md`, dated when written. The kinds:

| Kind        | Written when                                                                                                   |
|-------------|----------------------------------------------------------------------------------------------------------------|
| `finding`   | The report's approach doesn't work in Lean as stated, or Lean needs a decision the report doesn't make. The affected formalization waits on it. |
| `drift`     | `/report-drift` compared a report section with the Lean.                                                       |
| `review`    | The author asked for a critique of a report section.                                                           |
| `rationale` | Lean-side design reasoning worth carrying into the report (the role `lean/proto-design.org` used to play).     |
| `eval`      | A change in `eval/` or `pollux-go/` moved a number or figure the report cites.                                 |

## Header

Every note opens with:

```
Status: open | resolved: <how> (YYYY-MM-DD) | superseded by <file>
Report: <\label>, … @ <short sha>
Lean:   <file or declaration>, … @ <short sha>
```

The author resolves notes, usually by revising the report and sometimes by replying in the note. Claude updates `Status:` once the author has said how a note was resolved. Claude never deletes a note.

## Finding Template

```markdown
# <one-line claim, e.g. "thm:trans-valid is false with one-layer OneofPreserved">

## Summary
What the report says (quote or paraphrase, with `\label`), and what goes wrong in Lean.

## Evidence
The strongest available: a Lean counterexample (as in `lean/Pollux/Proto/OneofCounterexample.lean`),
then an unprovable goal state, then an argument. Include file:line.

## Options
Each candidate fix with its trade-offs, with a recommendation and its reason.

## Suggested report text
Optional LaTeX the author can adapt.

## Blocked
Which Lean work waits on this, and what can proceed meanwhile.
```

## Earlier Notes

These were written before this convention existed and have no header:

- `2026-09-01-review-proto-relations.md`: review of the relations section (then §5, now `sec:comp-rel`).
- `2026-09-08-review-lean-proto-layer.md`: a reader's guide to `Pollux/Proto` as of `e3f436f`, written as source material for the report.
- `2026-09-16-review-type-theory.txt`: transcript of a discussion of `sec:type-theory` against the Lean.
