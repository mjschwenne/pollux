---
name: formalize
description: Implement an item from the LaTeX report (a definition, theorem, relation, rule set, or proof technique) in the Lean formalization, faithful to the report's setup. Use when asked to formalize, implement, or port something from the report, or to bring Lean in line with a report section the author has settled.
argument-hint: "<report \\label, section, or description of the item>"
---

# Formalize a Report Item

Target: $ARGUMENTS

The report (`latex/`) is the specification and is read-only. You implement what it says. When it can't be implemented as written, you stop and write a finding. You never change the report, and you never quietly change the statement.

## 1. Read the item in context

- Locate it with `grep -rn '<label or key phrase>' latex/sections/`, then read the **whole enclosing section**, plus every definition it references (follow `\ref`s). `latex/CLAUDE.md` has the section map and reading conventions. Red text marks unsettled material, "UPDATE" subsections are status snapshots, and `minted` snippets are illustrations.
- Check `notes/` for open findings or drift notes touching this item. If one is open and blocking, stop and tell the author.
- Find what already exists: the report-to-Lean map in `lean/CLAUDE.md`, then grep `lean/Pollux/` for the concept and its likely names.

## 2. Separate what the report fixes from what it leaves to you

Write down, before touching Lean:

- **Fixed by the report**: the data representation, what each definition means, each theorem's hypotheses and conclusion (quantifier order and direction included), relation rules, and the proof strategy where the report names one.
- **Yours to decide**: names, file placement, helper lemmas, termination measures, tactics.
- **Unresolved**: anything the Lean needs that the report doesn't determine, or that looks wrong. If any item lands here and it affects a statement or definition, go to step 5 for that piece. Formalize the rest.

## 3. Write the statements first

- Translate with the notation table in `latex/CLAUDE.md`. Keep the report's hypotheses one for one. You may add a representation invariant the report itself names (e.g. `✓_w` as `Desc.AllWF`). Any other extra hypothesis is a finding, not a fix.
- Follow the Proto conventions in `lean/CLAUDE.md`: the seal (statements go through `get?`/`explode`, never `Desc.entries`), WF-free interface lemmas where possible, well-founded recursion on `descSize` through `get?`, `Value.valid_of_get?` to build validity, and the standard axioms only.
- Give each implementing declaration a docstring citation: `Report: <\label>.` For an unlabeled item, use the section label plus the item's title.
- Build with `sorry` bodies first (`cd lean && lake build`) to confirm the statements elaborate.

## 4. Prove or delegate

- Prove what is direct. For a hard proof, keep the `sorry` and hand it off with `/aristotle prepare`, or ask the author which they prefer.
- If a proof attempt suggests the statement is **false**, look for a concrete counterexample in Lean (the model is `lean/Pollux/Proto/OneofCounterexample.lean`) and go to step 5.

## 5. When the report can't be followed

Stop work on that piece. Write `notes/YYYY-MM-DD-finding-<slug>.md` using the template in `notes/README.md`: what the report says, the evidence, and the options with a recommendation. Tell the author. Don't adjust the statement to make it provable.

## 6. Finish

Run `/lean-check`. Then report back:

- the report item mapped to its Lean declarations (with `file:line`)
- anything proven versus left as `sorry` (and whether it went to Aristotle)
- findings written, and what they block

Don't commit unless the author asked.
