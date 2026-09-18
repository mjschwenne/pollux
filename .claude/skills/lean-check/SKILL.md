---
name: lean-check
description: Verify the Lean formalization. Builds lean/, reports every sorry, flags native_decide and new axioms, and prints the axioms of the declarations that changed. Use after any Lean edit, after integrating Aristotle output, and before saying Lean work is done.
argument-hint: "[declaration names to axiom-check; default: changed declarations]"
---

# Lean Check

A green `lake build` is not enough, because `sorry` is only a warning. Run all four steps and report each result plainly.

## 1. Build

```bash
cd lean && lake build 2>&1 | grep -E "error|warning: declaration uses 'sorry'|^Build" 
```

Any `error` is a failure: stop and report it. The Lean tooling can print long elaboration traces. Quote the first error and its location, not the whole trace.

## 2. Forbidden constructs

```bash
cd lean && grep -rnE "\bsorry\b|\badmit\b|native_decide|^\s*axiom\s|implemented_by|@\[extern" Pollux/
```

- `sorry`/`admit`: list each hit with its declaration. They are allowed only as live Aristotle targets or in a proof being written right now, and never in a commit (see `lean/CLAUDE.md`).
- `native_decide`, `axiom`, `implemented_by`, `extern`: always a failure. `native_decide` pulls in `Lean.ofReduceBool` and `Lean.trustCompiler`.

Ignore hits inside comments or docstrings that merely mention the words, but look at each one before dismissing it.

## 3. Axioms

Collect the declarations to check: the names in `$ARGUMENTS` if given; otherwise every `theorem`/`lemma`/`def` whose line appears in `git diff` or `git diff --cached` under `lean/`, plus new files from `git status`. Use fully qualified names (most Proto declarations live in `Pollux.Proto`, InterParse ones in `Pollux.InterParse`). Check the file's `namespace` if unsure.

Write a scratch file in the session scratchpad (never inside `lean/`):

```lean
import Pollux
#print axioms Pollux.Proto.Value.reinterpret_valid
-- one line per declaration
```

and run it from `lean/`:

```bash
cd lean && lake env lean <scratchpad>/Axioms.lean
```

The only acceptable axioms are `propext`, `Classical.choice`, and `Quot.sound` (or a subset). `sorryAx` means a transitive `sorry`. Anything else is a failure.

## 4. Report

One line each: build (ok / N errors), sorries (none / list), forbidden constructs (none / list), axioms (standard / offenders). If everything passes, say so without hedging.
