---
name: aristotle
description: Hand Lean sorries to the Aristotle automated prover (Harmonic) and integrate its results, verifying that no statement or definition changed. Use when proofs are left as sorry, when the author asks to send work to Aristotle, or when Aristotle results are ready to merge.
argument-hint: "prepare [declarations] | status [project-id] | integrate <project-id>"
---

# Aristotle Handoff

Mode and targets: $ARGUMENTS

Aristotle proves; it does not design. Every statement it receives must already be the faithful Lean reading of the report (see `/formalize`). Its output is accepted only if every statement and definition comes back unchanged.

The CLI is `aristotle` (default dev shell). It reads `ARISTOTLE_API_KEY` from the environment, which the dev-shell hook exports. Never print the key.

## prepare

1. **Targets.** List the `sorry`s to hand off (`grep -rn sorry lean/Pollux/`), restricted to the named declarations if any were given. Each target must be a finished statement with a `Report:` citation or a supporting lemma for one.
2. **Builds clean except for the sorries.** `cd lean && lake build`. The only warnings allowed are the targets' `declaration uses 'sorry'`.
3. **Snapshot the statements** so integration can diff against them. Save `git diff HEAD --stat` plus the signature (everything before `:=`) of every target and every definition in the touched files to `<scratchpad>/aristotle-<date>-statements.txt`. If the targets are committed, record the commit sha instead.
4. **Write the prompt.** Name each target (qualified name and file). State the constraints: do not change any statement, definition, or hypothesis; no `native_decide`, no new `axiom`; mathlib only; helper lemmas are fine. Add hints: the relevant existing lemmas, the eliminators (`MsgCompat.ind`/`DescCompat.ind`/`FieldCompat.ind` for the mutual relations), and the `get?`-form specs (`Value.get?_reinterpret`, `Value.get?_init`).
5. **Submit only with the author's go-ahead.** Submitting uploads the whole `lean/` project to Harmonic's service. If the author asked for submission, run it from the repo root:
   ```bash
   aristotle submit "<prompt>" --project-dir lean
   ```
   Otherwise stop here and give the author the exact command. Don't use `--wait`, because runs are long. Report the project id.

## status

`aristotle list --limit 5` or `aristotle show <project-id>`. Report state and recent events.

## integrate

1. Download to the scratchpad, never over the working tree: `aristotle download <project-id> --destination <scratchpad>/aristotle-<id>.tar.gz` (check the actual archive format), then unpack it there.
2. Diff each returned file against the working tree. **For every target and every definition, the text before `:=` must be byte-identical to the snapshot.** If any statement, definition, hypothesis, or instance changed, reject that change and take only the proof body. If Aristotle proved a statement only by altering it, or reports that it is false (e.g. proved the negation), that's a finding for `notes/`, since the report's claim may be wrong.
3. Copy over accepted proof bodies and any new helper lemmas. Place helpers near their use and keep the layered import order in `lean/CLAUDE.md`.
4. Run `/lean-check`. It must pass: no `sorry` left in the integrated targets, no `native_decide`, standard axioms only.
5. Leave the proofs as they are. Aristotle's style (`grind`, `aesop`, `simp_all +decide`) is dense but load-bearing. Tidy one only if you understand it fully and the author wants it.
6. Report which targets are now proven, which are still `sorry`, and anything rejected and why. Don't commit unless asked. The history's convention is "Integrate aristotle output for …".
