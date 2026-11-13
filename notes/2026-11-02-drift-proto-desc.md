# Drift: `sec:proto-desc` against `Pollux/Proto`

Status: open
Report: sec:proto-desc, fig:proto-desc-syn, def:dwf, def:dlegal, def:dsize, def:ddepth @ 653215e
Lean:   Pollux/Proto/Descriptor.lean, Pollux/Proto/Validity.lean, Pollux/Proto/Value.lean @ 653215e (Lean last changed 487d0bb, 2026-09-14)

The report section was last revised in 653215e (2026-10-28, "Model reserved field numbers"). The Lean descriptor layer hasn't changed since 2026-09-14, so every new item in the report is unimplemented. Related open note: `2026-10-28-finding-descriptor-recursion-symbol-table.org`. It covers message names and Σ, and several items below depend on how it is resolved.

## Summary

| Item | Report | Lean | Mark |
|---|---|---|---|
| `ScalarType` (15 scalars) | fig:proto-desc-syn, minted | `Descriptor.lean:93` | match |
| `Cardinality` (`SIG/OPT/REP/ONE g`) | fig:proto-desc-syn | `Descriptor.lean:119` | match |
| Field `⟨c, τ⟩` | fig:proto-desc-syn | `Field.mk`, `Descriptor.lean:132` | match |
| Field type: `τ_s` or message **name** `a`, resolved by Σ | fig:proto-desc-syn, def:dsize (`Σ(a)`) | `FieldType.msg (d : Desc)` nests the descriptor, `Descriptor.lean:135` | differs (open finding) |
| Descriptor `⟪r, l⟫` with reserved set `r` | fig:proto-desc-syn | `Desc.mk (es)`, no `r`, `Descriptor.lean:129` | report-only |
| Reserved set = list of inclusive ranges `(n₁, n₂)` | fig:proto-desc-syn, sec "Reserved Field Numbers" | none | report-only |
| `contains`, `containsRange`, `add`, `remove` on reserved sets, which preserve legal(d) | sec "Reserved Field Numbers" ("We've also implemented …") | none | report-only (the claim is stale) |
| `wfd`: unique keys, sorted, nested wfd | def:dwf | `Desc.AllWF`, `Descriptor.lean:357` (keys unique as a consequence of strict sorting) | match |
| `wfd`: reserved ranges have `n₁ ≤ n₂` and are sorted by lower bound | def:dwf | none | report-only |
| legal: field numbers in `[1, 2²⁹−1]`, not in `r` | def:dlegal | `FieldNumber.Valid` hard-codes "not in 19000–19999", `Validity.lean:40` | differs |
| legal: 19000–19999 ⊆ `r` | def:dlegal | constant in `FieldNumber.Valid` instead | differs |
| legal: consecutive ranges separated by a gap of at least two (merged) | def:dlegal | none | report-only |
| legal: message fields are always `OPT` | def:dlegal | `FieldOk` only forbids `SIG` on messages (`REP`/`ONE` messages allowed), `Validity.lean:50` | differs |
| legal: nested descriptors legal | def:dlegal | `Desc.Legal`, `Validity.lean:56` | match |
| `size_d` / `size_f` | def:dsize | `descSize`, `fieldSize`, … `Descriptor.lean:306` | differs (constants) |
| `depth_d` / `depth_f` | def:ddepth | none | report-only |
| `explode`, `get?` | minted, sec "Sealed & Unsealed" | `Descriptor.lean:176,180` | match |
| WF needed only for ext. equality, erase, `eq_of_explode_eq` | sec "Sealed & Unsealed" | `explode_erase`, `get?_erase_same`, `eq_of_explode_eq` need WF; `explode_ext` doesn't | match |
| well-founded recursion on size through `get?` | text before def:dsize | `descSize_lt_of_get?_msg`; `AllWF` and `Legal` use it | match |
| oneof as cardinality, tag equality = grouping | sec on oneof | `Cardinality.oneof`, `Value.OneofOk` | match |
| minted `Desc.mk (es : List ((_ : Int) × Field))` | minted | same | stale vs. the report's own figure (no `r`), but matches the Lean |
| "Omitted features: Reserved field numbers … Lean doesn't track it yet" | sec "Omitted Protobuf Features" | (true of Lean) | stale within the report: contradicts the new "Reserved Field Numbers" subsection |
| "Omitted: Recursive Messages … enforces a tree structure" | same | true of Lean | stale vs. fig:proto-desc-syn, which already has names |
| `insert`, `erase`, `ofList`, `ofList_allWF`, `AllWF.insert` | — | `Descriptor.lean` | lean-only |
| Field numbers are `Int` (minted) / `k ∈ ℕ` (figure) | minted vs. fig | `Int` | differs (minor; inside the report) |

Counts: match 9, differs 6, report-only 7, stale 3, lean-only 1 (group).

## Differs

### Message types are names resolved by Σ, not nested descriptors
**The report says:** `τ ::= τ_s | a`, and def:dsize recurses through `Σ(a)`.
**The Lean says:** `FieldType.msg (d : Desc)`. The tree representation can't express recursive messages.
**Newer:** the report (2026-10-28). This is the subject of the open finding `2026-10-28-finding-descriptor-recursion-symbol-table.org`. Under a cyclic Σ, def:dsize, def:ddepth, and the recursive parts of def:dwf and def:dlegal have no well-founded solution. That finding has to be settled first.

### Field-number range and the protoc block 19000–19999
**The report says:** numbers lie in `[1, 2²⁹−1]` and outside `r`, and legality *requires* `[19000, 19999] ∈ r`.
**The Lean says:** `FieldNumber.Valid` excludes 19000–19999 as a constant, with no `r`.
**Newer:** the report. Note that real `DescriptorProto.reserved_range` never contains 19000–19999 (protoc enforces it separately) and uses an *exclusive* end. So the `FileDescriptorSet` import path would have to insert this range and convert the bounds. Decide whether that is intended, or whether the protoc block should stay a constant alongside `r`.

### "Message fields are always explicitly marked as optional"
**The report says:** every message-typed field has cardinality `OPT`.
**The Lean says:** message fields can't be `SIG`. `REP` and `ONE g` are allowed.
**Newer:** the report wording is new, but read literally it rules out `repeated Foo` and message members of a oneof, both common in real schemas. I expect the intent is "never `SIG`", which is what Lean has. Please confirm or reword.

### `size_d` constants
**The report says:** `size(⟪r, []⟫) = 0`, `size_f(⟨c, τ_s⟩) = 1`, `size_f(⟨c, a⟩) = 1 + size_d(Σ(a))`.
**The Lean says:** `descSize = 1 + entryListSize`, `fieldSize = 1 + fieldTypeSize`, scalar `= 1`, msg `= 1 + descSize`. A scalar field therefore counts 2 and an empty descriptor counts 1.
**Newer:** unclear. Only strict decrease matters, and both versions provide it. If the finding's recommendation (drop size as a measure) is adopted, this item goes away.

## Report-only backlog, in dependency order

1. **Reserved range type and its WF:** a range `(n₁, n₂)` with `n₁ ≤ n₂`, kept in a list sorted by lower bound (def:dwf).
2. **`r` in `Desc`:** `Desc.mk (es) (rs)`, carried through `insert`/`erase`. `Desc.WF` gains the range WF. `eq_of_explode_eq` needs `d₁.reserved = d₂.reserved`, because `explode` is fields-only.
3. **Reserved-set operations:** `contains` (`∈`), `containsRange`, `add`, `remove`, with WF preservation.
4. **Legality clauses** from def:dlegal: not in `r`, the protoc block ⊆ `r`, the gap of two (merged), and the `OPT` rule (once settled).
5. **"Operations keep legal(d)":** this needs side conditions. `add` must not cover a declared field number, and `remove` must not remove anything from 19000–19999. The report should say so.
6. **`depth_d`** (def:ddepth): only after the symbol-table finding is settled, since it is infinite on cycles.
