Status: open
Report: preamble of pollux.tex; sec:proto, sec:philosophy, sec:proto-desc, sec:proto-msg, sec:proto-parse, sec:proto-transform, sec:proto-relations, sec:type-theory, sec:simpl-parse, sec:inter-parse @ 5f5d68c + uncommitted working tree (2026-10-13)
Lean:   none

# Review: where the report should use macros, and how they're named

The author asked where the report should use macros, and whether its symbols,
especially the notation it defines, are named so the `.tex` says what they mean.
This covers every file `pollux.tex` `\input`s, as they stand in the working tree.

## Summary

The varint block in the preamble (`\encop`/`\decop`/`\zz`/`\tosigned`, with a comment
naming the section it serves) is the model to follow. Most of the rest of the
report's own notation is typed out by hand:

1. **The four relation symbols the report defines (≺, ∝, ≪, ⪯) have no
   macros.** They appear 224 times as raw `\prec`, `\propto`, `\ll`, `\preceq`, and
   `\preceq` means three different relations. This is the biggest gap.
2. **Macros exist but aren't used.** Hand-written copies of `\tosigned`, `\Encodes`,
   `\uintn`, `\str`, `\byt`, `\imp`, `\ind`, `\none`, `\true`/`\false` and `\dom` sit
   next to the macros.
3. **Other notation the report defines has no macro.** That covers the descriptor
   and value brackets ⟪·⟫, `size_d`/`size_v`, `OneofPreserved(All)`, `parse`, `depth`,
   `Slot`, the `Σ; Γ ⊢` judgment form, `⊨_n`, wire types, and the InterParse
   constructors.
4. **Some macro names don't say what they mean, or are duplicates.** For example
   `\kle`, `\msg` (which is a descriptor), `\slot`/`\field` (same output),
   `\encodes`/`\Encodes`, and the `t` suffix on `\impt`. Thirteen macros are unused.
5. **Metavariables collide.** `c` is both a cardinality and a coercion, `f` is a field,
   a function and a map, and the field number is `n` in one grammar and `k`
   everywhere else.

Missing macros also let a few rendering bugs through. They're listed at the end.

## 1. The defined relations (highest priority)

The symbols are introduced at `sec:proto-relations` lines 30–36 and
`sec:ip-compat-rel` lines 317–325, then typed raw everywhere:

| Symbol    | Raw uses | Meanings in the report                                                                                                                                                                       |
|-----------|---------:|-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `\ll`     | 62       | descriptor compatibility (08, 09, 12)                                                                                                                                                         |
| `\propto` | 56       | type relation (08), field relation (09, 12), payload relation (09)                                                                                                                            |
| `\preceq` | 71       | message relation (08 `sec:msg-rel`), InterParse message relation (06 `M-Declare`, 12), the base of `\kle` (cardinality), plus `\preceq_e` for enums                                       |
| `\prec`   | 35       | value relation                                                                                                                                                                                 |

Naming each relation by its meaning lets the `.tex` read as the math does, and lets
a symbol change (the report has already changed notation more than once) take one
line instead of a regex over every section:

```LaTeX
% --- Compatibility relations (sec:proto-relations, sec:type-theory) -------
\newcommand{\valrel}{\prec}               % v1 : τ1 ≺ v2 : τ2   value relation
\newcommand{\typrel}{\propto}             % τ1 ∝ τ2, f1 ∝ f2    type / field relation
\newcommand{\dcompat}{\ll}                % d1 ≪ d2             descriptor compatibility
\newcommand{\msgrel}{\preceq}             % m1 ⪯ m2             message relation (InterParse, old §8)
\newcommand{\enumrel}{\preceq_e}          % e1 ⪯_e e2           enum relation
\newcommand{\cardrel}[2]{\preceq_{#1,#2}} % κ1 ⪯_{τ1,τ2} κ2     cardinality lifting (replaces \kle)

% Judgment forms
\newcommand{\judg}[2]{\Sigma; #1 \vdash #2}   % \judg{\Gamma}{d_1 \dcompat d_2 \coerce c}
\newcommand{\semjudg}[2][]{\vDash_{#1} #2}    % \semjudg[n]{g : \tau_1 \typrel \tau_2}
```

`Σ; Γ ⊢` (or `Σ; A ⊢`, `Σ; ∅ ⊢`) is typed out 34 times and `\vDash` 19 times, so
`\judg` and `\semjudg` pay for themselves. They also settle the `Γ`-vs-`A` question
(sec:type-theory uses both for the assumption context) in one place once you
decide it.

If the InterParse relations (12) and the Protobuf ones should be told apart in the
`.tex` even though they share glyphs, give them their own names
(`\ivalrel`, `\imsgrel`, ...) that expand to the same symbols.

## 2. Macros that exist but are bypassed

| Macro | Hand-written instead | Where |
|---|---|---|
| `\tosigned{m}{x}` | `\sigma_m(v_1)`, `\sigma_m(\zz{v_1})`, `\sigma_m(x) = …` | 08:203–211 (tab:varint-derived). `\tosigned` is otherwise unused. |
| `\uintn`, `\intn`, `\sintn`, `\bool` | `\texttt{uint[n]}`, `\texttt{int[n]}`, `\texttt{sint[n]}`, `\texttt{bool}` | 08:162–165 (tab:varint-conversion) |
| `\uintl`, `\uints` | `\mathtt{uint64}`, `\mathtt{uint32}` (and `\texttt{uint64}` in prose) | 08:89–96 |
| `\float`, `\double` | `\texttt{float}, \texttt{double}` | 08:60 (tab:val-spec) |
| `\str`, `\byt` | `\mathtt{string}`, `\mathtt{bytes}` | 09:298, 09:300 (T-StrByt, T-BytStr) |
| `\bool`, scalar macros | `\mathtt{bool}`, `\mathtt{int}` | 12:333–356 (InterParse types, so these may want their own macros, see §3) |
| `\imp`, `\opt`, `\rep` | `\mathtt{IMP}`, `\mathtt{OPT}`, `\mathtt{REP}` | 08:403, 08:409 |
| `\Encodes` | `\mathrm{Encodes}` ×8, `E_\tau(v, bs)`, `\mathrm{E}_{d_1}` | 03:105; 09:329, 337, 342, 346, 349, 369, 399; 08:74–80; 09:476 |
| `\ind{v}` | `\mathbb{1}[v_1]` | 12:333 |
| `\none` | `\text{none}` inside `\optt`, `\mathtt{NONE}` | 06:76, 06:296; 07:165 |
| `\true`, `\false` | `\mathtt{true}`, `\mathtt{false}` | 12:337–338. Both macros are otherwise unused. |
| `\dom{x}` | `\textrm{dom}(f)`, `\mathrm{dom}(m)` | 08:374, 08:404 |
| `\init` | `\mathrm{init}(d)` | 06:278 |
| `\mdoubleplus` | `++` | 09:388; 11:96–184 (Rocq section, lower priority) |
| `\some` | `\mathtt{Some}` | 08:462 |

The table of protobuf primitive types in `sec:proto` (tbl:proto-prim, tab:tags) uses
`\texttt{int32}` etc. Those are `.proto` keywords in a primer, so leaving them is
defensible, but using `\ints`, ... there too would make the whole report agree.

## 3. Defined notation with no macro yet

Each of these is notation the report itself introduces, used more than once:

| Notation | Uses | Suggested macro | Notes |
|---|---:|---|---|
| ⟪r, l⟫ descriptor | 05:204, 278 | `\desc{r}{l}` | The grammar in fig:proto-desc-syn defines it. |
| ⟪l⟫_v value | 06:85, 285, 303 | `\val{l}` | 06:285/303 drop the `_v` subscript that 06:85 has, which a macro would have kept. |
| `\texttt{[]}`, `\Colon` / `::` | 05:196–197, 286–287; 06:81–82, 289–290 | `\nil`, `\cons` | 05 uses `\Colon` in the grammar and `::` in `size_d`, while 09 writes `[\,]`. |
| `size_d`, `size_v` | 22 | `\dsize`, `\vsize` | def:dsize, def:vsize |
| `OneofPreserved`, `OneofPreservedAll` | 8 | `\oneofpres`, `\oneofpresall` | thm:trans-valid, D-Update, lem:msg-from-fields |
| `parse_d` | 12, in 4 typefaces | `\parse{d}` | `\mathrm{parse}_{d_2}` (09), `parse_{\tau_2}` in italics (08:80), `\mathtt{parse}_{d_1}` (08:461), `\mathsf{parse}` (09:389) |
| `ser_d`, `par_d` (InterParse) | 6 | `\iser{d}`, `\ipar{d}` | Don't call it `\par`, which is a TeX primitive. |
| `depth_v`, `depth_f`, `depth` | 8 | `\vdepth`, `\fdepth` | def:msg-depth. 09:337 has a bare `\mathrm{depth}(s)` for a slot, so pick which one it is. |
| `Slot(f)` | 09:73, 164 | `\Slot` | |
| `map`, `foldl`, `fix`, `merge`, `id` | many in 09 | `\fmap`, `\foldl`, `\fix`, `\merge`, `\idfn` | `merge` is `\mathrm` at 09:379 and `\mathsf` at 09:388–391. `fix` is `\mathsf` throughout. |
| wire types `VARINT`, `I64`, `I32`, `LEN ℓ` | YY, 03, 02 | `\wt{VARINT}`, `\wtlen{\ell}` | sec:proto-parse is new, so this is a good time to add them. |
| InterParse constructors `M_MISSING`, `M_MSG`, `F_MSG`, `F_INT`, ... | 24 | `\Mmissing`, `\Mmsg`, `\Fmsg`, `\Fint`, ... | See the drift item below. |
| `Bytes`, `Option`, `List` (as types) | 03:93 | optional | Used once, so low priority. |

**Drift worth noticing while doing this:** def:msg-depth (09:510) is a Protobuf
definition, yet it writes `v = \mathtt{F\_MSG}\ m'`, which is the InterParse field-type
constructor. 06:126 (`M-Declare`) also quotes InterParse constructors, but on purpose.
With macros like `\Fmsg`, the first one would stand out as the wrong format's name.

## 4. Names that don't say what they mean

| Current | Problem | Suggestion |
|---|---|---|
| `\kle{τ1}{τ2}` | "k-less-or-equal" is cryptic | `\cardrel{τ1}{τ2}` |
| `\comb{τ}` | abbreviation | `\combine{τ}` |
| `\msg{r}{f}` → `(r, f)` | It builds a **descriptor** (reserved set and fields) in old §8, and "message" means a value everywhere else. It's also a second notation for what fig:proto-desc-syn writes ⟪r, l⟫. | Fold into `\desc{r}{l}` |
| `\slot{a}{b}` and `\field{a}{b}` | Both expand to `\langle a, b\rangle`. `\slot` is used once (09:376), where its arguments are a *field* `⟨κ, τ⟩`, and slots are written with `\impt`/`\optt`/`\rept`. | Drop `\slot` and use `\field`. Also use `\field` for the 6 hand-written `\langle c, \tau\rangle` (05:192–193, 280–282; 07:130–135; 09:185, 549). |
| `\encodes` and `\Encodes` | identical, used once each | Keep one, and add the `^k` field-level form: `\newcommand{\Encodes}[2][]{\mathrm{Encodes}_{#2}^{#1}}`. |
| `\impt`, `\optt`, `\rept` | It's unclear what the `t` stands for. They're also overloaded: slot constructors in sec:proto-msg (`\optt{p}`) and type formers in sec:proto-relations (`\optt{\tau}`) and 09:566 (`\optt{X}`). | `\impslot{p}`, `\optslot{p}`, `\repslot{ps}` for values. If the type-former reading stays, give it separate names. |
| `\wfv` | Expands to `wfm`, so the macro says *v* and the output says *m*. def:vwf calls it a message. | `\wfm` (or change the output to match) |
| `\coerce` vs `\coercion` | `\coerce` is the ⇝ arrow and `\coercion` is the ₍d₁₎⟦m⟧₍d₂₎ bracket, and the two names are easy to swap. The bracket also reuses `\denote`'s ⟦·⟧ for something that isn't a denotation. | `\yields` or `\elab` for ⇝, `\transform{d_1}{m}{d_2}` for the bracket (the name `latex/CLAUDE.md` already uses). Consider a different bracket if ⟦·⟧ should only mean denotation. |
| `\lb`, `\ptag`, `\groups`, `\fdiv`, `\doubleplus`, `\sigt`, `\enum`, `\fixedn`, `\sfixedn`, `\tosignedop`, `\zzop`/`\unzzop` (only used inside `\zz`/`\unzz`) | unused in `\input` files | Delete the unused ones, or keep and comment them as reserved for enums/groups. `\true`, `\false` and `\tosigned` are unused only because of the bypasses in §2. |
| `\renewcommand{\mod}` | Clobbers amsmath's `\mod`. | `\newcommand{\fmod}{\mathbin{\%}}` (floored mod, as tab:varint-conversion defines it) |

Organizing the preamble the way the varint block already is would make it
self-documenting: group macros by the section they serve, and give each a one-line
comment with its meaning and the `\label` that defines it. Any macro whose output
alone doesn't say what it is (`\validv` → `m ⨾ d`, `\restr`, `\vints`) benefits most.

## 5. Metavariables

The table at 08:20–25 fixes metavariables, but the sections disagree with it and
with each other:

| Letter | Meanings |
|---|---|
| `c` | cardinality (fig:proto-desc-syn, thm:trans-valid 07:130, 09:549), and coercion (all of sec:type-theory). The 08 table says cardinality is `κ`, and 09's cardinality rules do use `κ`. |
| `f` | field, function `f : ⟦d₁⟧ → ⟦d₂⟧` (def:well-behaved, def:sem-compat), and the field map in old §8 |
| `k` vs `n` | field number is `n` in both grammars (`(n, f) :: l`, `(n, s) :: l`) and `k` everywhere else. `n` is also ℕ, the depth index, and bit width (`\mathtt{n}`). |
| `v` | the Value category in fig:proto-val-syn, a scalar value in sec:proto-relations, and "value" in the slot-level `size_v` cases (06:294–298), where it is a slot. Messages are `m` in every definition. |
| `s` | slot (fig:proto-val-syn), the string category `\mathrm{s}` in the same grammar, and the subscript in `τ_s` |
| `l` | field list and value list |
| `d` | descriptor, and a decorator `d ∈ {\imp, \opt}` (08:398, 08:403) |
| `m` | message, bit width `\mathtt{m}`, and a oneof map (08:404) |

Suggested resolution: `κ` for cardinality, `c` for coercion, `k` for field numbers,
`m` for messages, `s` for slots, `p` for payloads, and a different letter for the
string category. The vendored `latex-pl-syntax/metavarsx.sty` (`\NewMetaVariable`)
exists for exactly this, but `pollux.tex` doesn't load it. Fixing the letters is
the important part. Metavariable macros are optional.

## Rendering bugs that macros would have caught

- **06:153** `$\dom(d_2)$`: `\dom` takes `(` as its argument, so this renders as
  `dom(()d₂)`. It should be `$\dom{d_2}$`.
- **09:164** `\mathrm{Slot}{\kappa_1}(\tau_1) \rightarrow \mathrm{Slot}{k_2}(\tau_2)`:
  the subscript is missing (renders `Slotκ₁(τ₁)`), and it has `k_2` where `\kappa_2`
  is meant.
- **09:156** `\field{\kappa_1}{\tau_1} \ll \field{\kappa_2}{d_2}`: the relation is ≪
  where F-Field uses ∝, and the right side has `d_2` where `\tau_2` is meant.
- **09:338** `\assemble_{f2}`: should be `f_2`.
- **09:21** `\validv{m}{d}` in def:well-behaved: should presumably be `d_1`. This one
  isn't a macro issue, but it's on a line this note already touches.

## Also noticed

- `latex/CLAUDE.md`'s notation table is stale against the current preamble. It lists
  `d ✓_w`, `m ✓^d`, and a `\transform` macro, where the preamble now has `\wfd`,
  `\validv` (`m ⨾ d`), and `\coercion`. Once the macros settle, the table should list
  the macro names next to their Lean counterparts.
- The preamble loads `amsthm` twice (lines 15 and 18).
