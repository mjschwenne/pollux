Status: open
Report: sec:type-theory @ 3363eb4 (working-tree version, uncommitted)
Lean:   Pollux/Proto/Value.lean, Pollux/Proto/Validity.lean, Pollux/Proto/Transform.lean,
        Pollux/InterParse/Theorems/InterParseOk.lean @ 3363eb4

# What `sec:type-theory` still owes the 2026-09-16 review

## Summary

`2026-09-16-review-type-theory.txt` reviewed an earlier copy of this section
(`../pollux-report/sections/07-type-theoretic.tex`). Roughly half of it has
since landed. What has not landed is not scattered leftovers: it is the
section's central argument. The section currently states its thesis (recursion
does not force co-induction) and its consequence (the Lean plan) but not the
argument between them, and the one concrete instruction it gives Lean — the
$\Sigma$ context — names the wrong object.

Six items below are substantive; the rest are corrections. Item 6 is not from
the review --- it came up while the author was integrating item 1. Citations for all
of this are in `2026-09-22-reading-type-theory.md`, which was written from the
same review; this note does not repeat them.

## Already absorbed — no action

Recorded so these do not get re-checked: the $\exists\ bs \to \forall\ bs$
correction together with the paragraph justifying it; the
$\mathtt{Msg}/\mathtt{Msg}'/\mathtt{Msg}''$ transitivity example and the
`reserved` resolution; leading with the logical-relations claim rather than
closing on it; the Amadio–Cardelli attribution; the whole "Formalizing in Lean"
argument (no co-inductive types, no `paco`, hand-rolled gfp and bisimulation);
$\Sigma$ in place of $\mu$-binders; `reinterpret`'s termination measure moving
to the writer's value size; `Desc.OneofPreservedAll` becoming a finite
conjunction over reachable pairs.

## 1. The soundness architecture is never stated

**What the review says.** Keep the semantic definition primary and demote the
descriptor relation to a *sound decision procedure* for it.

**What the section says.** It gets close — "we probably still want to have a
relation on the descriptors \ldots\ provides a nice way to check compatibility
without having to construct the transformation directly" — but never writes the
statement down, and never says whether completeness is claimed. The words
"sound" and "complete" do not occur in `sec:philosophy`, `sec:comp-rel`, or
`sec:type-theory`.

**Why it matters.** Without it a reader cannot tell whether `sec:comp-rel`'s
relations *are* the definition of compatibility — in which case recursion
really does force co-induction, and the section's thesis fails — or an
approximation of the semantic definition, in which case it does not. That
choice is the section's entire content. It is also the obligation
`sec:comp-rel` inherits: right now $\ll$, $\propto$ and $\preceq$ are defined
with no stated relationship to `def:compat` or to the semantic judgment here.
Stating it costs two sentences and converts the section from a framing into a
specification.

**Suggested text**, to close the "Adding Recursion" subsection:

```latex
The two definitions are then related in one direction only. The relation is a
\emph{sound} checker for the semantic definition:
\[ \Sigma; \varnothing \vdash d_1 \ll d_2 \implies\ \vDash
  \transform{d_1}{\cdot}{d_2} : d_1 \preceq d_2 \]
We do not claim the converse. Completeness would say that every pair of
descriptors admitting \emph{some} compatible transformation is accepted by the
relation, which is both harder and less useful: the relation exists to be
checked, and it is allowed to be conservative. This is the standard
semantic-typing arrangement, where the syntactic rules are proved sound against
a meaning assigned independently of them.
```

**Note on the symbols**, see item 6: an earlier draft of this note wrote the
conclusion as the bare $d_1 \ll d_2$, which reads as a tautology because $\ll$
denotes both relations. The form above exhibits the witness instead, which is
both stronger and what Lean proves.

## 2. The argument that induction suffices is missing; only the conclusion is there

**What the section says.** "Rather than trying to prove
$\varnothing \vdash d_1 \ll d_2$, which would require co-induction, we show
$\mu\ F \ll \mu\ G \vdash F(\mu\ F) \ll G(\mu\ G)$ which can be done with
normal induction."

**What the review says.** Two independent finiteness facts, either of which
suffices:

- *Syntactic.* A cyclic descriptor is still finite syntax: the symbol table
  stores `Stream`'s second field as the *name* `Stream`, not as a copy of the
  descriptor. What is infinite is only what it unfolds to, and that unfolding
  is a regular tree — an infinite tree with finitely many distinct subtrees.
  The checker exploits this by carrying an *assumption set* $A$ (specified in
  item 3): a set of pairs of message names, where $(n_1, n_2) \in A$ means
  "$\Sigma(n_1) \ll \Sigma(n_2)$ has already been assumed". It starts empty —
  it is what the $\varnothing$ in the section's own
  $\varnothing \vdash d \ll d'$ is empty of — and grows as the derivation
  descends. Before recursing on a name pair the checker succeeds immediately if
  the pair is already in $A$, and otherwise adds it and unfolds. So every recursive step
  adds a pair, $A$ never shrinks, and the pairs are drawn from
  $\dom{\Sigma} \times \dom{\Sigma}$ — at most $N^2$ of them for $N$ messages
  in the file. The recursion can therefore descend at most $N^2$ times before
  every further call hits the assumption case, and the derivation is finite
  without anyone having to supply a decreasing measure.
- *Semantic.* Protobuf values are finite even under a cyclic schema. When the
  soundness proof re-encounters an assumed pair, it has necessarily descended
  under a `.msg` payload, so the value has strictly shrunk. Soundness is strong
  induction on the writer's value size — step-indexing where the index is an
  ordinary `Nat`, with no transfinite machinery.

**Why it matters.** This is the section's thesis and the sole justification for
the "Formalizing in Lean" subsection. As written it rests on an unargued
assertion carrying a `(likely \emph{not} actually correct)` hedge, so a reader
has no way to evaluate the Lean plan that follows from it. It also promotes the
`Stream`/`List` observation — currently a remark about a misleading name — to
what it actually is: the load-bearing semantic fact. Having *two* independent
arguments is worth saying out loud, because it means the result does not depend
on getting either the syntactic or the semantic story exactly right.

**Suggested text**, replacing the bare "which can be done with normal
induction":

```latex
Co-induction is avoided twice over, by two independent finiteness facts.

Syntactically, a cyclic descriptor is still finite syntax. The symbol table
stores \texttt{Stream}'s second field as the \emph{name} \texttt{Stream} rather
than as a copy of the descriptor, so what is infinite is only what the
descriptor unfolds to, and that unfolding is a regular tree: an infinite tree
with finitely many distinct subtrees. The checker exploits this by carrying an
assumption set $A$: a set of pairs of message names, where
$(n_1, n_2) \in A$ records that $\Sigma(n_1) \ll \Sigma(n_2)$ has already been
assumed. It is what the $\varnothing$ in $\varnothing \vdash d \ll d'$ above is
empty of, and it grows as the derivation descends. Before recursing on a pair
of names the checker succeeds immediately if that pair is already in $A$, and
otherwise adds the pair and unfolds. Every
recursive step therefore adds a pair, $A$ never shrinks, and the pairs are
drawn from $\dom{\Sigma} \times \dom{\Sigma}$, so for a file of $N$ messages the
recursion descends at most $N^2$ times before every further call is discharged
by assumption. The derivation is finite, and no decreasing measure has to be
supplied. Checking \texttt{Stream} against a \texttt{Stream}$'$ that adds a
\bool{} field takes two steps: $(\texttt{Stream}, \texttt{Stream}')$ is not yet
assumed, so it is added and both descriptors are unfolded; field 1 gives
$\ints \propto \ints$, and field 2 reduces to
$\Sigma; A \vdash \texttt{Stream} \ll \texttt{Stream}'$, which is now in $A$ and
closes. Without $A$ that last step reopens the first, which is exactly the
derivation-containing-itself problem above.

Semantically, a Protobuf message is finite even when its descriptor is cyclic.
This is the content of the observation that \texttt{Stream} is really a
\texttt{List}, and it is the load-bearing fact rather than a remark about
naming. Soundness is therefore strong induction on the writer's
value size: the relation only recurses under a \texttt{.msg} payload, so
whenever the proof reaches a pair already assumed in the context, the value it
holds has strictly shrunk. This is what licenses $A$: discharging a pair from
it applies an induction hypothesis at a smaller value rather than assuming the
conclusion. The index is an ordinary natural number, so this is
step-indexing in the Appel--McAllester sense with none of the transfinite
machinery. Either fact alone would be enough; Pollux has both.
```

## 3. $\Sigma$ is described as the wrong object

**What the section says.** "the lean formalization can use an additional
context $\Sigma$ which maps a name to a descriptor."

That is a symbol table. But the section *also* writes
$\varnothing \vdash d \ll d'$ two paragraphs earlier, and an empty symbol table
is not what is meant there — that is the assumption set of the judgment. The
section uses both readings under one symbol.

**What the review says.** They are different objects and both are needed:

| Object | What it is | What it buys |
|--------|------------|--------------|
| symbol table | name $\rightharpoonup$ descriptor, global, fixed by the `.proto` file | descriptors are finite *syntax* |
| assumption set | a finite set of name *pairs* assumed related, grows along the derivation | derivations are finite |

**Why it matters.** Nothing about a name-to-descriptor map terminates anything,
so conflating the two silently deletes the termination argument in (2) — the
monotone-growth argument is a statement about the assumption set. This is also
the one place the section hands the Lean formalization a concrete instruction,
so the under-specification propagates directly into `Pollux.Proto`'s relations,
which do not exist yet and would be built to it.

Separating the roles probably also dissolves the red open question at the end
of the subsection ("Would we want all the nested messages to always be in
$\Sigma$? The chains could get a lot larger than just the 533 cycles\ldots").
The symbol table can hold every message in the file — it is just the file, and
its size costs nothing. The assumption set only ever holds pairs on the current
derivation path, so it is bounded by the SCC size, which `sec:proto-desc`
measures at 22.

**Suggested text.** Keep $\Sigma$ for the symbol table as the section already
has it, and name the assumption set separately:

```latex
Two contexts are in play and it is worth keeping them apart. $\Sigma$ is the
symbol table, mapping a message name to its descriptor; it is global, fixed by
the \texttt{.proto} file, and makes a cyclic descriptor into finite syntax.
$A$ is the set of name pairs currently assumed compatible; it grows as the
derivation descends and is what makes the derivation finite. The judgment is
then $\Sigma; A \vdash d_1 \ll d_2$, with two rules for names:
\begin{mathpar}
  \infer[N-Assum]{ (n_1, n_2) \in A }{ \Sigma; A \vdash n_1 \ll n_2 }

  \infer[N-Unfold]{ (n_1, n_2) \notin A \\
    \Sigma; A \cup \{(n_1, n_2)\} \vdash \Sigma(n_1) \ll \Sigma(n_2) }{
    \Sigma; A \vdash n_1 \ll n_2 }
\end{mathpar}
Compatibility of a pair of top-level descriptors is
$\Sigma; \varnothing \vdash d_1 \ll d_2$. \textsc{N-Unfold} is where the
$\mu$-unfolding happens, and its side condition is what makes $A$ grow
monotonically inside the finite set $\dom{\Sigma} \times \dom{\Sigma}$.
```

(mathpartir's `\infer` takes premises then conclusion, with `\\` separating
premises, as in `D-Update` above.) With this in place the Löb-style rule earlier in the section is the
$\textsc{N-Unfold}$ premise, which is worth saying, and the hedge on it can go.

## 4. Two of the four "what survives recursion" facts were dropped

The section kept the `reinterpret` termination measure and
`Desc.OneofPreservedAll`. The review had two more, and I verified both still
hold (table at the end):

- **`Field.init` never recurses into a message descriptor.** Every `.msg` arm
  returns `.optional none`, because explicit presence means a message field's
  "nothing on the wire" value carries no descriptor
  (`Pollux/Proto/Value.lean:271`). So `init(d)` — `def:vvalid`'s companion in
  `sec:proto-msg`, and the definition a reader will *immediately* expect to
  diverge on a cyclic schema — is untouched, and so is the totality machinery
  built on it.
- **`Value.Valid` works unchanged.** It recurses on the *value*, consulting the
  descriptor only through `get?`; the nested case is
  `Payload.Matches | .msg v, .msg d' => Value.Valid d' v`
  (`Pollux/Proto/Validity.lean:130`–`164`). The design was made for other
  reasons and happens to be exactly what cyclic descriptors need.

**Why it matters.** The section claims recursion is a contained change. That is
only credible if it says which existing definitions survive it, and these are
precisely the two a careful reader would challenge — both look
descriptor-recursive from the report's presentation, and `def:vvalid` is
explicitly recursive in `sec:proto-msg`. Two sentences each, and they pre-empt
the obvious objection.

## 5. The report-to-Lean dictionary for the algebraic view

**What the review says.** Do not formalize the $\mu$-type presentation
literally — descriptors as functors, interpreted into Lean types. It is a
data-generic-programming project with positivity and universe problems, and the
resulting interpretation is disconnected from the wire-format proofs, so it
buys no proof leverage. Keep the algebraic view as the report's explanatory
lens, and give the reader the dictionary:

| Algebraic view | Lean realization |
|----------------|------------------|
| $\mu$ | the symbol table |
| unfolding | one `explode` resolution step |
| the Löb rule | the assumption set $A$ |
| the semantic judgment | the planned `Encodes`-based statement |

**What the section says.** Only a weak version of the negative half: "this
would be a lot of formalization and machinery which isn't really needed."

**Why it matters.** `sec:type-theory` is the one section using $\mu$, $F$ and
$G$, notation that appears nowhere else in the report. Without the dictionary
the reader is left with an analogy and the formalization with no instruction.
The $\mu$-unfolding-is-`explode` line in particular ties the section to
`sec:proto-desc`'s own descriptor model rather than to an imported metaphor,
and `explode` is already the report's word for exactly that one-layer
resolution step. The concrete reasons not to formalize $\mu$-types (positivity,
universes, disconnection from the wire proofs) are also what make this a
decision rather than a preference.

Related dangling dependency: `Encodes` occurs *only* in `sec:type-theory`. The
semantic definition on which the whole section rests is stated in terms of a
relation the report has not defined anywhere. Worth either defining it in
`sec:proto-msg` or flagging it as planned where it is first used.

## 6. $\ll$ denotes two different relations

Not from the review — raised by the author on 2026-09-22, on reading the
soundness statement in item 1, and prior to it.

**The collision.** Line 103 writes $\varnothing \vdash d \ll d'$, derivability
in the proof system. Line 110 *defines* $d_1 \ll d_2 := \exists f.\ \ldots$,
the semantic property. The two are seven lines apart in the same paragraph and
the turnstile is the only thing telling them apart. They are genuinely
different objects:

| | $\Sigma; A \vdash d_1 \ll d_2$ | $d_1 \ll d_2$ (line 110) |
|---|---|---|
| kind | inductively defined judgment | a property, defined by a formula |
| mentions | descriptors only | values, byte strings, the encoder, the parser |
| evidence | a finite derivation | a transformation $f$ and a proof about every encoding |
| decidable | yes, by proof search | no evident procedure |

**Why it matters.** The convention holds up until both appear in one formula,
at which point a soundness statement reads as a tautology — which is exactly
what happened to the display in item 1. It also already bites at line 119,
$\mu F \ll \mu G \vdash F(\mu F) \ll G(\mu G)$: both occurrences must be the
syntactic relation for the rule to mean anything, but under line 110 the bare
left-hand one reads as the semantic definition. That is the section's key rule,
so the ambiguity sits on the load-bearing formula.

**Fix.** Two options, best used together.

- *Let the turnstile carry the distinction.* Reserve $\vdash$ for derivability
  and $\vDash$ for the semantic definition, and never write $\ll$ bare. Line
  110 becomes $\vDash d_1 \ll d_2 := \exists f.\ \ldots$. This is the standard
  semantic-typing convention and the section already uses $\vDash$ this way at
  line 21, so it is continuous with what is there.
- *Exhibit the witness in the soundness statement.* $\vDash
  \transform{d_1}{\cdot}{d_2} : d_1 \preceq d_2$, reusing the $\vDash f : d_1
  \preceq d_2$ judgment from line 21 with the report's own transform macro.
  Stronger than the existential form, which follows by $\exists$-introduction,
  and it is the form Lean proves: `compatInterParseOk` names `compatTransform`
  rather than producing an existential.

**A symptom, raised by the author on 2026-09-22: which $\ll$ does the
assumption set belong to?** The syntactic one, and only it. $A$ lives in the
judgment $\Sigma; A \vdash d_1 \ll d_2$; the semantic definition is a formula
with no derivation to thread it through, and needs none, because it never
recurses on descriptor structure — it quantifies over values and byte strings,
which are finite whether or not $d_1$ is cyclic.

This is the sharpest available form of the argument in item 1 for making the
semantic definition primary, and the section should say it: **the recursion
problem only ever existed on the syntactic side.** The derivation-contains
-itself worry at line 79 is a statement about derivations. Nothing analogous
happens to the semantic definition, so it needs no repair, no assumption set
and no co-induction. $A$ is repair work on the checker alone.

The two meet only in the soundness proof, which cannot proceed with $A$
arbitrary and so must interpret it: for every $(n_1, n_2) \in A$, the semantic
property holds of $\Sigma(n_1), \Sigma(n_2)$ at all writer values of size
$< n$, concluding the property for $d_1, d_2$ at size $\le n$. Each syntactic
assumption is thereby *read as* an induction hypothesis at smaller value size,
which is exactly why \textsc{N-Assum} is sound. Interpreting a context as a
semantic hypothesis is the logical-relations move the section names in its
first subsection, so this is worth making explicit rather than leaving to the
reader. The correspondence to keep in view: $A$ is the syntactic half's
finiteness device and the step index is the semantic half's — the same role on
each side, which is why the two facts in item 2 are independent.

**Adjacent, unresolved.** `sec:comp-rel`'s summary table declares $\prec$,
$\propto$ and $\preceq$ but not $\ll$, and $\ll$ occurs nowhere in that
section. `sec:type-theory` then relates descriptors with $\preceq$ at lines 21
and 29 and with $\ll$ from line 70 on. Whether those are the same relation
under two names, or the descriptor relation and the message relation
respectively, is left to the reader. Worth settling in the same pass, since any
fix above has to commit to one reading.

## 7. The survey bridge

`sec:proto-desc` reports 533 mutually-recursive cycles with the longest at 22
messages. `sec:type-theory` cites those numbers only inside a red aside about
symbol-table size. The review's point is that they say something else and
better: the checker is not merely sound but *cheap*, because the assumption set
is bounded by the SCC size, so the worst case in real corpora is 22 pairs.

One sentence, and it turns `sec:proto-desc`'s survey from background into the
justification for this section's design — the design reads as inevitable rather
than speculative.

## Corrections to what is already there

- **The functor equation is internally inconsistent.** $F\ X = \ints +
  \optt{X}$ is a sum; $G\ X = \ints \times \bool \times \optt{X}$, two lines
  later, is a product. A descriptor is a record, and the sum form suggests a
  nil/cons choice that Protobuf fields do not have — nothing selects between
  `hd` and `tl`, both are present. Minimal fix: $F\ X = \ints \times \optt{X}$,
  leaving $G$ as is. (If explicit presence for the scalar is wanted too, it is
  $\optt{\ints} \times \optt{X}$; `hd` has implicit presence in proto3, so the
  minimal fix is the accurate one.) The list-ness then comes from finiteness of
  encodings, not from a sum — which is a cleaner statement of the section's own
  `Stream`/`List` point.
- **$\mu$ is overloaded.** $\mu\ X.\ F\ X$ is a recursive type; $\mu\ X.f$ in
  the typing rule is the fixpoint of a transformation. The review suggests
  $\mathrm{fix}\ x.\ \mathit{body}$ for the latter. Minor, except that this is
  the rule carrying the "likely not actually correct" hedge, and part of that
  hedge is notational rather than mathematical.
- **Truncated sentence**: "This would allow us to avoid co-induction, " ends on
  a comma.
- **Missing verb**: "all descriptor pairs with the syntactic property have a
  transformation which the semantic property" — presumably "which *satisfies*
  the semantic property".
- **Typos the review flagged that survive**: "would would", "were we see",
  "prospective" (for "perspective"), "we even if we".

## Not report material

The review also suggests a Lean counterexample file for the transitivity
failure, in the style of `lean/Pollux/Proto/OneofCounterexample.lean`. That is a
formalization backlog item for `sec:TODO`, not prose for this section — the
report already has the example as a figure and does not need it twice.

## Verified against the Lean

Every Lean-facing claim above was checked against the working tree at `3363eb4`
before being recommended:

| Claim | Status | Location |
|-------|--------|----------|
| `compatInterParseOk` is already this section's fundamental lemma | holds | `InterParse/Theorems/InterParseOk.lean:989` |
| `Field.init` never recurses into a message descriptor | holds | `Proto/Value.lean:271`–`276` |
| `Value.Valid` is value-structural, descriptor reached via `get?` | holds | `Proto/Validity.lean:130`–`164` |
| `reinterpret` terminates on `descSize d₂` | holds | `Proto/Transform.lean:82` |
| `Desc.OneofPreservedAll` is WF-recursion on `descSize d₂` | holds | `Proto/Transform.lean:388` |
| 533 cycles / max SCC 22 | in the report | `05-proto-desc.tex:374`–`375` |
| Amadio–Cardelli, Brandt–Henglein, TAPL, Appel–McAllester in `pollux.bib` | absent (49 entries) | — |
| `Encodes` defined outside `sec:type-theory` | absent | — |

The review's citation of `Transform.lean:132` for `Payload.reinterpret`'s
`.msg` arm has drifted; the corresponding `termination_by` is now at line 135.

One framing point from the review that did not make it into the section and is
worth a sentence: `compatInterParseOk` means this framework has already been
discharged once at full scale. The syntactic relation is `⋘`, the canonical
witness for the existential is `compatTransform`, and the round-trip theorem is
the fundamental lemma. Saying so reduces the section's genuinely new content to
a single decision — what to do when recursion arrives — which is a much
stronger position to argue from than presenting the whole framework as
prospective.
