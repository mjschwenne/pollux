Status: open
Report: sec:type-theory, sec:proto-relations, sec:proto-transform, sec:inter-parse @ 2002aed
        (working-tree version of 09-type-theoretic.tex, uncommitted)
Lean:   Pollux/Parse/{Serializer,Theorems}.lean,
        Pollux/InterParse/Theorems/InterParseOk.lean,
        Pollux/Proto/{Value,Validity,Transform}.lean @ 2002aed

# `sec:type-theory` against the two reviews, and the fundamental theorem stated

## Summary

The rewrite absorbed most of `2026-09-22-review-type-theory-gaps.md`. Items 1, 2,
3 and 6 have landed in substance; items 4, 5 and 7 have not, and three of the
loose ends the gaps note explicitly said would close once items 2 and 3 landed
are still open (the hedge at line 28, the tie-back of the `Stream` example to the
derivation-contains-itself problem, and the independence of the two finiteness
facts).

Two things are new here, neither in either note:

- **The section states the corollary, not the theorem.** The display at lines
  213--214 is the closed, `A = \varnothing` case. It cannot be proved by
  induction in that form, because $A$ is not empty inside a derivation. Section 2
  below states the theorem the induction actually proves, with the semantic
  reading of $A$ that the gaps note sketched in prose (item 6, closing
  paragraph) turned into a definition.
- **`compatInterParseOk` discharges the $\exists\ bs$ leg, not the $\forall\ bs$
  leg.** `Serializer` is a function (`Parse/Serializer.lean:20`), so
  `LimitParseOkCompat''` quantifies over the canonical serializer's single output.
  The gaps note's verification table records `compatInterParseOk` as "this
  section's fundamental lemma | holds", which is true of its shape but not of its
  strength, and the section now turns on exactly that distinction (lines
  193--199). Details in section 5.

There are also four report-internal inconsistencies in the newly written text
(section 4), and the four typos the 2026-09-16 review flagged all survive
(section 6).

*Expanded 2026-09-28 after a walkthrough with the author:* section 2's proof
shape now spells out why the two inductions are both needed, the off-by-one at
\textsc{N-Assum} and what the strict $<$ buys, the auxiliary induction
\textsc{N-Unfold} costs, the guard as a side condition on the rule system, and
the fact that `limitRecursiveStateCompat_correct` already is this combinator. It
also adds one correction the earlier draft got wrong by inheritance: the index
should be **depth**, not value size.

*Expanded again 2026-09-29:* the author has since absorbed `def:sem-compat`,
`def:sem-assum`, `thm:fundamental` and `cor:compat-sound` into the section
(`09-type-theoretic.tex:79`--`112`), on depth rather than size, so section 2's
suggested LaTeX below is now a record of what landed rather than a proposal.
The new subsection "Whether the rules should carry the index" answers the
follow-up question about indexing \textsc{N-Assum}, \textsc{N-Unfold} and
\textsc{F-Msg}.

## 1. Scorecard against `2026-09-22-review-type-theory-gaps.md`

| Item | Status | Where |
|------|--------|-------|
| 1. soundness architecture stated | **landed** | 210--222 |
| 2. two finiteness facts | **landed**, less the independence claim and the closing tie-back | 154--191 |
| 3. $\Sigma$ vs. $A$ separated | **landed**, but introduced 25 lines after first use, and the hedge it was meant to retire is still there | 136--152 |
| 4. `Field.init` / `Value.Valid` survive recursion | **not landed** (a garbled half of the `Value.Valid` claim only) | 257--258 |
| 5. report-to-Lean dictionary for the algebraic view | **partial**: unfolding $=$ `explode` and Löb $= A$ are there; $\mu =$ symbol table and the semantic judgment are not; the concrete reasons not to formalize $\mu$-types are not | 247--250 |
| 6. $\ll$ denotes two relations | **landed notationally** ($\vDash$ vs. $\vdash$, witness exhibited); the "recursion only ever existed on the syntactic side" argument and the semantic reading of $A$ are not there | 118, 213--214 |
| 7. survey bridge (checker is cheap) | **not landed**: the numbers are still attached to symbol-table size | 243 |

Corrections from the same note: the functor equation is fixed to a product (96),
$\mathsf{fix}\ x.\ body$ replaces the overloaded $\mu$ (29), the truncated
sentence is gone, and the missing verb is supplied (15). The four typos are not.

## 2. The fundamental theorem

The section names three things but writes down only the first and the third:

1. the semantic interpretation (lines 21--22 and 118--119, the same definition
   twice in different dress);
2. the semantic reading of the assumption set — absent;
3. the statement that derivability implies semantic compatibility (213--214).

(3) is the corollary. The theorem is (3) generalized over $A$ using (2), and that
generalization is forced: the inner induction on a derivation of
$\Sigma; A \vdash d_1 \ll d_2$ meets \textsc{N-Assum} with $A$ non-empty, so the
closed statement is not an induction hypothesis. This is the standard
context-generalization step of a logical relation, and writing it down is the
thing that makes the section's own claim — that the argument is a logical
relation — checkable rather than a label.

### Suggested LaTeX

```latex
\begin{definition}[Semantic compatibility]\label{def:sem-compat}
  A function $f : \denote{d_1} \rightarrow \denote{d_2}$ \emph{carries $d_1$ into
  $d_2$ up to size $n$}, written $\vDash_n f : d_1 \preceq d_2$, when
  \[ \forall\ m \checkmark^{d_1} \text{ with } \mathrm{size}_v(m) \le n,\
    \forall\ bs.\ \mathrm{Encodes}_{d_1}(m, bs) \rightarrow
    \mathrm{parse}_{d_2}(bs) = \some{f(m)}. \]
  It \emph{carries $d_1$ into $d_2$}, written $\vDash f : d_1 \preceq d_2$, when
  it does so at every size, and $\vDash d_1 \ll d_2$ abbreviates
  $\exists\ f.\ \vDash f : d_1 \preceq d_2$.
\end{definition}

\begin{definition}[Semantic reading of an assumption set]\label{def:sem-assum}
  $\vDash_n A$ holds when every assumed pair is semantically compatible at every
  \emph{strictly} smaller size:
  \[ \forall\ (a_1, a_2) \in A.\ \forall\ j < n.\ \vDash_j
    \transform{\Sigma(a_1)}{\cdot}{\Sigma(a_2)} : \Sigma(a_1) \preceq \Sigma(a_2). \]
\end{definition}

\begin{theorem}[Fundamental Theorem]\label{thm:fundamental}
  Let $\Sigma$ be a closed symbol table, let $d_1 \checkmark_w$ and
  $d_2 \checkmark_w$, and let $A \subseteq \dom{\Sigma} \times \dom{\Sigma}$.
  Then for every $n$,
  \[ \Sigma; A \vdash d_1 \ll d_2 \ \wedge\ \vDash_n A \implies\ \vDash_n
    \transform{d_1}{\cdot}{d_2} : d_1 \preceq d_2. \]
\end{theorem}

\begin{corollary}[Soundness of the compatibility relation]\label{cor:compat-sound}
  $\vDash_n \varnothing$ holds vacuously at every $n$, so
  \[ \Sigma; \varnothing \vdash d_1 \ll d_2 \implies\ \vDash
    \transform{d_1}{\cdot}{d_2} : d_1 \preceq d_2. \]
\end{corollary}
```

In English: **every derivable compatibility judgment is inhabited by the
report's own transform.** The relation is the syntax, $\transform{d_1}{\cdot}{d_2}$
is the canonical witness, and the theorem is the bridge — the syntactic judgment
never has to be believed, only checked.

### Proof shape, and why the index bookkeeping belongs in the report

Strong induction on $n$, and inside it induction on the derivation. Neither
alone works, and the way each fails is the argument:

- **Derivation induction alone fails at \textsc{N-Assum}.** It is a *leaf* — no
  premise. Derivation induction supplies "the statement holds for every
  subderivation", and a leaf has none, so the case closes holding
  $(a_1,a_2) \in A$ and nothing else. That is the report's own
  derivation-contains-itself problem from line 79, resurfacing inside the proof
  rather than inside the derivation. $A$ buys a finite *derivation*; on its own
  it buys no proof.
- **Size induction alone fails everywhere else.** The index only moves when the
  proof enters a nested message. A \textsc{D-Update} across forty scalar fields,
  and any chain of \textsc{N-Unfold}s, all happen at one index, and size
  induction gives no handle on which rule justified compatibility at a given
  field.

So the outer strong induction on $n$ supplies the statement at every smaller
index, *for any $A$ and any descriptor pair* — the universally quantified form is
the only thing that can discharge a leaf — and the inner derivation induction
walks the rules at the current index.

**\textsc{F-Msg} is the only rule that moves the index.** A nested message is a
strict subvalue, so the obligation it generates is at some $j < n$. Everything
below depends on this, and it is a property of the rule system, not of the proof.

**\textsc{N-Assum} has an apparent off-by-one, and resolving it is the point.**
$\vDash_n A$ supplies the assumed pairs at indices $j < n$, while the goal at the
node looks like it sits at $n$. It does not, for a structural reason:
\textsc{N-Assum} and \textsc{N-Unfold} conclude a judgment about *names*, and a
name enters a descriptor judgment only as a message-typed field. So a name node
is reachable only through \textsc{F-Msg}, the index has already dropped to some
$j < n$, and $\vDash_n A$ applies exactly. Were the strictness relaxed to
$\le$, \textsc{N-Assum} would conclude the statement at $n$ from itself at $n$,
and `thm:fundamental` would hold for *every* $A$, including one asserting
compatibility of two unrelated descriptors. The strict $<$ is the $\triangleright$
of Löb's rule $\triangleright P \rightarrow P \vdash P$, discharged here by
well-founded recursion rather than a modality because values are finite.

**\textsc{N-Unfold} costs a second, auxiliary strong induction.** At index
$j < n$ with the subderivation
$D : \Sigma; A \cup \{(a_1,a_2)\} \vdash \Sigma(a_1) \ll \Sigma(a_2)$,
applying the outer induction hypothesis $P(j)$ to $D$ requires
$\vDash_j (A \cup \{(a_1,a_2)\})$. The old pairs come from $\vDash_n A$ since
$j < n$; the *new* pair at each $i < j$ requires $P(i)$ applied to the same $D$,
which requires $\vDash_i (A \cup \{(a_1,a_2)\})$ — the same obligation one index
down. So $\forall j.\ \vDash_j (A \cup \{(a_1,a_2)\})$ is itself proved by strong
induction on $j$, vacuously at $0$. It bottoms out, but it is a second induction
and the report should not imply it is a single appeal.

That is the precise content of the gaps note's item 6 sentence ("for every
$(n_1,n_2) \in A$, the semantic property holds of $\Sigma(n_1), \Sigma(n_2)$ at
all writer values of size $< n$, concluding the property for $d_1, d_2$ at size
$\le n$"), and the note had it right. Stating it as `def:sem-assum` +
`thm:fundamental` does three things the prose version does not: it makes
\textsc{N-Assum} visibly sound rather than circular, it identifies where the step
index is consumed, and it is the statement Lean will carry.

### The guard is a side condition on the rules, and it must be checked

All of the above rests on one syntactic fact:

> Every path from the \textsc{N-Unfold} that adds $(a_1,a_2)$ to an
> \textsc{N-Assum} that uses it passes through \textsc{F-Msg}.

It holds for the current rules for a one-line reason — \textsc{N-Unfold}'s
premise is a descriptor judgment, and a descriptor judgment mentions a name only
through a message-typed field. But it is a standing constraint on every rule ever
added to $\ll$: any rule that closes a name judgment at the same index at which
its pair was assumed breaks `thm:fundamental` silently, with no failure visible
at the rule itself. This is Brandt--Henglein's side condition, which
`2026-09-22-reading-type-theory.md` states as "the assumption is only used after
passing through a type constructor"; here the constructor is the `.msg` payload.

Being a specification-level fact about the rule system, it belongs beside
\textsc{N-Unfold} in the report rather than in a Lean comment. It is also the
sharpest reason the report needs to settle section 4's item 1 (the
\textsc{D-Update} premise) before Lean builds anything: a drop rule or a
transitivity rule stated at the wrong level is exactly the shape of rule that
breaks the guard.

The same guard has to hold in three places at once, and the proof needs all three
to agree: the **relation** descends only at \textsc{F-Msg}, the **transform**
descends only at `Payload.reinterpret`'s `.msg`/`.msg` arm
(`Transform.lean:132`), and the **parser** descends only into a length-delimited
submessage. That triple alignment is the `Field.init` observation of section 3
seen from the proof side.

### Whether the rules should carry the index

*Added 2026-09-29, answering the author's question.* First, why the index is on
the semantic side at all, since that is what makes the asymmetry look odd. The
two sides are different kinds of object and each carries its own well-founded
measure. The syntactic judgment is inductively defined, so a derivation is
already a finite object to recurse on, and $A$ is what keeps it finite under
recursion. The semantic statement quantifies over an unbounded set of writer
values, so its proof recurses on values, and $\vDash_n$ is that recursion's
variable made visible in the statement. Without it, `thm:fundamental` is not in a
form strong induction on depth can consume, and `def:sem-assum` cannot say
"assumed at strictly smaller depth", which is the entire content of the Löb step.

The index is eliminable, and `def:sem-compat` already says so: $\vDash$ is
$\vDash_n$ at every depth, and every value has a finite depth, so nothing is lost
at the end. That is the difference from Appel--McAllester, where the index is
forced by the semantics because the domain equation has no solution and the
unindexed relation does not exist. Here the semantics is fine unindexed; the
index is forced by the *proof*. Recording that distinction in the section is
worth a sentence, because the section calls the argument step-indexed and a
reader who knows the step-indexing literature will expect the stronger reason.

The same point sizes the two sides. The semantic definition needs the whole
natural number, since it quantifies over all depths. The rules need at most one
bit, "here" versus "one below", and that bit is already recoverable from the
judgment form. So erasing the subscript from the rules costs nothing, while
erasing it from `def:sem-compat` would destroy the statement.

*Added 2026-09-29, answering the author's question.* The off-by-one above is
resolved by a fact about the whole rule system (the guard), not by anything
readable at \textsc{N-Assum}. Putting an index on the judgment would make it
local. There are two ways to get that, and the cheaper one is already available.

**(a) Index the judgment.** Write $\Sigma; A \vdash_n d_1 \ll d_2$, make
\textsc{F-Msg} the only rule that moves $n$, and tag each assumption with the
index at which it was added: $A$ holds triples $(a_1, a_2, i)$, \textsc{N-Unfold}
adds $(n_1, n_2, n)$ at its own $n$, and \textsc{N-Assum} carries the premise
$(n_1, n_2, i) \in A$ **with $n < i$**. Then `def:sem-assum` becomes
$\forall (a_1,a_2,i) \in A.\ \forall j < i.\ \vDash_j \ldots$, and \textsc{N-Assum}
is sound by reading the rule. This is Löb made explicit: the pair is assumed
*later* and is usable only strictly later. The cost is that $\ll$ stops being a
single relation and becomes an indexed family, so "compatible" has to mean
"derivable at every $n$", and section 3's cheap-checker argument has to be
restated over that family. Amadio--Cardelli and Brandt--Henglein both keep the
rule system unindexed for exactly this reason: the index is a device of the
soundness proof, not part of the specification.

**(b) Stratify `thm:fundamental` by judgment form instead.** The system already
has two judgment forms and the report writes both with $\ll$:

| Form | Concluded by | Premise of |
|------|--------------|------------|
| name judgment $\Sigma; A \vdash n_1 \ll n_2$ | \textsc{N-Assum}, \textsc{N-Unfold} | \textsc{F-Msg} only |
| descriptor judgment $\Sigma; A \vdash d_1 \ll d_2$ | \textsc{D-Update} | \textsc{N-Unfold} |

Under a symbol table `FieldType` is `msg (n : Name)` rather than today's
`msg (d : Desc)` (`05-proto-desc.tex:29`), so $d_1[k]$ in \textsc{F-Msg}
(`:139`) *is* a name and that rule's premise is always a name judgment. So state
the theorem at two tiers:

- descriptor judgment $\Rightarrow$ $\vDash_n$, i.e. writer values of depth $\le n$;
- name judgment $\Rightarrow$ $\vDash_{n-1}$, i.e. writer values of depth $< n$.

Every case then closes without a path argument. \textsc{N-Assum}'s goal is at
$< n$ and `def:sem-assum` supplies exactly that. \textsc{N-Unfold} concludes a
name judgment at $< n$ from a descriptor judgment at $\le n$, which is a
weakening since $\vDash_n$ is downward closed. \textsc{F-Msg} takes a name
judgment at $< n$ and concludes a field statement at $\le n$, which matches
because a nested message has depth strictly below its parent's.
\textsc{D-Update} stays at $\le n$ throughout.

**Recommendation: (b).** It gives the same local soundness as (a), costs nothing
in the statement of $\ll$ or in the checker, and needs no new syntax — only a
sentence naming the two judgment forms and a two-tier statement of
`thm:fundamental`. The index is then visible as the tier, and the tier is
visible in the rule.

**What \textsc{F-Msg} looks like under (b).** It carries no index, which is the
point: the tier is read off the judgment form, so nothing is annotated. The only
edit is to the two components the rule currently gets wrong: the premise is a
name judgment, and the second component of each pair is a field *type* rather
than $d_i[k]$. The cardinality stays, and stays equal on both sides, since
cardinality changes are other $\propto$ rules' business:
\[ \infer[F-Msg]{ \Sigma; A \vdash a_1 \ll a_2 }{
     \Sigma; A \vdash \langle c, \mathtt{F\_MSG}\ a_1 \rangle \propto
                      \langle c, \mathtt{F\_MSG}\ a_2 \rangle } \]
against the indexed variant under (a), which is the same rule with the
subscripts written in:
\[ \infer[F-Msg]{ \Sigma; A \vdash_n a_1 \ll a_2 }{
     \Sigma; A \vdash_{n+1} \langle c, \mathtt{F\_MSG}\ a_1 \rangle \propto
                            \langle c, \mathtt{F\_MSG}\ a_2 \rangle } \]
The two are the same rule, because the subscript is recoverable from whether the
judgment is about a name or about a field or descriptor. That is the whole
content of the recommendation.

The obligation the rule generates in the proof: the name-tier hypothesis gives
compatibility of $\Sigma(a_1)$ with $\Sigma(a_2)$ on writer values of depth
$< n$, the value in field $k$ is a nested message whose depth is $<$ its
parent's, and the parent has depth $\le n$, so the two meet. This is the step
that consumes the index, and it is the only one.

Three notational consequences if the author takes this:

- Field types gain a name form, $\tau ::= \tau_s \mid \mathtt{F\_MSG}\ a$,
  replacing the syntax figure's $\langle c, d \rangle$ field alternative
  (`05-proto-desc.tex:69`--`70`) with $\langle c, \tau \rangle$ throughout. This
  is the symbol-table change `sec:proto-desc:333`--`335` already promises.
- If field types keep an inline-descriptor form alongside the name form,
  \textsc{F-Msg} splits in two. The descriptor form stays at the descriptor tier
  and needs no drop, and it does not endanger the guard, since the guard
  constrains only name judgments.
- **Names need a syntactic category, which the report does not yet have.** The
  syntax figure (`05-proto-desc.tex:35`--`85`) declares naturals, scalar types,
  cardinality, field, field list, reserved set and descriptor, and no names, so
  the $n_1, n_2$ of \textsc{N-Assum} and \textsc{N-Unfold}
  (`09-type-theoretic.tex:66`--`71`) and the $a_1, a_2$ of `def:sem-assum` are
  both currently undeclared meta-variables. Worse, $n$ is the figure's own
  meta-variable for the naturals (`:38`), and it is also the depth index of
  `def:sem-compat`, so the same letter carries three meanings in one section.
  The fix is one category and one line about $\Sigma$:

  ```latex
  \category[Name]{a}
  \alternative{\mathit{id}}
  ```

  with $\Sigma$ a finite map from names to descriptors, $\dom{\Sigma}$ its key
  set, and *closed* meaning every name occurring in a field type of some
  $\Sigma(a)$ lies in $\dom{\Sigma}$, which is the hypothesis `thm:fundamental`
  already states (`:101`). Then names are $a$ throughout, the naturals keep $n$
  for field numbers, and the depth index keeps $n$ in the semantic definitions
  where no name appears. Field types become
  $\tau ::= \tau_s \mid \mathtt{F\_MSG}\ a$ as above.

**Stating the stratified theorem.** Two tiers, not three: descriptor and field
judgments sit at $\le n$, name judgments at $< n$, and \textsc{F-Msg} is the
crossing. Scalar field obligations do not shrink, so the field tier has to travel
with the descriptor tier; the drop happens inside \textsc{F-Msg}, between its
conclusion and its premise.

The statement needs two things the report does not have yet. First, depth, which
`def:sem-compat` still marks `%TODO` at `:88`. Taking it from `valueDepth`
(`InterParse/Descriptor.lean:686`--`693`) so the two agree:
\[ \mathrm{depth}_v(m) = \max_{(k,v) \in m} \mathrm{depth}_f(v), \qquad
   \mathrm{depth}_f(v) = \begin{cases}
     0 & v \text{ scalar or missing} \\
     \mathrm{depth}_v(m') + 1 & v = \mathtt{F\_MSG}\ m'
   \end{cases} \]
with the max over an empty field list taken as $0$, so a message with no
message-typed field has depth $0$, and with $\mathrm{depth}_f$ of a repeated
field the max over its elements. Second, a field-level companion to
`def:sem-compat`, which can reuse the value-level encodes relation
`sec:proto-relations` already has (`08-proto-relations.tex:74`):

```latex
\begin{definition}[Semantic compatibility, field level]\label{def:sem-compat-fld}
  A function $g : \denote{\tau_1} \rightarrow \denote{\tau_2}$ \emph{carries
  $\tau_1$ into $\tau_2$ up to depth $n$}, written $\vDash_n g : \tau_1 \propto
  \tau_2$, when
  \[ \forall\ v \checkmark^{\tau_1} \text{ with } \mathrm{depth}_f(v) \le n,\
    \forall\ bs.\ \mathrm{E}_{\tau_1}(v, bs) \rightarrow
    \mathrm{parse}_{\tau_2}(bs) = \some{g(v)}. \]
\end{definition}
```

Then the theorem is one strong induction on $n$ wrapping one mutual induction
over the three derivation forms:

```latex
\begin{theorem}[Fundamental Theorem]\label{thm:fundamental}
  Let $\Sigma$ be a closed symbol table and let
  $A \subseteq \dom{\Sigma} \times \dom{\Sigma}$. Fix $n$ and assume
  $\vDash_n A$. Then
  \begin{enumerate}
    \item if $\Sigma; A \vdash d_1 \ll d_2$ with $d_1 \checkmark_w$ and
      $d_2 \checkmark_w$, then
      $\vDash_n \transform{d_1}{\cdot}{d_2} : d_1 \ll d_2$;
    \item if $\Sigma; A \vdash \tau_1 \propto \tau_2$, then
      $\vDash_n \transform{\tau_1}{\cdot}{\tau_2} : \tau_1 \propto \tau_2$;
    \item if $\Sigma; A \vdash a_1 \ll a_2$, then $\vDash_n \{(a_1, a_2)\}$.
  \end{enumerate}
\end{theorem}
```

Clause 3 is the move that makes the stratification pay. Its conclusion is
`def:sem-assum` at the singleton, so the name tier is not a new notion at all: it
is the same predicate the assumption set is read by. \textsc{N-Assum} then closes
in one step, since $(a_1,a_2) \in A$ and $\vDash_n A$ give $\vDash_n
\{(a_1,a_2)\}$ by definition, and the off-by-one never arises because the strict
$<$ is inside $\vDash_n$ on both sides. Written as $\vDash_{n-1}$ instead, clause
3 would need truncated subtraction at $n = 0$ and would stop matching
`def:sem-assum` syntactically.

The rules then discharge as follows, and only the third line touches the outer
induction hypothesis:

| Rule | Has | Needs | Step |
|------|-----|-------|------|
| \textsc{D-Update} | field tier at $n$ | descriptor tier at $n$ | fields of a message of depth $\le n$ have $\mathrm{depth}_f \le n$ |
| \textsc{F-Msg} | name tier at $n$, i.e. $\vDash_j$ for all $j < n$ | field tier at $n$ | the field value is $m'$ with $\mathrm{depth}_v(m') + 1 \le n$, so $j = n-1$ serves |
| \textsc{N-Unfold} | descriptor tier at $n$ under $A \cup \{(a_1,a_2)\}$ | name tier at $n$ | needs $\vDash_n (A \cup \{(a_1,a_2)\})$, the auxiliary induction above |
| \textsc{N-Assum} | $\vDash_n A$ | name tier at $n$ | immediate, $(a_1,a_2) \in A$ |

`cor:compat-sound` is unchanged: $\vDash_n \varnothing$ holds at every $n$, so
clause 1 at every $n$ gives $\vDash \transform{d_1}{\cdot}{d_2} : d_1 \ll d_2$.

Clause 2 needs a field-level transform to exhibit. `Payload.reinterpret`
(`Transform.lean:132`) is it, so the report's $\transform{\cdot}{\cdot}{\cdot}$
notation should be declared at both levels rather than only at descriptors.

**What the field tier actually contributes, since its message case looks
vacuous.** The author's observation is correct for a singular message field:
clause 2 at $\langle c, \mathtt{F\_MSG}\ a_1 \rangle$ unfolds almost at once into
clause 3. The residue is small but not empty, and it is worth naming, because it
is where the second measure of `Parse/Theorems.lean:740`--`741` lives.

- **Framing.** A message field encodes as tag, length, body. Clause 3 speaks only
  about the body. So the message case of clause 2 is the lemma that framing is
  transparent: the length prefix is copied rather than reinterpreted, and the
  reader's parser consumes exactly the declared length, leaving the right
  remainder. That is the parser leg of the triple alignment above, and it is the
  only place the byte-length decrease appears. It is also the leg that needs the
  $\mathrm{E}$ relation the report has at value level and Lean does not have at
  all (section 5).
- **Cardinality.** This is the part that is not thin. `sec:proto-desc`'s syntax
  and Lean both keep cardinality beside the field type (`05-proto-desc.tex:69`,
  `:29`), so a repeated message field's value is several entries at one key and
  clause 2 quantifies over all of them. The message case then needs an
  element-wise lift of clause 3 plus the concatenation lemma for repeated
  encoding, which is genuinely more than an unfolding. Presence is the same story
  in miniature: the `.optional none` case never reaches clause 3 at all, which is
  the `Field.init` observation of section 3.
- **The scalar rules are the real content.** \textsc{F-Bool-Int},
  \textsc{F-Int-Bool} and the integer width rules
  (`08-proto-relations.tex`, `sec:proto-compat-ints`) have nothing to do with
  messages, and they are where field compatibility does its work. Clause 2 looks
  degenerate only if one reads its message case first.

Two structural consequences. First, clause 2 cannot be folded into clause 1:
$\propto$ has its own rules, including \textsc{F-Trans} and \textsc{F-Refl}
(`12-inter-parse.tex:360`--`362`), so the mutual induction needs a clause per
judgment form whether or not one of them is thin. Second, and this is the pleasing
part, the devolution lands on clause 3 rather than clause 1, and clause 3 is the
tier below. So the rule that does the least semantic work is the rule that does
all of the index work. That is not a coincidence: a rule can only be semantically
thin at a message boundary, and a message boundary is the only place the depth can
drop.

**`sec:proto-relations` folds cardinality into $\tau$ and nothing else does.**
Line 44--46 says protobuf decorators, "technically part of the field level
specification, have been incorporated into the type level", so $\tau$ there
carries presence and repetition. `sec:proto-desc`'s syntax figure (`:69`--`70`)
and Lean's `Field.mk card ty` (`:29`) keep them separate, and
`sec:type-theory`'s \textsc{F-Msg} (`:139`) writes the separated form. Recommend
the separated form everywhere, since two of the three already use it and it is
what Lean will carry; then `sec:proto-relations` owes a line retiring the folded
reading. This matters here because it decides whether the repeated case above
sits inside clause 2 or above it.

Under (b) the guard of the previous subsection restates as a rule-table
property that can be checked by eye rather than by tracing derivations:

> \textsc{F-Msg} is the only rule with a name judgment as a premise, and its
> conclusion is about a value one message-nesting deeper.

That is still a standing constraint on new rules, but a reader can now verify it
from the rules alone. The shape that breaks it is a rule concluding a descriptor
judgment from a name judgment without descending into the value; a transitivity
or drop rule stated at the wrong level is exactly that shape, which is section
4's item 1 again.

Either way the report should write \textsc{F-Msg}'s premise as a name judgment
once the symbol table lands, which also fixes the $\langle c, \tau \rangle$
mismatch flagged in section 6 at line 139.

### Less prospective than it looks: the combinator already exists

`limitRecursiveStateCompat_correct` (`Parse/Theorems.lean:730`--`760`) is already
a step-indexed fundamental-theorem combinator. It takes `depth : α → Nat` (the
index), `linkedState : σ → σ → Prop` (the syntactic judgment threaded through the
recursion), and a hypothesis (`:737`--`756`) that is literally
$\triangleright P \rightarrow P$: assume the property for every `x'` with
`depth x' < depth x` at every linked state pair, conclude it at `x`.
`compatInterParseOk` instantiates `linkedState := fun a b => a ⋘ b ∧ b.AllWF` and
`depth := valueDepth` (`InterParseOk.lean:1004`), and `IH'`
(`InterParseOk.lean:1009`--`1015`) is exactly $\vDash_{<n}$.

So the shape is proved, not prospective, and the delta recursion introduces is
narrow. Today the context is *universally quantified* over all pairs with
`d₁' ⋘ d₂'`, which is sound because a finite descriptor tree always lets you
produce the nested pair's derivation on demand. Under a symbol table you
sometimes hold only $(a_1,a_2) \in A$, so that universally quantified premise has
to be replaced by the finite $A$ together with `def:sem-assum`. That is a much
smaller claim than presenting the whole framework as future work, and it is the
framing the gaps note's closing paragraph asks for.

### The index should be depth, not size

This refines the measure instruction in section 3 and contradicts three
documents at once: report line 252, the 2026-09-16 review, and the gaps note all
say the new termination measure should be the writer's value **size**. InterParse
already uses **depth** (`valueDepth`, `InterParse/Descriptor.lean:685`--`693`:
the max over message-typed fields of the nested depth plus one), and depth is the
better index here — it decrements exactly at the guard and at nothing else, while
size also varies with sibling fields, which this argument never uses.

Two consequences if `Pollux.Proto` follows InterParse:

- `Value.reinterpretEntries` recurses over the *reader's* field list without
  changing depth, so the measure becomes lexicographic
  $(\mathrm{depth}(v), \mathrm{entryListSize}(es))$ rather than the current
  scaled-by-4 chain (`Transform.lean:82`, `:94`, `:104`, `:124`, `:135`).
- `limitRecursiveStateCompat_correct` requires **both** `depth x' < depth x` and
  `Input.length inp' < Input.length enc` (`Parse/Theorems.lean:740`--`741`). The
  byte stream carries its own measure, so the report should not present the value
  index as the only thing that decreases.

If the report prefers $\mathrm{size}_v$ for exposition — it is already defined in
`def:vsize`, and depth is not defined anywhere in the report — that is a
defensible choice, but then either `def:vsize` gains a depth companion or the
Lean/report correspondence for the measure needs a line saying they differ and
why both work.

### Hypotheses the section's displays are missing

Both displays (21--22, 118--119) omit hypotheses Lean's version has:

- $d_1 \checkmark_w$ and $d_2 \checkmark_w$. `compatInterParseOk` takes
  `d₁.AllWF`, `d₂.AllWF` and `v.AllWF` (`InterParseOk.lean:990`). The report's
  $m \checkmark^{d_1}$ (`def:vvalid`) covers the value; nothing covers the
  descriptors. Per `latex/CLAUDE.md`'s implicit-side-conditions rule this is the
  report under-stating, not Lean over-stating.
- $\Sigma$ closed: every name occurring in a field type of some $\Sigma(n)$ is in
  $\dom{\Sigma}$. Without it \textsc{N-Unfold}'s $\Sigma(n_1)$ is undefined, and
  the $|\dom{\Sigma}|^2$ bound at line 169 has nothing to range over.
- Parsing **succeeds**. Lines 22 and 119 write
  $\mathrm{parse}_{d_2}(bs) = f(m)$, but `def:compat` in `sec:philosophy` writes
  $decode(encode(m_1)) = \some{m_2}$ and Lean concludes
  `∃ x', par d₂ enc = .success x' Input.default`. Success is part of the claim,
  not an ambient assumption — which matters, because line 185 currently reads as
  though it were assumed ("our definitions always work with the idea that parsing
  will succeed").

### Lean correspondence

| Report | Lean | File |
|--------|------|------|
| $\vDash_n f : d_1 \preceq d_2$ with $f$ exhibited | `LimitParseOkCompat'' (fun a b v v' => v' = compatTransform a b v) parseValue serialValue d₁ d₂ v` | `InterParseOk.lean:995` |
| `thm:fundamental` (no $A$; InterParse descriptors are finite trees) | `compatInterParseOk` | `InterParseOk.lean:989` |
| canonical witness $\transform{d_1}{\cdot}{d_2}$ | `compatTransform` / `Value.reinterpret` | `Theorems/CompatTransform.lean`, `Proto/Transform.lean:80` |
| $\vDash_n A$ | nothing yet | — |

## DONE 3. What items 4, 5 and 7 still owe, and one strengthening

**Item 4 is half-landed and the two halves are crossed.** Lines 257--258 give the
`Value.Valid` conclusion with the `Field.init` reason: "since messages can always
be omitted, having a cyclic descriptor \ldots\ doesn't complicate
Definition~\ref{def:vvalid}". Omission is why `Field.init` is safe. `def:vvalid`
is safe for a different reason — `Value.Valid` recurses on the *value* and reaches
the descriptor only through `get?` (`Validity.lean:130`--`164`). Both facts are
worth a sentence each, and they are the two a reader challenges first.

**`Field.init` is load-bearing, not defensive.** This is a strengthening of item
4 that neither note makes. The termination-measure switch the section asks for at
lines 252--254 only works because of it. `Value.reinterpretAt` falls back to
`f₂.init` whenever the writer has nothing at $k$ (`Transform.lean:100`--`104`),
and `Field.init`'s `.msg` arm returns `.optional none` without touching the
descriptor (`Value.lean:271`--`276`). So the *only* recursive path through
`Value.reinterpret` is `Payload.reinterpret`'s `.msg`/`.msg` arm
(`Transform.lean:132`), which descends to a strict subvalue. That is precisely
why the writer's value size is a legal measure under a cyclic schema, and it is
also the \textsc{F-Msg} step of the proof sketch in section 2. Item 4 and item 2's
semantic bullet are the same fact seen twice; saying so costs one sentence and
makes both look inevitable.

**Item 5's dangling notation is cheaper to fix than the note thought.**
`\mathrm{Encodes}` still occurs only in `sec:type-theory` (lines 21, 119). But
`sec:proto-relations` already has the relational encoding at value level:
$E_{\tau}(v, bs)$, "$v$ can be encoded as bytes $bs$ under type $\tau$"
(`08-proto-relations.tex:74`), used in the `\prec` definition in exactly the
$\forall\ bs$ shape this section argues for (`:80`). So `Encodes` is the message-level
lift of a relation the report already has, and the fix is to name it as such —
$E_{d}(m, bs)$, say — rather than to introduce a new one. (Small bug at
`:80` while you are there: $E_{\tau}(v_1, bs)$ should be $E_{\tau_1}$.)

$\denote{d_1}$ at line 118 is a second dangling notation. $\denote{\cdot}$ is
defined in the report only for scalar types (`08-proto-relations.tex:133`--`144`,
$\denote{\tau}$ is the specification-level Lean type). $\denote{d}$ for a
descriptor — presumably $\{\,m \mid m \checkmark^{d}\,\}$ — is not defined
anywhere.

**Item 7 is still unwritten and the numbers are attached to the wrong argument.**
Line 243 uses the max-SCC figure to argue the symbol table is cheap to store. The
survey's real payoff is that the *checker* is cheap: pairs in $A$ can only come
from names reachable from the two roots, and a derivation only stays open while
it is inside a cycle, so $|A|$ is bounded by the product of the two SCC sizes,
not by $|\dom{\Sigma}|^2$. With `tab:recur-summary`'s longest cycle at 22
messages, that is at most $22 \times 22 = 484$ pairs in the worst case observed
in the corpus, against a $|\dom{\Sigma}|^2$ bound in the hundreds of millions.

Note this corrects the gaps note, which says $A$ is "bounded by the SCC size,
which `sec:proto-desc` measures at 22" (item 3, and again in item 7). $A$ holds
*pairs*, so the bound is the product. The conclusion survives — 484 is still
nothing — but the report should not print 22 as the bound on $|A|$.

## 4b. Spotted 2026-09-29

**The 484 figure landed on $\Sigma$ instead of on $A$.** Lines 319--320 now read
"recursive cycle contains 22 with a maximum $\Sigma$ size of $22 \times 22 = 484$
messages". The product bounds $|A|$, not $|\Sigma|$: $A$ holds *pairs* of names
drawn from the two cycles, while $\Sigma$ holds the messages themselves and is
bounded by the schema's size. Section 3 of this note is the source of the 484 and
states it of $A$. As written the sentence also still attaches the number to
storage cost rather than to checking cost, which is item 7's actual point.

## DONE 4. Report-internal inconsistencies in the new text

None of these are in either note; they arrived with the rewrite.

1. **\textsc{D-Update} at lines 69--71 forbids the drop the section relies on.**
   The premise is $\dom{d} \subseteq \dom{d'}$, which excludes dropping a field,
   yet lines 37--62 discuss dropping as "already implemented in
   Section~\ref{sec:proto-transform}" and the $\mathtt{Msg}/\mathtt{Msg}'/\mathtt{Msg}''$
   example drops one. `sec:inter-parse`'s \textsc{D-Update}
   (`12-inter-parse.tex:373`--`376`) has the mandatory-domain premise instead and
   is marked red; `sec:proto-transform:95` says the Protobuf drop rule "will be
   scoped to only be applied only when $\dom{d_1} \not\subset \dom{d_2}$". Three
   different stories. Since the rule is introduced as "a descriptor rule like
   this one" it may be intentionally illustrative, but as written it contradicts
   the section's own example nine lines later.
2. **Line 73 is trivially true.** $\dom{d_{mand}} \supseteq \dom{d_{mand}}$; the
   prime is missing. `sec:inter-parse:374` has
   $\dom{d_{mand}} \supseteq \dom{d_{mand}'}$.
3. **Line 21 is an implication where it means a definition.** It reads
   $\vDash f : d_1 \preceq d_2 \rightarrow \forall m, bs.\ \ldots$, i.e. "if the
   judgment holds then \ldots". Line 118 gets the same content right with $:=$.
   The two should also be explicitly linked — line 118 is the existential closure
   of line 21 — since the section uses both and never says they are the same
   definition.
4. **The relation symbols do not agree across sections, and the section commits
   to a reading without saying so.** This settles the "adjacent, unresolved" item
   at the end of gaps item 6, with evidence:

   | Section | $\ll$ | $\preceq$ |
   |---------|-------|-----------|
   | `sec:inter-parse` (`:322`--`325`) | descriptor relation | message relation, $m_1 : d_1 \preceq m_2 : d_2$ |
   | `sec:proto-transform` (`thm:faith`, `:207`) | descriptor relation | — |
   | `sec:proto-relations` (`:31`--`35`) | **not declared**, occurs nowhere | "message relation" $m_1 \preceq m_2$, where a message is $\msg{r}{f}$ — i.e. a *descriptor* |
   | `sec:type-theory` | syntactic descriptor judgment | semantic descriptor judgment (21, 214) |

   So $\ll$ is consistent everywhere it is declared, and $\preceq$ is not:
   `sec:proto-relations` uses it for descriptors under the older "message $=
   (r, f)$" vocabulary, everything newer uses it for values under descriptors.
   `sec:type-theory` then writes $d_1 \preceq d_2$ between descriptors, which
   agrees with `sec:proto-relations` and clashes with `sec:inter-parse` and
   `sec:proto-transform`. Worth one decision and a line in
   `sec:proto-relations`'s summary table either way; the fundamental theorem in
   section 2 above is written in the section's own reading.

5. **The semantic finiteness argument chains two independent facts as if one
   implied the other** (lines 177--187). Values are finite because
   `sec:proto-msg`'s value syntax is an inductive definition — full stop, no
   appeal to implementations needed. The 100-layer (10,000 in Go) limit is a
   claim about *parsers rejecting deep inputs*, which is implementation-specific,
   not needed for the induction, and weaker in the wrong direction (it would make
   the argument depend on a document that can change). Recommend keeping the
   limits as a remark that real parsers agree, and resting the argument on
   inductiveness. Same paragraph: "even use fuel in the proofs if needed" is
   unnecessary once the step index *is* $\mathrm{size}_v(m)$, which is the
   sentence right after it.

## DONE 5. Corrections to the notes

- **`sec:comp-rel` does not exist.** `2026-09-22-review-type-theory-gaps.md`
  cites it seven times (items 1, 3, 5, 6) for `08-proto-relations.tex`, whose
  label is `sec:proto-relations` (`:1`). `latex/CLAUDE.md`'s layout table has the
  same stale label. `sec:type-theory:245` cites it correctly. Worth fixing in
  `latex/CLAUDE.md` when convenient — flagged here rather than edited, since that
  file is yours.
- **$|A|$ is bounded by the product of the SCC sizes, not by 22.** See section 3.
- **`compatInterParseOk` proves the $\exists\ bs$ leg.** The gaps note's
  verification table and the 2026-09-16 review both present it as the discharged
  form of this section's semantic definition. `LimitParseOkCompat''` is
  \[ \forall\ enc.\ wf\ d_1\ x \rightarrow ser\ d_1\ x = \mathtt{success}\ ()\ enc
     \rightarrow \exists\ x'.\ par\ d_2\ enc = \mathtt{success}\ x'\ \wedge\ R\ d_1\ d_2\ x\ x' \]
  (`Parse/Theorems.lean:665`--`671`), and `Serializer ι α wf := α → Result ι Unit`
  (`Parse/Serializer.lean:20`) is a function, so the $\forall\ enc$ plus the
  equation pins $enc$ to the canonical encoding. That is the functional
  round trip, which is exactly the $\exists\ bs$ form lines 193--199 argue is too
  weak. The $\forall\ bs$ form needs the relational encoding, which exists in the
  report at value level ($E_\tau$) and nowhere in Lean.

  This does not damage either note's conclusion — the framework *has* been
  discharged once at full scale, and the shapes do correspond — but the claim
  should be stated as "the canonical-serializer leg of this section's definition",
  and the gap should be named, because closing it is the varint/`Encodes` layer's
  job and it is the section's own headline distinction.
- **Line drift since `3363eb4`:** none of the gaps note's Lean citations moved.
  `compatInterParseOk` is still `InterParseOk.lean:989`, `Field.init` still
  `Value.lean:271`, `Value.Valid` still `Validity.lean:130`, `reinterpret`'s
  `termination_by` still `Transform.lean:82`, `OneofPreservedAll`'s still
  `Transform.lean:388`, `Payload.reinterpret`'s `.msg` arm still
  `Transform.lean:132`.

## DONE 6. Typos and notation

Surviving from the 2026-09-16 review (all four the gaps note re-flagged):

- 70: "would would require"
- 76: "were we see the recursive type" → "where"
- 94: "From the prospective" → "perspective"
- 204: "However, we even if we present"

New in the rewritten text:

- 34: "were each index is the size" → "where"
- 73: missing prime, see 4.2
- 100: $G\ X = \mathtt{int} \times \mathtt{bool} \times \optt{X}$ uses raw
  `\mathtt{}` where line 96 uses the macros; should be
  $\ints \times \bool \times \optt{X}$
- 111, 176: $\Sigma, \varnothing$ and $\Sigma, A$ with a comma, against
  $\Sigma; A$ at 140, 143, 146, 150 and 213
- 111: $\Sigma$ first appears here, 25 lines before it is introduced (136)
- 154: "Co-induction is avoided for two independent finiteness facts" → "by"
- 168--169: "Every recursive call can add a pair so $A$ never shrinks so $A$ can
  grow to at most" — two `so`s; and
  $|\dom{\Sigma} \times \dom{\Sigma}| = \mathcal{O}(\dom{\Sigma}^2)$ needs bars
  on the right: $\mathcal{O}(|\dom{\Sigma}|^2)$
- 181: bare URL in `\footnote{}`; wants `\url{}` or a `pollux.bib` entry
- 188--190: "We saw this with the \texttt{Stream} example, which reveals an
  important semantic fact we can take advantage of rather than a naming
  discrepancy" — garbled
- 217: "We do not claim completeness for the logical relation" — completeness is
  a property of the *compatibility relation*, not of the logical relation
- 243: "a reasonably cheap options" → "option"
- 255: `% TODO` left in
- 257: "having a cyclic descriptor cyclic doesn't complicate" — stray "cyclic"
- 28 / 30: the hedge "(likely \emph{not} actually correct)" should go, per gaps
  item 3 — \textsc{N-Unfold} is now in the section and its premise *is* this
  rule, which is worth one sentence. Line 30 also says "the bound variable $X$"
  while the rule at 29 binds $x$.
- 78: \textsc{F-Msg} relates $\langle k, d_1[k] \rangle \propto \langle k, d_2[k] \rangle$.
  A field in `sec:proto-desc` is $\langle c, \tau \rangle$ (cardinality, type),
  so this reads as a field whose cardinality is a field number.
  `sec:inter-parse:358` writes it as
  $d_1 \ll d_2 \vdash \mathtt{F\_MSG}\ d_1 \propto \mathtt{F\_MSG}\ d_2$.

## 7. Verified against the Lean at `2002aed`

| Claim | Status | Location |
|-------|--------|----------|
| `compatInterParseOk` takes `d₁.AllWF`, `v.AllWF`, `d₂.AllWF`, `d₁ ⋘ d₂` | holds | `InterParse/Theorems/InterParseOk.lean:989`--`991` |
| `LimitParseOkCompat''` pins the encoding to the canonical serializer's output | holds | `Parse/Theorems.lean:665`--`671`, `Parse/Serializer.lean:20` |
| parse success is in the conclusion, not a hypothesis | holds | `Parse/Theorems.lean:671` |
| `Field.init`'s `.msg` arm returns `.optional none`, no descriptor recursion | holds | `Proto/Value.lean:271`--`276` |
| `reinterpretAt` falls back to `f₂.init` when the writer has no slot | holds | `Proto/Transform.lean:100`--`104` |
| the only recursive path is `Payload.reinterpret`'s `.msg`/`.msg` arm | holds | `Proto/Transform.lean:132` |
| `Value.Valid` is value-structural, descriptor via `get?` | holds | `Proto/Validity.lean:130`--`164` |
| `reinterpret` terminates on `4 * descSize d₂` | holds | `Proto/Transform.lean:82` |
| `Desc.OneofPreservedAll` is WF-recursion on `descSize d₂` | holds | `Proto/Transform.lean:388` |
| `limitRecursiveStateCompat_correct` is a step-indexed $\triangleright P \to P$ combinator | holds | `Parse/Theorems.lean:730`--`760` |
| it requires both a depth decrease and an input-length decrease | holds | `Parse/Theorems.lean:740`--`741` |
| `compatInterParseOk` instantiates `linkedState := a ⋘ b ∧ b.AllWF`, `depth := valueDepth` | holds | `InterParseOk.lean:1004` |
| `valueDepth` is nesting depth, not value size | holds | `InterParse/Descriptor.lean:685`--`693` |
| 533 cycles / longest 22 messages | in the report | `05-proto-desc.tex:374`--`376` (`tab:recur-summary`) |
| $E_\tau(v,bs)$ defined at value level, $\forall\ bs$ shape | in the report | `08-proto-relations.tex:74`, `:80` |
| `Encodes` / $\denote{d}$ defined outside `sec:type-theory` | absent | — |
| Amadio--Cardelli, Brandt--Henglein, TAPL, Appel--McAllester in `pollux.bib` | still absent | — |

## Blocked

Nothing in Lean waits on this. `Pollux.Proto`'s compatibility relations do not
exist yet, so `def:sem-compat`, `def:sem-assum` and `thm:fundamental` are the
statements to build them against once you have settled section 4's items 1 and 4
(the \textsc{D-Update} premise and the $\preceq$/$\ll$ split). The $\forall\ bs$
leg additionally waits on the `Encodes` lift discussed in section 3.
