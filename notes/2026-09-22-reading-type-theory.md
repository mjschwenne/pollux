Status: open
Report: sec:type-theory @ 3363eb4 (with uncommitted working-tree edits)
Lean:   none

# Reading list for the type-theoretic view of descriptors

## Summary

`2026-09-16-review-type-theory.txt` draws on four areas of PL theory: logical
relations, recursive subtyping, step-indexing with the Löb rule, and the
algebraic (functor and μF) view of recursive types. This note gives
graduate-level sources for each, in rough order of how much they matter for
Pollux.

All citations were written from memory. Check venues and years before any of
them go into `pollux.bib`.

## Where each term in the review comes from

| Term in the review                                   | Area                        | Start with                                   |
|------------------------------------------------------|-----------------------------|----------------------------------------------|
| logical relation, fundamental lemma                  | Logical relations           | Skorstengaard; Ahmed's OPLSS lectures        |
| syntactic `⊢` vs. semantic `⊨` judgment              | Semantic typing             | Dreyer et al. blog post                      |
| μ, fold/unfold, equi- vs. iso-recursive              | Recursive types             | TAPL ch. 20                                  |
| Amadio–Cardelli, Brandt–Henglein, Σ of assumed pairs | Recursive subtyping         | TAPL ch. 21; Gapeyev–Levin–Pierce            |
| regular trees, finitely many subterm pairs           | Recursive subtyping         | TAPL ch. 21                                  |
| Löb rule, step-indexing, Appel–McAllester            | Step-indexed models         | Appel–McAllester; Dreyer–Ahmed–Birkedal      |
| `F X`, `μX. F X`, functors                           | Initial algebras            | Jacobs–Rutten                                |
| coinduction, greatest fixed point                    | Coinduction                 | Kozen–Silva (already cited); TAPL §21.1      |

## If you only read three things

1. **Dreyer et al., "The Type Soundness Theorem That You Really Want to Prove
   (and Now You Can)"**, SIGPLAN PL Perspectives blog, 2018. It takes about an
   hour and covers the big picture. It explains semantic typing: you define
   what a type *means*, then prove each syntactic typing rule sound against
   that meaning. `sec:type-theory` is heading toward this setup, with the
   semantic `d₁ ≪ d₂` as the primary definition and the descriptor relation as
   a sound checker. The full-length version is Timany, Krebbers, Dreyer and
   Birkedal, *A Logical Approach to Type Soundness* (JACM 2024).
2. **Lau Skorstengaard, *An Introduction to Logical Relations*** (lecture
   notes, arXiv 2019). The best single introduction to logical relations. It
   goes from STLC normalization to parametricity and then to recursive types
   with step-indexing.
3. **Pierce, *Types and Programming Languages*, chapters 20–21.** Chapter 20
   introduces μ-types, fold/unfold, and equi- versus iso-recursive types.
   Chapter 21 bears most directly on the checker. It covers induction versus
   coinduction as least and greatest fixed points, regular trees, and the
   subtyping algorithm that carries a set of assumed pairs. It also shows why
   that set stays finite (the section on counting subexpressions). The
   review's Σ context is this algorithm with message names as the pairs.

## By topic

### Logical relations

- Amal Ahmed's OPLSS lectures on logical relations. The videos are on the
  OPLSS site and are a good companion to Skorstengaard.
- TAPL ch. 12 (Normalization) is the smallest complete example. Robert
  Harper's short note "How to (Re)Invent Tait's Method" explains *why* the
  definition looks the way it does.
- Karl Crary, "Logical Relations and a Case Study in Equivalence Checking", a
  chapter in Pierce (ed.), *Advanced Topics in Types and Programming
  Languages* (2005). It proves a decision procedure correct against a semantic
  notion of equivalence, which is closely analogous to proving the Pollux
  relation sound against the semantic definition.
- *Software Foundations* vol. 2, chapter `Norm`, works through the same
  material in Rocq.
- ReLoC (Frumin, Krebbers and Birkedal, already in `pollux.bib`). Its
  refinement judgment `e ⪯ e' : τ` is a logical relation, and the section's
  `⊨ f : d₁ ⪯ d₂` has the same shape.

### Recursive subtyping

- Gapeyev, Levin and Pierce, "Recursive Subtyping Revealed" (JFP 2002). The
  tutorial paper TAPL ch. 21 is based on. Read it before the originals.
- Brandt and Henglein, "Coinductive Axiomatization of Recursive Type Equality
  and Subtyping" (Fundamenta Informaticae 1998). The source of the section's
  "Löb rule". Its key rule lets you *assume* the conclusion, as long as the
  assumption is only used after passing through a type constructor. In
  Pollux, that constructor is the `.msg` payload.
- Amadio and Cardelli, "Subtyping Recursive Types" (TOPLAS 1993). The
  original. It's dense, so read it last or skim it.

### Step-indexing and the Löb rule

- Appel and McAllester, "An Indexed Model of Recursive Types for Foundational
  Proof-Carrying Code" (TOPLAS 2001). Short and readable.
- Nakano, "A Modality for Recursion" (LICS 2000). Where the "later" modality
  ▷ comes from.
- Dreyer, Ahmed and Birkedal, "Logical Step-Indexed Logical Relations" (LICS
  2009). Where Löb induction became the standard proof principle for logical
  relations.
- Birkedal and Bizjak, *Lecture Notes on Iris*. Covers ▷ and Löb with
  exercises. The guarded-modality parser-combinator paper already in
  `pollux.bib` (Allais) uses the same modality in a parsing setting.

Caveat: protobuf values are always finite, so in Pollux the "step index" is
just the size of the value, and ordinary well-founded induction is enough.
Read this literature to understand why the Löb rule is sound in general, and
to see that Pollux is the easy case. Pollux doesn't need its heavier
machinery.

### Functors and μF

- Jacobs and Rutten, "A Tutorial on (Co)Algebras and (Co)Induction" (EATCS
  Bulletin, 1997). Explains why `F X = int × option X` is a functor, what the
  least fixed point μF is, and where the fold/unfold correspondence comes
  from.
- Harper, *Practical Foundations for Programming Languages* (2nd ed., 2016).
  See the chapters on generic programming, inductive and coinductive types,
  and recursive types, plus the later chapters on equality and parametricity.
- Kozen and Silva, "Practical Coinduction" (already in `pollux.bib`) is a good
  bridge between the two views.

### Closest to Pollux itself

- Fisher, Mandelbaum and Walker, "The Next 700 Data Description Languages"
  (POPL 2006; JACM 2010). Gives a type-theoretic semantics to data
  description languages, where each description is read as both a type and a
  parser. The nearest published relative of treating a descriptor as a type,
  and a plausible citation for `sec:type-theory`.

## Suggested order

1. The Dreyer et al. blog post.
2. Skorstengaard (or Ahmed's lectures) through the step-indexing chapter.
3. TAPL chapters 20–21.
4. Brandt–Henglein, which should make the section's rule look familiar.
5. Appel–McAllester and Jacobs–Rutten, as needed.
