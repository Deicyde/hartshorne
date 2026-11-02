---
article_id: af_d30e42b7fc6d70a061a0fd65
---

# Hartshorne, Algebraic Geometry

An ordered guide to the definitions, theorems, and proof prerequisites in
Hartshorne's *Algebraic Geometry*, with links to their Lean 4 formalizations.

Chapter I begins with affine and projective varieties over a fixed
algebraically closed field. Coordinate rings, regular functions, and local
rings connect polynomial equations with geometry; rational maps and function
fields lead to birational equivalence and nonsingular curve models.

Chapters II and III introduce schemes, sheaves, and cohomology. They provide
the language used to study the curves and surfaces of Chapters IV and V.
The appendices develop intersection theory and Riemann–Roch, transcendental
methods, and the zeta-function and étale-cohomology framework of the Weil
conjectures.

## How to read this book

Choose a chapter below and start with its introduction. Individual statement
cards show the mathematics, source references, and current formalization
status. Follow **Depends on** for the definitions needed to understand a
statement, and **Proof depends on** for the additional results used to prove it.

The dependency map complements this reading order by showing connections
between topics and statements. A chapter's generated progress summary reports
its current formalization state without duplicating counts in the prose.

## Scope and progress

The [coverage contract](../coverage/README.md) records the adopted running
text, the exercises needed by later material, and the explicit exclusions and
deferred source obligations. Exact locators and supporting references are in
the [source notes](../sources/hartshorne.md).

Completed Chapter I milestones include the variety and coordinate-ring
correspondence, normalization and projective models of nonsingular curves,
and the intersection-theory development of Section I.7. Further results are
formalized in the later chapters. The individual cards and generated summaries
are the current record of what is proved and what remains.

A decomposed source area has explicit roadmap statements; it need not be
fully formalized. The fully proved percentage counts formalizable leaf
targets, while source coverage is tracked separately.

## Chapters

- [Affine varieties](affine-varieties/README.md) — Hartshorne I.1. The $Z$/$I$
  correspondence, the Nullstellensatz, irreducible decomposition, and dimension.
- [Projective varieties](projective-varieties/README.md) — Hartshorne I.2. The
  same dictionary made homogeneous, and the affine charts that make $\mathbb{P} ^{n}$
  locally affine.
- [Morphisms](morphisms/README.md) — Hartshorne I.3. Regular functions, the
  category of varieties, and the equivalence with finitely generated domains.
- [Rational maps](rational-maps/README.md) — Hartshorne I.4. Maps defined only
  on an open set, birational equivalence, and the classification of varieties by
  their function fields.
- [Nonsingular varieties](nonsingular-varieties/README.md) — Hartshorne I.5
  through [Theorem I.5.3](nonsingular-varieties/singular-locus.md). Regular local rings, the Jacobian criterion, and the
  proper closed singular locus.
- [Local structure of nonsingular curves](nonsingular-curves/README.md) — the
  opening of Hartshorne I.6 through
  [Lemma I.6.4](nonsingular-curves/local-ring-inclusion-determines-point.md).
  Valuation rings, DVRs, and the
  determination of a point by its local ring.
- [Normalization and the valuation-space curve](curve-normalization/README.md)
  — [Theorem I.3.9A](curve-normalization/finite-integral-closure.md) and
  [Theorem I.6.3A](curve-normalization/krull-akizuki/dedekind-integral-closure.md),
  Hartshorne I.6.5–6.7, finite poles, affine DVR
  models, and abstract nonsingular curves.
- [Projective models of curves](projective-models/README.md) — Exercise
  I.3.3(a)–(c) as used by
  [Theorem I.6.9](projective-models/function-field-projective-model.md),
  [Proposition I.6.8](projective-models/projective-extension.md) through
  [Corollary I.6.12](projective-models/curve-category-equivalence.md),
  projective completions, and the contravariant function-field
  equivalence.
- [Intersections in projective space](intersections-projective-space/README.md)
  — Hartshorne I.7, from dimension bounds through Hilbert polynomials and
  Bézout.
- [Schemes](schemes/README.md) — Hartshorne Chapter II: schemes, modules,
  divisors, projective geometry, differentials, and formal schemes.
- [Cohomology](cohomology/README.md) — Hartshorne Chapter III: derived
  functors, sheaf and projective cohomology, duality, families, smoothness,
  formal functions, semicontinuity, and base change.
- [Curves](curves/README.md) — Hartshorne Chapter IV: Riemann–Roch,
  ramification, elliptic and canonical curves, and space curves.
- [Surfaces](surfaces/README.md) — Hartshorne Chapter V: intersection theory,
  ruled and cubic surfaces, birational geometry, and numerical classification.
- [Intersection theory](intersection-theory/README.md) — Hartshorne Appendix A:
  Chow groups, Chern classes, positivity, and Riemann–Roch.
- [Intersection comparisons](intersection-comparisons/README.md) — downstream
  comparisons between Appendix A's Chow/cohomological products and the direct
  surface intersection theories of Chapter V.
- [Transcendental methods](transcendental-methods/README.md) — Hartshorne
  Appendix B: analytification, GAGA, algebraicity, and Picard theory.
- [Zeta functions and the Weil conjectures](weil-conjectures/README.md) —
  Hartshorne Appendix C: finite-field zeta functions, ℓ-adic cohomology,
  Frobenius traces, and the Weil theorem package.
- [Source and milestone ledger](remaining-book/README.md) — book passages,
  prerequisites, and source obligations for Chapters II–V and Appendices A–C.
