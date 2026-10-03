---
article_id: af_d30e42b7fc6d70a061a0fd65
---

# Hartshorne, Algebraic Geometry

A Lean 4 formalization of the classical variety theory in Chapter I of Robin
Hartshorne's *Algebraic Geometry*, built on Mathlib.

Chapter I develops algebraic geometry over a fixed algebraically closed field
with as little machinery as possible: no schemes, no sheaves, no cohomology.
That makes it the part of the book a formalization can attack directly, and it
is also the part Mathlib has not built. Mathlib's algebraic geometry starts at
`Spec` and works upward through schemes; the classical objects Hartshorne begins
with — an affine variety as an irreducible closed subset of `𝔸ⁿ`, its coordinate
ring, its regular functions — have no counterpart there.

The first destination is Corollary I.3.8: the functor sending an affine variety
to its coordinate ring is an arrow-reversing equivalence onto the finitely
generated integral domains over `k`. Getting there requires the `Z`/`I`
correspondence and the Nullstellensatz (§1), the same correspondence made
homogeneous together with the affine charts on `ℙⁿ` (§2), and the three rings
attached to a variety with their computation in the affine and projective cases
(§3). Section 4 then loosens isomorphism to birational equivalence and proves
the coarser classification: the function field determines a variety up to
birational equivalence.

The original I.1–I.4 scope is complete: 85 of its 86 leaves are proved in this
project and one is supplied by Mathlib. The geometric core of §I.5 through
Theorem 5.3 is complete as well: its regular-local/cotangent-space criterion is
an exact Mathlib result and the other 15 leaves are proved here. Across that
completed scope, all 102 formalization leaves are done: 100 in this project and
two in Mathlib. Theorem I.3.9A and the needed consequence of Exercise I.4.8(a)
enter only in the new milestone below.

The opening of §I.6 through Lemma 6.4 contributes 12 more leaves. They develop
valuation and DVR background, identify local rings of nonsingular curves as
discrete valuation rings in their function fields, and prove that the local
ring determines the point. All are complete: ten are proved in this project and
two are exact Mathlib results. Thus the completed 114-leaf portion contains 110
project formalizations and four Mathlib results.

The completed 26-leaf milestone has two independent fronts. One proves the exact
nonseparable integral-closure Theorems 3.9A and 6.3A. The other uses two
separable normalization charts to prove finite poles, construct affine models
of function-field DVRs, and build the abstract valuation-space curve through
Proposition 6.7. Both fronts are complete. The expanded roadmap therefore has
140 leaves, all formalized: 136 in this project and four in Mathlib.

The 23-leaf projective-model milestone adopts Exercise 3.3(a)–(c) where
Theorem 6.9 uses it, proves extension to projective targets, constructs
nonsingular projective models, and reaches the category equivalences of
Corollary 6.12. Exercise
3.3(a) is the existing completed local-ring map; the 23 new leaves comprise
two for Exercise 3.3(b),(c) and 21 for Proposition 6.8 through Corollary 6.12.
All are now formalized. The accepted fine roadmap therefore has 163 complete
leaves: 159 proved in this project and four supplied by Mathlib.

Hartshorne §I.7 has a 50-leaf fine roadmap developing the affine and projective
dimension theorems, integer-graded Hilbert theory, projective degree, and
Bézout. Forty-seven leaves are formalized and three remain; exact aggregate
progress is derived from the graph.

Read the [coverage contract](../coverage/README.md) before reading progress off
this book: §§1–4, the geometric core of §5 through Theorem 5.3, and §6 through
Corollary 6.12 are decomposed here. Apart from the regularity clause of
Theorem I.5.4A used in V.5, the remaining completion material is deferred;
§I.7 is finely decomposed, §I.8 is dispositioned claim by claim,
Chapter II has a fine schemes DAG, all of Chapter III has a fine cohomology
DAG, all of Chapter IV has a fine curves DAG, and all of Chapter V has a fine
surfaces DAG. Appendices A–C are
approved coarse milestones deferred
until their turn. The complete source partition is recorded in the
[source notes](../sources/hartshorne.md).

## Chapters

- [Affine varieties](affine-varieties/README.md) — Hartshorne I.1. The `Z`/`I`
  correspondence, the Nullstellensatz, irreducible decomposition, and dimension.
- [Projective varieties](projective-varieties/README.md) — Hartshorne I.2. The
  same dictionary made homogeneous, and the affine charts that make `ℙⁿ`
  locally affine.
- [Morphisms](morphisms/README.md) — Hartshorne I.3. Regular functions, the
  category of varieties, and the equivalence with finitely generated domains.
- [Rational maps](rational-maps/README.md) — Hartshorne I.4. Maps defined only
  on an open set, birational equivalence, and the classification of varieties by
  their function fields.
- [Nonsingular varieties](nonsingular-varieties/README.md) — Hartshorne I.5
  through Theorem 5.3. Regular local rings, the Jacobian criterion, and the
  proper closed singular locus.
- [Local structure of nonsingular curves](nonsingular-curves/README.md) — the
  opening of Hartshorne I.6 through Lemma 6.4. Valuation rings, DVRs, and the
  determination of a point by its local ring.
- [Normalization and the valuation-space curve](curve-normalization/README.md)
  — Theorems 3.9A and 6.3A, Hartshorne I.6.5–6.7, finite poles, affine DVR
  models, and abstract nonsingular curves.
- [Projective models of curves](projective-models/README.md) — Exercise
  I.3.3(a)–(c) as used by Theorem 6.9, Proposition I.6.8 through Corollary
  I.6.12, projective completions, and the contravariant function-field
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
- [Remaining-book roadmap](remaining-book/README.md) — approved coarse
  milestones for Appendices A–C.
