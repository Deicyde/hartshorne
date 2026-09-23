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

The next 24 leaves are planned in two independent fronts. One proves the exact
nonseparable integral-closure Theorems 3.9A and 6.3A. The other uses two
separable normalization charts to prove finite poles, construct affine models
of function-field DVRs, and build the abstract valuation-space curve through
Proposition 6.7. The expanded roadmap therefore has 138 leaves, with 114
complete and 24 planned.

Read the [coverage contract](../coverage/README.md) before reading progress off
this book: §§1–4, the geometric core of §5 through Theorem 5.3, and §6 through
Proposition 6.7 are decomposed here. The completion material later in §5 and
the projective-model material from Proposition 6.8 onward are deferred; the
unadopted exercises, §7 onward, and Chapters II–V are out of scope. The complete
source partition is recorded in the [source notes](../sources/hartshorne.md).

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
