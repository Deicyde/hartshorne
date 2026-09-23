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

Sections I.1–I.4 are complete: 85 of their 86 leaves are proved in this project
and one is supplied by Mathlib. The geometric core of §I.5 through Theorem 5.3
is complete as well: its regular-local/cotangent-space criterion is an exact
Mathlib result and the other 15 leaves are proved here. Across the roadmap, all
102 formalization leaves are complete: 100 in this project and two in Mathlib.

Read the [coverage contract](../coverage/README.md) before reading progress off
this book: §§1–4 and the geometric core of §5 through Theorem 5.3 are
decomposed here. The completion, Cohen-structure, and analytic-isomorphism
material later in §5 is deferred; Theorem 5.7A, the §5 exercises, §6 onward,
and Chapters II–V are out of scope. The complete source partition is recorded
in the [source notes](../sources/hartshorne.md).

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
