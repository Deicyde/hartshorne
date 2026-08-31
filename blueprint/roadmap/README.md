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

The goal of the sections below is Corollary I.3.8: the functor sending an affine
variety to its coordinate ring is an arrow-reversing equivalence onto the
finitely generated integral domains over `k`. Getting there requires the
`Z`/`I` correspondence and the Nullstellensatz (§1), the same correspondence
made homogeneous together with the affine charts on `ℙⁿ` (§2), and the three
rings attached to a variety with their computation in the affine and projective
cases (§3).

Read the [coverage contract](../coverage/README.md) before reading progress off
this book: §§1–3 are decomposed here, and the rest of Hartshorne is located in
the [source notes](../sources/hartshorne.md) but carries no articles.

## Chapters

- [Affine varieties](affine-varieties/README.md) — Hartshorne I.1. The `Z`/`I`
  correspondence, the Nullstellensatz, irreducible decomposition, and dimension.
- [Projective varieties](projective-varieties/README.md) — Hartshorne I.2. The
  same dictionary made homogeneous, and the affine charts that make `ℙⁿ`
  locally affine.
- [Morphisms](morphisms/README.md) — Hartshorne I.3. Regular functions, the
  category of varieties, and the equivalence with finitely generated domains.
