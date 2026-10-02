---
article_id: af_ff73a1797a4821e2d824dc1d
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# A zero-dimensional projective variety is a point

Let `Y` be a projective variety. If

`projDim Y = 0`,

then there is a projective point `P` such that `Y = {P}`. The main
declaration is planned as
`Hartshorne.IsProjVariety.eq_singleton_of_projDim_eq_zero`.

Choose `P ∈ Y`. The singleton `{P}` is a projective variety of dimension zero.
If it were a proper closed subset of `Y`, strict dimension drop would force
its dimension below zero, contradicting the projective-point Hilbert
polynomial calculation. Thus `Y = {P}`. This is the Bézout closed-point bridge
used when Corollary 7.8 replaces zero-dimensional intersection components by
their points.

## Depends on

- [Projective and quasi-projective varieties](../../projective-varieties/projective-variety.md)
- [Proper closed subsets of projective varieties have smaller dimension](../dimension/projective-proper-closed-dimension-drop.md)

## Proof depends on

- [A projective point has Hilbert polynomial and degree one](projective-point-degree.md)
- [The homogeneous prime at a point](../../morphisms/projective-rings/point-ideal.md)

## Sources

- [Hartshorne I.7, proof of Corollary 7.8 (p. 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
