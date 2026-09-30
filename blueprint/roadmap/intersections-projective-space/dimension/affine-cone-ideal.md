---
article_id: af_de59d13f77cc40e1ae7b206d
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# The affine cone and its ideal

For a nonempty projective algebraic set `Y ⊆ ℙ(k, σ)`, define its affine cone
as the origin together with all nonzero affine representatives of points of
`Y`.  It is an affine algebraic set and its vanishing ideal is exactly the
homogeneous ideal `J(Y)`, regarded as an ordinary ideal of
`MvPolynomial σ k`.  The sole main declaration is planned as
`Hartshorne.vanishingIdeal_affineCone`.

First identify the geometric cone with `zeroLocus k (J(Y))`: homogeneity makes
vanishing independent of the chosen nonzero representative, and every
positive-degree homogeneous equation vanishes at the origin.  The homogeneous
ideal correspondence makes `J(Y)` radical, so the affine Nullstellensatz
recovers it exactly rather than only up to radical.

## Depends on

- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)
- [Algebraic sets and radical ideals](../../affine-varieties/radical-ideal-correspondence.md)

## Proof depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, Exercise 2.10(a), required in the proof of Theorem 7.2](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
