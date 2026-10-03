---
article_id: af_105e5c9ea0f8b6df2e6d90c7
declaration: definition
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Pointwise multiplicity for reducible plane curves

Let `Y,Z ⊆ ℙ²` be pure one-dimensional projective algebraic sets with no
common irreducible component.  Define the intersection multiplicity at a point
`P` by summing `projectiveIntersectionMultiplicity` over all pairs of
components `C ⊆ Y`, `D ⊆ Z` and all singleton components of `C ∩ D` whose
carrier contains `P`.

Prove that `Y ∩ Z` is finite and that summing this pointwise multiplicity over
its points is equal to the corresponding finite triple sum over component
pairs and their intersection components.  This is the reindexing bridge from
the existing irreducible-component multiplicity API to Hartshorne's pointwise
formulation for reducible curves.

## Depends on

- [Projective algebraic sets are finite unions of their components](projective-components-finite-cover.md)
- [Bézout's theorem for distinct plane curves](plane-curve-bezout.md)

## Proof depends on

- [A zero-dimensional projective variety is a point](projective-zero-dimensional-variety-point.md)

## Sources

- [Hartshorne I.7, Remark 7.8.2 (p. 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
