---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Affine.lean
---

# A finite principal-open affine criterion

If `f₁,…,fᵣ ∈ Γ(X,𝒪_X)` generate the unit ideal and every principal open
`X_{fᵢ}` is affine, then `X` is affine.  This criterion is the unique main
result of the article.

The displayed Lean theorem is the exact principal-open criterion of Exercise
2.17(b); Mathlib's `IsZariskiLocalAtTarget (isomorphisms Scheme)` supplies
part (a) as a proof input.  Glue the chart maps to `Spec Γ(X,𝒪_X)` and apply
target-locality.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- [Morphisms to an affine scheme](morphisms-to-affine.md)
- [The qcqs principal-open lemma](qcqs-principal-open-sections.md)

## Sources

- [Hartshorne II.2, Exercise 2.17(a),(b), used in Serre's affineness criterion](../../../sources/hartshorne-ii-2.md#exercises-212-through-219)
