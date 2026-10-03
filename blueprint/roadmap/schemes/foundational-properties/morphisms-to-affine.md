---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.ΓSpec.adjunction
mathlib_file: Mathlib/AlgebraicGeometry/GammaSpecAdjunction.lean
---

# Morphisms to an affine scheme

For a scheme `X` and a commutative ring `A`, there is a natural equivalence

`Hom_Sch(X, Spec A) ≃ Hom_CommRing(A, Γ(X,𝒪_X))`.

This is Exercise 2.4.  Mathlib packages it as the Gamma–Spec adjunction; its
unit is `X → Spec Γ(X,𝒪_X)` and its counit is the global-section isomorphism
for a spectrum.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- [Spec is fully faithful](../spectrum-and-schemes/spec-fully-faithful.md)

## Sources

- [Hartshorne II.2, Exercise 2.4, used in products and later constructions (p. 79)](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)
