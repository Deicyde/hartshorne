---
declaration: lemma
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Proper.lean
---

# Proper affine morphisms are finite

A scheme morphism is finite exactly when it is both proper and affine. In
particular, every proper morphism of affine varieties is finite, which is
Exercise 4.6.

On affine charts, properness gives universal closedness and local finite type.
The valuative intersection theorem makes the corresponding ring map integral;
finite type plus integrality makes it module-finite. Conversely, finite
morphisms are affine, separated, locally finite type, and universally closed.

The exact upstream equivalence is stronger than Hartshorne's stated affine-
variety direction and should be the public API.

## Depends on

- [Proper morphisms](proper-morphism.md)
- [Finite morphisms](../first-properties/finite-morphism.md)

## Proof depends on

- [Integral closure as an intersection of valuation rings](integral-closure-as-valuations.md)

## Sources

- [Hartshorne II.4, Exercise 4.6](../../../sources/hartshorne-ii-4.md#adopted-exercises)
