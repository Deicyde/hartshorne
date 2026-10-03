---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen
mathlib_file: Mathlib/AlgebraicGeometry/FunctionField.lean
---

# Affine opens have fraction field `K(X)`

Let `X` be integral and let `U ⊆ X` be a nonempty affine open. Then the
function field `X.functionField`, defined as the stalk at the generic point, is
a fraction ring of `Γ(X,U)`.

This is exactly `functionField_isFractionRing_of_isAffineOpen`. The supporting
function-field definition and field instance are existing API, but are not
additional main results of this leaf.

## Depends on

- [Integral if and only if reduced and irreducible](../first-properties/integral-iff-reduced-irreducible.md)

## Proof depends on

- Generic points of irreducible schemes and the affine stalk-localization theorem.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
