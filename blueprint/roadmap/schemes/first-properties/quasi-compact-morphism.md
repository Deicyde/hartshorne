---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean
---

# Quasi-compact morphisms

For a morphism `f : X → Y`, `QuasiCompact f` holds if and only if the inverse
image of every affine open of `Y` is quasi-compact.

The forward implication is immediate because affine opens are quasi-compact.
For the converse, cover a quasi-compact open of `Y` by finitely many affine
opens and use stability of compactness under finite unions.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- Affine opens form a basis and are quasi-compact.

## Sources

- [Hartshorne II.3 (finite-type-and-finite-morphisms)](../../../sources/hartshorne-ii-3.md#finite-type-and-finite-morphisms)
