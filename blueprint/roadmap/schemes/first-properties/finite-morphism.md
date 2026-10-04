---
article_id: af_6f4cedce9dd6f4d6acb39f77
declaration: class
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsFinite
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Finite.lean
---

# Finite morphisms

A morphism `f : X → Y` is finite when every affine open `V ⊆ Y` has affine inverse image and the induced coordinate-ring map is module finite.

Use `IsFinite`, whose fields are the affine-morphism condition and module finiteness on affine target opens.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- Module finiteness is preserved under localization.

## Sources

- [Hartshorne II.3 (finite-type-and-finite-morphisms)](../../../sources/hartshorne-ii-3.md#finite-type-and-finite-morphisms)
