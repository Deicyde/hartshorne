---
declaration: class
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsClosedImmersion
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean
---

# Closed immersions and closed subschemes

A morphism is a closed immersion when its underlying map is a closed embedding and its induced maps on stalks are surjective. A closed subscheme of `X` is such a morphism into `X`, considered up to isomorphism over `X`.

Represent the property by `IsClosedImmersion`. Represent closed subschemes by the full subcategory of objects over `X` satisfying that property, so isomorphic representatives are automatically identified categorically.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- Equivalence between sheaf surjectivity and stalkwise surjectivity.

## Sources

- [Hartshorne II.3 (subschemes-and-dimension)](../../../sources/hartshorne-ii-3.md#subschemes-and-dimension)
