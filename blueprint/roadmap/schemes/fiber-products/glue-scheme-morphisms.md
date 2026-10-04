---
article_id: af_1dc9a0a215615df771005773
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.Cover.glueMorphisms
mathlib_file: Mathlib/AlgebraicGeometry/Gluing.lean
---

# Gluing scheme morphisms

Morphisms from the members of an open cover of `X` to a scheme `Y` that agree on every pairwise overlap glue to a unique morphism `X → Y`.

Construct the map with `Scheme.Cover.glueMorphisms`. The supporting exact lemma
`Scheme.Cover.ι_glueMorphisms` proves the prescribed restrictions, and
`Scheme.Cover.hom_ext` gives uniqueness from equality on the cover.

## Depends on

- [Gluing schemes](../spectrum-and-schemes/gluing.md)
- [Open subschemes](../spectrum-and-schemes/open-subscheme.md)

## Proof depends on

- `Scheme.Cover.ι_glueMorphisms`, `Scheme.Cover.hom_ext`, the overlap
  pullbacks, and the scheme gluing universal property.

## Sources

- [Hartshorne II.3 (fiber-products-fibers-and-base-extension)](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
