---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# The scheme-theoretic image

For every morphism `f : Z → X`, there is a closed subscheme
`f.image → X` through which `f` factors, and it is initial among closed
subschemes with that property.

Reuse Mathlib's current API: `Scheme.Hom.image` is the subscheme defined by
`f.ker`, `Scheme.Hom.imageι` is its closed immersion, and
`Scheme.Hom.toImage_imageι` is the factorization. The `kerAdjunction` supplies
the universal comparison to every other closed factorization.

## Depends on

- [Closed immersions and closed subschemes](closed-immersions.md)

## Proof depends on

- `Scheme.Hom.image`, `Scheme.Hom.imageι`, `Scheme.Hom.toImage`, and
  `Scheme.kerAdjunction` from `Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean`.

## Sources

- [Hartshorne II.3 (subschemes-and-dimension)](../../../sources/hartshorne-ii-3.md#subschemes-and-dimension)
