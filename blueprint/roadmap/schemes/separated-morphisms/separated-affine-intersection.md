---
declaration: lemma
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsAffineOpen.inf
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Affine.lean
---

# Affine intersections in a separated scheme

If the diagonal of a scheme `X` is affine, the intersection `U ⊓ V` of two
affine opens is affine. In particular this holds when `X` is separated, because
a closed immersion is affine.

Identify the intersection with the pullback of `U → X ← V`. This pullback
is also obtained from the diagonal of `X` by base change along
`U × V → X × X`. Affineness is stable under base change, so the pullback
is affine. This is the form later used to make all finite intersections in an
affine cover affine.

## Depends on

- [Separated morphisms](separated-morphism.md)
- [The universal property of a fiber product](../fiber-products/fiber-product-universal-property.md)

## Proof depends on

- Closed immersions are affine and affine morphisms are stable under base
  change.

## Sources

- [Hartshorne II.4, Exercise 4.3](../../../sources/hartshorne-ii-4.md#adopted-exercises)
