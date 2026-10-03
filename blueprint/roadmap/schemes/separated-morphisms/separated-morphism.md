---
declaration: class
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsSeparated
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Separated.lean
---

# Separated morphisms

A morphism `f : X ⟶ Y` is separated when its diagonal
`pullback.diagonal f : X ⟶ X ×[Y] X` is a closed immersion. A scheme is
separated when its structure morphism to the terminal scheme `Spec ℤ` is
separated.

The pullback universal property constructs the diagonal and proves that its
two projections are the identity. Use Mathlib's existing morphism property and
scheme-level specialization rather than introducing another predicate.

## Depends on

- [The universal property of a fiber product](../fiber-products/fiber-product-universal-property.md)
- [Closed immersions and closed subschemes](../subschemes-and-dimension/closed-immersions.md)
- [The spectrum of the integers is terminal](../foundational-properties/spec-z-terminal.md)

## Proof depends on

- No proof beyond the defining pullback equations.

## Sources

- [Hartshorne II.4 (separatedness-and-the-valuative-criterion)](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)
