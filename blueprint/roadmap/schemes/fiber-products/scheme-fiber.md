---
article_id: af_c95901dee504501d1eb554dd
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.Hom.fiber
mathlib_file: Mathlib/AlgebraicGeometry/Fiber.lean
---

# The fiber of a morphism

For `f : X → Y` and `y ∈ Y`, the scheme-theoretic fiber is `X_y = X ×_Y Spec κ(y)`, naturally a scheme over the residue field `κ(y)`.

Instantiate the scheme pullback with the canonical morphism from the spectrum of the residue field of `y`.

## Depends on

- [Fiber products of schemes exist](schemes-have-fiber-products.md)
- [Field-valued points](../foundational-properties/field-valued-points.md)

## Proof depends on

- The canonical morphism `Spec κ(y) → Y` supplied by the field-valued-points
  equivalence.

## Sources

- [Hartshorne II.3 (fiber-products-fibers-and-base-extension)](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
