---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.pullbackSpecIso
mathlib_file: Mathlib/AlgebraicGeometry/Pullbacks.lean
---

# Fiber products of affine schemes

For `R`-algebras `A` and `B`, `Spec A ×_{Spec R} Spec B` is canonically isomorphic to `Spec(A ⊗[R] B)`, and the two projections correspond to the tensor-product inclusions.

The tensor product is the pushout of commutative rings. Apply the contravariant `Spec` functor to obtain a pullback and identify its projections.

## Depends on

- [The universal property of a fiber product](fiber-product-universal-property.md)
- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)

## Proof depends on

- The pushout universal property of `Algebra.TensorProduct`.

## Sources

- [Hartshorne II.3 (fiber-products-fibers-and-base-extension)](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
