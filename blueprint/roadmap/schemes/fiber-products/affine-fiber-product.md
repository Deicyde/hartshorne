---
article_id: af_47bd3e64e420200b6686678a
declaration: def
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.pullbackSpecIso
mathlib_file: Mathlib/AlgebraicGeometry/Pullbacks.lean
---

# Fiber products of affine schemes

For $R$-algebras $A$ and $B$, $\operatorname{Spec} A \times _{\operatorname{Spec} R} \operatorname{Spec} B$ is canonically isomorphic to $\operatorname{Spec}(A\otimes_R B)$, and the two projections correspond to the tensor-product inclusions.

The tensor product is the pushout of commutative rings. Apply the contravariant $\operatorname{Spec}$ functor to obtain a pullback and identify its projections.

## Depends on

- [The universal property of a fiber product](fiber-product-universal-property.md)
- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)

## Proof depends on

- The tensor product is the pushout of commutative algebras.

## Sources

- [Hartshorne II.3 (fiber-products-fibers-and-base-extension)](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
