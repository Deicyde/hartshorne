---
article_id: af_328d48a36735372ccbdec00c
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover
mathlib_file: Mathlib/AlgebraicGeometry/Pullbacks.lean
---

# Gluing local fiber products

If `{Xᵢ}` is an open cover of `X` and every `Xᵢ ×_S Y` exists, then these local products glue to a fiber product `X ×_S Y`.

Identify pairwise overlaps using the open-restriction theorem and uniqueness of pullbacks. The canonical identifications satisfy the cocycle condition. Glue the schemes and projections, then glue universal lifts.

## Depends on

- [Restricting a fiber product to an open subscheme](fiber-product-restrict-open.md)
- [Gluing scheme morphisms](glue-scheme-morphisms.md)

## Proof depends on

- Uniqueness of pullbacks and the scheme gluing theorem.

## Sources

- [Hartshorne II.3 (fiber-products-fibers-and-base-extension)](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
