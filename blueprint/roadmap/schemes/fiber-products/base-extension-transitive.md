---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: CategoryTheory.Limits.pullbackAssoc
mathlib_file: Mathlib/CategoryTheory/Limits/Shapes/Pullback/Assoc.lean
---

# Transitivity of base extension

For `S'' → S' → S`, there is a canonical isomorphism `(X ×_S S') ×_{S'} S'' ≅ X ×_S S''`, compatible with all projections.

Apply the associativity isomorphism for iterated pullbacks and simplify the identity leg of the resulting pullback.

## Depends on

- [Base extension](base-extension.md)

## Proof depends on

- Pullback associativity and the fact that pulling back along an identity is trivial.

## Sources

- [Hartshorne II.3 (fiber-products-fibers-and-base-extension)](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
