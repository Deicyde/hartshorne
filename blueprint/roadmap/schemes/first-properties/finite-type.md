---
article_id: af_9c4d4fb277a1234fb29a6c06
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
lean: Hartshorne.FiniteType
---

# Morphisms of finite type

A morphism is of finite type exactly when it is locally of finite type and quasi-compact.

Use the conjunction `LocallyOfFiniteType f ∧ QuasiCompact f`; do not introduce a competing typeclass because Mathlib intentionally exposes the two reusable components.

## Depends on

- [Morphisms locally of finite type](locally-finite-type.md)
- [Quasi-compact morphisms](quasi-compact-morphism.md)

## Proof depends on

- Exercise 3.3(a), identifying Hartshorne's finite-cover clause with quasi-compactness.

## Sources

- [Hartshorne II.3 (finite-type-and-finite-morphisms)](../../../sources/hartshorne-ii-3.md#finite-type-and-finite-morphisms)
