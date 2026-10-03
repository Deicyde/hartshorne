---
declaration: class
origin: cited
source_units: [chapter-ii-section-4]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsProper
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Proper.lean
---

# Proper morphisms

A morphism is proper when it is separated, universally closed, and locally of
finite type. This is equivalent to Hartshorne's definition using finite type:
universal closedness already implies quasi-compactness, so local finite type
plus universal closedness supplies the missing finite-cover condition.

Use Mathlib's `IsProper` class. Its decomposition into reusable morphism
properties is exposed by `isProper_eq`; do not introduce a second predicate
using the project's finite-type conjunction.

## Depends on

- [Separated morphisms](../separated-morphisms/separated-morphism.md)
- [Universally closed morphisms](universally-closed-morphism.md)
- [Morphisms of finite type](../first-properties/finite-type.md)

## Proof depends on

- Universal closedness implies quasi-compactness.

## Sources

- [Hartshorne II.4, definition of properness](../../../sources/hartshorne-ii-4.md#properness-and-the-valuative-criterion)
