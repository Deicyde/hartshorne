---
article_id: af_73881b6e8d56162d53f2cfa2
declaration: class
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsReduced
mathlib_file: Mathlib/AlgebraicGeometry/Properties.lean
---

# Reduced schemes

A scheme `X` is reduced when every ring `Γ(X,U)` is reduced.

This leaf records Hartshorne's definition using Mathlib's `IsReduced` class.
Detection on stalks is already a separate II.2 result and is not bundled into
this declaration.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Proof depends on

- The ring-level predicate `IsReduced`.

## Sources

- [Hartshorne II.3 (reduced-integral-and-noetherian-schemes)](../../../sources/hartshorne-ii-3.md#reduced-integral-and-noetherian-schemes)
