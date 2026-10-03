---
declaration: abbrev
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Scheme.Over
mathlib_file: Mathlib/AlgebraicGeometry/Over.lean
---

# Schemes over a base

A scheme over `S` is a scheme `X` with a structure morphism `X → S`.  A
morphism of `S`-schemes is a scheme morphism commuting with the two structure
maps.  These are the objects and morphisms of the slice category `Over S`.

Mathlib provides the categorical slice and the wrappers `Scheme.Over` and
`Scheme.Hom.IsOver`; `Scheme.Hom.isOver_iff` is the commuting-triangle
condition.

## Depends on

- [Schemes and affine schemes](scheme.md)

## Sources

- [Hartshorne II.2, schemes over a base (p. 78)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
