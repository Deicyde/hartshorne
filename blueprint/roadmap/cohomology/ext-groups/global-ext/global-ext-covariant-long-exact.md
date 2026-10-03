---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
mathlib: true
mathlib_declaration: CategoryTheory.Abelian.Ext.covariantSequence_exact
mathlib_file: Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean
---

# The covariant long exact sequence of global Ext

For an object `F` and a short exact sequence
`0 ⟶ G' ⟶ G ⟶ G'' ⟶ 0`, the groups `Ext^n(F,-)` form the natural
covariant long exact sequence

`0 ⟶ Hom(F,G') ⟶ Hom(F,G) ⟶ Hom(F,G'') ⟶ Ext^1(F,G') ⟶ ⋯`.

Pinned Mathlib's `Ext.covariantSequence` constructs each six-term piece, and
`Ext.covariantSequence_exact` is the exact main result.

## Depends on

- [Global Ext groups](global-ext-groups.md)

## Sources

- [Hartshorne III.6, derived-functor properties, printed p.233](../../../../sources/hartshorne-iii-6.md#definitions-and-restriction-printed-pp233234)
