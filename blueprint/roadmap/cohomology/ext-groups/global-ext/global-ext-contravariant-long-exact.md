---
article_id: af_5c9140e60814e85734b627d4
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
mathlib: true
mathlib_declaration: CategoryTheory.Abelian.Ext.contravariantSequence_exact
mathlib_file: Mathlib/Algebra/Homology/DerivedCategory/Ext/ExactSequences.lean
---

# The contravariant long exact sequence of global Ext

For a short exact sequence `0 ⟶ F' ⟶ F ⟶ F'' ⟶ 0` and an object `G`, the
groups `Ext^n(-,G)` form the natural contravariant long exact sequence

`0 ⟶ Hom(F'',G) ⟶ Hom(F,G) ⟶ Hom(F',G) ⟶ Ext^1(F'',G) ⟶ ⋯`.

Pinned Mathlib's `Ext.contravariantSequence` constructs each six-term piece,
and `Ext.contravariantSequence_exact` is the exact main result.

## Depends on

- [Global Ext groups](global-ext-groups.md)

## Sources

- [Hartshorne III.6, Proposition 6.4, printed p.234](../../../../sources/hartshorne-iii-6.md#exact-sequences-and-locally-free-resolutions-printed-pp234235)
