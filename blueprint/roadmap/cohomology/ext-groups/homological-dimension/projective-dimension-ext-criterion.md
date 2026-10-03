---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
mathlib: true
mathlib_declaration: CategoryTheory.hasProjectiveDimensionLT_iff
mathlib_file: Mathlib/CategoryTheory/Abelian/Projective/Dimension.lean
---

# Projective-dimension bounds detected by Ext

For an object `M` in an abelian category with `HasExt` and a natural number
`n`, Mathlib's predicate `HasProjectiveDimensionLT M n` is equivalent to

`∀ i ≥ n, ∀ N, Ext^i(M,N)=0`.

Consequently `HasProjectiveDimensionLE M n`, which abbreviates the preceding
predicate at `n+1`, is equivalent to vanishing in every degree `i>n`. For
modules this is Hartshorne's condition `pd(M)≤n`; the case `n=0` recovers that
`M` is projective iff `Ext^1(M,N)=0` for every `N`.

The exact main result is `hasProjectiveDimensionLT_iff`; the weak inequality
and projective criteria are stated consequences, not alternative definitions.

## Depends on

- [Global Ext groups](../global-ext/global-ext-groups.md)

## Sources

- [Hartshorne III.6, Proposition 6.10A, printed p.237](../../../../sources/hartshorne-iii-6.md#quoted-homological-algebra-printed-pp236237)
- Matsumura [2], pp.127–128, as cited by Hartshorne.
