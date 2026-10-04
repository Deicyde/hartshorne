---
article_id: af_bbf20495425732b134fda979
declaration: def
origin: bridged
source_units: [chapter-iii-sections-1-4]
---

# Cohomological dimension

For a Noetherian separated scheme `X`, define `cd(X) : WithTop Nat` as the
infimum of the extended natural numbers `n` such that, for every
quasi-coherent `F` and every natural degree `i` with `n < i`,
`H^i(X,F)=0`. Thus `cd(X)=top` exactly when no finite bound exists.

When a finite least bound exists, this agrees with Hartshorne's definition in
Exercise 4.8.

## Depends on

- [Sheaf cohomology and the Ext model](../sheaf-cohomology/sheaf-cohomology.md)
- [Abelian closure of quasi-coherent sheaves](../../schemes/modules-and-quasicoherent/quasicoherent-abelian-closure.md)
- [Separated morphisms](../../schemes/separated-morphisms/separated-morphism.md)

## Proof depends on

- `top` is always a bound vacuously, so the defining infimum is over a
  nonempty set.

## Sources

- [Hartshorne III, Exercise 4.8, finite definition (p.224)](../../../sources/hartshorne-iii-3-4.md#adopted-exercises-and-later-use)
- [Project-authored extended-value convention](../../../sources/hartshorne-iii-3-4.md#project-authored-representation-choices)
