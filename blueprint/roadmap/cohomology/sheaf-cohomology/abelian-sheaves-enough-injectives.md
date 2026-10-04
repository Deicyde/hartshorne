---
article_id: af_5ddce4f07a05e48ab6f2631d
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-1-4]
mathlib: true
mathlib_declaration: CategoryTheory.IsGrothendieckAbelian.enoughInjectives
mathlib_file: Mathlib/CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean
---

# Abelian sheaves have enough injectives

For every topological space `X`, the abelian category of sheaves of abelian
groups on `X` has enough injectives.

Pinned Mathlib makes `TopCat.Sheaf AddCommGrpCat X` a Grothendieck abelian
category in `Mathlib/Topology/Sheaves/Abelian.lean`; the generic instance
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives` then supplies this
exact result. This route does not identify abelian sheaves with module sheaves.

## Depends on

- [Sheaves of abelian groups](../../schemes/sheaves/sheaves-of-abelian-groups.md)

## Sources

- [Hartshorne III.2, Corollary 2.3, printed p. 207](../../../sources/hartshorne-iii-1-2.md#enough-injectives-and-cohomology-printed-pp-206208)
