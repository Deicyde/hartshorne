---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.limit_isSheaf
mathlib_file: Mathlib/Topology/Sheaves/Limits.lean
---

# Kernels of sheaf morphisms

The pointwise kernel of a morphism of sheaves of abelian groups satisfies the
sheaf condition. It is therefore the categorical kernel in the sheaf category,
and a sheaf morphism is monic exactly when all its maps on sections are
injective.

Mathlib's `TopCat.limit_isSheaf` proves the general result that a pointwise
limit of sheaves is a sheaf; kernels are its walking-parallel-pair instance.
The forgetful functor from sheaves creates these limits.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, presheaf kernels and injective sheaf morphisms (pp. 63–64)](../../../sources/hartshorne-ii-1.md#kernels-images-quotients-and-exactness-printed-pp-6365)
