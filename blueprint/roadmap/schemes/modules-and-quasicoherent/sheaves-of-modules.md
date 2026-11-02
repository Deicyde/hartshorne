---
article_id: af_d698b877b48593d5c5ce14ee
declaration: structure
origin: cited
mathlib: true
mathlib_declaration: SheafOfModules
mathlib_file: Mathlib/Algebra/Category/ModuleCat/Sheaf.lean
---

# Sheaves of modules

For a ringed space $(X, \mathcal{O}_X)$, define a sheaf of $\mathcal{O}_X$-modules as a presheaf
of modules whose underlying presheaf of abelian groups is a sheaf.  A morphism
acts linearly on sections over every open, and exactness is exactness of the
underlying sheaves of abelian groups.  The category is abelian and has all
limits and colimits, supplying Hartshorne's kernels, cokernels, images,
quotients, sums, products, and limits.

## Depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md)

## Proof depends on

- Limits and colimits of sheaves of modules, and the abelian structure on that
  category.

## Sources

- [Hartshorne II.5, definitions on printed p. 109](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
