---
declaration: structure
origin: cited
source_units: [chapter-ii-section-5]
mathlib: true
mathlib_declaration: SheafOfModules
mathlib_file: Mathlib/Algebra/Category/ModuleCat/Sheaf.lean
---

# Sheaves of modules

For a ringed space `(X, O_X)`, define a sheaf of `O_X`-modules as a presheaf
of modules whose underlying presheaf of abelian groups is a sheaf.  A morphism
acts linearly on sections over every open, and exactness is exactness of the
underlying sheaves of abelian groups.  The category is abelian and has all
limits and colimits, supplying Hartshorne's kernels, cokernels, images,
quotients, sums, products, and limits.

Mathlib's `SheafOfModules` is stated more generally for a sheaf of rings on a
site; a topological ringed space is the instance used here.  For a scheme `X`,
the notation `X.Modules` specializes this construction to its structure
sheaf.

## Depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md)

## Proof depends on

- Limits and colimits of sheaves of modules, and the abelian structure on that
  category.

## Sources

- [Hartshorne II.5, definitions on printed p. 109](../../../sources/hartshorne-ii-5.md#modules-quasi-coherence-and-exactness)
