---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: CategoryTheory.Sheaf.isSheaf_of_isLimit
mathlib_file: Mathlib/CategoryTheory/Sites/Limits.lean
---

# Limits of sheaves are computed pointwise

The category of sheaves of abelian groups admits products and inverse limits,
and the underlying presheaf of such a limit is the pointwise limit. In
particular, for an inverse system `{Fᵢ}` and every open `U`,

`(lim Fᵢ)(U) ≅ lim Fᵢ(U)`.

The unique main result is the pointwise-limit assertion. Pinned Mathlib proves
that a limiting presheaf of sheaves is a sheaf in
`CategoryTheory.Sheaf.isSheaf_of_isLimit`; the resulting
`createsLimitsOfShape` instance says that the forgetful functor creates these
limits. The product half of Exercise 1.9 and Exercise 1.12 are instances.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Exercises 1.9 and 1.12 (pp. 66–67), used on p. 109 and in Proposition 9.2](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)

