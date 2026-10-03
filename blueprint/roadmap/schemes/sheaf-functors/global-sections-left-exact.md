---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Sheaf.sections_exact_of_left_exact
mathlib_file: Mathlib/Topology/Sheaves/AddCommGrpCat.lean
---

# Global sections are left exact

For every open `U`, if `0 ⟶ F' ⟶ F ⟶ F''` is exact as a sequence of
sheaves of abelian groups, then

`0 ⟶ F'(U) ⟶ F(U) ⟶ F''(U)`

is exact. This is exactly
`TopCat.Sheaf.sections_exact_of_left_exact` in the pinned checkout and is the
input Hartshorne cites in Proposition 5.6.

## Depends on

- [Kernels of sheaf morphisms](../sheaves/sheaf-kernels.md)

## Proof depends on

- [Limits of sheaves are computed pointwise](../sheaves/limits-of-sheaves.md)

## Sources

- [Hartshorne II.1, Exercise 1.8 (p. 66), used on p. 113](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
