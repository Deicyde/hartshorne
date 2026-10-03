---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
mathlib_file: Mathlib/Topology/Sheaves/Abelian.lean
---

# Exactness is detected on stalks

A complex of sheaves of abelian groups is exact if and only if its stalk at
every point is exact. Consequently stalks commute with kernels and images, and
a sheaf morphism is monic or epic exactly when every stalk map is injective or
surjective, respectively.

The main statement is exactly
`TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` in pinned Mathlib. The mono
clause is also supplied by `TopCat.Presheaf.mono_iff_stalk_mono`; the epi
clause follows from the locally-surjective API.

## Depends on

- [Stalks and germs](stalks-and-germs.md)
- [Kernels of sheaf morphisms](sheaf-kernels.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Caution 1.2.1 (p. 65) and Exercise 1.2(a–c) (p. 66)](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
