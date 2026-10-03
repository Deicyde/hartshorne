---
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: CategoryTheory.sheafificationAdjunction
mathlib_file: Mathlib/CategoryTheory/Sites/Sheafification.lean
---

# The associated sheaf

Every presheaf `F` has an associated sheaf `F⁺` and a canonical map
`F ⟶ F⁺` such that every map from `F` to a sheaf factors uniquely through
`F⁺`. Consequently the pair is unique up to unique isomorphism, and
sheafification of an existing sheaf is isomorphic to it.

The exact upstream result is the adjunction
`CategoryTheory.sheafificationAdjunction`; its unit is `toSheafify`, and
`sheafifyLift_unique` is Hartshorne's factorization uniqueness.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)

## Proof depends on

- [Stalks and germs](stalks-and-germs.md), for Hartshorne's explicit locally-germ construction.

## Sources

- [Hartshorne II.1, Proposition–Definition 1.2 (p. 64)](../../../sources/hartshorne-ii-1.md#associated-sheaves-printed-p-64)
