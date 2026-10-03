---
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: irreducibleSetEquivPoints
mathlib_file: Mathlib/Topology/Sober.lean
---

# Irreducible closed subsets have unique generic points

Every nonempty irreducible closed subset `Z` of a scheme `X` has a unique point
`η` with `closure {η} = Z`.

The stable upstream declaration `irreducibleSetEquivPoints` gives an order
equivalence between irreducible closed subsets and points in any quasi-sober
`T₀` space.  Schemes have both instances: quasi-sobriety is proved locally
from affine spectra and uniqueness follows from `T₀`.  Specializing that
stable declaration is exactly Exercise 2.9.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Sources

- [Hartshorne II.2, Exercise 2.9, already invoked by the comparison paragraph on p. 77](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)
