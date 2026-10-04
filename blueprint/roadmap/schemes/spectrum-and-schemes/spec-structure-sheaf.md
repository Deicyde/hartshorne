---
article_id: af_e41dd70530b195f86aa3a012
declaration: def
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: AlgebraicGeometry.Spec.structureSheaf
mathlib_file: Mathlib/AlgebraicGeometry/StructureSheaf.lean
---

# The structure sheaf on Spec

For an open `U ⊆ Spec A`, define `𝒪(U)` to consist of dependent functions
whose value at `𝔭` lies in `A_𝔭` and which locally have the form `a/f` with
the denominator outside every prime of the chosen neighbourhood.  Pointwise
ring operations and restriction make this a sheaf of commutative rings.

Mathlib implements the local-quotient predicate as
`StructureSheaf.isLocallyFraction` and packages the resulting sheaf as
`Spec.structureSheaf`.

## Depends on

- [The Zariski topology on Spec](spec-zero-loci.md)

## Sources

- [Hartshorne II.2, definition of the structure sheaf (p. 70)](../../../sources/hartshorne-ii-2.md#structure-sheaf-and-proposition-22)
