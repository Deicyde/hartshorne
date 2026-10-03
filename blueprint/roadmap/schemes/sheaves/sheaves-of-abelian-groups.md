---
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Sheaf
mathlib_file: Mathlib/Topology/Sheaves/Sheaf.lean
---

# Sheaves of abelian groups

On a topological space `X`, a presheaf of abelian groups is a contravariant
functor from the category of open subsets of `X` to `AddCommGrpCat`. A sheaf is
such a functor in which compatible sections on an open cover glue uniquely.
Morphisms are natural transformations, and sections restrict functorially.

Use Mathlib's broader presheaf convention. Hartshorne additionally requires
zero sections on the empty open; for sheaves this follows from
`TopCat.Sheaf.isTerminalOfEmpty`, so no project-specific presheaf wrapper is
needed. The unique-gluing formulation is supplied by
`TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing`.

## Depends on

No project-local prerequisites.

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, definitions of presheaf and sheaf (p. 61)](../../../sources/hartshorne-ii-1.md#presheaves-and-sheaves-printed-p-61)
