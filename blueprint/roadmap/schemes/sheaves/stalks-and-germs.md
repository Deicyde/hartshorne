---
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
mathlib: true
mathlib_declaration: TopCat.Presheaf.stalk
mathlib_file: Mathlib/Topology/Sheaves/Stalks.lean
---

# Stalks and germs

For a presheaf `F` and `x : X`, its stalk is the filtered colimit of `F(U)`
over open neighbourhoods of `x`. A section over a neighbourhood determines a
germ, and a presheaf morphism induces a functorial map on stalks.

Mathlib supplies this construction as `TopCat.Presheaf.stalk`, with
`stalkFunctor` and `germ`. Its concrete filtered-colimit API also states that
each stalk element is represented by a germ and characterizes equality after
restriction to a smaller neighbourhood.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, definition of the stalk and germs (p. 62)](../../../sources/hartshorne-ii-1.md#stalks-germs-and-morphisms-printed-pp-6263)
