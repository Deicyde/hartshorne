---
article_id: af_f6b00ffd802f94ba2fdc9a07
declaration: definition
origin: cited
mathlib: true
mathlib_declaration: TopCat.Presheaf.stalk
mathlib_file: Mathlib/Topology/Sheaves/Stalks.lean
---

# Stalks and germs

For a presheaf $F$ and $x \in X$, its stalk is the filtered colimit of $F(U)$
over open neighbourhoods of $x$. A section over a neighbourhood determines a
germ, and a presheaf morphism induces a functorial map on stalks.

Every stalk element is represented by a germ of a section. Two
representatives define the same germ exactly when they agree after
restriction to a smaller neighbourhood.

## Depends on

- [Sheaves of abelian groups](sheaves-of-abelian-groups.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, definition of the stalk and germs (p. 62)](../../../sources/hartshorne-ii-1.md#stalks-germs-and-morphisms-printed-pp-6263)
