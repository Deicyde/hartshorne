---
article_id: af_48d847ea51110e7a17d28bf9
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# The sheaf of local morphisms

For sheaves of abelian groups `F` and `G` on `X`, define a presheaf by

`U ↦ Hom(F|U, G|U)`

with restriction by restricting natural transformations, give these sets their
pointwise abelian-group structure, and prove that the result is a sheaf. This
is the additive sheaf Hom used for sheaves of modules on printed p. 109.

Mathlib's `CategoryTheory.sheafHom` proves the corresponding exact Type-valued
statement, but it does not expose Hartshorne's AddCommGrp-valued object, so the
source-shaped definition remains a project leaf.

## Depends on

- [Inverse image of a sheaf](inverse-image.md)

## Proof depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md)

## Sources

- [Hartshorne II.1, Exercise 1.15 (p. 67), used on p. 109](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)

