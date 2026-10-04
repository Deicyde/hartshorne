---
article_id: af_dcdda2fad8a15289fa0cc489
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Gluing sheaves on an open cover

Let `{Uᵢ}` cover `X`, let `Fᵢ` be a sheaf on `Uᵢ`, and suppose isomorphisms
`φᵢⱼ : Fᵢ|Uᵢ∩Uⱼ ≅ Fⱼ|Uᵢ∩Uⱼ` satisfy the identity and cocycle conditions.
Construct a sheaf `F` on `X` with compatible isomorphisms `F|Uᵢ ≅ Fᵢ`, and
prove uniqueness up to unique isomorphism respecting those identifications.

Mathlib contains gluing machinery for presheafed and sheafed spaces, but no
exact theorem for sheaves on a fixed topological space was found. This node is
the prerequisite Hartshorne invokes for reduced induced subschemes on p. 86.

## Depends on

- [Inverse image of a sheaf](inverse-image.md)

## Proof depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md)

## Sources

- [Hartshorne II.1, Exercise 1.22 (p. 69), used on pp. 86 and 88](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
