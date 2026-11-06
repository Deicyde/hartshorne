---
article_id: af_dcdda2fad8a15289fa0cc489
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.SheafGluing.GluingData.exists_unique_gluing Hartshorne.SheafGluing.exists_unique_gluing_addCommGrp
---

# Gluing sheaves on an open cover

Let $\{U_{i}\}$ cover $X$, let $F_{i}$ be a sheaf on $U_{i}$, and suppose isomorphisms
$\varphi _{ij} : F_{i}|U_{i}\cap U_{j} \cong F_{j}|U_{i}\cap U_{j}$ satisfy the identity and cocycle conditions.
Construct a sheaf $F$ on $X$ with compatible isomorphisms $F|U_{i} \cong F_{i}$, and
prove uniqueness up to unique isomorphism respecting those identifications.

This is the gluing result invoked in the construction of reduced
induced subschemes.

## Depends on

- [Inverse image of a sheaf](inverse-image.md)

## Proof depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md)

## Sources

- [Hartshorne II.1, Exercise 1.22 (p. 69), used on pp. 86 and 88](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
