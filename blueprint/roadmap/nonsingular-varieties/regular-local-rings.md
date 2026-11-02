---
article_id: af_3d9205412938cca078b5120b
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: IsRegularLocalRing.iff_finrank_cotangentSpace
mathlib_file: Mathlib/RingTheory/RegularLocalRing/Defs.lean
---

# Regular local rings

Let $A$ be a Noetherian local ring, let $\mathfrak m$ be its maximal
ideal, and let $\kappa=A/\mathfrak m$ be its residue field. The ring is
*regular* if

$$\dim_\kappa(\mathfrak m/\mathfrak m^2)=\dim A.$$

Equivalently, the minimal number of generators of the maximal ideal is
the dimension of the ring. Regularity is invariant under ring
isomorphisms, as used in the comparison of local rings on different charts.

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne I.5, definition of a regular local ring (p. 32)](../../sources/hartshorne.md#i5)
