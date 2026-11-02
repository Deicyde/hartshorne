---
article_id: af_fd9faf4b83e613d588358c6c
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.isReduced_of_isReduced_stalk
mathlib_file: Mathlib/AlgebraicGeometry/Properties.lean
---

# Reduced schemes are detected on stalks

A scheme is reduced—every ring of sections has no nonzero nilpotents—if and
only if every local ring $\mathcal{O} _{X,x}$ is reduced.

For the local-to-global implication, a nilpotent section has zero
germ everywhere and is zero by the sheaf axiom. For the reverse
implication, a nilpotent germ has a nilpotent representative after
shrinking its neighbourhood. This is Hartshorne's Exercise II.2.3(a).

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)

## Sources

- [Hartshorne II.2, Exercise 2.3(a), used on p. 82](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)
