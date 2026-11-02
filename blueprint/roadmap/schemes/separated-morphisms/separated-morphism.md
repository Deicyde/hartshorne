---
article_id: af_f36463cd8b128458d64f56d7
declaration: class
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsSeparated
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/Separated.lean
---

# Separated morphisms

A morphism $f:X\to Y$ is separated when its diagonal
$\Delta_f:X\to X\times_Y X$ is a closed immersion. A scheme is
separated when its structure morphism to $\operatorname{Spec}\mathbb Z$
is separated.

The fiber-product universal property constructs the diagonal; both
of its projections are the identity of $X$.

## Depends on

- [The universal property of a fiber product](../fiber-products/fiber-product-universal-property.md)
- [Closed immersions and closed subschemes](../subschemes-and-dimension/closed-immersions.md)
- [The spectrum of the integers is terminal](../foundational-properties/spec-z-terminal.md)

## Proof depends on

- No proof beyond the defining pullback equations.

## Sources

- [Hartshorne II.4 (separatedness-and-the-valuative-criterion)](../../../sources/hartshorne-ii-4.md#separatedness-and-the-valuative-criterion)
