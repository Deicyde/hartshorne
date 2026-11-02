---
article_id: af_10beeea75107994712e1057d
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveIntersectionMultiplicity
---

# Intersection multiplicity with a hypersurface

Let $Y\subseteq\mathbb P^n$ be a projective variety, let $H$ be a
hypersurface not containing $Y$, and let $Z$ be an irreducible component
of $Y\cap H$ with homogeneous prime ideal $\mathfrak p_Z$. Define

$$i(Y,H;Z)=\mu_{\mathfrak p_Z}\bigl(S/(I(Y)+I(H))\bigr).$$

This is a finite nonnegative integer. The component correspondence makes
$\mathfrak p_Z$ a minimal prime of the intersection module, so finiteness
follows from the graded-multiplicity theorem.

## Depends on

- [Multiplicity in a graded prime filtration](../hilbert/graded-multiplicity.md)
- [Projective intersection components on an affine chart](../dimension/projective-intersection-components.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, definition before Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
