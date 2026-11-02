---
article_id: af_2b64070bd52242f68017926b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projective_dimension_theorem
---

# The projective dimension theorem for components

Let $Y,Z\subseteq\mathbb P^n$ be projective varieties and let $W$ be
an irreducible component of $Y\cap Z$. Then

$$\dim Y+\dim Z\leq\dim W+n.$$

This is Hartshorne's Theorem I.7.2, equivalently
$\dim W\geq\dim Y+\dim Z-n$.

Choose a standard affine chart meeting $W$. The chart-component theorem
identifies its image with an irreducible component of the intersection of
the two chart pieces and preserves all three dimensions. The affine
dimension theorem in this chart gives the result.

## Depends on

- [The affine dimension theorem](affine-dimension-theorem.md)
- [Projective intersection components on an affine chart](projective-intersection-components.md)

## Sources

- [Hartshorne I.7, first clause of Theorem 7.2 (pp. 48--49)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
