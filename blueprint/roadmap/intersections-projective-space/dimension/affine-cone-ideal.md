---
article_id: af_de59d13f77cc40e1ae7b206d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.vanishingIdeal_affineCone
---

# The affine cone and its ideal

Let $Y\subseteq\mathbb P^n$ be a nonempty projective algebraic set.
Its *affine cone* $C(Y)\subseteq\mathbb A^{n+1}$ consists of the origin
and all nonzero homogeneous-coordinate representatives of points of $Y$.
It is an affine algebraic set and

$$I(C(Y))=J(Y),$$

where the homogeneous ideal on the right is viewed as an ordinary ideal
of $k[x_0,\ldots,x_n]$.

Homogeneity identifies the cone with the affine zero set of $J(Y)$,
including the origin. The ideal $J(Y)$ is radical, so the affine
Nullstellensatz recovers it exactly.

## Depends on

- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)
- [Algebraic sets and radical ideals](../../affine-varieties/radical-ideal-correspondence.md)

## Proof depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.2, Exercise 2.10(a), required in the proof of Theorem 7.2](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
