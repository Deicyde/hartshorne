---
article_id: af_1f107512e01c4032a330c528
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projective_inter_nonempty_of_dim
---

# Projective varieties of complementary dimension meet

Let $Y,Z\subseteq\mathbb P^n$ be projective varieties of dimensions
$r,s$. If $n\leq r+s$, then $Y\cap Z$ is nonempty.

Their affine cones are varieties of dimensions $r+1$ and $s+1$ in
$\mathbb A^{n+1}$, both containing the origin. The affine dimension theorem
shows that a component of the cones' intersection has positive dimension.
It therefore contains a point other than the origin. Projectivizing that
point gives a point of $Y\cap Z$.

## Depends on

- [The affine cone and its ideal](affine-cone-ideal.md)
- [Irreducibility of the affine cone](affine-cone-irreducible.md)
- [Dimension of the affine cone](affine-cone-dimension.md)
- [The affine dimension theorem](affine-dimension-theorem.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](../../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.7, second clause of Theorem 7.2 (pp. 48--49)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
