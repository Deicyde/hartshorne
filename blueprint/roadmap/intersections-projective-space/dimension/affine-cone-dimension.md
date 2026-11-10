---
article_id: af_9d9300915c4c47e6aac793b5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.dim_affineCone
---

# Dimension of the affine cone

For every nonempty projective algebraic set $Y$, its affine cone $C(Y)$
satisfies

$$\dim C(Y)=\dim Y+1.$$

This is Hartshorne's Exercise I.2.10(c), used for projective varieties in
[Theorem I.7.2](projective-dimension-theorem.md).

For irreducible $Y$, the coordinate ring of the cone is $S(Y)$, so the
homogeneous-coordinate-ring dimension theorem applies. For general
nonempty $Y$, take its finite irredundant decomposition. Taking cones
commutes with finite unions and preserves irreducibility, while the
dimension of a finite closed union is the maximum of the component
dimensions.

## Depends on

- [The affine cone and its ideal](affine-cone-ideal.md)
- [Irreducibility of the affine cone](affine-cone-irreducible.md)
- [Dimension of the homogeneous coordinate ring](../../projective-varieties/homogeneous-coordinate-ring-dimension.md)
- [Dimension is the dimension of the coordinate ring](../../affine-varieties/dim-eq-coordinate-ring-dim.md)

## Proof depends on

- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)
- [Projective and quasi-projective varieties](../../projective-varieties/projective-variety.md)
- [Projective space is a Noetherian space](../../projective-varieties/projective-space-noetherian.md)

## Sources

- [Hartshorne I.2, Exercise 2.10(c), required in the proof of Theorem 7.2](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
