---
article_id: af_9d9300915c4c47e6aac793b5
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.dim_affineCone
---

# Dimension of the affine cone

For every nonempty projective algebraic set `Y`,

`dim (affineCone Y) = projDim Y + 1`.

The sole main declaration is planned as `Hartshorne.dim_affineCone`.  The
statement retains the full generality of Exercise I.2.10(c), rather than only
the projective-variety specialization used in Theorem 7.2.

For irreducible `Y`, the cone's coordinate ring is `S(Y)`, and the existing
homogeneous-coordinate-ring theorem gives the result.  For general nonempty
algebraic `Y`, pass to its finite irredundant decomposition: taking cones
commutes with that finite union, the preceding irreducibility result identifies
the components, and the dimension of a finite closed union is the maximum of
the component dimensions.

## Depends on

- [The affine cone and its ideal](affine-cone-ideal.md)
- [Irreducibility of the affine cone](affine-cone-irreducible.md)
- [Dimension of the homogeneous coordinate ring](../../projective-varieties/homogeneous-coordinate-ring-dimension.md)
- [Dimension is the dimension of the coordinate ring](../../affine-varieties/dim-eq-coordinate-ring-dim.md)

## Proof depends on

- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)
- [Projective and quasi-projective varieties](../../projective-varieties/projective-variety.md)

## Sources

- [Hartshorne I.2, Exercise 2.10(c), required in the proof of Theorem 7.2](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
