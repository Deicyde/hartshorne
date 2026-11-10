---
article_id: af_4efd62a06d98b4e4b1a19941
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projDim_univ Hartshorne.projDim_univ_fin Hartshorne.projDim_univ_add_one Hartshorne.projDim_eq_projDim_closure Hartshorne.closure_chartMap_image Hartshorne.isOpenMap_chartInv Hartshorne.chartMap_image_univ
---

# Dimension in projective space

$\dim \mathbb{P} ^{n} = n$, and if $Y \subseteq \mathbb{P} ^{n}$ is quasi-projective then $\dim Y = \dim \overline{Y}$
(Exercise 2.7).

The first follows from the previous node applied to $Y = \mathbb{P} ^{n}$. The second reduces
to the affine statement of [Proposition I.1.10](../affine-varieties/dim-quasi-affine.md) through the charts.

This closes §2: projective space has the dimension it should, and dimension is
insensitive to passing between a quasi-projective variety and its closure, so
later sections can compute dimension on whichever representative is convenient.


## Proof

Every standard affine chart of $\mathbb P^n$ is isomorphic to
$\mathbb A^n$. The charts cover projective space, so its dimension is $n$.
Equivalently, its homogeneous coordinate ring is the polynomial ring
$k[x_0,\ldots,x_n]$, of dimension $n+1$.

For a quasi-projective variety $Y$, a chart identifies $Y\cap U_i$ with
a quasi-affine variety whose closure is the chart image of
$\overline Y\cap U_i$. The affine equality
[\(\dim V=\dim\overline V\)](../affine-varieties/dim-quasi-affine.md),
together with the chart dimension comparison, gives
$\dim Y=\dim\overline Y$.

## Depends on

- [Projective and quasi-projective varieties](projective-variety.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [Dimension of the homogeneous coordinate ring](homogeneous-coordinate-ring-dimension.md)
- [Dimension of a quasi-affine variety](../affine-varieties/dim-quasi-affine.md)
- [Varieties are covered by affine pieces](affine-cover.md)
- [The dimension of affine space](../affine-varieties/dim-affine-space.md)

## Sources

- [Hartshorne I.2, Exercise 2.7 (p. 12)](../../sources/hartshorne.md#i2)
