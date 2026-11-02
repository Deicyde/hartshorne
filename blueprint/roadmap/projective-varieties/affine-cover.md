---
article_id: af_cace6cae38334dde8edf5e10
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isAffineVariety_chartMap_image Hartshorne.isQuasiAffineVariety_chartMap_image Hartshorne.iUnion_standardChart Hartshorne.chartMap_image_eq_chartInv_preimage Hartshorne.homogeneousVanish_iff_eval_dehomogenize Hartshorne.dehomogenize_mem_vanishingIdeal_iff Hartshorne.homogeneousVanish_of_mem_homogeneousVanishingIdeal
---

# Varieties are covered by affine pieces

If $Y$ is a projective variety then the sets $Y \cap U_{i}$ for $i = 0,\ldots ,n$ form an
open cover of $Y$, and each is carried by $\varphi _{i}$ to an affine variety. If $Y$ is
quasi-projective the same holds with quasi-affine varieties (Corollary 2.3).

The cover is immediate — some homogeneous coordinate of any point is nonzero —
and the identification of the pieces is the chart homeomorphism restricted to
$Y$. The content is that irreducibility and the appropriate closedness survive
the restriction: $Y \cap U_{i}$ is a nonempty open subset of an irreducible space,
hence irreducible, and its image is closed in $\mathbb{A} ^{n}$ when $Y$ is closed in $\mathbb{P} ^{n}$.

Together with the previous node this is the statement that projective geometry
is locally affine, which is the organising idea of the rest of the book.

## The cover at the level of ideals

Theorem 3.4 needs the piece the topological statement leaves out: how $J(Y)$ and
$I(Y_{i})$ correspond. It is not that $\alpha$ carries one onto the other — it does not,
since $x_{i} - 1$ and its multiples are killed by $\alpha$ for free. What holds, for
homogeneous $g$, is

$\alpha (g) \in I(Y_{i}) \Longleftrightarrow x_{i} \cdot g \in J(Y)$,

and with a single power of $x_{i}$, not an unspecified one. The single power is the
geometry: $x_{i} \cdot g$ vanishes off the chart because $x_{i}$ does, and on the chart
because $g$ does. That is the shape a localisation at $x_{i}$ wants, which is why
it is the form recorded.

## Depends on

- [The standard affine charts](standard-affine-charts.md)
- [Projective and quasi-projective varieties](projective-variety.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)

## Sources

- [Hartshorne I.2, Corollary 2.3 (p. 11)](../../sources/hartshorne.md#i2)
