---
article_id: af_a47f6234405f4e478248f773
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.projectiveIntersectionComponent_chart
---

# Projective intersection components on an affine chart

Let $W$ be an irreducible component of the intersection of projective
varieties $Y$ and $Z$, and choose a standard affine chart $U_i$ meeting
$W$. The chart image of $W\cap U_i$ is an irreducible component of the
intersection of the chart pieces of $Y$ and $Z$. The dimensions of $Y$,
$Z$, and $W$ agree with those of their respective chart pieces.

Restriction to an open subset transports any irreducible component meeting
it to a component of the open subspace. The chart homeomorphism then
transports the component to affine space. The dimensions agree because
the chosen chart meets all three varieties.

## Depends on

- [The standard affine charts](../../projective-varieties/standard-affine-charts.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)
- [Dimension in projective space](../../projective-varieties/projective-dimension.md)

## Proof depends on

- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.7, affine-chart reduction in the proof of Theorem 7.2](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
