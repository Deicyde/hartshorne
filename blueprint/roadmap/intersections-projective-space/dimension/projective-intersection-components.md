---
article_id: af_a47f6234405f4e478248f773
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# Projective intersection components on an affine chart

Let `W` be an irreducible component of `Y ∩ Z` in projective space, and choose
a standard chart `U_i` meeting `W`.  Under the standard chart homeomorphism,
`W ∩ U_i` is an irreducible component of the intersection of the affine chart
pieces of `Y` and `Z`; moreover the dimensions of `Y`, `Z`, and `W` agree with
the dimensions of their respective chart pieces.  The sole main declaration
is planned as `Hartshorne.projectiveIntersectionComponent_chart`.

Restriction along the open embedding into `Y ∩ Z` transports an irreducible
component that meets the chart to an irreducible component of the open
subspace.  The chart homeomorphism then transports it to affine space.
Existing chart-dimension results identify the three dimensions because the
chosen chart meets all three varieties.

## Depends on

- [The standard affine charts](../../projective-varieties/standard-affine-charts.md)
- [Varieties are covered by affine pieces](../../projective-varieties/affine-cover.md)
- [Dimension in projective space](../../projective-varieties/projective-dimension.md)

## Proof depends on

- [Decomposition into irreducible components](../../affine-varieties/irreducible-decomposition.md)

## Sources

- [Hartshorne I.7, affine-chart reduction in the proof of Theorem 7.2](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
