---
article_id: af_f0ee017b12507b77a218cfce
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# Dimension criteria for generated and very ample curve divisors

Let `D` be a divisor on a Chapter IV curve. Then:

1. `|D|` has no base points if and only if, for every closed point `P`,
   `dim|D-P| = dim|D|-1`;
2. `D` is very ample if and only if, for every pair of closed points `P,Q`,
   including `P=Q`,
   `dim|D-P-Q| = dim|D|-2`.

The dimensions lie in the integers. In the repeated-point case the divisor is
`D-2P`, and the condition detects separation of tangent vectors rather than
only separation of distinct points.

## Depends on

- [Divisor sections and complete linear systems](../../riemann-roch/curve-divisor-sections.md)
- [The point-divisor exact sequence](../../riemann-roch/point-divisor-exact-sequence.md)
- [Base-point-freeness and global generation](../../../schemes/projective-geometry/linear-systems-ampleness/basepoint-free-iff-generated.md)
- [Separation of points and tangent vectors](../../../schemes/projective-geometry/linear-systems-ampleness/separates-points-tangents-iff-closed-immersion.md)

## Proof depends on

- Global sections of the point-divisor sequence show that subtracting one
  point drops projective dimension by zero or one, and it drops by zero
  exactly at a base point.
- Apply the II.7 closed-immersion criterion separately to distinct points and
  to the first infinitesimal neighbourhood of one point.

## Sources

- [Hartshorne IV.3, Proposition 3.1, pp.307–308](../../../../sources/hartshorne-iv-3.md)
