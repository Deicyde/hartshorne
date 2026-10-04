---
article_id: af_250fea92495f2285d2e325da
declaration: theorem
origin: cited
source_units: [chapter-i-section-3-projection-exercise]
---

# Projection from a point is a morphism

Let `H ~= P^n_k` be a hyperplane in `P^(n+1)_k` and let `P` be a point not
on `H`. For `Q != P`, let `pi_P(Q)` be the intersection with `H` of the unique
line through `P` and `Q`. Then

`pi_P : P^(n+1)_k \ {P} -> H`

is a morphism. After projective coordinates put `P` at the omitted coordinate
point and `H` at the corresponding coordinate hyperplane, it is the morphism
defined by the remaining homogeneous coordinates.

## Depends on

- [Projective space over a scheme](../../../schemes/proper-and-projective/projective-space-over-scheme.md)
- [Morphisms from generated invertible sheaves](../../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)

## Proof depends on

- The remaining coordinates have no common zero away from `P` and define
  compatible morphisms on the standard affine charts.

## Sources

- [Hartshorne I.3, Exercise 3.14(a), p.22](../../../../sources/hartshorne.md#i3)
