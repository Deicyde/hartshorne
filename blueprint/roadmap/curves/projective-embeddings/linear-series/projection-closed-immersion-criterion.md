---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# Projection is an embedding away from secants and tangents

Let `X -> P^n` be an embedded Chapter IV curve and let `O` be a point outside
`X`. Construct projection from `O` as the morphism

`pi_O : X -> P^(n-1)`

defined by the subsystem of hyperplanes through `O`. Then `pi_O` is a closed
immersion if and only if `O` lies on no secant line and no embedded tangent
line of `X`.

## Depends on

- [Secant and tangent incidence for an embedded curve](secant-tangent-incidence-api.md)
- [Projection from a point is a morphism](../prerequisites/projection-from-point-morphism.md)
- [Morphisms from generated invertible sheaves](../../../schemes/projective-geometry/linear-systems-ampleness/morphism-from-generated-line-bundle.md)
- [Separation of points and tangent vectors](../../../schemes/projective-geometry/linear-systems-ampleness/separates-points-tangents-iff-closed-immersion.md)

## Proof depends on

- Hartshorne I Exercise 3.14 constructs projective projection from a point.
- Hyperplanes through `O` fail to separate `P,Q` exactly when `O` lies on
  their secant, and fail to separate the tangent direction at `P` exactly
  when `O` lies on the embedded tangent line.

## Sources

- [Hartshorne IV.3, Proposition 3.4, p.309](../../../../sources/hartshorne-iv-3.md)
