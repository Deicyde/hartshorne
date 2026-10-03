---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# A nodal plane projection exists

Let `X` be a curve embedded in `P^3`. There is a point `O notin X` such that
projection from `O` is birational onto its plane image and that image has no
singularities other than ordinary nodes.

This theorem is valid in every characteristic. The proof retains the
inseparable strange-curve branch used to establish the required good secants.
If `X` lies in a plane, choose `O` outside that plane; projection restricts
to an isomorphism from the plane onto the target plane, so the image is the
original nonsingular curve. The incidence argument handles the nonplanar case.

## Depends on

- [The nodal projection center criterion](../linear-series/nodal-projection-local-criterion.md)
- [The bad projection centers have dimension at most two](bad-center-dimension-bound.md)
- [The secant incidence has dimension at most three](../linear-series/secant-incidence-dimension.md)
- [A generically finite morphism is finite over a dense open](../../../schemes/normalization-and-exercises/generically-finite-becomes-finite.md)

## Proof depends on

- Separate the planar case by the projection isomorphism just described.
- Build the projective-line bundle of points on secants over
  `X times X minus diagonal`; it is not globally a chosen product with `P^1`.
- If its evaluation image has dimension three, generic finiteness gives an
  open set of centers lying on only finitely many secants; otherwise a center
  outside the image lies on none.
- Intersect that open with the complement of the dimension-two bad-center
  locus, then apply the nodal projection criterion.

## Sources

- [Hartshorne IV.3, Theorem 3.10, pp.313–314](../../../../sources/hartshorne-iv-3.md#nodal-projections-and-bad-secants-pp310314)
