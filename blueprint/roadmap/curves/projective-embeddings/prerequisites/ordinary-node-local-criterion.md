---
article_id: af_85b8c912e45f2b2c152b9ce5
declaration: definition
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.planeLocalEquation Hartshorne.IsPlaneDoublePoint Hartshorne.IsOrdinaryNode Hartshorne.translatedPlaneCurve Hartshorne.ordinaryNode_blowup Hartshorne.isOrdinaryNode_of_two_blowup_points
---

# Ordinary nodes and their two branches

A point $P$ of a plane curve is an ordinary node when it has multiplicity two
and the quadratic initial form of a local equation is a product of two
distinct linear factors. These factors are the two tangent directions.

Blowing up the plane curve at $P$ replaces the node by two distinct regular
points, one for each tangent direction. Conversely, a double point over
which the blown-up curve has two distinct points is an ordinary node; this
converse supplements Hartshorne's Exercise 5.6(b).

## Depends on

- [Blowing up a point](../../../rational-maps/blowing-up.md)
- [Intrinsic nonsingularity](../../../nonsingular-varieties/intrinsic-nonsingularity.md)

## Proof depends on

- On each standard blowup chart, divide the local equation by its exceptional
  factor; the two simple roots of the initial quadratic give the two regular
  points over $P$.
- [Hypersurfaces and codimension one](../../../affine-varieties/hypersurface-dimension.md)

## Sources

- [Hartshorne I.5, Exercise 5.6(b), p.37](../../../../sources/hartshorne.md#i5-exercises-and-exercise-only-prerequisite)
