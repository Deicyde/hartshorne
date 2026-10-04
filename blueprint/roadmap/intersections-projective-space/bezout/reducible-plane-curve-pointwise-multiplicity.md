---
article_id: af_105e5c9ea0f8b6df2e6d90c7
declaration: definition
origin: bridged
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.reduciblePlaneCurveIntersectionMultiplicity
---

# Pointwise multiplicity for reducible plane curves

Let `Y,Z ⊆ ℙ²` be projective algebraic sets with
`projDim Y = projDim Z = 1`, every irreducible component carrier of either set
of projective dimension one, and no common component, meaning

`projectiveComponentCarrier C.1 ≠ projectiveComponentCarrier D.1`

for every `C : irreducibleComponents ↑Y` and
`D : irreducibleComponents ↑Z`.

For an ambient point `P`, define the natural-valued pointwise multiplicity
`reduciblePlaneCurveIntersectionMultiplicity Y Z P` by

`∑ C ∈ projectiveComponents Y, ∑ D ∈ projectiveComponents Z,`
`  ∑ W ∈ projectiveComponents`
`    (projectiveComponentCarrier C.1 ∩ projectiveComponentCarrier D.1),`
`  if P ∈ projectiveComponentCarrier W.1 then`
`    projectiveIntersectionMultiplicity C D W else 0`.

This definition is the unique main declaration. Supporting theorems prove
that `Y ∩ Z` is finite, that every component `W` occurring above has singleton
carrier, and that the sum of the pointwise multiplicities over the finite set
`Y ∩ Z` equals the displayed finite triple sum with the indicators removed.
This is a project-authored reindexing definition implementing the extension
asserted, but not defined, in Remark 7.8.2. The Lean declaration makes the
proof arguments implicit in the schematic multiplicity call precise.

## Depends on

- [Projective algebraic sets are finite unions of their components](projective-components-finite-cover.md)
- [Intersection multiplicity with a hypersurface](projective-intersection-multiplicity.md)

## Proof depends on

- [Bézout's theorem for distinct plane curves](plane-curve-bezout.md)
- [Projective codimension one is a hypersurface](../dimension/projective-codimension-one-hypersurface.md)
- [Proper closed subsets of projective varieties have smaller dimension](../dimension/projective-proper-closed-dimension-drop.md)
- [Proper hypersurface sections are equidimensional](hypersurface-section-components-equidimensional.md)
- [A zero-dimensional projective variety is a point](projective-zero-dimensional-variety-point.md)

## Sources

- [Hartshorne I.7, Remark 7.8.2 (p. 54)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
