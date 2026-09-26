---
article_id: af_0231ea26be501ebabff4b989
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
---

# Abstract valuation curves have dimension one

Every nonempty abstract nonsingular open curve in `C_K` is a curve: its
topological dimension is exactly one.  The sole main declaration is planned
as `Hartshorne.ValuationSpace.abstractNonsingularCurve_isCurve`.

The word "curve" here must retain the project's exact `IsCurve` contract; a
bound `dim ≤ 1` is not source-faithful.  The proof uses that a nonempty open
subset of the infinite cofinite space is infinite and has exactly the generic
point/closed-point chain length encoded by the current variety dimension.

## Depends on

- [Abstract nonsingular curves](../curve-normalization/abstract-nonsingular-curve.md)
- [Curves](../nonsingular-curves/curve.md)

## Proof depends on

- [Valuation-space topology](../curve-normalization/valuation-space/valuation-space-topology.md)
- [The valuation space is infinite](../curve-normalization/valuation-space/valuation-space-infinitude.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Sources

- [Hartshorne I.6, definition on p. 42 and Theorem 6.9 on p. 44](../../sources/hartshorne.md#i6-projective-models)
