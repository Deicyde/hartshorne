---
declaration: theorem
origin: bridged
source_units: [chapter-iv-section-3]
---

# Projection from a strange point is inseparable

Let `X subset P^3` be strange with strange point `A`. Projection from `A` is
either constant, in which case `X` is a line, or its induced extension of
function fields is inseparable. In the nonconstant case the characteristic is
`p>0`; after choosing Samuel's affine coordinates, the coordinate functions
`y,z` on `X` belong to `K(X)^p`.

## Depends on

- [Strange curves and the basic examples](strange-curve-api.md)
- [Ramification has finite support](../../ramification/finite-ramification-support.md)
- [Differentials of finitely generated field extensions](../../../schemes/differentials/kaehler-differentials/field-differentials-dimension.md)

## Proof depends on

- Every tangent direction is killed by projection from `A`, so a nonconstant
  separable projection would be ramified everywhere, contradicting finite
  ramification support after normalizing the image.
- For a one-dimensional function field over the perfect field `k`, the kernel
  of the universal derivation is `K(X)^p`.

## Sources

- [Hartshorne IV.3, projection step in Theorem 3.9, p.312](../../../../sources/hartshorne-iv-3.md#nodal-projections-and-bad-secants-pp310314)
- [Samuel, *Lectures on Old and New Results on Algebraic Curves*](../../../../sources/hartshorne-iv-3.md#external-sources-and-blockers)
