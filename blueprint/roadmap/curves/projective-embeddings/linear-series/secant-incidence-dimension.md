---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-3]
---

# The secant incidence has dimension at most three

For an embedded Chapter IV curve `X -> P^n`, the union `Sec(X)` of actual
secant lines is a locally closed subset of projective space of dimension at
most three. It is the image of the secant incidence over `X times X` with the
diagonal removed, whose total dimension is at most three.

## Depends on

- [Secant and tangent incidence for an embedded curve](secant-tangent-incidence-api.md)
- [Dimension of a product](../../../intersections-projective-space/dimension/affine-product-dimension.md)
- [Dimension of a scheme](../../../schemes/subschemes-and-dimension/scheme-dimension.md)

## Proof depends on

- The incidence has a one-dimensional projective-line fibre over the
  two-dimensional parameter space `X times X` off the diagonal.
- Dimension does not increase under the image of a finite-type morphism, and
  Chevalley's theorem first makes that image constructible; the incidence
  closure and diagonal boundary analysis give the asserted locally closed
  stratum.

## Sources

- [Hartshorne IV.3, secant-variety estimate in Proposition 3.5, p.310](../../../../sources/hartshorne-iv-3.md)
