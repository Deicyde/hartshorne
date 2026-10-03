---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# Legendre normal form

Every pointed elliptic curve over an algebraically closed field of
characteristic different from two has a plane model

`y^2 = x*(x-1)*(x-lambda)`

with `lambda != 0,1`, carrying the chosen point to `(0:1:0)`. Projection to
the `x`-line is the degree-two map branched at `0,1,lambda,infinity`.

## Depends on

- [The general Weierstrass equation from a genus-one curve](elliptic-general-weierstrass-equation.md)
- [The Legendre S3 action](legendre-s3-action.md)

## Proof depends on

- Complete the square, factor the nonsingular cubic, and apply an affine
  coordinate change sending two distinct roots to `0,1`.

## Sources

- [Hartshorne IV.4, Proposition 4.6, pp.319–320](../../../../sources/hartshorne-iv-4.md)
