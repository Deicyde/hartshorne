---
article_id: af_f67130b01a3dcb9212031fa6
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# The Legendre Hasse polynomial

Assume `p != 2`, put `m=(p-1)/2`, and let

`X_lambda : y^2 z = x(x-z)(x-lambda*z)`

with `lambda != 0,1`. Define

`h_p(lambda) = sum_(i=0)^m binom(m,i)^2 * lambda^i`.

Then `X_lambda` has Hasse invariant zero exactly when
`h_p(lambda)=0`.

## Depends on

- [The plane-cubic coefficient criterion](plane-cubic-hasse-coefficient.md)

## Proof depends on

- Extract the coefficient of `(xyz)^(p-1)` from the two factors
  `(y^2z)^m` and `(x(x-z)(x-lambda*z))^m`.

## Sources

- [Hartshorne IV.4, Corollary 4.22, p.333](../../../../sources/hartshorne-iv-4.md#the-hasse-invariant-printed-pp332335)
