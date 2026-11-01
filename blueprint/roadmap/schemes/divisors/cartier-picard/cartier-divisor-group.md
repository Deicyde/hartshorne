---
article_id: af_e7a329960aac05b71c31dfa5
declaration: abbrev
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.structureUnitsAddSheaf AlgebraicGeometry.Scheme.totalQuotientUnitsAddSheaf AlgebraicGeometry.Scheme.structureUnitsToTotalQuotientUnitsAdd AlgebraicGeometry.Scheme.cartierDivisorSheaf AlgebraicGeometry.Scheme.toCartierDivisorSheaf AlgebraicGeometry.Scheme.CartierDivisor
---

# The Cartier divisor group

For an arbitrary scheme `X`, define the sheaf of Cartier divisors as the
additive cokernel `K_X^* / O_X^*`, and define the Cartier divisor group as
`Γ(X, K_X^* / O_X^*)`.

Transport the multiplicative unit sheaves to additive commutative groups
before taking the cokernel, as in the source. Verify that this categorical
cokernel agrees with the explicit sheafified pointwise cokernel.

## Depends on

- [The total quotient sheaf](total-quotient-sheaf.md)
- [Quotient sheaves and their stalks](../../sheaves/quotient-sheaf-stalks.md)

## Proof depends on

- Injectivity of `O_X^* -> K_X^*` follows from the monomorphism
  `O_X -> K_X`.
- Cokernels of additive sheaves are computed by sheafifying the pointwise
  cokernel.

## Sources

- [Hartshorne II.6, Cartier divisor definitions on printed p.141](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)
