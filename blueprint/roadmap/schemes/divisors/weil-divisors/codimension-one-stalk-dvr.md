---
article_id: af_f4ea32035ecabdcf1674e94f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.codimensionOneStalk_isDiscreteValuationRing AlgebraicGeometry.Scheme.functionField_isFractionRing_of_stalk_of_satisfiesConditionStar AlgebraicGeometry.Scheme.ordHom_eq_codimensionOneStalkValuation AlgebraicGeometry.Scheme.ord_eq_codimensionOneStalkValuation
---

# Codimension-one stalks are DVRs

If $X$ satisfies $(*)$ and $x\in X$ is a point of codimension one,
then $\mathcal{O}_{X,x}$ is a discrete valuation ring with fraction
field $K(X)$. Its normalized valuation is the valuation attached to
the prime divisor with generic point $x$.

Thus the order of vanishing along that divisor is the corresponding
discrete valuation.

## Depends on

- [Regularity in codimension one](regular-in-codimension-one.md)
- [Affine opens have fraction field $K(X)$](../../normalization-and-exercises/function-field-integral-scheme.md)
- [Characterizations of discrete valuation rings](../../../nonsingular-curves/dvr-characterizations.md)

## Proof depends on

- The function field is the fraction field of the local ring.

## Sources

- [Hartshorne II.6, valuation of a prime divisor on printed p.130](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
