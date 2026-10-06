---
article_id: af_f4ea32035ecabdcf1674e94f
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.codimensionOneStalk_isDiscreteValuationRing AlgebraicGeometry.Scheme.functionField_isFractionRing_of_stalk_of_satisfiesConditionStar AlgebraicGeometry.Scheme.ordHom_eq_codimensionOneStalkValuation AlgebraicGeometry.Scheme.ord_eq_codimensionOneStalkValuation
---

# Codimension-one stalks are DVRs

If `X` satisfies `(*)` and `x : X` has `coheight x = 1`, then the local ring
`O_{X,x}` is a discrete valuation ring. Its fraction field identifies with
`X.functionField`, so its normalized valuation is the valuation attached to
the prime divisor whose generic point is `x`.

This theorem supplies the precise hypothesis under which Mathlib's
`Scheme.ord` agrees with Hartshorne's DVR valuation.

## Depends on

- [Regularity in codimension one](regular-in-codimension-one.md)
- [Affine opens have fraction field `K(X)`](../../normalization-and-exercises/function-field-integral-scheme.md)
- [Characterizations of discrete valuation rings](../../../nonsingular-curves/dvr-characterizations.md)

## Proof depends on

- `Scheme.functionField_isFractionRing_of_stalk` and localization of the
  function field at a point.

## Sources

- [Hartshorne II.6, valuation of a prime divisor on printed p.130](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
