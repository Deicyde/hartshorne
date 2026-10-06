---
article_id: af_60da3831a0a4680540efae3e
declaration: definition
origin: cited
source_units: [chapter-ii-sections-6-7]
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.totalQuotientPresheaf AlgebraicGeometry.Scheme.totalQuotientSheaf AlgebraicGeometry.Scheme.toTotalQuotientSheaf AlgebraicGeometry.Scheme.totalQuotientSheaf_mono AlgebraicGeometry.Scheme.structureUnitsSheaf AlgebraicGeometry.Scheme.totalQuotientUnitsSheaf AlgebraicGeometry.Scheme.structureUnitsToTotalQuotientUnits AlgebraicGeometry.Scheme.totalQuotientPresheaf_isFractionRing_of_isAffineOpen
---

# The total quotient sheaf

For an arbitrary scheme `X` and an affine open `U = Spec A`, define the total
quotient ring `K(U)` by inverting the non-zero-divisors of `A`. On a general
open `U`, invert the sections of `O_X(U)` whose germs are non-zero-divisors at
every point, and sheafify the resulting presheaf to obtain the sheaf of total
quotient rings `K_X`.

Also expose the sheaves of multiplicative units `K_X^*` and `O_X^*`. The
construction must not assume that `X` is reduced or integral.

## Depends on

- [The associated sheaf](../../sheaves/associated-sheaf.md)
- [Schemes and affine schemes](../../spectrum-and-schemes/scheme.md)

## Proof depends on

- Localization at the submonoid of non-zero-divisors.
- Compatibility of the affine and stalkwise definitions under restriction.

## Sources

- [Hartshorne II.6, total quotient rings and sheaf on printed p.141](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)
