---
article_id: af_a4a0543ea6d3bb728811d630
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Tangent vectors and the dual numbers

Let `X` be a scheme over a field `k`, and let `x : X` be `k`-rational.  If
`D = k[ε]/(ε²)`, then `k`-morphisms `Spec D → X` whose closed point maps to
`x` correspond bijectively to the Zariski tangent space

`T_xX = Hom_k(𝔪_x/𝔪_x², k)`.

Use the field-valued-point classification to fix `x`, then identify the local
maps `𝒪_{X,x} → D` reducing to the residue map with `k`-derivations to `k`.
Such derivations vanish on `𝔪_x²` and are uniquely linear maps from
`𝔪_x/𝔪_x²`; conversely a linear functional defines the `ε` coefficient.
Mathlib supplies `DualNumber`, but no exact scheme-level equivalence was found.

## Depends on

- [Schemes and affine schemes](../spectrum-and-schemes/scheme.md)
- [Schemes over a base](../spectrum-and-schemes/over-base.md)

## Proof depends on

- [Field-valued points of a scheme](field-valued-points.md)

## Sources

- [Hartshorne II.2, Exercise 2.8, used in deformation theory and smoothness (p. 80)](../../../sources/hartshorne-ii-2.md#exercises-21-through-29)
