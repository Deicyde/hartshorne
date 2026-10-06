---
article_id: af_0fa1175e2576c8992d008986
declaration: definition
origin: cited
source_units: [chapter-ii-sections-6-7]
statement: formalized
lean: AlgebraicGeometry.Scheme.IsRegularInCodimensionOne AlgebraicGeometry.Scheme.SatisfiesConditionStar
---

# Regularity in codimension one

Define a scheme `X` to be regular in codimension one when every point `x`
with `coheight x = 1` has a regular local ring `O_{X,x}`. Package
Hartshorne's standing condition `(*)` as the conjunction that `X` is
Noetherian, integral, separated, and regular in codimension one.

The completion criterion is this scheme-level predicate and its projections;
no global regularity or local-factoriality is included in the definition.

## Depends on

- [Codimension in a scheme](../../subschemes-and-dimension/scheme-codimension.md)
- [Integral schemes](../../first-properties/integral-scheme.md)
- [Noetherian schemes and finite affine covers](../../first-properties/noetherian-scheme.md)
- [Separated morphisms](../../separated-morphisms/separated-morphism.md)

## Proof depends on

- `ringKrullDim_stalk_eq_coheight` for translating Hartshorne's
  one-dimensional-local-ring formulation.

## Sources

- [Hartshorne II.6, definition and condition `(*)` on printed p.130](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
