---
article_id: af_e597df3a5b7fded55fe3733e
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
---

# Transporting valuation curves along a field equivalence

A `k`-algebra equivalence `e : K ≃ₐ[k] L` between one-dimensional function
fields transports function-field DVRs and induces an isomorphism of their
abstract valuation curves, compatible with residue evaluation and regular
functions.  The sole main declaration is planned as
`Hartshorne.ValuationSpace.abstractNonsingularCurveIsoOfAlgEquiv`.

This bridge is required because Proposition 6.7 constructs the valuation curve
of each affine model's own `FunctionField`, while Theorem 6.9 must compare both
models inside the originally fixed field `K`.

## Depends on

- [Discrete valuation rings of a function field](../curve-normalization/function-field-dvrs.md)
- [Abstract nonsingular curves](../curve-normalization/abstract-nonsingular-curve.md)
- [The function field of an abstract nonsingular curve](../curve-normalization/valuation-space-function-field.md)

## Proof depends on

- [Residue fields of function-field DVRs](../curve-normalization/valuation-residue-field.md)
- [Regular functions on the valuation space](../curve-normalization/valuation-regular-functions.md)
- [Nonsingular curves are open subcurves of their valuation spaces](../curve-normalization/curve-to-valuation-space-iso.md)

## Sources

- [Hartshorne I.6, compatible function-field identifications in Theorem 6.9 (p. 44)](../../sources/hartshorne.md#i6-projective-models)
