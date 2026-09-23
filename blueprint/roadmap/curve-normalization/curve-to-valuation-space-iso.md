---
article_id: af_013c74c106370228b55e5404
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-abstract-curves]
---

# Nonsingular curves are open subcurves of their valuation spaces

Let `Y` be a nonsingular quasi-projective curve, let `K = K(Y)`, and let `U`
be the image of the point-to-local-ring map `Y → C_K`.  Then the resulting
homeomorphism

`Y ≃ U`

is an isomorphism from `Y` to the abstract nonsingular curve associated to the
open subset `U`.  This is Proposition 6.7.

It remains only to compare regular functions.  For every open `V ⊆ Y`, the
existing intersection theorem identifies its regular functions inside `K(Y)`
with

`⋂_{P ∈ V} 𝒪_{P,Y}`.

Under the point-to-local-ring homeomorphism this is exactly the definition of
regular functions on the corresponding open subset of `U`.  Residue
evaluation agrees with evaluation of a germ at `P`, so the homeomorphism and
its inverse both pull regular functions back to regular functions.

State the conclusion using `VarietyHom.IsIso`; do not weaken it to a
homeomorphism or a bare bijection.

## Depends on

- [Abstract nonsingular curves](abstract-nonsingular-curve.md)
- [The local-ring map has open image](curve-local-ring-map-open.md)

## Proof depends on

- [Residue fields of function-field DVRs](valuation-residue-field.md)
- [Global regular functions are the intersection of the local rings](../morphisms/global-functions/global-regular-intersection-local-rings.md)
- [Local rings are unchanged on open neighbourhoods](../nonsingular-varieties/local-ring-open-invariance.md)
- [Rational maps and function fields](../rational-maps/rational-map-function-field.md)

## Sources

- [Hartshorne I.6, Proposition 6.7 (pp. 42--43)](../../sources/hartshorne.md#i6-abstract-nonsingular-curves)
