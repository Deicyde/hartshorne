---
article_id: af_ac2003f542f79c13b0dab5f6
declaration: theorem
origin: cited
source_units: [chapter-i-section-6-projective-model]
---

# A dominating function-field DVR

Let `Y` be a curve with an affine-open basis and `Q ∈ Y`.  There is a
function-field DVR `R ⊆ K(Y)` dominating the image of `𝒪_{Q,Y}` in
`K(Y)`.  The sole main declaration is planned as
`Hartshorne.Variety.HasAffineOpenBasis.exists_functionFieldDVR_dominating_localRing`.

Hartshorne uses this assertion parenthetically to prove surjectivity of the
projective diagonal.  Mathlib supplies a valuation subring dominating any
local subring, but not the required discreteness.  In transcendence degree
one, Krull--Akizuki makes the valuation overring Noetherian and
one-dimensional; the nonfield valuation-ring criterion then makes it a DVR.

## Depends on

- [Curves](../nonsingular-curves/curve.md)
- [The local ring is a localisation](../morphisms/local-ring-is-localization.md)
- [Discrete valuation rings of a function field](../curve-normalization/function-field-dvrs.md)

## Proof depends on

- [Every local subring is dominated by a valuation ring](../nonsingular-curves/valuation-ring-dominates-local-subring.md)
- [The Krull--Akizuki theorem](../curve-normalization/krull-akizuki/krull-akizuki.md)
- [Dimension of the local ring of a variety](../nonsingular-curves/local-ring-dimension.md)
- [Characterizations of discrete valuation rings](../nonsingular-curves/dvr-characterizations.md)

## Sources

- [Hartshorne I.6, parenthetical valuation-ring argument in the proof of Theorem 6.9 (p. 45)](../../sources/hartshorne.md#i6-projective-models)
