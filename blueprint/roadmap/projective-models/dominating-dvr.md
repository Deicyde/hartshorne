---
article_id: af_ac2003f542f79c13b0dab5f6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.HasAffineOpenBasis.exists_functionFieldDVR_dominating_localRing
---

# A dominating function-field DVR

Let $Y$ be a curve with an affine-open basis and $Q \in Y$.  There is a
discrete valuation ring of the function field $R \subseteq K(Y)$ dominating the image of $\mathcal{O} _{Q,Y}$ in
$K(Y)$.

Hartshorne uses this assertion parenthetically to prove surjectivity of the
projective diagonal.  A valuation ring dominates any local subring. In transcendence degree
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
- [The function field is the fraction field of every local ring](../nonsingular-curves/local-ring-fraction-field.md)

## Sources

- [Hartshorne I.6, parenthetical valuation-ring argument in the proof of Theorem 6.9 (p. 45)](../../sources/hartshorne.md#i6-projective-models)
