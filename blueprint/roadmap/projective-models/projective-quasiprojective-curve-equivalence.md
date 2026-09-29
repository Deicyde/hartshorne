---
article_id: af_8e64f12c6fbbdf121cc5ab92
declaration: def
origin: bridged
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveQuasiProjectiveCurveEquivalence
---

# Projective and quasi-projective curve categories are equivalent

The functor from nonsingular projective curves with dominant morphisms to
quasi-projective curves with dominant rational maps is an equivalence of
categories.  The sole main declaration is planned as
`Hartshorne.projectiveQuasiProjectiveCurveEquivalence`.

The functor regards a projective presentation as quasi-projective and sends a
dominant morphism to its full-domain rational map.  Full faithfulness is the
unique-extension theorem for dominant rational maps, and essential
surjectivity is Corollary 6.11: every curve is birational to a nonsingular
projective curve.  The forward functor is fixed by this description; no
definitional choice of quasi-inverse is asserted.

## Depends on

- [The three curve categories](curve-categories.md)

## Proof depends on

- [Extension of dominant rational maps](projective-rational-map-extension.md)
- [Projective models of curves](curve-projective-model.md)

## Sources

- [Hartshorne I.6, Corollary 6.12 and its proof (pp. 45--46)](../../sources/hartshorne.md#i6-projective-models)
