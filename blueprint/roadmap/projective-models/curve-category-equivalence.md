---
article_id: af_5bd96acb0a5232df552012b0
declaration: def
origin: cited
source_units: [chapter-i-section-6-projective-model]
---

# The curve/function-field category equivalence

The category of nonsingular projective curves with dominant morphisms is
equivalent to the category of quasi-projective curves with dominant rational
maps, and its opposite is equivalent to the category of one-dimensional
function fields with `k`-homomorphisms.  The sole main declaration is planned
as `Hartshorne.projectiveCurveFunctionFieldEquivalence`; its packaged data
must expose both equivalences asserted by Corollary 6.12.

Contravariance is part of the type: a field homomorphism `K₂ → K₁` gives a
map `C_{K₁} → C_{K₂}`.  Essential surjectivity uses the nonsingular
projective model.  Full faithfulness uses extension and uniqueness of dominant
rational maps, while the functor laws follow from that uniqueness.  The
quasi-projective and projective categories are compared by passing to dense
open representatives.

## Depends on

- [The three curve categories](curve-categories.md)

## Proof depends on

- [Extension of dominant rational maps](projective-rational-map-extension.md)
- [Projective models of curves](curve-projective-model.md)
- [Rational maps and function fields](../rational-maps/rational-map-function-field.md)
- [Nonsingular projective models of function fields](function-field-projective-model.md)

## Sources

- [Hartshorne I.6, Corollary 6.12 and its proof (pp. 45--46)](../../sources/hartshorne.md#i6-projective-models)
