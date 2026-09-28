---
article_id: af_bd9cf43e2cf8441147189992
declaration: def
origin: bridged
source_units: [chapter-i-section-6-projective-model]
---

# Quasi-projective curves and one-dimensional function fields are equivalent

The opposite of the category of quasi-projective curves with dominant
rational maps is equivalent to the category of one-dimensional function
fields with `k`-homomorphisms.  The sole main declaration is planned as
`Hartshorne.quasiProjectiveCurveFunctionFieldEquivalence`.

The forward functor forgets the chosen quasi-projective presentation and then
uses the function-field functor of Theorem 4.4.  It lands in transcendence
degree one by `HasAffineOpenBasis.isCurve_iff_trdeg_eq_one` and is fully
faithful by Theorem 4.4.  For essential surjectivity, realize a
one-dimensional function field affinely, pass to its projective closure, and
transport the function field and curve dimension across the resulting
birational equivalence.  Contravariance remains explicit in the source
category's opposite.  Only the forward function-field functor is fixed; no
definitional choice of quasi-inverse is asserted.

## Depends on

- [The three curve categories](curve-categories.md)

## Proof depends on

- [Rational maps and function fields](../rational-maps/rational-map-function-field.md)
- [Curves](../nonsingular-curves/curve.md)
- [The projective closure of an affine variety](../rational-maps/projective-closure.md)
- [Birational varieties have isomorphic function fields](../rational-maps/birational-function-fields.md)

## Sources

- [Hartshorne I.6, Corollary 6.12 and its proof (pp. 45--46)](../../sources/hartshorne.md#i6-projective-models)
