---
article_id: af_5bd96acb0a5232df552012b0
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveCurveFunctionFieldEquivalence
---

# The curve/function-field category equivalence

The function-field construction gives a contravariant equivalence between
nonsingular projective curves with dominant morphisms and finitely generated
function fields of transcendence degree one over $k$.

This is the composite of the projective/quasi-projective comparison with the
quasi-projective-curve/function-field equivalence. A field homomorphism
$K_2\to K_1$ induces a map $C_{K_1}\to C_{K_2}$, so the direction of
morphisms is reversed. The forward construction on curves is pullback of
rational functions.

## Depends on

- [The three curve categories](curve-categories.md)

## Proof depends on

- [Projective and quasi-projective curve categories are equivalent](projective-quasiprojective-curve-equivalence.md)
- [Quasi-projective curves and one-dimensional function fields are equivalent](quasiprojective-curve-function-field-equivalence.md)

## Sources

- [Hartshorne I.6, Corollary 6.12 and its proof (pp. 45--46)](../../sources/hartshorne.md#i6-projective-models)
