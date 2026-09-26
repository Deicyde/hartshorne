---
article_id: af_27f35d9b8908d59f68689bd5
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
---

# The function field of the diagonal model

For the dense projective diagonal `φ : C_K → Y`, the induced map on
function fields identifies `K(Y)` with `K` as `k`-algebras.  The sole main
declaration is planned as
`Hartshorne.projectiveDiagonal_functionFieldAlgHom_bijective`.

The proof restricts to either affine chart, where the map is already the
chosen compatible function-field equivalence.  Projection identities and
functoriality then identify the global map.  As a supporting consequence, the
image closure has dimension exactly one, not merely dimension at most one.

## Depends on

- [The projective diagonal model](projective-diagonal.md)
- [The function field of an arbitrary variety](../morphisms/function-field-abstract.md)
- [The function field is functorial for dominant morphisms](../morphisms/function-field-functorial.md)

## Proof depends on

- [A two-chart affine cover of the valuation curve](two-affine-chart-cover.md)
- [Rational maps and function fields](../rational-maps/rational-map-function-field.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)

## Sources

- [Hartshorne I.6, function-field comparison in the proof of Theorem 6.9 (pp. 44--45)](../../sources/hartshorne.md#i6-projective-models)
