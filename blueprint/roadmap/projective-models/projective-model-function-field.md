---
article_id: af_27f35d9b8908d59f68689bd5
declaration: theorem
origin: bridged
source_units: [chapter-i-section-6-projective-model]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveDiagonal_functionFieldAlgHom_bijective
---

# The function field of the diagonal model

For a `ProjectiveDiagonalModel` and its dense map `φ : C_K → Y`, the induced
map `φ* : K(Y) → K(C_K)` on function fields is bijective.  The sole main
declaration is formalized as
`Hartshorne.projectiveDiagonal_functionFieldAlgHom_bijective`.

The proof restricts to either affine chart, where the map is already the
chosen compatible function-field equivalence.  Projection identities and
functoriality then identify the global map.  As a supporting consequence, the
resulting algebra equivalence, composed with the canonical identification
`K(C_K) ≃ₐ[k] K`, identifies `K(Y)` with `K`, and the image closure has
dimension exactly one rather than merely dimension at most one.

## Depends on

- [The projective diagonal model](projective-diagonal.md)
- [The function field of an arbitrary variety](../morphisms/function-field-abstract.md)
- [The function field is functorial for dominant morphisms](../morphisms/function-field-functorial.md)

## Proof depends on

- [A two-chart affine cover of the valuation curve](two-affine-chart-cover.md)
- [The function field of an abstract nonsingular curve](../curve-normalization/valuation-space-function-field.md)
- [Rational maps and function fields](../rational-maps/rational-map-function-field.md)
- [Curves](../nonsingular-curves/curve.md)

## Sources

- [Hartshorne I.6, function-field comparison in the proof of Theorem 6.9 (pp. 44--45)](../../sources/hartshorne.md#i6-projective-models)
