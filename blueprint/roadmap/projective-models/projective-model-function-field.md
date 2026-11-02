---
article_id: af_27f35d9b8908d59f68689bd5
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.projectiveDiagonal_functionFieldAlgHom_bijective
---

# The function field of the diagonal model

For the dense diagonal morphism $\varphi:C_K\to Y$ of the projective
model, the induced map

$$\varphi^*:K(Y)\longrightarrow K(C_K)$$

is bijective. Composing its inverse identification with the canonical
isomorphism $K(C_K)\cong K$ identifies $K(Y)$ with $K$.

On either affine chart, the pullback is already the chosen function-field
isomorphism. Projection identities and functoriality identify this chart
map with the global pullback. Consequently $Y$ has dimension exactly one.

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
