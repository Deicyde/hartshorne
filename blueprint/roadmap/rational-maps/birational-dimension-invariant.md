---
article_id: af_5df81cbf56c04ce019c9249d
declaration: theorem
origin: cited
source_units: [chapter-i-section-8-recaps]
statement: formalized
proof: formalized
lean: Hartshorne.birational_topologicalKrullDim_eq
---

# Dimension is a birational invariant

Let `X` and `Y` be separated varieties over the same algebraically closed
field, each equipped with the affine-open-basis structure used by the Chapter I
variety API. If `X` and `Y` are birationally equivalent, then

`dim X = dim Y`.

The proof passes through the function field. Birationality gives a
`k`-algebra equivalence `K(X) ≃ₐ[k] K(Y)`, hence equality of transcendence
degrees. The affine-open-basis dimension theorem identifies each variety's
topological Krull dimension with the transcendence degree of its function
field.

## Depends on

- [Birational maps](birational-map.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [Birational varieties have isomorphic function fields](birational-function-fields.md)
- [Open affine sets are a base for the topology](affine-base.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)

## Local API

The pinned project already contains the two substantive inputs:
`Hartshorne.birational_iff_nonempty_functionField_algEquiv` and
`Hartshorne.Variety.HasAffineOpenBasis.exists_dimension_eq_trdeg`.
`AlgEquiv.trdeg_eq` supplies the intervening equality, so this leaf is a short
packaging theorem rather than a new dimension-theory development.

## Sources

- [Hartshorne I.8, birational invariance of dimension (p. 57)](../../sources/hartshorne.md#i8-what-is-algebraic-geometry)
