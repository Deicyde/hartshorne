---
article_id: af_c9ec3c715008de92212224d1
declaration: def
origin: cited
source_units: [chapter-i-section-6-valuations, chapter-i-section-6-local-structure]
---

# Curves

A curve is a variety of dimension one. For the abstract variety interface used
after §4, define `X.IsCurve` by

`topologicalKrullDim X.carrier = 1`.

For a variety with an affine-open basis, the existing dimension theorem then
identifies this condition with
`Algebra.trdeg k X.FunctionField = 1`, matching Hartshorne's phrase “function
field of dimension one.” Record these two formulations as an equivalence or a
companion theorem, without building a second notion of dimension.

## Depends on

- [Varieties](../morphisms/variety.md)

## Proof depends on

- [Every variety is birational to a hypersurface](../rational-maps/birational-hypersurface.md)

## Sources

- [Hartshorne I.6, opening discussion of curves and one-dimensional function fields (p. 39)](../../sources/hartshorne.md#i6-valuation-and-dvr-background)
