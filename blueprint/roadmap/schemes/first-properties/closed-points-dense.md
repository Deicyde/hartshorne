---
article_id: af_57c8a849b2c90ab49dc2af1c
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-1-3]
statement: formalized
proof: formalized
lean: Hartshorne.closedPoints_dense_of_finiteType
---

# Closed points are dense over a field

If `X` is finite type over a field, the closed points of `X` are dense.

A field spectrum is Jacobson, and local finite type preserves the Jacobson-space property. In a Jacobson space the closure of the closed points is the whole space.

## Depends on

- [Morphisms of finite type](finite-type.md)

## Proof depends on

- `LocallyOfFiniteType.jacobsonSpace` and `closure_closedPoints`.

## Sources

- [Hartshorne II.3 (later-used-exercises)](../../../sources/hartshorne-ii-3.md#later-used-exercises)
