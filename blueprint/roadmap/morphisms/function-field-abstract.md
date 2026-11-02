---
article_id: af_c5aaa0cd7091b530bdb5a3c7
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.Variety.FunctionField
---

# The function field of an arbitrary variety

For a variety $X$, rational functions are represented by regular functions
on nonempty open subsets, with representatives identified when they
agree on their common domain. These classes form the function field $K(X)$.
For a quasi-affine variety, this agrees canonically with the construction
in affine coordinates.

A nonzero rational function is nonzero on a nonempty open subset. Its
reciprocal is regular there, so it is invertible. Sums and products are
defined on intersections of domains, which are nonempty by irreducibility.
Unlike a germ, a rational function is not required to have a domain
containing any fixed point.

## Depends on

- [The function field](function-field.md)
- [Varieties](variety.md)

## Proof depends on

- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)

## Sources

- [Hartshorne I.3, definition of $K(Y)$ (p. 16)](../../sources/hartshorne.md#i3)
