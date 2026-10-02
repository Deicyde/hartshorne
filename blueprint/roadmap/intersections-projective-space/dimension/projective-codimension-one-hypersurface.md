---
article_id: af_c1ad20c4747293c5e4936d68
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.projective_codimension_one_iff_hypersurface
---

# Projective codimension one is a hypersurface

Let `Y ⊆ ℙⁿ` be a projective variety. Then `dim Y = n-1` if and only if
`Y = Z(f)` for one irreducible homogeneous polynomial `f` of positive degree.

This dimension-theoretic prerequisite is Exercise 2.8, adopted because
Corollary 7.8 treats either plane curve as the hypersurface in Theorem 7.7.
The proof translates dimension to the
height-one homogeneous prime `J(Y)` and uses principality in the polynomial
UFD; the converse reads the quotient dimension back geometrically.

## Depends on

- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)
- [Dimension of the homogeneous coordinate ring](../../projective-varieties/homogeneous-coordinate-ring-dimension.md)
- [Hypersurfaces and codimension one](../../affine-varieties/hypersurface-dimension.md)

## Proof depends on

- [The dimension formula for a finitely generated domain](../../affine-varieties/dim-formula-catenary.md)

## Sources

- [Hartshorne I.2, Exercise 2.8 (p. 12), as used in Corollary I.7.8](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
