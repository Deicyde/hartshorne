---
article_id: af_2a3cea68a7953dda12f13d0c
declaration: theorem
origin: cited
source_units: [chapter-i-section-5-geometry]
statement: formalized
lean: Hartshorne.jacobianRank_add_dim_le_ambient Hartshorne.jacobianRank_le_ambient_sub_dim Hartshorne.not_isAffineNonsingularAt_iff_jacobianRank_lt
---

# The Jacobian rank bound

Let `Y ⊆ 𝔸ⁿ` be an affine variety of dimension `r`. At every point
`P ∈ Y`,

`jacobianRank(Y,P) ≤ n − r`.

Indeed, Proposition 5.2A gives
`r = dim 𝒪_{P,Y} ≤ dim_k(𝔪_P/𝔪_P²)`, while the dimension formula
from Theorem 5.1's proof gives
`dim_k(𝔪_P/𝔪_P²) + jacobianRank(Y,P) = n`. Subtracting in `ℕ`
yields the displayed inequality.

This direction matters: the Jacobian rank cannot exceed the codimension. Hence
a point fails to be nonsingular precisely when the rank is *strictly less* than
`n − r`, which is the determinantal condition used to prove closedness.

## Depends on

- [Jacobian rank is independent of generators](jacobian-rank-invariance.md)
- [Nonsingular points of an affine variety](affine-nonsingular-points.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [The cotangent-dimension bound](cotangent-dimension-bound.md)
- [The defining ideal and the local cotangent space](defining-ideal-cotangent-sequence.md)
- [The local ring and function field of an affine variety](../morphisms/affine-variety-rings.md)

## Sources

- [Hartshorne I.5, Proposition 5.2A and proof of Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
