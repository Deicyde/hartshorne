---
article_id: af_2136720d3c5831f8df18c545
declaration: def
origin: cited
source_units: [chapter-i-section-5-geometry]
---

# Nonsingular points of an affine variety

Let `Y ⊆ 𝔸ⁿ` be an affine variety of dimension `r`. A point `P ∈ Y`
is *nonsingular in affine coordinates* when

`jacobianRank(Y,P) = n − r`.

The variety is nonsingular in affine coordinates when every point is. To avoid
subtraction in `WithBot ℕ∞`, define the Lean predicate by the equivalent
existential condition

`∃ r : ℕ, dim Y = (r : WithBot ℕ∞) ∧ jacobianRank(Y,P) + r = n`.

Finite dimensionality of an affine coordinate ring supplies the witness, and
the Jacobian rank bound later recovers Hartshorne's literal `n − r` form.

Using the intrinsic row space from the preceding node makes this a predicate of
`Y` and `P`, not of a chosen list of equations. The finite-generator theorem
then recovers Hartshorne's literal matrix definition for every presentation of
`I(Y)`.

## Depends on

- [Jacobian rank is independent of generators](jacobian-rank-invariance.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [A finitely generated algebra over a field has finite dimension](../affine-varieties/dim-fg-algebra-finite.md)
- [The dimension of affine space](../affine-varieties/dim-affine-space.md)

## Sources

- [Hartshorne I.5, definition of affine nonsingularity (pp. 31-32)](../../sources/hartshorne.md#i5)
