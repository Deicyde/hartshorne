---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projDim_univ Hartshorne.projDim_univ_fin Hartshorne.projDim_univ_add_one Hartshorne.projDim_eq_projDim_closure Hartshorne.closure_chartMap_image Hartshorne.isOpenMap_chartInv Hartshorne.chartMap_image_univ
---

# Dimension in projective space

`dim ℙⁿ = n`, and if `Y ⊆ ℙⁿ` is quasi-projective then `dim Y = dim Ȳ`
(Exercise 2.7).

The first follows from the previous node applied to `Y = ℙⁿ`. The second reduces
to the affine statement of Proposition 1.10 through the charts.

This closes §2: projective space has the dimension it should, and dimension is
insensitive to passing between a quasi-projective variety and its closure, so
later sections can compute dimension on whichever representative is convenient.

## Status

Proved. Both halves fall out of the previous node.

For `ℙⁿ` itself the shortest route is not through `S(ℙⁿ) = k[x₀,…,xₙ]` but
through the charts, which the previous node already matched with `ℙⁿ`: every
chart of `ℙⁿ` is *all* of `𝔸ⁿ`, since `φᵢ(ℙⁿ ∩ Uᵢ) = φᵢ⁻¹⁻¹(ℙⁿ)` is the whole
affine space. So `dim ℙⁿ` is the dimension of affine space in one variable
fewer, which is already computed. The polynomial-ring reading is recorded too
(`projDim_univ_add_one`), and agrees: `S(ℙⁿ)` is the polynomial ring because
`J(ℙⁿ) = 0`, and its dimension is `n + 1`.

For the quasi-projective half, one inequality is the general fact that a
subspace has no larger dimension. The other goes through a chart: `φᵢ(Y ∩ Uᵢ)`
is quasi-affine and its closure in `𝔸ⁿ` is `φᵢ(Ȳ ∩ Uᵢ)`, because `φᵢ⁻¹` is an
open map and preimages along open maps commute with closure. Proposition 1.10
says those two have the same dimension, and the previous node identifies the
second with `dim Ȳ`.

Proposition 1.10 had been stated for an ambient space `𝔸ᵐ` indexed by `Fin m`;
the chart variables are indexed by `{j : σ // j ≠ i}` instead, so it was
restated over an arbitrary finite index type. The index type has to sit in
universe zero for the dimension formula, whose ring and base field must share a
universe — the same restriction every other dimension result in the chapter
carries.

## Depends on

- [Projective and quasi-projective varieties](projective-variety.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [Dimension of the homogeneous coordinate ring](homogeneous-coordinate-ring-dimension.md)
- [Dimension of a quasi-affine variety](../affine-varieties/dim-quasi-affine.md)
- [Varieties are covered by affine pieces](affine-cover.md)

## Sources

- [Hartshorne I.2, Exercise 2.7 (p. 12)](../../sources/hartshorne.md#i2)
