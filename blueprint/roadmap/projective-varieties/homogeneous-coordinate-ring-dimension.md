---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ringKrullDim_homogeneousCoordinateRing_eq_projDim_add_one Hartshorne.ringKrullDim_homogeneousCoordinateRing Hartshorne.projDim_eq_dim_chart Hartshorne.dim_chart_eq_dim_chart Hartshorne.ker_dehomogenize Hartshorne.ker_coordChartHom Hartshorne.coordChartQuotEquiv Hartshorne.height_chartSectionIdeal Hartshorne.mk_X_sub_one_ne_zero Hartshorne.topologicalKrullDim_chartPiece_eq_krullDim_meeting
---

# Dimension of the homogeneous coordinate ring

For a projective variety `Y ⊆ ℙⁿ`, `dim S(Y) = dim Y + 1` (Exercise 2.6).

Hartshorne's hint is to identify `A(Yᵢ)` with the degree-zero part of the
localization `S(Y)_{xᵢ}` and then show `S(Y)_{xᵢ} ≅ A(Yᵢ)[xᵢ, xᵢ⁻¹]`, comparing
transcendence degrees to get the `+1`.

## Status

Proved, by the quotient rather than the localization.

The `+1` is the dimension of the affine cone over `Y`, and the cheapest way to
see it is that `Yᵢ` is a *hyperplane section* of that cone:

`S(Y)/(xᵢ − 1) ≅ A(Yᵢ)`.

That is the same identification Hartshorne's hint makes, read on the quotient
instead of the localization, and it avoids the Laurent-polynomial ring entirely.
Dehomogenisation is surjective onto `A(Yᵢ)`, and its kernel is `(xᵢ − 1)` on the
nose: upstairs the kernel of `α` on the polynomial ring is `(xᵢ − 1)`, by an
induction on monomials, and the ideal dictionary
(`dehomogenize_mem_vanishingIdeal_iff`) converts a polynomial killed modulo
`I(Yᵢ)` into one killed modulo `J(Y)` after subtracting a multiple of `xᵢ − 1`.

The dimension then drops by exactly one because `(xᵢ − 1)` has height one: at
least one since `S(Y)` is a domain and `xᵢ − 1` is nonzero, at most one by
Krull's principal ideal theorem, which is in Mathlib. Theorem 1.8A(b) converts
the height into the drop. Transcendence degrees are never mentioned, though they
are still there inside 1.8A(b).

Nonvanishing of `xᵢ − 1` in `S(Y)` is the one place the grading is used: `xᵢ` is
homogeneous of degree one and `1` of degree zero, so they can agree only in the
zero ring.

The geometric half, `dim Y = dim Yᵢ`, is the reverse inequality of Proposition
1.10 again, and again the easy direction is that a subspace has no larger
dimension. A chain of irreducible closed subsets of `Y` need not meet a *given*
chart — its bottom term can be a point outside `Uᵢ` — but it meets some chart,
since the charts cover `ℙⁿ` and every term contains the bottom one. Each chain is
therefore bounded by `dim Y_j` for a `j` depending on the chain, and the
algebraic half is what says all those bounds are the same number.

Mathlib supplies the step that would otherwise be the work here:
`IrreducibleCloseds.orderIsoOfIsOpenEmbedding` matches the irreducible closed
subsets of an open subspace with those of the ambient space that meet it, which
is exactly restricting a chain and taking closures back.

## Depends on

- [The homogeneous vanishing ideal](homogeneous-vanishing-ideal.md)
- [Projective and quasi-projective varieties](projective-variety.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [The standard affine charts](standard-affine-charts.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](../affine-varieties/dim-formula-catenary.md)

## Sources

- [Hartshorne I.2, Exercise 2.6 (pp. 11-12)](../../sources/hartshorne.md#i2)
