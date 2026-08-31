---
declaration: theorem
origin: cited
---

# Dimension of the homogeneous coordinate ring

For a projective variety `Y ⊆ ℙⁿ`, `dim S(Y) = dim Y + 1` (Exercise 2.6).

Hartshorne's hint is the route: with `Yᵢ = φᵢ(Y ∩ Uᵢ)`, identify `A(Yᵢ)` with
the degree-zero part of the localization `S(Y)_{xᵢ}`, then show
`S(Y)_{xᵢ} ≅ A(Yᵢ)[xᵢ, xᵢ⁻¹]`. Comparing transcendence degrees via Theorem 1.8A
gives the `+1`, and the same comparison shows `dim Y = dim Yᵢ` whenever `Yᵢ` is
nonempty.

The `+1` is the dimension of the affine cone over `Y`, which is the geometric
reason for it. Formalizing the Laurent-polynomial isomorphism is likely the
bulk of the work; the transcendence degree bookkeeping is short once it is in
place.

## Depends on

- [The homogeneous vanishing ideal](homogeneous-vanishing-ideal.md)
- [Projective and quasi-projective varieties](projective-variety.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [The standard affine charts](standard-affine-charts.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)

## Sources

- [Hartshorne I.2, Exercise 2.6 (pp. 11-12)](../../sources/hartshorne.md#i2)
