---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isAffineVariety_chartMap_image Hartshorne.isQuasiAffineVariety_chartMap_image Hartshorne.iUnion_standardChart Hartshorne.chartMap_image_eq_chartInv_preimage Hartshorne.homogeneousVanish_iff_eval_dehomogenize Hartshorne.dehomogenize_mem_vanishingIdeal_iff Hartshorne.homogeneousVanish_of_mem_homogeneousVanishingIdeal
---

# Varieties are covered by affine pieces

If `Y` is a projective variety then the sets `Y ∩ Uᵢ` for `i = 0,…,n` form an
open cover of `Y`, and each is carried by `φᵢ` to an affine variety. If `Y` is
quasi-projective the same holds with quasi-affine varieties (Corollary 2.3).

The cover is immediate — some homogeneous coordinate of any point is nonzero —
and the identification of the pieces is the chart homeomorphism restricted to
`Y`. The content is that irreducibility and the appropriate closedness survive
the restriction: `Y ∩ Uᵢ` is a nonempty open subset of an irreducible space,
hence irreducible, and its image is closed in `𝔸ⁿ` when `Y` is closed in `ℙⁿ`.

Together with the previous node this is the statement that projective geometry
is locally affine, which is the organising idea of the rest of the book.

## The cover at the level of ideals

Theorem 3.4 needs the piece the topological statement leaves out: how `J(Y)` and
`I(Yᵢ)` correspond. It is not that `α` carries one onto the other — it does not,
since `xᵢ − 1` and its multiples are killed by `α` for free. What holds, for
homogeneous `g`, is

`α(g) ∈ I(Yᵢ) ↔ xᵢ · g ∈ J(Y)`,

and with a single power of `xᵢ`, not an unspecified one. The single power is the
geometry: `xᵢ · g` vanishes off the chart because `xᵢ` does, and on the chart
because `g` does. That is the shape a localisation at `xᵢ` wants, which is why
it is the form recorded.

## Depends on

- [The standard affine charts](standard-affine-charts.md)
- [Projective and quasi-projective varieties](projective-variety.md)
- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)

## Sources

- [Hartshorne I.2, Corollary 2.3 (p. 11)](../../sources/hartshorne.md#i2)
