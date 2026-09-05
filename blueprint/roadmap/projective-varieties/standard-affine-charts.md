---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.chartHomeomorph Hartshorne.homogenize Hartshorne.dehomogenize Hartshorne.eval_homogenize Hartshorne.eval_dehomogenize Hartshorne.chartEquiv Hartshorne.dehomogenize_homogenize Hartshorne.eq_zero_of_dehomogenize_eq_zero Hartshorne.chartInvVec_div Hartshorne.awayDehomogenize Hartshorne.awayToPoly Hartshorne.awayChartEquiv
---

# The standard affine charts

Let `Hᵢ = Z(xᵢ)` and `Uᵢ = ℙⁿ ∖ Hᵢ`. The map `φᵢ : Uᵢ → 𝔸ⁿ` sending
`(a₀,…,aₙ)` to `(a₀/aᵢ, …, aₙ/aᵢ)` with the `i`-th entry omitted is a
homeomorphism for the induced Zariski topology on `Uᵢ` and the Zariski topology
on `𝔸ⁿ` (Proposition 2.2).

The proof is the dehomogenisation/homogenisation pair. Taking `i = 0` and
`A = k[y₁,…,yₙ]`, define `α : S^h → A` by `α(f) = f(1, y₁, …, yₙ)` and
`β : A → S^h` by `β(g) = x₀^{deg g} · g(x₁/x₀, …, xₙ/x₀)`. Then `α` and `β`
carry closed sets to closed sets in either direction, which makes `φ` a closed
bijection with closed inverse.

This is the key result of §2 and the most-used result of Chapter I: it is what
lets every local question about a projective variety be answered affinely. It is
upgraded from a homeomorphism to an isomorphism of varieties in §3, once
morphisms exist; see [the chart isomorphism](../morphisms/chart-isomorphism.md).

## What `α` and `β` do to polynomials

Proposition 2.2 needs only that the pair moves closed sets in both directions.
Theorem 3.4 needs more: that `α` is a bijection from the homogeneous
polynomials, up to powers of `xᵢ`, onto all polynomials in the affine
coordinates. Both halves are recorded here, since they are statements about the
same pair.

One half is bookkeeping: `α(β(g)) = g`, because `β` pads each monomial with a
power of `xᵢ` and `α` sets `xᵢ` to `1`.

The other half is that `α` is injective on homogeneous polynomials, and it is
proved by evaluation rather than by comparing supports. If `α(g) = 0` then `g`
vanishes at every vector with `i`-th coordinate `1`, hence by homogeneity
wherever the `i`-th coordinate is nonzero; so `xᵢ · g` vanishes identically and,
over an infinite field, is zero. Homogeneity is doing the work and cannot be
dropped: `xᵢ − 1` is killed by `α` and is not zero.

Together these give the ring-level form of Proposition 2.2: `S_(xᵢ) ≅ k[y]`,
the degree-zero part of `S` localised at `xᵢ` being the coordinate ring of the
chart. The map needs no grading to define — `α` sends `xᵢ` to a unit, so it
factors through the localisation at `xᵢ` outright, and the degree-zero part is
carried along. Theorem 3.4 is stated in terms of `S(Y)_(xᵢ)`, and this is the
ambient case of it.

## Depends on

- [The Zariski topology on projective space](projective-zariski-topology.md)
- [The Zariski topology on affine space](../affine-varieties/zariski-topology.md)

## Sources

- [Hartshorne I.2, Proposition 2.2 (pp. 10-11)](../../sources/hartshorne.md#i2)
