---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isIso_chartHom Hartshorne.chartHom Hartshorne.chartInvHom Hartshorne.chartVariety Hartshorne.chartTarget Hartshorne.isQuasiProjVariety_standardChart Hartshorne.isQuasiProjVariety_inter_standardChart Hartshorne.eval_rep_chartInv_div Hartshorne.isGlobalRegular_chartCoord
---

# The charts are isomorphisms of varieties

The chart `φᵢ : Uᵢ → 𝔸ⁿ` of Proposition 2.2 is an isomorphism of varieties, not
merely a homeomorphism (Proposition 3.3).

It is proved here in the form `φᵢ : Yᵢ → φᵢ(Yᵢ)` for a quasi-projective `Y`,
with `Yᵢ = Y ∩ Uᵢ`; taking `Y = ℙⁿ` gives Hartshorne's statement. The general
form is not decoration. Hartshorne states 3.3 for the chart and then applies it
to `Yᵢ` without comment, which is standard practice and is a different theorem;
Theorem 3.4 uses only the version with `Y` in it. Nothing in the proof changes,
because the two ingredients — that `xᵢ` is nowhere zero on the chart, and that
dehomogenising inverts the ratio description — are conditions on points of the
chart, and `Yᵢ` has only fewer of them.

Only the regular functions remain to be checked. On `Uᵢ` they are locally
quotients of homogeneous polynomials of equal degree in `x₀,…,xₙ`; on `𝔸ⁿ` they
are locally quotients of polynomials in `y₁,…,yₙ`; and the maps `α` and `β` from
the proof of Proposition 2.2 identify the two descriptions.

Small as it is, this node is what transfers Theorem 3.2 to projective varieties.
Without it the chart gives only a homeomorphism, and the counterexamples in
Exercise 3.2 show a homeomorphism carries no information about regular
functions.

## The two directions are checked by different means

Forward is Lemma 3.6, and this is where it repays being stated for an arbitrary
source: the coordinates of `φᵢ` are `x_j/x_i`, ratios of homogeneous polynomials
of degree one whose denominator is nowhere zero on `Uᵢ` by the definition of the
chart, so the criterion applies with nothing else to check.

Backward is not covered by that lemma, whose target must be affine, so the
pullback of a regular function is checked by hand. A regular function on an open
subset of `Uᵢ` is locally `g/h` with `g` and `h` homogeneous of the same degree,
and `β` turns that into `α(g)/α(h)`, a ratio of polynomials in the affine
coordinates. Two facts make it go through: the ratio of two homogeneous
polynomials of equal degree does not see the choice of representative, and
`β(y)` may be represented by the vector with `1` in slot `i`, which is exactly
what dehomogenising computes with.

Treating `Uᵢ` as a variety at all needs `ℙⁿ` to be irreducible; see
[projective and quasi-projective varieties](../../projective-varieties/projective-variety.md).

The elaboration pathology recorded on [Varieties](../variety.md) recurred here, in
the same form and with the same fix: a hypothesis applied as `hne _ hx` leaves a
metavariable, the elaborator falls back on unfolding `eval` over `MvPolynomial`,
and the proof times out. Naming the point makes it match by cheap definitional
equality.

## Depends on

- [Morphisms](../morphism.md)
- [The standard affine charts](../../projective-varieties/standard-affine-charts.md)
- [Regular functions on a quasi-projective variety](../regular-function-quasi-projective.md)

## Sources

- [Hartshorne I.3, Proposition 3.3 (p. 18)](../../../sources/hartshorne.md#i3)
