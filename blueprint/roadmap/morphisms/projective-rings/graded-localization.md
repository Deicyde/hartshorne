---
declaration: abbrev
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.gradedLocalization Hartshorne.gradedLocalizationAway Hartshorne.isField_gradedLocalization_bot Hartshorne.awayToAtPrime Hartshorne.awayPrime Hartshorne.powers_le_primeCompl Hartshorne.isUnit_mk_of_num_notMem Hartshorne.exists_decompose_notMem Hartshorne.decompose_mul_eq_zero Hartshorne.awayToAtPrime_mk Hartshorne.isLocalization_awayPrime
---

# Graded localization

For a graded ring `S` and a homogeneous prime `𝔭`, let `T` be the homogeneous
elements of `S` not in `𝔭`. Then `T⁻¹S` inherits a grading with
`deg(f/g) = deg f − deg g`, and `S_(𝔭)` denotes its degree-zero part. It is a
local ring with maximal ideal `(𝔭 · T⁻¹S) ∩ S_(𝔭)`. When `S` is a domain and
`𝔭 = (0)`, `S_((0))` is a field. Similarly `S_(f)` is the degree-zero part of
`S_f` for `f` homogeneous.

This is the construction Theorem 3.4 is phrased in, and it is the one place in
Chapter I where the grading is allowed to take negative values.

## What Mathlib supplies

`HomogeneousLocalization.AtPrime` is Hartshorne's `S_(𝔭)` and
`HomogeneousLocalization.Away` is his `S_(f)`, both developed for the `Proj`
construction, and the local ring instance is there too. Mathlib builds the
degree-zero part directly rather than grading the localization and cutting it
down afterwards. That is the same ring and it sidesteps the negative degrees,
so nothing is lost by adopting it; the project fixes those as its names, as the
dimension node does for `ringKrullDim`.

What is not upstream is the last clause: that `S_((0))` is a field when `S` is a
domain. Theorem 3.4(c) is a statement about exactly that ring, so it is proved
here. The argument is Hartshorne's — `a/b` with `a ≠ 0` has inverse `b/a` — run
through `val`, since for `𝔭 = (0)` in a domain the ambient localization is the
fraction field.

## `S_(𝔭)` is a localisation of `S_(f)`

The other thing not upstream, and the one Theorem 3.4 actually turns on: for `f`
homogeneous of degree one with `f ∉ 𝔭`,

`S_(𝔭) = (S_(f))_𝔮`,

where `𝔮` is the prime of `S_(f)` lying under the maximal ideal of `S_(𝔭)`
(`Hartshorne.isLocalization_awayPrime`). Hartshorne passes over this. Having
identified `𝒪_P` with a localisation of `A(Yᵢ)`, he writes the answer as a
localisation of `S(Y)`, and the two agree only because inverting `xᵢ` first
changes nothing at `𝔭`, where `xᵢ` is invertible already.

Taking `𝔮` as the contraction of the maximal ideal, rather than describing it by
numerators, means primality comes for free and the first localisation axiom is
one line: `S_(𝔭)` is local, so anything outside `𝔮` maps to a unit.

Two hypotheses earn their place. Degree one is not cosmetic: for `f` of degree
`d`, a fraction `a/b` can only be rewritten with a power of `f` underneath when
`d` divides the common degree, and the statement fails as written. Degree one is
what Theorem 3.4 has, `f` being a coordinate.

Homogeneity of `𝔭` is used exactly once, in the third axiom. An equality in
`S_(𝔭)` produces some `s ∉ 𝔭` annihilating a homogeneous element, and what is
needed is a *homogeneous* such `s`. One graded component of `s` avoids `𝔭`
because `𝔭` is homogeneous, and it still annihilates, because the product lives
in a single degree and Mathlib computes that component directly.

## Depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.3, definition of `S_(𝔭)` and `S_(f)` (p. 18)](../../../sources/hartshorne.md#i3)
