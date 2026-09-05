---
declaration: abbrev
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.gradedLocalization Hartshorne.gradedLocalizationAway Hartshorne.isField_gradedLocalization_bot
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

## Depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.3, definition of `S_(𝔭)` and `S_(f)` (p. 18)](../../../sources/hartshorne.md#i3)
