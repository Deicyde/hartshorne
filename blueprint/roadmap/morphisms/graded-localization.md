---
declaration: def
origin: cited
---

# Graded localization

For a graded ring `S` and a homogeneous prime `𝔭`, let `T` be the homogeneous
elements of `S` not in `𝔭`. Then `T⁻¹S` inherits a grading with
`deg(f/g) = deg f − deg g`, and `S_(𝔭)` denotes its degree-zero part. It is a
local ring with maximal ideal `(𝔭 · T⁻¹S) ∩ S_(𝔭)`. When `S` is a domain and
`𝔭 = (0)`, `S_((0))` is a field. Similarly `S_(f)` is the degree-zero part of
`S_f` for `f` homogeneous.

This is the construction Theorem 3.4 is phrased in, and it is the one place in
Chapter I where the grading is allowed to take negative values. Mathlib has
graded localizations in the `HomogeneousLocalization` API developed for the `Proj`
construction; check whether `HomogeneousLocalization.AtPrime` matches Hartshorne's
`S_(𝔭)` before defining anything new.

## Depends on

- [Homogeneous ideals](../projective-varieties/homogeneous-ideal.md)
- [The homogeneous vanishing ideal](../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.3, definition of `S_(𝔭)` and `S_(f)` (p. 18)](../../sources/hartshorne.md#i3)
