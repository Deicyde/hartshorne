---
declaration: def
origin: bridged
source_units: [chapter-iv-sections-1-2]
---

# The ramification-index bridge

Let `f : X -> Y` be a finite morphism of curves, let `P : X`, and put
`Q=f(P)`. For a uniformizer `t` of the DVR `O_(Y,Q)`, define

`e_P = v_P(f^#t)`.

Prove independence of `t`, identify `e_P` with the coefficient of `P` in
`f^*Q` and with Mathlib's ideal-theoretic ramification index for the induced
extension of DVRs, and show `e_P=1` exactly when `f` is unramified at `P`.
Ramification is tame in characteristic zero, or in characteristic `p` when
`p` does not divide `e_P`; otherwise it is wild.

## Depends on

- [Nonsingular curve local rings are DVRs](../../nonsingular-curves/nonsingular-curve-local-ring-dvr.md)
- [Pullback of divisors along finite curve morphisms](../../schemes/divisors/curve-divisors/finite-curve-divisor-pullback.md)
- [Étale, flat-unramified, and differential criteria](../../cohomology/smooth-morphisms/criteria/etale-flat-unramified-equivalences.md)

## Proof depends on

- Uniformizers differ by units and local ring maps preserve units.
- `Ideal.ramificationIdx` for the corresponding prime ideals in affine DVR
  neighbourhoods.

## Sources

- [Hartshorne IV.2, ramification definitions, p.299](../../../sources/hartshorne-iv-2.md#finite-maps-ramification-and-the-different-pp299301)
