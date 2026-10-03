---
declaration: theorem
origin: background
source_units: [chapter-iv-analytic-background]
mathlib: true
mathlib_declaration: PeriodPair.derivWeierstrassP_sq
mathlib_file: Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean
---

# The Weierstrass differential equation

Let `L` be a pair of complex periods and let `z` lie outside its lattice.
Pinned Mathlib proves

`P'[L](z)^2 = 4*P[L](z)^3 - L.g2*P[L](z) - L.g3`.

This is the differential-equation part of Hartshorne's Theorem 4.12B. The
separate claim that `P,P'` generate every elliptic function is not included in
this Mathlib status.

## Sources

- [Hartshorne IV.4, Theorem 4.12B, p.327](../../../../sources/hartshorne-iv-4.md)
- Hurwitz–Courant, II.1 §§8–9.
