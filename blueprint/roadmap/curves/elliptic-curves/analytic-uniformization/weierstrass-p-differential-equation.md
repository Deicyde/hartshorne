---
article_id: af_2d9e96d3864feab2b19cf38e
declaration: theorem
origin: background
mathlib: true
mathlib_declaration: PeriodPair.derivWeierstrassP_sq
mathlib_file: Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean
---

# The Weierstrass differential equation

Let $L$ be a pair of complex periods and let $z$ lie outside its lattice.
The corresponding Weierstrass function satisfies

$$\wp_L'(z)^2=4\wp_L(z)^3-g_2(L)\wp_L(z)-g_3(L).$$

This is the differential-equation part of Hartshorne's Theorem IV.4.12B.
Generation of the elliptic-function field by $\wp$ and $\wp'$ is a
[separate result](elliptic-function-field-generation.md).

## Depends on

No project-local prerequisites.

## Sources

- [Hartshorne IV.4, Theorem 4.12B, p.327](../../../../sources/hartshorne-iv-4.md)
- Hurwitz–Courant, II.1 §§8–9.
