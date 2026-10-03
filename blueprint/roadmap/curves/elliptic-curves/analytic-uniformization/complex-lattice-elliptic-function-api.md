---
declaration: structure
origin: background
source_units: [chapter-iv-analytic-background]
not_ready: true
---

# Complex lattices and elliptic functions

For `tau : C` with `tau notin R`, let `Lambda=Z+Z*tau`. Package the complex
torus `C/Lambda`, its points, and the field of meromorphic functions invariant
under translation by `Lambda`. Define the Weierstrass functions `P` and `P'`,
their poles, periodicity, the lattice invariants `g2,g3`, and divisors of
elliptic functions on `C/Lambda`.

Pinned Mathlib already provides `PeriodPair`, its lattice, the convergent
Weierstrass series, meromorphicity, periodicity, and pole orders. It does not
bundle the quotient complex torus or the field of periodic meromorphic
functions used by Hartshorne.

This node is not ready until those quotient and function-field
representations, and their comparison with divisors on a compact Riemann
surface, are fixed.

## Depends on

No project-local prerequisites. This is the analytic representation root.

## Proof depends on

- `PeriodPair.weierstrassP`, `PeriodPair.derivWeierstrassP`, and their
  periodicity and meromorphicity declarations in pinned Mathlib.
- Hurwitz–Courant, II.1 §6, for Hartshorne's analytic construction.

## Sources

- [Hartshorne IV.4, elliptic-function definitions, pp.326–327](../../../../sources/hartshorne-iv-4.md)
- Hurwitz–Courant, *Allgemeine Funktionentheorie und elliptische Funktionen*, II.1 §6.
