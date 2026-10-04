---
article_id: af_9d8ff6a77ffaa25257116225
declaration: theorem
origin: background
source_units: [chapter-iii-sections-8-9]
---

# Zeroth cohomology of a bounded flat acyclic complex

Let `C` be a bounded cochain complex of flat modules over a ring `A`,
concentrated in degrees greater than or equal to zero. If `H^i(C)=0` for every
positive degree, then `H^0(C)` is flat over `A`.

## Depends on

- Cochain complexes, their cycles and cohomology, and flat modules.

## Proof depends on

- [Flat modules in short exact sequences](flat-modules-short-exact-calculus.md)
- Split the bounded exact positive-degree tail into short exact sequences of
  cycles, boundaries, and terms, and descend from the final nonzero degree.

The nonnegative concentration is essential: it identifies `H^0(C)` with the
kernel of the first differential, as in the Cech resolution used by
Hartshorne.

## Sources

- [Hartshorne III.9, proof of Theorem 9.9, pp.261–262](../../../../sources/hartshorne-iii-9.md#hilbert-polynomials-and-projective-families-pp261263)
