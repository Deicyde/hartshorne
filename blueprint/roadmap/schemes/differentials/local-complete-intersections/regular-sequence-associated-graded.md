---
declaration: theorem
origin: background
source_units: [chapter-ii-section-8]
not_ready: true
---

# The associated graded algebra of a regular-sequence ideal

Let `A` be a Cohen–Macaulay local ring and let `I = (x_1, ..., x_r)`, where
the generators form a regular sequence. The natural graded algebra map

`Sym_(A/I)(I/I^2) -> direct-sum_(n >= 0) I^n/I^(n+1)`

is an isomorphism. In particular, `I/I^2` is free of rank `r` and every
degree-`n` map `Sym^n(I/I^2) -> I^n/I^(n+1)` is an isomorphism.

## Depends on

- [Regular sequences and Cohen–Macaulay quotients](cohen-macaulay-regular-sequence-quotient.md)

## Proof depends on

- Mathlib's `SymmetricAlgebra`, ideal-power quotients, and `reesAlgebra`
  provide algebraic representations but not the required isomorphism.
- Hartshorne cites Matsumura [2], p.110, but the exact passage has not yet
  been adopted.

## Sources

- [Hartshorne II.8, Theorem 8.21A(e) (p.185)](../../../../sources/hartshorne-ii-8.md#local-algebra-and-local-complete-intersections)
- [Unresolved exact-passage obligation](../../../../sources/hartshorne-ii-8.md#external-proof-sources-and-unresolved-obligations)
