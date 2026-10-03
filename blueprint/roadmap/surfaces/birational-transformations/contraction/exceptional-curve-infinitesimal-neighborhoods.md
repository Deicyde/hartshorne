---
declaration: isomorphism
origin: cited
source_units: [chapter-v-section-5]
---

# Infinitesimal neighborhoods of a minus-one curve

Let `I` be the ideal sheaf of an exceptional curve of the first kind `Y`,
and let `Y_n` be cut out by `I^n`.  Then

`I^n/I^(n+1) ~= O_(P^1)(n)`.

After choosing a basis `x,y` of `H^0(P^1,O(1))` and compatible lifts, there
are compatible, noncanonical ring isomorphisms

`H^0(Y_n,O_(Y_n)) ~= k[[x,y]]/(x,y)^n`.

The indexing has `Y_1=Y`; no assertion of a canonical coordinate choice is
made.

## Depends on

- [Exceptional curves of the first kind](exceptional-curve-first-kind.md)
- [Self-intersection as normal-bundle degree](../../intersection-theory/foundations/self-intersection-normal-bundle-degree.md)
- [The ideal sheaf of an effective Cartier divisor](../../../schemes/divisors/cartier-picard/effective-cartier-ideal-sheaf.md)
- [Top cohomology of twists on projective space](../../../cohomology/projective-cohomology/projective-space-top-twist-cohomology.md)

## Proof depends on

- The conormal bundle is `I/I^2 ~= O_(P^1)(1)`.  Use the exact sequences
  `0 -> I^n/I^(n+1) -> O_(Y_(n+1)) -> O_(Y_n) -> 0`, the vanishing of
  `H^1(P^1,O(n))`, and induction on `n`, preserving multiplication of the
  lifted parameters.

## Sources

- [Hartshorne V.5, Theorem 5.7, Step 5, p.415](../../../../sources/hartshorne-v-5.md)
