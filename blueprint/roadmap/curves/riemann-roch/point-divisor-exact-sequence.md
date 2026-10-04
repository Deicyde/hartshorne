---
article_id: af_b488a50018db3449aeac5cfd
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# The point-divisor exact sequence

Let `P` be a closed point of a Chapter IV curve. As an effective Cartier
divisor, `P` has ideal sheaf `O_X(-P)` and an exact sequence

`0 -> O_X(-P) -> O_X -> k(P) -> 0`.

For every divisor `D`, tensoring by the invertible sheaf `O_X(D+P)` gives

`0 -> O_X(D) -> O_X(D+P) -> k(P) -> 0`.

The final identification uses `k(P)=k` and the fact that tensoring a
one-dimensional skyscraper fibre by an invertible sheaf does not change its
isomorphism class.

## Depends on

- [The Chapter IV curve convention](curve-convention.md)
- [Effective Cartier divisors as closed subschemes](../../schemes/divisors/cartier-picard/effective-cartier-closed-subscheme.md)
- [Ideal sheaf of an effective Cartier divisor](../../schemes/divisors/cartier-picard/effective-cartier-ideal-sheaf.md)
- [Arithmetic of associated divisor sheaves](../../schemes/divisors/cartier-picard/cartier-associated-sheaf-arithmetic.md)

## Proof depends on

- A closed point on a regular one-dimensional scheme is an effective Cartier
  divisor, and tensoring by an invertible module preserves short exactness.

## Sources

- [Hartshorne IV.1, point exact sequence in the proof of Theorem 1.3, p.296](../../../sources/hartshorne-iv-1.md#canonical-divisors-and-riemannroch-printed-pp295296)
