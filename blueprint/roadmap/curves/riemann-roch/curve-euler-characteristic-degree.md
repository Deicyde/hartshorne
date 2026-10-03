---
declaration: theorem
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Euler characteristic and divisor degree

For every divisor `D` on a Chapter IV curve of genus `g`,

`chi(O_X(D)) = deg D + 1 - g`.

Here Euler characteristic is integer-valued. The proof starts from
`chi(O_X)=1-g` and reaches every divisor by finitely many additions or
subtractions of closed points.

## Depends on

- [The Chapter IV curve convention](curve-convention.md)
- [The point-divisor exact sequence](point-divisor-exact-sequence.md)
- [Euler characteristic is additive](../../cohomology/projective-cohomology-exercises/euler-characteristic-additive.md)
- [Principal curve divisors have degree zero](../../schemes/divisors/curve-divisors/principal-divisor-degree-zero.md)

## Proof depends on

- The skyscraper sheaf `k(P)` has Euler characteristic one, and both Euler
  characteristic and divisor degree increase by one on replacing `D` by
  `D+P`.

## Sources

- [Hartshorne IV.1, Euler-characteristic calculation in Theorem 1.3, pp.295–296](../../../sources/hartshorne-iv-1.md#canonical-divisors-and-riemannroch-printed-pp295296)
