---
declaration: theorem
origin: cited
source_units: [chapter-v-section-1]
---

# Transverse intersections and restricted divisor degree

Let `C` be a smooth irreducible curve on a Chapter V surface and let `D` be
an effective curve meeting `C` transversally. Then

`#(C intersect D) = deg_C(O_X(D)|_C)`.

The left side counts closed points, while the restriction line bundle
corresponds to the scheme-theoretic intersection divisor on `C`.

## Depends on

- [Transverse intersection of curves](transverse-curve-intersection.md)
- [Ideal sheaf of an effective Cartier divisor](../../../schemes/divisors/cartier-picard/effective-cartier-ideal-sheaf.md)
- [Divisors of invertible-sheaf sections](../../../schemes/projective-geometry/linear-systems-ampleness/divisor-of-invertible-section.md)
- [Principal curve divisors have degree zero](../../../schemes/divisors/curve-divisors/principal-divisor-degree-zero.md)

## Proof depends on

- Tensor `0 -> O_X(-D) -> O_X -> O_D -> 0` with `O_C`; transversality
  identifies the quotient with the reduced intersection divisor.

## Sources

- [Hartshorne V.1, Lemma 1.3, p.358](../../../../sources/hartshorne-v-1.md)
