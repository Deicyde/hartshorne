---
article_id: af_2ef77b7fb24c148d306eb5b9
declaration: theorem
origin: cited
source_units: [chapter-v-section-1]
---

# Adjunction for a smooth curve on a surface

Let `C` be a smooth curve of genus `g` on a Chapter V surface with canonical
divisor `K`. Then

`2*g-2 = C.(C+K)`.

The equality is integer-valued and independent of the representative of `K`.

## Depends on

- [The divisor intersection pairing](../foundations/divisor-intersection-pairing.md)
- [Self-intersection and the normal bundle](../foundations/self-intersection-normal-bundle-degree.md)
- [Adjunction for an effective Cartier divisor](../../../schemes/differentials/canonical-bertini/adjunction-effective-cartier-divisor.md)
- [The degree of a canonical divisor](../../../curves/riemann-roch/canonical-divisor-degree.md)
- [Transverse intersections and restricted divisor degree](../foundations/transverse-intersection-restriction-degree.md)

## Proof depends on

- Sheaf adjunction gives
  `omega_C ~= (omega_X tensor O_X(C))|_C`; restriction degree translates the
  right side to `C.(K+C)` and curve adjunction gives degree `2g-2`.

## Sources

- [Hartshorne V.1, Proposition 1.5, p.361](../../../../sources/hartshorne-v-1.md)
