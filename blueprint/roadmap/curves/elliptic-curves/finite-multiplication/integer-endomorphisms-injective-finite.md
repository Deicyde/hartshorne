---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# Integer endomorphisms are injective and finite

For a pointed elliptic curve over an algebraically closed field of
characteristic different from two, the map

`Z -> End(X,P_0)`,  `n |-> [n]`

is an injective ring homomorphism. For every nonzero integer `n`, `[n]` is a
nonconstant finite curve morphism.

## Depends on

- [The endomorphism ring](../group-law-foundations/elliptic-endomorphism-ring.md)
- [Multiplication by two](multiplication-by-two-degree-kernel.md)
- [Nonconstant maps of complete curves are finite](../../../schemes/divisors/curve-divisors/nonconstant-complete-curve-map-finite.md)
- [Degree and flatness of a finite curve morphism](../../ramification/finite-curve-morphism-flat-degree.md)

## Proof depends on

- Induct on positive `n`. For odd `n=2r+1`, `[n]=0` would make `[2r]`
  inversion, contradicting the degree of its factor `[2]`; the even case
  factors through `[2]`. Negative integers follow by inversion.

## Sources

- [Hartshorne IV.4, Proposition 4.10, p.323](../../../../sources/hartshorne-iv-4.md)
