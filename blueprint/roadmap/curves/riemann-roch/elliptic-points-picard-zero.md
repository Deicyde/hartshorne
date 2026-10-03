---
declaration: equivalence
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# Points of a genus-one curve and its degree-zero Picard group

Let `X` be a Chapter IV curve of genus one and choose a closed point `P_0`.
The map

`P |-> O_X(P-P_0)`

is a bijection from the closed points of `X` to the subgroup `Pic^0(X)` of
degree-zero invertible-sheaf classes. Transporting addition gives a group
structure on the point set with identity `P_0`.

This is an equivalence of sets with a transported group structure. It does
not yet construct scheme morphisms for addition and inverse, and `Pic^0` is
the kernel of degree rather than a Picard-scheme component.

## Depends on

- [The Riemann–Roch theorem](riemann-roch.md)
- [The degree of a canonical divisor](canonical-divisor-degree.md)
- [A divisor with a nonzero section has nonnegative degree](nonzero-sections-nonnegative-degree.md)
- [Divisor classes and the Picard group](../../schemes/divisors/cartier-picard/divisor-class-picard-equivalence.md)

## Proof depends on

- For every degree-zero divisor `D`, Riemann–Roch gives `l(D+P_0)=1`, so its
  unique effective representative of degree one is a single closed point.
- Uniqueness proves injectivity and permits transport of the group laws.

## Sources

- [Hartshorne IV.1, Example 1.3.7, p.297](../../../sources/hartshorne-iv-1.md#consequences-of-riemannroch-printed-pp296297)
