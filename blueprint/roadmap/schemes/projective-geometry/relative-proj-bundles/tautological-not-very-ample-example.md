---
declaration: example
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# The tautological sheaf need not be very ample

Take `X = P^1` and `E = O_X(-1)`. Since `E` has rank one, the quotient
functor gives `P(E) ≅ X` over `X`, and under this isomorphism the tautological
sheaf satisfies `O_{P(E)}(1) ≅ E`. It is not relatively very ample: a relative
projective-space immersion would make it a quotient of a finite free sheaf,
hence globally generated, whereas `O_{P^1}(-1)` has no nonzero global
sections.

## Depends on

- [Projective bundles](projective-bundle.md)
- [The tautological quotient and functor of points](projective-bundle-tautological-quotient.md)
- [Relative twisting sheaves and very ampleness](../../projective-sheaves/relative-twisting-and-very-ample.md)

## Proof depends on

- [The Picard group of projective space](../../divisors/cartier-picard/projective-space-picard-group.md)
- The calculation `Gamma(P^1,O(-1)) = 0`.

## Sources

- [Hartshorne II.7, Caution 7.8.8 and Exercise 7.14(a) (pp.161, 171)](../../../../sources/hartshorne-ii-7.md#adopted-exercises)
