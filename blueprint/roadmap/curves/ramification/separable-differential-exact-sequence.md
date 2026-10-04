---
article_id: af_98f5a9ebe6d2ee0d7943b38e
declaration: exact sequence
origin: cited
source_units: [chapter-iv-sections-1-2]
---

# The differential sequence of a separable curve morphism

Let `f : X -> Y` be a finite separable morphism of curves. Then the standard
transitivity sequence is exact also on the left:

`0 -> f^* Omega_Y -> Omega_X -> Omega_(X/Y) -> 0`.

## Depends on

- [The transitivity sequence for differential sheaves](../../schemes/differentials/scheme-differentials/relative-differentials-transitivity.md)
- [Differentials of finitely generated field extensions](../../schemes/differentials/kaehler-differentials/field-differentials-dimension.md)
- [Differentials and canonical divisors on a curve](../riemann-roch/curve-differentials-canonical-divisor.md)

## Proof depends on

- Separability makes `Omega_(K(X)/K(Y))` zero, so the map between the two
  invertible differential sheaves is nonzero at the generic point.
- A generically nonzero morphism from an invertible sheaf on an integral
  scheme is injective.

## Sources

- [Hartshorne IV.2, Proposition 2.1, p.300](../../../sources/hartshorne-iv-2.md#finite-maps-ramification-and-the-different-pp299301)
- [Stacks Project, generically étale criterion, tag 0C1C](../../../sources/hartshorne-iv-2.md#external-proof-sources)
