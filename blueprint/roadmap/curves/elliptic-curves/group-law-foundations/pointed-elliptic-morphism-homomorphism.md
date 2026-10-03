---
declaration: theorem
origin: cited
source_units: [chapter-iv-section-4]
---

# Pointed morphisms are homomorphisms

Let `f : (X,P_0) -> (X',P'_0)` be a morphism of pointed elliptic curves.
Then `f(P+Q)=f(P)+f(Q)` for all points, and this equality is one of scheme
morphisms.

## Depends on

- [Divisor pushforward descends to Picard groups](../../adopted-exercises/finite-curve-divisor-pushforward-pic.md)
- [Collinearity and the point-group law](elliptic-collinearity-group-law.md)
- [A pointed elliptic curve is a group variety](elliptic-group-variety.md)

## Proof depends on

- If `f` is constant the statement is immediate. Otherwise it is finite, and
  pushing forward `P+Q~R+P_0` gives the corresponding relation on `X'`.
- Density of closed points promotes the pointwise equality to morphisms.

## Sources

- [Hartshorne IV.4, Lemma 4.9, p.322](../../../../sources/hartshorne-iv-4.md)
