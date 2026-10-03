---
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Pullback compatibility for divisor sheaves on curves

Let `f : X → Y` be a finite morphism of nonsingular curves. For every Weil
divisor `D` on `Y`, prove a natural isomorphism

`f* O_Y(D) ≅ O_X(f*D)`.

On the left, `f*` is pullback of invertible sheaves; inside the right-hand
divisor, it is the valuation-weighted pullback `Div Y → Div X`. This is
Exercise 6.8(b), and it is the compatibility used in IV.2.

## Depends on

- [Pullback of divisors along finite curve morphisms](../curve-divisors/finite-curve-divisor-pullback.md)
- [The invertible sheaf associated to a Cartier divisor](../cartier-picard/cartier-divisor-associated-sheaf.md)
- [Pullback on Picard groups](picard-pullback.md)
- [Weil classes and the Picard group on a locally factorial scheme](../cartier-picard/locally-factorial-class-picard-equivalence.md)

## Proof depends on

- Pulling back a local equation multiplies its order at `P` by the
  ramification index over `f(P)`.
- Isomorphisms of invertible sheaves may be checked on a trivializing cover.

## Sources

- [Hartshorne II.6, Exercise 6.8(b) on printed p.148](../../../../sources/hartshorne-ii-6.md#adopted-exercises-and-later-use-evidence)
