---
article_id: af_6529eecc05e492dff53a5801
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# The Picard group of a product when H¹ vanishes

Let `X` be an integral projective scheme over an algebraically closed field
with `H^1(X,O_X)=0`, and let `T` be a connected finite-type scheme over that
field, not necessarily reduced. The restrictions of any invertible sheaf on
`X times T` to the closed fibres over `T` are mutually isomorphic, and the map

`Pic(X) times Pic(T) -> Pic(X times T)`

given by pullback from the two factors and tensor product is an isomorphism.

## Depends on

- [Cohomology and base change](../theorems/cohomology-and-base-change.md)
- [Pullback on Picard groups](../../../schemes/divisors/divisor-exercises/picard-pullback.md)
- [The Picard group as first unit-sheaf cohomology](../../cohomology-exercises/picard-h1-units.md)

## Proof depends on

- Vanishing of `H^1(X,O_X)` makes infinitesimal variation of a line bundle on
  the fibres trivial; the argument must include nilpotent thickenings of `T`
  and cannot be reduced to its closed-point set.
- Use the base-change theorem directly to make the fibre class locally
  constant over all of connected `T`, then construct the descended line
  bundle from the pushforward and evaluation map on the whole scheme before
  normalizing at one closed fibre.

## Sources

- [Hartshorne III, Exercise 12.6, p.292](../../../../sources/hartshorne-iii-11-12.md#exercise-12-disposition-pp291292)
