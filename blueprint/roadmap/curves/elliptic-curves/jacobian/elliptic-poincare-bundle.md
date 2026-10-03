---
declaration: def
origin: cited
source_units: [chapter-iv-section-4]
---

# The normalized Poincaré class of an elliptic curve

Let `(X,P_0)` be a pointed elliptic curve, let `Delta` be the diagonal in
`X times X`, and let `p_1` be the first projection. The line bundle

`P = O(Delta) tensor p_1^* O(-P_0)`

has restriction over a point `P` of the second factor equal to the degree-zero
class `O(P-P_0)`. It is trivial on `X times {P_0}`, so it is normalized along
the parameter-axis base point. Its restriction to `{P_0} times X` is
`O_X(P_0)`, not trivial; tensoring also by `p_2^*O(-P_0)` gives a doubly
normalized actual bundle without changing the relative Picard class.

## Depends on

- [Effective Cartier divisors and locally principal subschemes](../../../schemes/divisors/cartier-picard/effective-cartier-closed-subscheme.md)
- [The invertible sheaf associated to a Cartier divisor](../../../schemes/divisors/cartier-picard/cartier-divisor-associated-sheaf.md)
- [Pullback on Picard groups](../../../schemes/divisors/divisor-exercises/picard-pullback.md)
- [Points of a genus-one curve and its degree-zero Picard group](../../riemann-roch/elliptic-points-picard-zero.md)

## Sources

- [Hartshorne IV.4, Theorem 4.11, p.325](../../../../sources/hartshorne-iv-4.md)
