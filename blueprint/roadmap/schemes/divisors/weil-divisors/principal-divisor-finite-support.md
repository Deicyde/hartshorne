---
article_id: af_7d9268752399c74032a1c3c3
declaration: theorem
origin: cited
source_units: [chapter-ii-sections-6-7]
---

# Principal divisors have finite support

Let `X` satisfy `(*)` and let `f : K(X)` be nonzero. Then
`ord_x(f) = 0` for all but finitely many codimension-one points `x`.
Consequently the coefficients `ord_x(f)` define a Weil divisor `(f)`, and
`f ↦ (f)` is a homomorphism from `K(X)^*` to the additive group `Div X`.

This is Lemma 6.1 together with the immediately following definition. The
unique main result is finite support; the divisor and homomorphism are its
canonical interface.

## Depends on

- [The Weil divisor group](weil-divisor-group.md)
- [Affine opens have fraction field `K(X)`](../../normalization-and-exercises/function-field-integral-scheme.md)

## Proof depends on

- `Scheme.ord`, `Scheme.ord_mul`, and `Scheme.ord_of_isUnit` from
  `Mathlib/AlgebraicGeometry/OrderOfVanishing.lean`.
- A proper closed subset of a Noetherian space has only finitely many
  codimension-one irreducible components relevant to a principal zero locus.

## Sources

- [Hartshorne II.6, Lemma 6.1 and principal divisors on printed p.131](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
