---
article_id: af_7d9268752399c74032a1c3c3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.finite_support_ord_of_satisfiesConditionStar
---

# Principal divisors have finite support

Let $X$ satisfy $(*)$ and let $f : K(X)$ be nonzero. Then
$\operatorname{ord} _x(f) = 0$ for all but finitely many codimension-one points $x$.
Consequently the coefficients $\operatorname{ord} _x(f)$ define a Weil divisor $(f)$, and
$f \mapsto (f)$ is a homomorphism from $K(X)^*$ to the additive group $\operatorname{Div} X$.

This is Lemma 6.1 together with the immediately following definition.

## Depends on

- [The Weil divisor group](weil-divisor-group.md)
- [Affine opens have fraction field $K(X)$](../../normalization-and-exercises/function-field-integral-scheme.md)

## Proof depends on

- Order of vanishing is additive on products and vanishes on units.
- A proper closed subset of a Noetherian space has only finitely many
  codimension-one irreducible components relevant to a principal zero locus.

## Sources

- [Hartshorne II.6, Lemma 6.1 and principal divisors on printed p.131](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
