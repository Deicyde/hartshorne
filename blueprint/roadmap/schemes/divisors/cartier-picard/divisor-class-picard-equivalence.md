---
article_id: af_29c80a8b62684c58f6141b1b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.exists_invertibleTotalQuotientSubmodule_iso AlgebraicGeometry.Scheme.exists_cartierDivisor_sheaf_iso AlgebraicGeometry.Scheme.cartierClassToPicard_surjective AlgebraicGeometry.Scheme.cartierClassToPicard_bijective AlgebraicGeometry.Scheme.cartierClassEquivPicard AlgebraicGeometry.Scheme.cartierClassEquivPicard_apply
---

# Cartier classes and the Picard group of an integral scheme

If $X$ is an integral scheme, prove that every invertible sheaf is isomorphic
to an invertible subsheaf of the constant function-field sheaf $K_X$.
Consequently the canonical injection is an isomorphism

$\operatorname{CaCl}(X)\cong\operatorname{Pic}(X)$.

The proof tensors an invertible sheaf with $K_X$, identifies the result with a
rank-one constant sheaf on the irreducible space, and proves that the natural
map into that sheaf is injective.

## Depends on

- [Cartier classes inject into the Picard group](cartier-class-to-picard.md)
- [Affine opens have fraction field $K(X)$](../../normalization-and-exercises/function-field-integral-scheme.md)

## Proof depends on

- Local triviality of an invertible sheaf.
- Nonempty open subsets of an irreducible space intersect.
- Injectivity of regular functions into the function field.

## Sources

- [Hartshorne II.6, Proposition 6.15 on printed p.145](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)
