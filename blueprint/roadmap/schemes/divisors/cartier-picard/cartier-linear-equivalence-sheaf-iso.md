---
article_id: af_23baadb1329327bb38ba2ae5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AlgebraicGeometry.Scheme.CartierDivisor.linearEquivalent_iff_nonempty_iso
---

# Linear equivalence is isomorphism of divisor sheaves

For Cartier divisors $D_1,D_2$ on a scheme $X$,

$D_1\sim D_2$ if and only if $\mathcal{O}_X(D_1) \cong \mathcal{O}_X(D_2)$

as abstract invertible sheaves, after forgetting their embeddings in the
total quotient sheaf.

This is Hartshorne's Proposition II.6.13(c). After reducing by the associated-sheaf arithmetic
to $D=D_1-D_2$, a trivialization of $\mathcal{O}_X(D)$ supplies a nowhere-vanishing
global rational section whose inverse represents $D$ as principal.

## Depends on

- [Arithmetic of associated divisor sheaves](cartier-associated-sheaf-arithmetic.md)

## Proof depends on

- A trivialization of an embedded invertible subsheaf of $K_X$ is a global
  rational unit exactly when the associated divisor is principal.

## Sources

- [Hartshorne II.6, Proposition 6.13(c) on printed p.144](../../../../sources/hartshorne-ii-6.md#cartier-divisors-and-invertible-sheaves)
