---
declaration: theorem
origin: cited
---

# Decomposition into irreducible components

In a Noetherian topological space every nonempty closed subset `Y` is a finite
union `Y = Y₁ ∪ … ∪ Y_r` of irreducible closed subsets, and if no `Yᵢ` contains
another then the `Yᵢ` are uniquely determined. They are the *irreducible
components* of `Y`. Specialised to `𝔸ⁿ`, every algebraic set is uniquely a union
of finitely many varieties, none containing another (Corollary 1.6).

Existence is Noetherian induction on the set of closed subsets admitting no such
decomposition; uniqueness is a short argument comparing two decompositions
componentwise.

Mathlib has existence, as
`TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`, and
separately `NoetherianSpace.finite_irreducibleComponents`. Neither is
Hartshorne's statement: the first gives no irredundancy or uniqueness. Treat
them as reusable inputs, not as the result, and do not mark this node as
upstreamed on their strength.

## Depends on

- [Affine space is a Noetherian space](affine-space-noetherian.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Sources

- [Hartshorne I.1, Proposition 1.5 and Corollary 1.6 (p. 5)](../../sources/hartshorne.md#i1)
