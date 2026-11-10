---
article_id: af_22f01c81477978c9b3e3208c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.smoothOfRelativeDimension_iff_forall_isRegularAt Hartshorne.smoothOfRelativeDimension_iff_isRegular Hartshorne.topologicalKrullDim_irreducibleComponents_fiber Hartshorne.topologicalKrullDim_irreducibleComponents_of_fiber
---

# Smoothness and regularity over an algebraically closed field

Let $X$ be a finite-type scheme over an algebraically closed field $k$, and let
$n \ge 0$. Then $X \to \operatorname{Spec} k$ is smooth of relative dimension $n$ if and
only if every local ring of $X$ is regular and every irreducible component of $X$ has
dimension $n$.

For an integral separated $X$ of dimension $n$, this identifies smoothness with
Hartshorne's nonsingularity predicate from II.8. Over a non-perfect field, a regular
scheme need not be smooth.

## Depends on

- [Hartshorne's smoothness criterion](hartshorne-smoothness-criterion.md)
- [Regular points and nonsingular schemes](../../../schemes/differentials/scheme-differentials/regular-points-and-nonsingular-schemes.md)
- [Differentials characterize nonsingular varieties](../../../schemes/differentials/scheme-differentials/differentials-characterize-nonsingular.md)

## Proof depends on

- [The regular-local differential criterion](../../../schemes/differentials/kaehler-differentials/regular-local-differential-criterion.md)
- Algebraically closed fields are perfect.

## Sources

- [Hartshorne III.10, Example 10.0.3, p.268](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
- [Hartshorne II.8, Theorems 8.8 and 8.15](../../../../sources/hartshorne-ii-8.md)
