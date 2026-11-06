---
article_id: af_512e70305ef49d24027b0d85
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ValuationCenter.subsingleton_of_isSeparated Hartshorne.ValuationCenter.point_eq_of_isSeparated
---

# Separated schemes have unique valuation centers

Let $X$ be an integral scheme of finite type over a field $k$. If $X$ is
separated over $k$, every valuation of $K(X)/k$ has at most one center on $X$.

Two centers give two lifts of the same valuative square whose generic map is
the canonical map $\operatorname{Spec} K(X) \longrightarrow X$ and whose base map is
$\operatorname{Spec} R \longrightarrow \operatorname{Spec} k$. Separatedness supplies uniqueness in the valuative
criterion, so the lifts, and hence their closed-point images, agree.

The finite-type hypothesis is kept as in the source; it is not needed,
because uniqueness of lifts in the valuative criterion uses only that $X$ is
separated over $k$.

The theorem deliberately asserts only uniqueness: a nonproper separated
scheme need not contain a center for every valuation.

## Depends on

- [Centers of valuations](valuation-center.md)
- [Separated morphisms](separated-morphism.md)

## Proof depends on

- [Valuative criterion for separatedness](valuative-criterion-separated.md)
- The canonical structure map of an integral scheme over $k$.

## Sources

- [Hartshorne II.4, Exercise 4.5(a)](../../../sources/hartshorne-ii-4.md#adopted-exercises)
