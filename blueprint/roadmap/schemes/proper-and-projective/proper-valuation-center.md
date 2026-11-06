---
article_id: af_8f10ec4eab25b1087868de48
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ValuationCenter.nonempty_unique_of_isProper Hartshorne.ValuationCenter.existsUnique_point_of_isProper Hartshorne.ValuationCenter.existsUnique_dominates_of_isProper
---

# Proper schemes have valuation centers

Let $X$ be an integral scheme of finite type over a field $k$. If $X$ is
proper over $k$, every valuation of $K(X)/k$ has exactly one center on $X$.

The canonical generic-point map and the valuation-ring structure map form a
valuative square for $X \longrightarrow \operatorname{Spec} k$. Properness gives a unique lift
$\operatorname{Spec} R \longrightarrow X$; its closed-point image is the required center. The domination
formulation follows from the center equivalence, and uniqueness also follows
from separatedness.

The finite-type hypothesis is kept as in the source; it is already part of
properness over $k$.

## Depends on

- [Centers of valuations](../separated-morphisms/valuation-center.md)
- [Proper morphisms](proper-morphism.md)

## Proof depends on

- [Valuative criterion for properness](valuative-criterion-proper.md)
- [Separated schemes have unique valuation centers](../separated-morphisms/separated-unique-valuation-center.md)

## Sources

- [Hartshorne II.4, Exercise 4.5(b)](../../../sources/hartshorne-ii-4.md#adopted-exercises)
