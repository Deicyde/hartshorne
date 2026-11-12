---
article_id: af_84d5f368413d6cf560e50055
declaration: theorem
origin: cited
lean: Hartshorne.AffineNonsingularLifting.exists_lift_of_isRegular
statement: formalized
proof: formalized
---

# Infinitesimal lifting for a nonsingular affine scheme

Let $k$ be algebraically closed and let $A$ be a finitely generated
$k$-algebra such that $\operatorname{Spec} A$ is nonsingular. For every surjection of
$k$-algebras $B' \to B$ with square-zero kernel and every $k$-algebra map
$A \to B$, there is a lift $A \to B'$.

## Depends on

- [The conormal sequence for a nonsingular closed immersion](../scheme-differentials/nonsingular-closed-immersion-conormal.md)
- [Differentials characterize nonsingularity](../scheme-differentials/differentials-characterize-nonsingular.md)

## Proof depends on

- Embed $A$ as a quotient of a polynomial algebra and split the resulting
  conormal sequence after applying $\operatorname{Hom} (-, I)$.
- The infinitesimal lifting property of a formally smooth algebra.
- [The differential criterion for smoothness over a field](../../../cohomology/smooth-morphisms/criteria/differential-criterion-smooth-over-field.md)

## Sources

- [Hartshorne II.8, Exercise 8.6 (pp.188–189)](../../../../sources/hartshorne-ii-8.md#adopted-exercises-and-later-use-evidence)
