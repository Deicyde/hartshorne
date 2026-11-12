---
article_id: af_84d5f368413d6cf560e50055
declaration: theorem
origin: cited
lean: Hartshorne.AffineNonsingularLifting.exists_lift_of_isDomain_of_isRegular Hartshorne.AffineNonsingularLifting.exists_lift_of_isRegular
statement: formalized
proof: formalized
---

# Infinitesimal lifting for a nonsingular affine scheme

Let $k$ be algebraically closed and let $A$ be a finitely generated
$k$-algebra such that $\operatorname{Spec} A$ is a nonsingular variety over $k$. For every
surjection of $k$-algebras $B' \to B$ with square-zero kernel and every $k$-algebra map
$A \to B$, there is a lift $A \to B'$.

The proof uses only that every local ring of $\operatorname{Spec} A$ is regular; the variety
hypothesis is kept because it is Hartshorne's setting.

## Depends on

No project-local statement prerequisites.

## Proof depends on

- [The conormal sequence for a nonsingular closed immersion](../scheme-differentials/nonsingular-closed-immersion-conormal.md)
- [Differentials characterize nonsingularity](../scheme-differentials/differentials-characterize-nonsingular.md)
- Follow the book's steps (a)–(c), with $I$ the kernel of $B' \to B$: two lifts
  $A \to B'$ of $A \to B$ differ by an $A$-module map $\Omega_{A/k} \to I$; write
  $A = P/J$ with $P = k[x_{1}, \ldots, x_{n}]$ and lift $P \to A \to B$ to
  $h \colon P \to B'$; by Theorem 8.17 the sequence
  $0 \to J/J^{2} \to \Omega_{P/k} \otimes A \to \Omega_{A/k} \to 0$ is exact, and since
  $\Omega_{A/k}$ is locally free (Theorem 8.15) it stays exact after applying
  $\operatorname{Hom}_{A}(-, I)$, so $h|_{J}$ extends to a derivation $\theta \colon P \to I$
  and $h - \theta$ induces the lift $A \to B'$.

## Sources

- [Hartshorne II.8, Exercise 8.6 (pp.188–189)](../../../../sources/hartshorne-ii-8.md#adopted-exercises-and-later-use-evidence)
