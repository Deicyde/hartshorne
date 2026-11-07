---
article_id: af_6c5def371c0511bc41bb5822
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveSpace_satisfiesConditionStar Hartshorne.projectiveSpaceWeilDivisorDegree Hartshorne.projectiveSpaceWeilDivisorDegree_apply Hartshorne.projectivePrimeDivisorEquationDegree_eq Hartshorne.projectiveHyperplanePrimeDivisor Hartshorne.projectiveSpace_linearEquivalent_degree_smul_hyperplane Hartshorne.projectiveSpaceWeilDivisorDegree_principalDivisor Hartshorne.projectiveSpaceClassGroupEquiv Hartshorne.projectiveSpaceClassGroupEquiv_weilDivisorClassHom Hartshorne.projectiveSpaceClassGroupEquiv_hyperplane
---

# The class group of projective space

Let $k$ be a field and $n \ge 1$. For a Weil divisor on $\mathbb{P}^n_k$, define its
degree by weighting each prime divisor by the degree of its hypersurface.
If $H$ is a hyperplane, then $D\sim\deg(D)H$. Every principal divisor has
degree zero, and degree induces an isomorphism $\operatorname{Cl}(\mathbb{P}^n_k)\cong\mathbb{Z}$ sending $H$
to $1$.

The positive-dimension hypothesis is explicit: $\mathbb{P}^0$ does not have the stated
class group.

## Depends on

- [Linear equivalence and the Weil class group](weil-linear-equivalence.md)
- [Projective space over a ring](../../projective-spectrum/projective-space-over-ring.md)
- [Projective codimension one is a hypersurface](../../../intersections-projective-space/dimension/projective-codimension-one-hypersurface.md)
- [Ambient hypersurfaces cut divisors](../divisor-exercises/projective-intersection-divisor.md)

## Proof depends on

- Unique factorization of homogeneous polynomials and homogeneous
  representatives of rational functions of equal degree.
- [Codimension-one stalks are DVRs](codimension-one-stalk-dvr.md)
- [The projective-space case of Bertini](../../differentials/canonical-bertini/bertini-projective-space-case.md)

## Sources

- [Hartshorne II.6, Proposition 6.4 on printed pp.132–133](../../../../sources/hartshorne-ii-6.md#weil-divisors-and-class-groups)
