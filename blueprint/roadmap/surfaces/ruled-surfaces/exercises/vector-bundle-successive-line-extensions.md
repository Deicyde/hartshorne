---
article_id: af_caf33dec696382cdfa3d5a22
declaration: theorem
origin: cited
lean: Hartshorne.exists_lineBundleFiltration Hartshorne.exists_lineBundleFiltration_of_projective
statement: formalized
proof: formalized
---

# Vector bundles on curves are successive extensions of line bundles

Let $E$ be a finite locally free sheaf of rank $r$ on a nonsingular projective
curve $C$ over an algebraically closed field $k$. There is a filtration by
locally free subsheaves

$0=E_0 \subset E_1 \subset \ldots \subset E_r=E$

such that every quotient $E_i/E_{i-1}$ is invertible.

Nonsingularity is not used: the statement holds for any integral projective curve
over $k$.

## Depends on

- [Nonsingular curves over a field](../../../schemes/divisors/curve-divisors/nonsingular-curve.md)

## Proof depends on

- [A nowhere-vanishing section of a high-rank generated bundle](../../prerequisites/globally-generated-bundle-nowhere-vanishing-section.md)
- [Serre global generation](../../../schemes/projective-sheaves/serre-global-generation.md)
- Twist by a sufficiently positive invertible sheaf, apply II Exercise 8.2
  to split off a locally free rank-one subsheaf with locally free quotient,
  and induct on the rank; tensoring back preserves the filtration.

## Sources

- [Hartshorne V.2, Exercise 2.3(a), p.383](../../../../sources/hartshorne-v-2.md#exercise-disposition-printed-pp383386)
