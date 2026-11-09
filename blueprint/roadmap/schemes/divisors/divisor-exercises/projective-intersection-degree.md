---
article_id: af_a3cb5f556ad22a8f6e4d2bd1
declaration: theorem
origin: cited
---

# Degree of an ambient hypersurface section

In the setting of the ambient intersection divisor, for an irreducible
hypersurface $V$ not containing $X$, prove that the valuation multiplicity of
$V\cdot X$ along each component is the local intersection multiplicity.
Consequently, when $\dim X\ge 1$, generalized Bezout gives
$\deg(V\cdot X)=\deg(V)\deg(X)$.

Now let $D=\sum_j n_j V_j$ be any Weil divisor on $\mathbb{P}^n_k$, a finite
$\mathbb{Z}$-combination of irreducible hypersurfaces $V_j$, none of which
contains $X$, and let $D\cdot X=\sum_j n_j\,(V_j\cdot X)$ be the linear
extension of the ambient intersection divisor. Its degree on $\mathbb{P}^n_k$ is
$\deg D=\sum_j n_j\deg V_j$. Prove that when $\dim X\ge 1$,

$\deg(D\cdot X)=(\deg D)(\deg X)$.

The dimension bound is the hypothesis of generalized Bezout and cannot be
dropped: if $X$ is a closed point not on $V$, then $V\cdot X=0$ while
$\deg(V)\deg(X)=\deg(V)\ge 1$.

This is the adopted content of Exercise 6.2(c). The wider conclusions in
parts (b),(d), including descent to class groups and their diagram, remain
outside this node.

## Depends on

- [Ambient hypersurfaces cut divisors](projective-intersection-divisor.md)
- [Degree of a projective Weil divisor](projective-weil-divisor-degree.md)
- [Projective hypersurface Bezout](../../../intersections-projective-space/bezout/projective-hypersurface-bezout.md)
- [Intersection multiplicity with a hypersurface](../../../intersections-projective-space/bezout/projective-intersection-multiplicity.md)
- [Projective intersection components correspond to minimal primes](../../../intersections-projective-space/bezout/projective-intersection-components-minimal-primes.md)

## Proof depends on

- Equality between the DVR order of a local hypersurface equation and the
  corresponding local intersection multiplicity.
- Additivity of projective degree over top-dimensional components with
  multiplicity.
- [Codimension-one stalks are DVRs](../weil-divisors/codimension-one-stalk-dvr.md)
- [Algebraic sets and homogeneous radical ideals](../../../projective-varieties/homogeneous-ideal-correspondence.md)
- [Proper closed subsets of projective varieties have smaller dimension](../../../intersections-projective-space/dimension/projective-proper-closed-dimension-drop.md)
- [A zero-dimensional projective variety is a point](../../../intersections-projective-space/bezout/projective-zero-dimensional-variety-point.md)

## Sources

- [Hartshorne II.6, Exercise 6.2(c) on printed p.146](../../../../sources/hartshorne-ii-6.md#adopted-exercises-and-later-use-evidence)
