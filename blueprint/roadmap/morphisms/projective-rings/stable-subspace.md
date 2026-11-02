---
article_id: af_0e226ccf6491b72157afd22a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.isIntegral_of_mul_mem Hartshorne.exists_algebraMap_eq_of_isIntegral Hartshorne.exists_algebraMap_eq_of_mul_mem Hartshorne.fg_projCoordGrading Hartshorne.finiteDimensional_projCoordGrading
---

# An element stabilising a finite-dimensional subspace is integral

Let $K$ be a $k$-algebra domain, let $V\subseteq K$ be a nonzero
finite-dimensional $k$-subspace, and let $f\in K$ satisfy $fV\subseteq V$.
Then $f$ is integral over $k$. If $k$ is algebraically closed, then $f\in k$.

The determinant trick applied to multiplication by $f$ on $V$ gives a
monic polynomial relation. Equivalently, for nonzero $v\in V$, the map
$a\mapsto av$ injects $k[f]$ into $V$, so $k[f]$ is finite-dimensional.
Over an algebraically closed field the minimal polynomial is linear,
making $f$ a constant.

Each homogeneous piece of $S(Y)$ is finite-dimensional: it is the image
of a finite-dimensional homogeneous polynomial piece. This is the
finiteness used in [Theorem I.3.4(a)](projective-global-regular.md).

## Depends on

- [Graded localization](graded-localization.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
