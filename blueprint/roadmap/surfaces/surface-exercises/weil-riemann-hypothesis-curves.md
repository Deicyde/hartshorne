---
article_id: af_22f2dfb1016d73261a11dc02
declaration: theorem
origin: cited
---

# Weil's Riemann-hypothesis bound for curves

Let $C$ be a nonsingular projective genus-$g$ curve over $\mathbb F_q$, and let $N$
be the number of $\mathbb F_q$-rational points. Write $N=1-a+q$. Then

$|a| \le 2\cdot g\cdot \sqrt{q}$.

Equivalently, $|N-(q+1)| \le 2\cdot g\cdot \sqrt{q}$.

## Depends on

- [The Castelnuovo–Severi product inequality](castelnuovo-severi-product-inequality.md)
- [Self-intersection is the degree of the normal bundle](../intersection-theory/foundations/self-intersection-normal-bundle-degree.md)
- [Local intersection multiplicity on a surface](../intersection-theory/foundations/local-intersection-multiplicity.md)
- [Global intersections are sums of local lengths](../intersection-theory/foundations/intersection-number-sum-local-lengths.md)
- [Degree of Frobenius on a curve](../../curves/ramification/curve-frobenius-finite-degree.md)
- [Absolute Frobenius and Hartshorne's Frobenius twist](../../curves/ramification/scheme-frobenius-twist.md)

## Proof depends on

- On $C \times C$, the diagonal satisfies $\Delta ^2=2-2\cdot g$. The graph $\Gamma$
  of $q$-power Frobenius satisfies $\Gamma ^2=q\cdot (2-2\cdot g)$ and
  $\Gamma\cdot\Delta=N$, the last equality by fixed-point intersection lengths.
- Apply the product inequality to every integral combination
  $r\cdot \Gamma +s\cdot \Delta$ and require the resulting binary quadratic form to have
  nonpositive discriminant.

## Sources

- [Hartshorne V.1, Exercise 1.10, p.368](../../../sources/hartshorne-v-1.md#exercise-disposition-printed-pp366368)
