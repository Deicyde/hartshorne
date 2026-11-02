---
article_id: af_c1f0eb64f03403a0fa846bde
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.mul_mem_gradedImage
---

# The degree bound

If $t$ lies in the fraction field of $S(Y)$ and $x_{i}^{N_{i}} \cdot t \in S(Y)$ for every
chart $U_{i}$ meeting $Y$, then $t \cdot S(Y)_N \subseteq S(Y)_N$ for any $N$ at least the sum
of the $N_{i}$.

This is Hartshorne's "let $N\geq\sum_i N_i$" in the proof of
[Theorem 3.4(a)](projective-global-regular.md). It is the only combinatorial
step in that part and the only place the cover being finite is used.

## The pigeonhole

$S(Y)_N$ is spanned by classes of degree-$N$ monomials, so it is enough to treat
$x^\alpha$, and there are two cases.

If some $\alpha _{i} > 0$ with $Y \cap U_{i}$ empty, then $x_{i}$ vanishes on $Y$, the class of
$x^\alpha$ is zero, and there is nothing to check. Otherwise $\alpha$ is supported on the
charts that meet $Y$, and $\sum_i\alpha_i=N\geq\sum_i N_i$ over those forces $\alpha _{i} \ge N_{i}$ for some
$i$; then $x^\alpha$ absorbs the denominator and $x^\alpha \cdot t = (x^\alpha /x_{i}^{N_{i}}) \cdot g_{i}$ has
degree $(N - N_{i}) + N_{i}$.

The two cases are what makes the hypothesis "for every chart meeting $Y$" rather
than "for every chart" the right one: the charts that miss $Y$ contribute
nothing because their variables are already zero in $S(Y)$.

## Depends on

- [Graded localization](graded-localization.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
