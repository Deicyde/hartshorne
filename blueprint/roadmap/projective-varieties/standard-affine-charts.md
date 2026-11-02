---
article_id: af_dddc3e684133ba9c97f4a783
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.chartHomeomorph Hartshorne.chartEquiv Hartshorne.awayChartEquiv
---

# The standard affine charts

Let $H_{i} = Z(x_{i})$ and $U_{i} = \mathbb{P} ^{n} \setminus H_{i}$. The map $\varphi _{i} : U_{i} \to \mathbb{A} ^{n}$ sending
$(a_{0},\ldots ,a_{n})$ to $(a_{0}/a_{i}, \ldots , a_{n}/a_{i})$ with the $i$-th entry omitted is a
homeomorphism for the induced Zariski topology on $U_{i}$ and the Zariski topology
on $\mathbb{A} ^{n}$ (Proposition 2.2).

The proof is the dehomogenisation/homogenisation pair. Taking $i = 0$ and
$A = k[y_{1},\ldots ,y_{n}]$, define $\alpha : S^h \to A$ by $\alpha (f) = f(1, y_{1}, \ldots , y_{n})$ and
$\beta : A \to S^h$ by $\beta (g) = x_{0}^{\deg g} \cdot g(x_{1}/x_{0}, \ldots , x_{n}/x_{0})$. Then $\alpha$ and $\beta$
carry closed sets to closed sets in either direction, which makes $\varphi$ a closed
bijection with closed inverse.

This is the key result of §2 and the most-used result of Chapter I: it is what
lets every local question about a projective variety be answered affinely. It is
upgraded from a homeomorphism to an isomorphism of varieties in §3, once
morphisms exist; see [the chart isomorphism](../morphisms/projective-rings/chart-isomorphism.md).

## What $\alpha$ and $\beta$ do to polynomials

Proposition 2.2 needs only that the pair moves closed sets in both directions.
Theorem 3.4 needs more: that $\alpha$ is a bijection from the homogeneous
polynomials, up to powers of $x_{i}$, onto all polynomials in the affine
coordinates. Both halves are recorded here, since they are statements about the
same pair.

One half is bookkeeping: $\alpha (\beta (g)) = g$, because $\beta$ pads each monomial with a
power of $x_{i}$ and $\alpha$ sets $x_{i}$ to $1$.

Within each fixed homogeneous degree, $\alpha$ is injective. This is
proved by evaluation rather than by comparing supports. If $\alpha (g) = 0$ then $g$
vanishes at every vector with $i$-th coordinate $1$, hence by homogeneity
wherever the $i$-th coordinate is nonzero; so $x_{i} \cdot g$ vanishes identically and,
over an infinite field, is zero. Homogeneity is doing the work and cannot be
dropped: $x_{i} - 1$ is killed by $\alpha$ and is not zero.

Together these give the ring-level form of Proposition 2.2: $S_{(x_i)}\cong k[y]$,
the degree-zero part of $S$ localised at $x_{i}$ being the coordinate ring of the
chart. The map needs no grading to define — $\alpha$ sends $x_{i}$ to a unit, so it
factors through the localisation at $x_{i}$ outright, and the degree-zero part is
carried along. Theorem 3.4 is stated in terms of $S(Y)_{(x_i)}$, and this is the
ambient case of it.

## Depends on

- [The Zariski topology on projective space](projective-zariski-topology.md)
- [The Zariski topology on affine space](../affine-varieties/zariski-topology.md)

## Sources

- [Hartshorne I.2, Proposition 2.2 (pp. 10-11)](../../sources/hartshorne.md#i2)
