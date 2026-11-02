---
article_id: af_99905fcdb2a616c538f5d376
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.graphProjection_isIso
---

# The complement of a hypersurface is affine

Let $0 \ne f \in k[x_{1},\ldots ,x_n]$, let $Y = Z(f)$, and write
$D(f)=\mathbb A^n\setminus Y$. Then $D(f)$ is isomorphic to the graph hypersurface

$H_f = Z(x_{n+1} f - 1) \subseteq \mathbb{A} ^{n+1}$.

In particular $D(f)$ has an affine presentation (Lemma 4.2). The nonzero
hypothesis is essential in the project's irreducible, nonempty notion of a
variety: for $f = 0$, the complement is empty.

## The proof

Projection $\pi : H_f \to \mathbb{A} ^{n}$, $(a_{1},\ldots ,a_{n+1}) \mapsto (a_{1},\ldots ,a_n)$, lands in $D(f)$ and
is a morphism because its coordinates are regular. It is inverse on points to

$(a_{1},\ldots ,a_n) \mapsto (a_{1},\ldots ,a_n, 1/f(a_{1},\ldots ,a_n))$, whose last coordinate is a regular
function on $D(f)$ because $f$ is nowhere zero there. The criterion for maps to
affine varieties therefore makes this inverse a morphism. The graph
hypersurface is an affine variety because its coordinate algebra is the
localization at $f$, hence a domain; that algebra calculation is split into
[its own node](principal-open-coordinate-ring.md).

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)
- [Morphisms](../morphisms/morphism.md)
- [The graph hypersurface has localized coordinate ring](principal-open-coordinate-ring.md)

## Proof depends on

- [Criterion for a morphism to an affine variety](../morphisms/morphism-to-affine-criterion.md)

## Sources

- [Hartshorne I.4, Lemma 4.2 (p. 25)](../../sources/hartshorne.md#i4)
