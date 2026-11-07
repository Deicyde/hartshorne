---
article_id: af_9adbd4ff3083345a89959c56
declaration: theorem
origin: bridged
---

# Local rings of a fibre product

Let $f : X \to Y$ and $g : Y' \to Y$ be morphisms of schemes, and let
$X' = X \times_Y Y'$ with projections $p : X' \to X$ and $q : X' \to Y'$. Let
$x' \in X'$, with $x = p(x')$, $y' = q(x')$ and $y = f(x) = g(y')$. The stalk
maps $p^\#_{x'}$ and $q^\#_{x'}$ agree on $\mathcal{O}_{Y,y}$, so they induce a
ring homomorphism

$\mathcal{O}_{X,x} \otimes_{\mathcal{O}_{Y,y}} \mathcal{O}_{Y',y'} \to \mathcal{O}_{X',x'}$.

This homomorphism is a localization at the prime ideal $\mathfrak{p}$ of the
tensor product lying under the maximal ideal of $\mathcal{O}_{X',x'}$:

$\mathcal{O}_{X',x'} \cong (\mathcal{O}_{X,x} \otimes_{\mathcal{O}_{Y,y}} \mathcal{O}_{Y',y'})_{\mathfrak{p}}$.

In particular $\mathcal{O}_{X',x'}$ is flat over the tensor product.

Choose an affine open $W = \operatorname{Spec} R$ containing $y$, and affine
opens $V = \operatorname{Spec} A$ over $W$ containing $x$ and
$V' = \operatorname{Spec} B$ over $W$ containing $y'$. Then $V \times_W V'$ is
an open subscheme of $X'$ containing $x'$, isomorphic to
$\operatorname{Spec}(A \otimes_R B)$. Open immersions preserve local rings, and
the local ring of a spectrum at a prime is the localization there. So, with
$\mathfrak{q}$, $\mathfrak{q}'$, $\mathfrak{r}$ and $P$ the primes of $x$, $y'$,
$y$ and $x'$, the map above is
$A_{\mathfrak{q}} \otimes_{R_{\mathfrak{r}}} B_{\mathfrak{q}'} \to (A \otimes_R B)_P$.
Its source is itself a localization of $A \otimes_R B$ at a multiplicative set
contained in the complement of $P$, so its target is the localization of its
source at the prime $\mathfrak{p}$ induced by $P$.

## Depends on

- [Fiber products of schemes exist](schemes-have-fiber-products.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- [Fiber products of affine schemes](affine-fiber-product.md)
- [Restricting a fiber product to an open subscheme](fiber-product-restrict-open.md)
- [Open immersions and open subschemes](../subschemes-and-dimension/open-immersions.md)
- [The stalk of Spec](../spectrum-and-schemes/spec-stalk.md)
- A tensor product of localizations of $R$-algebras is a localization of
  their tensor product.
- [Localizations are flat](../../cohomology/flat-families/flatness/localization-is-flat.md)

## Sources

- [Hartshorne II.3, Theorem 3.3 (construction of fibre products), pp.87–88](../../../sources/hartshorne-ii-3.md#fiber-products-fibers-and-base-extension)
