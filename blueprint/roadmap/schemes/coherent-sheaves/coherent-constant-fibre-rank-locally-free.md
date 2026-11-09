---
article_id: af_3d213fc9bd0b719e0a518a70
declaration: theorem
origin: cited
---

# Constant fibre dimension forces local freeness

Let $X$ be a reduced Noetherian scheme, let $F$ be a coherent
$\mathcal{O}_X$-module, and let $n \ge 0$. For $x \in X$ put

$\varphi(x) = \dim_{k(x)} \left(F_x \otimes_{\mathcal{O}_{X,x}} k(x)\right)$,

where $k(x)$ is the residue field of $\mathcal{O}_{X,x}$. Then $F$ is locally
free of rank $n$ if and only if $\varphi(x) = n$ for every $x \in X$.

The direction from local freeness to constant fibre dimension holds on any
scheme. The converse is local on $X$, so the Noetherian hypothesis may be
weakened to locally Noetherian.

Fix $x \in X$ and put $R = \mathcal{O}_{X,x}$ and $M = F_x$. Lifting a basis of
$M \otimes k(x)$, Nakayama's lemma gives a surjection $R^n \to M$; let $K$ be
its kernel. A minimal prime $\mathfrak{p}$ of $R$ corresponds to a point $\eta$ of $X$
specializing to $x$, with $R_{\mathfrak{p}} = \mathcal{O}_{X,\eta}$ and
$M_{\mathfrak{p}} = F_\eta$. The ring $R_{\mathfrak{p}}$ is a field, because it
is reduced with a single prime, so $F_\eta$ has dimension $\varphi(\eta) = n$
and $R_{\mathfrak{p}}^n \to M_{\mathfrak{p}}$ is a surjection of
$n$-dimensional vector spaces. Hence $K_{\mathfrak{p}} = 0$.
Thus every coordinate of an element of $K$ lies in every minimal prime of $R$.
Since $R$ is reduced and the nilradical is the intersection of the minimal
primes, $K = 0$. Thus $F_x$ is free of rank $n$ for every $x$, and the free
locus criterion makes $F$ locally free of rank $n$.

## Depends on

- [Coherent affine-local criterion](../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Locally free and invertible modules](../modules-and-quasicoherent/locally-free-and-invertible.md)
- [Reduced schemes](../first-properties/reduced-scheme.md)

## Proof depends on

- [The free locus of a coherent sheaf](coherent-free-locus.md)
- Over a reduced ring, the localization at a minimal prime is a field, and the
  intersection of the minimal primes, which is the nilradical, is zero.

## Informally uses

- [Reduced schemes are detected on stalks](../foundational-properties/reduced-iff-stalks.md)

## Sources

- [Hartshorne II.5, Exercise 5.8(c), p.125](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
