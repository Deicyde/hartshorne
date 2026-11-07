---
article_id: af_3d213fc9bd0b719e0a518a70
declaration: theorem
origin: cited
---

# Constant fibre dimension forces local freeness

Let $X$ be an integral Noetherian scheme, let $F$ be a coherent
$\mathcal{O}_X$-module, and let $n \ge 0$. For $x \in X$ put

$\varphi(x) = \dim_{k(x)} \left(F_x \otimes_{\mathcal{O}_{X,x}} k(x)\right)$,

where $k(x)$ is the residue field of $\mathcal{O}_{X,x}$. Then $F$ is locally
free of rank $n$ if and only if $\varphi(x) = n$ for every $x \in X$.

The direction from local freeness to constant fibre dimension holds on any
scheme. The converse is local on $X$, so the Noetherian hypothesis may be
weakened to locally Noetherian.

## Depends on

- [Coherent affine-local criterion](../modules-and-quasicoherent/coherent-affine-local-criterion.md)
- [Locally free and invertible modules](../modules-and-quasicoherent/locally-free-and-invertible.md)

## Proof depends on

- [The free locus of a coherent sheaf](coherent-free-locus.md)
- Over a local domain, a finitely generated module whose fibre at the closed
  point and fibre at the generic point have the same dimension is free: lift a
  basis of the closed fibre by Nakayama's lemma to a surjection from a free
  module of that rank, which is injective after passing to the fraction field.

## Sources

- [Hartshorne II.5, Exercise 5.8(c), integral case, p.125](../../../sources/hartshorne-ii-5.md#adopted-exercises-and-later-use-evidence)
