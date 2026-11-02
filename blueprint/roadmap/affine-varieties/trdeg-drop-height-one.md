---
article_id: af_8a649f06764de378e6f03c08
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: Hartshorne.exists_trdeg_of_height_eq_one
---

# A height-one prime drops the transcendence degree by one

Let $B$ be a finitely generated domain over $k$ and $\mathfrak{p} \subseteq B$ a prime of height
one. Then $\operatorname{trdeg} _k K(B/\mathfrak{p} ) = \operatorname{trdeg} _k K(B) - 1$.

This is the heart of [the dimension formula](dim-formula-catenary.md). Once it
is available the general case follows by induction along a maximal chain below
$\mathfrak{p}$, each step of which is a height-one prime in the quotient by the one below.

## The argument

Take a Noether normalisation $k[y_{1},\ldots ,y_d] \subseteq B$, so $B$ is integral over a
polynomial ring and $d = \operatorname{trdeg} _k K(B)$. Let $\mathfrak{q} = \mathfrak{p} \cap k[y]$.

- $\operatorname{ht}\mathfrak q=\operatorname{ht}\mathfrak p=1$, by
  [the height comparison](height-comap-integral.md) together with the fact that the fibres of
  an integral extension are zero-dimensional.
- A height-one prime of a UFD is principal, so $\mathfrak{q} = (f)$ with $f$ irreducible,
  and $k[y]/\mathfrak{q}$ has transcendence degree $d - 1$ by
  [the hypersurface computation](polynomial-hypersurface-trdeg.md).
- $B/\mathfrak{p}$ is integral over $k[y]/\mathfrak{q}$, so it has the same transcendence degree.

## Depends on

- [Height is preserved by contraction along an integral extension](height-comap-integral.md)
- [A hypersurface in affine space drops the transcendence degree by one](polynomial-hypersurface-trdeg.md)
- [Dimension of a finitely generated domain](dim-fg-domain.md)

## Proof depends on

- [Krull dimension is invariant under integral extensions](dimension-integral-extension.md)

## Sources

- [Hartshorne I.1, Theorem 1.8A (p. 6)](../../sources/hartshorne.md#i1)
