---
article_id: af_01b34428bd087a4d13d151be
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.height_maximalIdealAt_eq Hartshorne.ringKrullDim_localRingAt_eq_dim
---

# The local ring and function field of an affine variety

Let $Y\subseteq\mathbb A^n$ be an affine variety and let $P\in Y$.
Then

- $\mathcal O_{P,Y}\cong A(Y)_{\mathfrak m_P}$ and
  $\dim\mathcal O_{P,Y}=\dim Y$;
- $K(Y)$ is the fraction field of $A(Y)$ and has transcendence degree
  $\dim Y$ over $k$.

These are Hartshorne's Theorem I.3.2(c) and (d). A germ at $P$ has the
form $g/h$ with $h(P)\ne0$, which identifies the local ring with the
localization at $\mathfrak m_P$. Its dimension is
$\operatorname{ht}\mathfrak m_P$, and the dimension formula identifies
this height with $\dim Y$. The function-field statement follows from
the fraction-field construction and the dimension theorem for finitely
generated domains.

The other two clauses are [global regular functions and the coordinate ring](global-regular-eq-coordinate-ring.md) and
[points and maximal ideals](points-eq-maximal-ideals.md).

## Depends on

- [The local ring at a point](local-ring.md)
- [The local ring is local](local-ring-is-local.md)
- [The function field](function-field.md)
- [The underlying maps into germs and rational functions are injective](function-field-injections.md)
- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [The local ring is a localisation](local-ring-is-localization.md)
- [The function field is the fraction field](function-field-is-fraction-field.md)

## Proof depends on

- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](../affine-varieties/dim-formula-catenary.md)

## Sources

- [Hartshorne I.3, Theorem 3.2 (p. 17)](../../sources/hartshorne.md#i3)
