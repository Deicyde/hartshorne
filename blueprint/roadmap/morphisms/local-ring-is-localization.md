---
article_id: af_ee8518fd16a5e78a6cd4a378
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.localizationEquivLocalRing
---

# The local ring is a localisation

For an affine variety $Y$ and a point $P\in Y$,

$$\mathcal O_{P,Y}\cong A(Y)_{\mathfrak m_P},\qquad
\dim\mathcal O_{P,Y}=\operatorname{ht}\mathfrak m_P.$$

This is the localization clause of Hartshorne's Theorem I.3.2(c).
Polynomial functions not vanishing at $P$ have invertible germs, so the
coordinate-ring map factors through the localization. Every germ is a
quotient $g/h$ with $h(P)\ne0$, proving surjectivity. The identity principle
proves injectivity. The dimension of a localization at a prime is the
height of that prime.

[The remaining dimension assertion](affine-variety-rings.md) uses
[the dimension formula](../affine-varieties/dim-formula-catenary.md)
to identify $\operatorname{ht}\mathfrak m_P$ with $\dim Y$.

## Depends on

- [The local ring at a point](local-ring.md)
- [The local ring is local](local-ring-is-local.md)
- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(c) (p. 17)](../../sources/hartshorne.md#i3)
