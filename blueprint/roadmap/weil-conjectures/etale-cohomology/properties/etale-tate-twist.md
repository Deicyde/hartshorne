---
article_id: af_ff6d7af098cf0bc01e1bf79a
declaration: def
origin: bridged
---

# Étale Tate twists

For $\ell$ invertible on $X$, define

$\mathbb{Z}/\ell ^r\mathbb{Z}(1)=\mu _{(\ell ^r)}$

on the small étale site.  Tensor powers give positive twists, duals give
negative twists, and inverse limit followed by rationalization gives
$\mathbb Z_\ell(q)$ and $\mathbb Q_\ell(q)$ for every integer $q$.

Here the negative twists are the tensor powers of the dual
$\mathbb{Z}/\ell ^r\mathbb{Z}(-1)=\mathcal{H}om(\mu _{(\ell ^r)},\mathbb{Z}/\ell ^r\mathbb{Z})$,
so that $\mathbb{Z}/\ell ^r\mathbb{Z}(-q)=\mathbb{Z}/\ell ^r\mathbb{Z}(-1)^{\otimes q}$ for $q\ge 1$.
For each $q$, $\mathbb Z_\ell(q)$ is the inverse system
$(\mathbb{Z}/\ell ^r\mathbb{Z}(q))_r$, where $\mathbb{Z}/\ell ^r\mathbb{Z}(0)=\mathbb{Z}/\ell ^r\mathbb{Z}$.
For $r\le s$ its transition maps are the reductions $\mathbb{Z}/\ell ^s\mathbb{Z}\to\mathbb{Z}/\ell ^r\mathbb{Z}$
for $q=0$; the $q$-th tensor powers of $\mu _{(\ell ^s)}\to\mu _{(\ell ^r)}$, $\zeta\mapsto\zeta^{\ell^{s-r}}$,
for $q>0$; and for $q<0$ the $(-q)$-th tensor powers of the map
$\mathbb{Z}/\ell ^s\mathbb{Z}(-1)\to\mathbb{Z}/\ell ^r\mathbb{Z}(-1)$ sending $\tau$ to the unique $\tau'$
with $\ell^{s-r}\tau'=\tau|_{\mu _{(\ell ^r)}}$. Then
$H^i(X,\mathbb Z_\ell(q))=\varprojlim_r H^i_{\mathrm{et}}(X,\mathbb{Z}/\ell ^r\mathbb{Z}(q))$, and

$H^i(X,\mathbb Q_\ell(q))=H^i(X,\mathbb Z_\ell(q))\otimes_{\mathbb Z_\ell}\mathbb Q_\ell$.

Twists are retained explicitly even though Hartshorne suppresses them.  They
control trace normalization and Frobenius eigenvalues.

## Depends on

- [Constant torsion sheaves](../foundations/constant-torsion-etale-sheaf.md)
- [The classical inverse system](../foundations/classical-ell-adic-inverse-system.md)
- [The sheaf of roots of unity](../foundations/etale-roots-of-unity-sheaf.md)
- [Tensor products of abelian sheaves](../foundations/site-sheaf-tensor-product.md)
- [The internal Hom of abelian étale sheaves](../foundations/etale-sheaf-hom.md)
- [Rational ℓ-adic cohomology](../foundations/rational-ell-adic-cohomology.md)
- [The ℓ-adic integers and coefficient field](../foundations/ell-adic-integers-and-field.md)

## Sources

- [Hartshorne Appendix C §3, suppressed twist in properties 3.4 and 3.8, pp.453–454](../../../../sources/hartshorne-appendix-c-3.md#properties-31-through-35-printed-p453)
- SGA 4–5, Tate twists.
