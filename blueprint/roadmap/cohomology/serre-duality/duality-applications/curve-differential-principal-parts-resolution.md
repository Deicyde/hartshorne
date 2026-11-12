---
article_id: af_feca80dc54e856ab0cad99fd
declaration: short exact sequence
origin: cited
lean: Hartshorne.differentialPrincipalPartsComplex Hartshorne.curveDifferential_principalPartsResolution
---

# The differential principal-parts resolution

For a complete nonsingular curve $X$ over an algebraically closed field $k$,
with function field $K$, let $\Omega _K$ denote the constant sheaf with value
$\Omega _{(K/k)}$. There is a flasque resolution

$0\longrightarrow\Omega_X\longrightarrow\Omega_K\longrightarrow\bigoplus_{P\in X_{\mathrm{closed}}}i_{P,*}\left(\Omega_{K/k}/\Omega_{X,P}\right)\longrightarrow0$.

Consequently $H^{1}(X,\Omega _X)$ is the cokernel of the rational-differential
principal-parts map. Unlike the special $\mathbb{P}^{1}$ resolution, no surjectivity on
global sections before taking this cokernel is asserted.

## Depends on

- [The constant sheaf](../../../schemes/sheaves/constant-sheaf.md)
- [Skyscraper and closed extension by zero](../../../schemes/sheaf-functors/closed-extension-by-zero.md)
- [The canonical sheaf](../../../schemes/differentials/canonical-bertini/canonical-sheaf.md)
- [The function field of a projective variety](../../../morphisms/projective-rings/projective-function-field.md)
- [Nonsingular curves over a field](../../../schemes/divisors/curve-divisors/nonsingular-curve.md)

## Proof depends on

- [Exactness is detected on stalks](../../../schemes/sheaves/stalkwise-exactness.md)
- [Flasque sheaves are acyclic](../../sheaf-cohomology/flasque-sheaf-acyclic.md)
- [The long exact sequence of sheaf cohomology](../../sheaf-cohomology/sheaf-cohomology-long-exact-sequence.md)
- [Acyclicity of $O$ on the projective line](../../sheaf-cohomology/projective-line-regular-sheaf-acyclic.md)
- Local freeness of $\Omega _X$ of rank one.
- The general curve principal-parts decomposition over closed points, proved
  stalkwise rather than imported from the special $\mathbb{P}^{1}$ case.

## Sources

- [Hartshorne III.7, differential principal-parts resolution, p.248](../../../../sources/hartshorne-iii-7.md#residues-on-curves-pp247248)
