---
article_id: af_4d439f866589bc1e692ad888
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isRegular_iff_relativeDifferentials_isLocallyFreeOfRank Hartshorne.isIntegral_of_isRegular
---

# Differentials characterize nonsingular varieties

Let $X$ be an irreducible separated scheme of finite type over an
algebraically closed field $k$, and let $n = \dim X$. Then $\Omega_{X/k}$ is
locally free of constant rank $n$ if and only if $X$ is a nonsingular variety
over $k$.

This is a statement about the differential sheaf.  Its fiber at a closed
point is compared with the cotangent space before applying the regular-local
criterion.

## Depends on

- [Quasi-coherence and coherence of differentials](relative-differentials-quasicoherent.md)
- [Regular points and nonsingular schemes](regular-points-and-nonsingular-schemes.md)

## Proof depends on

- [The regular-local differential criterion](../kaehler-differentials/regular-local-differential-criterion.md)
- [Localizations of regular local rings](../kaehler-differentials/regular-localization.md)
- [Dimension at a closed point](../../subschemes-and-dimension/dimension-at-closed-point.md)
- [Fibres of the differential sheaf on an affine chart](relative-differentials-affine-fibre.md)
- [The free locus of a coherent sheaf](../../coherent-sheaves/coherent-free-locus.md)
- [Constant fibre dimension forces local freeness](../../coherent-sheaves/coherent-constant-fibre-rank-locally-free.md)
- [The reduced induced closed subscheme](../../subschemes-and-dimension/reduced-induced-closed-subscheme.md)
- Closed points are dense, and every nonclosed local ring is a localization of
  a local ring at a suitable closed point.

## Sources

- [Hartshorne II.8, Theorem 8.15, printed pp. 177–178](../../../../sources/hartshorne-ii-8.md)
