---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-6-7]
---

# Stalks of sheaf Ext

Let `X` be locally Noetherian, let `F` be coherent (hence locally finitely
presented), let `G` be any `O_X`-module, and let `x ∈ X`. For every `i ≥ 0`,
construct natural isomorphisms

`𝓔xt^i_X(F,G)_x ≅ Ext^i_{O_{X,x}}(F_x,G_x)`.

The local finite-presentation hypothesis on `F` is essential even in degree
zero. On an affine neighborhood of `x`, choose a possibly infinite free
resolution whose individual terms have finite rank; its stalk is a projective
resolution over `O_{X,x}`.

## Depends on

- [Sheaf Ext restricts to open subsets](sheaf-ext-restrict-open.md)
- [Locally free resolutions compute sheaf Ext](locally-free-resolution-sheaf-ext.md)

## Proof depends on

- [Restriction preserves stalks](../../../schemes/sheaf-functors/restriction-stalk.md)
- [Exactness is detected on stalks](../../../schemes/sheaves/stalkwise-exactness.md)
- Noetherianity keeps every successive syzygy finite, producing the required
  termwise finite-rank free resolution on an affine neighborhood.

## Sources

- [Hartshorne III.6, Proposition 6.8, printed pp.235–236](../../../../sources/hartshorne-iii-6.md#tensor-stalk-and-projective-comparison-printed-pp235236)
