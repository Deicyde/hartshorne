---
article_id: af_be595eb6efbe593de0abb2cf
declaration: def
origin: cited
source_units: [chapter-ii-section-9]
---

# Completion of a coherent module

Let `X` be Noetherian, let `Y ↪ X` have module ideal sheaf `I`, and let `F`
be a coherent `O_X`-module. Define its completion along `Y` by

`Fhat = lim_n (F / I^(n+1) F)|_|Y|`.

Construct the natural `O_(Xhat_Y)`-module structure. Powers and quotients are
taken on the module ideal sheaf obtained from the existing
`IdealSheafData` bridge.

## Depends on

- [Formal completion as a locally ringed space](../formal-neighborhoods/formal-completion.md)
- [Sheaves of modules](../../modules-and-quasicoherent/sheaves-of-modules.md)
- [Module ideal sheaves and ideal data](../../coherent-sheaves/module-ideal-sheaf-data.md)

## Proof depends on

- Limits of sheaves of modules and compatibility of scalar actions with the
  quotient transition maps.
- [Coherent affine-local criterion](../../modules-and-quasicoherent/coherent-affine-local-criterion.md)

## Sources

- [Hartshorne II.9, completion of a coherent sheaf (p.194)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
