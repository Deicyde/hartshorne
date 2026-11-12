---
article_id: af_1c551cbfa54d20b0877b5c0d
declaration: theorem
origin: cited
lean: Hartshorne.affineFormal_globalSections_shortExact
statement: formalized
proof: formalized
---

# Exactness of affine formal global sections

Let $\widehat{X}$ be affine formal and let

$0 \longrightarrow F' \longrightarrow F \longrightarrow F'' \longrightarrow 0$

be exact. If $F'$ is coherent, then the induced sequence

$0 \longrightarrow \Gamma (\widehat{X} ,F') \longrightarrow \Gamma (\widehat{X} ,F) \longrightarrow \Gamma (\widehat{X} ,F'') \longrightarrow 0$

is exact. Neither $F$ nor $F''$ is assumed coherent.

## Depends on

- [Coherent modules on a Noetherian formal scheme](coherent-formal-module.md)
- [Affine formal schemes](../formal-neighborhoods/formal-spectrum.md)

## Proof depends on

- [Exactness of affine global sections](../../modules-and-quasicoherent/affine-global-sections-exact.md)
- [Exactness of inverse limits under Mittag–Leffler](../inverse-systems/inverse-limit-exact-mittag-leffler.md)
- [Reconstruction from infinitesimal reductions](coherent-formal-module-reconstruction.md)
- [Limits of sheaves are computed pointwise](../../sheaves/limits-of-sheaves.md)
- Surjectivity of the reduction transition maps supplies Mittag–Leffler.

## Sources

- [Hartshorne II.9, Exercise 9.3(a,b) (pp.199–200)](../../../../sources/hartshorne-ii-9.md#adopted-exercises-and-deferred-material)
