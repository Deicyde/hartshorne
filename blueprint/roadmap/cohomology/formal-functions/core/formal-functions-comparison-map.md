---
article_id: af_702716c82479811e1a71b787
declaration: natural transformation
origin: cited
source_units: [chapter-iii-sections-11-12]
not_ready: true
---

# The formal-functions comparison map

For a projective morphism `f : X -> Y` of Noetherian schemes, a coherent
`O_X`-module `F`, a point `y : Y`, and `i : Nat`, construct the natural map

`completion_(m_y) ((R^i f_* F)_y) -> lim_n H^i(X_n,F_n)`.

At stage `n`, the map is the residue-thickening base-change comparison

`(R^i f_*F)_y tensor O_(Y,y)/m_y^(n+1) -> H^i(X_n,F_n)`.

Prove compatibility with transition maps, functoriality in `F`, and agreement
in degree zero with restriction of sections. This leaf constructs the map and
makes no isomorphism claim.

## Depends on

- [Infinitesimal fibres](infinitesimal-fibers.md)
- [The higher-direct-image base-change map](../../flat-families/families-hilbert/higher-direct-image-base-change-map.md)
- [Higher direct images over an affine target](../../higher-direct-images/affine-target-higher-direct-images.md)
- [Adic completion of rings and modules](../../../schemes/formal-schemes/adic-completion/adic-completion.md)
- [Inverse systems and the Mittag–Leffler condition](../../../schemes/formal-schemes/inverse-systems/inverse-system-mittag-leffler.md)

## Proof depends on

- Identification of the pulled-back higher direct image on each one-point
  affine thickening with its module of global sections.
- Finite-module completion as the inverse limit of maximal-ideal quotients.

The existing higher-direct-image base-change-map node is not ready and pinned
Mathlib has no replacement module-sheaf natural transformation. That missing
representation determines this leaf's `not_ready` status.

## Sources

- [Hartshorne III.11, construction preceding Theorem 11.1, pp.276–277](../../../../sources/hartshorne-iii-11-12.md#infinitesimal-fibres-and-formal-functions-pp276279)
- [Stacks Project, theorem on formal functions, tag 02OC](../../../../sources/hartshorne-iii-11-12.md#infinitesimal-fibres-and-formal-functions-pp276279)
