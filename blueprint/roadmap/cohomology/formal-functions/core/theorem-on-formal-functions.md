---
article_id: af_3eabc65b585d3e0d5f4560a5
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# The theorem on formal functions

Let `f : X -> Y` be a projective morphism of Noetherian schemes, let `F` be a
coherent `O_X`-module, let `y : Y`, and let `i : Nat`. The natural map is an
isomorphism

`completion_(m_y) ((R^i f_*F)_y) ~= lim_n H^i(X_n,F_n)`.

This is the projective theorem stated by Hartshorne. The proper generalization
in EGA and Stacks is recorded as external prior art, not substituted into the
main statement.

## Depends on

- [The formal-functions comparison map](formal-functions-comparison-map.md)
- [Formal functions for projective twists](formal-functions-projective-twist-case.md)
- [The Artin–Rees kernel system is pro-zero](artin-rees-pro-zero-kernel.md)
- [Finite twisted-free covers](../../../schemes/projective-sheaves/finite-twisted-free-cover.md)
- [Projective morphisms](../../../schemes/proper-and-projective/projective-morphism.md)
- [Finite pushforward preserves coherence](../../../schemes/modules-and-quasicoherent/finite-pushforward-coherent.md)
- [Closed pushforward preserves cohomology](../../sheaf-cohomology/closed-pushforward-cohomology.md)
- [Coherence of projective higher direct images](../../higher-direct-images/projective-higher-direct-images-coherent.md)
- [Flat base change for higher direct images](../../flat-families/families-hilbert/flat-base-change-higher-direct-images.md)
- [Exactness of finite-module completion](../../../schemes/formal-schemes/adic-completion/finite-module-completion-exact.md)
- [Exactness of inverse limits under Mittag–Leffler](../../../schemes/formal-schemes/inverse-systems/inverse-limit-exact-mittag-leffler.md)

## Proof depends on

- A finite relative-projective embedding and exactness of pushforward along
  the resulting closed immersion.
- Descending induction on cohomological degree and the subtle five lemma.
- Finite-length stage cohomology systems satisfy Mittag–Leffler.

## Sources

- [Hartshorne III.11, Theorem 11.1, pp.277–279](../../../../sources/hartshorne-iii-11-12.md#infinitesimal-fibres-and-formal-functions-pp276279)
- [EGA III §4 and Stacks Project tag 02OC](../../../../sources/hartshorne-iii-11-12.md#infinitesimal-fibres-and-formal-functions-pp276279)
