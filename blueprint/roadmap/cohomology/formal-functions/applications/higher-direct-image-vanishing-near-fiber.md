---
article_id: af_ce246e58846a20eb743cbb26
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Higher direct-image vanishing near a fibre

Let `f : X -> Y` be a projective morphism of Noetherian schemes and let `F`
be a coherent `O_X`-module flat over `Y`. If, for some `i` and `y : Y`,

`H^i(X_y,F_y) = 0`,

then `R^i f_*F` is zero on an open neighbourhood of `y`.

This exercise is used in Hartshorne V.2.4 to deduce higher-direct-image
vanishing for line bundles on the fibres of a ruled surface.

## Depends on

- [Infinitesimal fibres](../core/infinitesimal-fibers.md)
- [The theorem on formal functions](../core/theorem-on-formal-functions.md)
- [Faithfulness of maximal-adic completion on finite modules](../core/maximal-adic-completion-faithful-finite.md)
- [A module sheaf flat over a base](../../flat-families/flatness/module-sheaf-flat-over-base.md)
- [Coherence of projective higher direct images](../../higher-direct-images/projective-higher-direct-images-coherent.md)

## Proof depends on

- Flatness filters each infinitesimal restriction `F_n` with successive
  quotients obtained from `F_y` by tensoring with
  `m_y^j/m_y^(j+1)`; induction gives `H^i(X_n,F_n)=0` for every `n`.
- Formal functions makes the completed stalk of `R^i f_*F` zero. Faithful
  completion kills the finite stalk, and coherence spreads this vanishing to
  a neighbourhood of `y`.

## Sources

- [Hartshorne III.11, Exercise 11.8, p.281](../../../../sources/hartshorne-iii-11-12.md#exercise-11-disposition-pp280281)
- [Hartshorne V.2, Lemma 2.4, p.371](../../../../sources/hartshorne-iii-11-12.md#exercise-11-disposition-pp280281)
