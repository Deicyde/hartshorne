---
article_id: af_fe76125c48f7e7797010595e
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Cohomology and base change

Let `f : X -> Y` be projective between Noetherian schemes and let `F` be a
coherent `O_X`-module flat over `Y`. Fix `y : Y` and `i >= 0`. If

`phi^i(y) : (R^i f_* F) tensor k(y) -> H^i(X_y,F_y)`

is surjective, then it is an isomorphism, and after shrinking to a
neighbourhood `U` of `y`, every `phi^i(y')` for `y' : U` is an isomorphism.

If `i > 0` and `phi^i(y)` is surjective, the following are equivalent:

1. `phi^(i-1)(y)` is surjective;
2. `R^i f_* F` is locally free on a neighbourhood of `y`.

## Depends on

- [Residue-field surjectivity implies right exactness](residue-base-change-surjective-implies-right-exact.md)
- [The exactness loci are open](../finite-free-complex/cohomology-functor-exactness-locus-open.md)
- [The higher-direct-image base-change map](../../flat-families/families-hilbert/higher-direct-image-base-change-map.md)
- [Coherence of projective higher direct images](../../higher-direct-images/projective-higher-direct-images-coherent.md)

## Proof depends on

- Localize at `y`, translate residue-field surjectivity into right exactness,
  and use the finite-free complex criteria to spread the condition over an
  open neighbourhood.

## Sources

- [Hartshorne III.12, Theorem 12.11, pp.290–291](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
- [EGA III, §7.7](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
