---
article_id: af_e109ddc0a4a353d0a283e020
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Fibrewise-isomorphic line bundles descend from the base

Let `f : X -> Y` be a flat projective morphism of finite-type schemes over an
algebraically closed field, where `Y` is integral and every fibre is integral.
If invertible sheaves `L` and `M` on `X` have isomorphic restrictions on the
scheme-theoretic fibre `X_y` for every `y : Y`, then there is an invertible
sheaf `N` on `Y` and an isomorphism

`L ~= M tensor f^* N`.

## Depends on

- [Cohomology and base change](../theorems/cohomology-and-base-change.md)
- [Grauert's constant-cohomology theorem](../theorems/grauert-constant-cohomology.md)
- [The group of invertible sheaves](../../../schemes/divisors/cartier-picard/invertible-sheaf-group.md)
- [Module push-pull adjunction](../../../schemes/modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- Apply degree-zero base change to `L tensor M^vee`; its pushforward is an
  invertible sheaf on `Y`, and the adjunction evaluation is an isomorphism on
  every fibre and hence globally.

## Sources

- [Hartshorne III, Exercise 12.4, p.291](../../../../sources/hartshorne-iii-11-12.md#exercise-12-disposition-pp291292)
