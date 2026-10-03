---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Grauert's constant-cohomology theorem

Let `f : X -> Y` be a projective morphism of Noetherian schemes, with `Y`
integral, and let `F` be a coherent `O_X`-module flat over `Y`. Fix `i`. If

`y |-> dim_k(y) H^i(X_y,F_y)`

is constant, then `R^i f_* F` is locally free and the natural residue-field
base-change map

`(R^i f_* F) tensor k(y) -> H^i(X_y,F_y)`

is an isomorphism for every `y : Y`.

## Depends on

- [Upper semicontinuity of fibre cohomology](../foundations/fiber-cohomology-upper-semicontinuous.md)
- [A finite-free complex computes projective cohomology](../finite-free-complex/projective-cohomology-finite-free-model.md)
- [Coherence of projective higher direct images](../../higher-direct-images/projective-higher-direct-images-coherent.md)
- [The higher-direct-image base-change map](../../flat-families/families-hilbert/higher-direct-image-base-change-map.md)

## Proof depends on

- Constant dimensions force the relevant differential ranks in the
  finite-free model to be locally constant; kernels, images, and cohomology
  are then finite locally free and commute with residue fields.

## Sources

- [Hartshorne III.12, Corollary 12.9, pp.288–289](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
- [EGA III, §7.7 and Stacks Project, tag 0BDN](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
