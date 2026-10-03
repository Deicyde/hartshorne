---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Right exactness and the cohomology-tensor comparison

For every `A`-module `M`, functoriality gives a natural map

`phi_M : T^i(A) tensor_A M -> T^i(M)`.

For a fixed `i`, the following are equivalent:

1. `T^i` is right exact;
2. `phi_M` is an isomorphism for every `M`;
3. `phi_M` is surjective for every `M`.

## Depends on

- [Cohomology after tensor is a delta functor](cohomology-tensor-delta-functors.md)
- [A finite-free model for projective cohomology](projective-cohomology-finite-free-model.md)
- [Cohomology commutes with filtered colimits](../../sheaf-cohomology/cohomology-filtered-colimit.md)

## Proof depends on

- Finite free presentations prove the isomorphism for finitely generated
  modules under right exactness; direct limits extend it to every module.
- Exactness in the middle of `T^i` turns surjectivity of every `phi_M` into
  right exactness.

## Sources

- [Hartshorne III.12, Proposition 12.5, pp.286–287](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
