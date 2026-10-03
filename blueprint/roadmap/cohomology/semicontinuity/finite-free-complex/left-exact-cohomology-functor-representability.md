---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Left exact cohomology functors are finitely represented

Let `L` be the finite-free model and put

`W^i = coker(L^(i-1) -> L^i)`.

For a fixed `i`, the following are equivalent:

1. `T^i` is left exact;
2. `W^i` is a projective `A`-module;
3. there is a finitely generated `A`-module `Q` and a natural isomorphism
   `T^i(M) ~= Hom_A(Q,M)` for every `A`-module `M`.

The representing module `Q` is unique up to the canonical isomorphism induced
by the two representing natural isomorphisms.

## Depends on

- [A finite-free model for projective cohomology](projective-cohomology-finite-free-model.md)

## Proof depends on

- The exact sequence `0 -> T^i(M) -> W^i tensor M -> L^(i+1) tensor M`.
- A finitely generated flat module is projective, and duality for finite
  projective modules identifies the displayed kernel with `Hom_A(Q,M)`.

## Sources

- [Hartshorne III.12, Proposition 12.4 and Remark 12.4.1, pp.284–286](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
