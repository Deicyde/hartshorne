---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Residue-field surjectivity implies right exactness

Let `A` be a Noetherian local ring with residue field `k`, let
`f : X -> Spec A` be projective, and let `F` be coherent and flat over `A`.
If the comparison map

`H^i(X,F) tensor_A k -> H^i(X_k,F_k)`

is surjective, then the functor

`M |-> H^i(X,F tensor_A M)`

is right exact on `A`-modules.

## Depends on

- [The theorem on formal functions](../../formal-functions/core/theorem-on-formal-functions.md)
- [Faithfulness of maximal-adic completion on finite modules](../../formal-functions/core/maximal-adic-completion-faithful-finite.md)
- [The tensor comparison and right exactness](../finite-free-complex/cohomology-tensor-comparison-right-exact.md)
- [Fibre cohomology as residue-field tensor cohomology](../../flat-families/families-hilbert/fiber-cohomology-residue-field-tensor.md)

## Proof depends on

- Lift surjectivity from the residue field to finite-length modules, then to
  all infinitesimal quotients; use formal functions and faithful exact
  completion to recover surjectivity over `A`.

## Sources

- [Hartshorne III.12, Proposition 12.10, pp.289–290](../../../../sources/hartshorne-iii-11-12.md#semicontinuity-grauert-and-base-change-pp287291)
