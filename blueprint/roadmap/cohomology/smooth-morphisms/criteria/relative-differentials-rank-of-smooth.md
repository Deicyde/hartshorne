---
declaration: theorem
origin: cited
source_units: [chapter-iii-section-10]
---

# Constant fibre dimension of relative differentials

Let `f : X -> Y` be a morphism of finite-type schemes over a field, with `X`
integral. Hartshorne's third smoothness clause,

`dim_k(x) (Omega[X/Y]_x tensor k(x)) = n` for every `x : X`,

is equivalent to `Omega[X/Y]` being locally free of constant rank `n`. No
smoothness assumption is made. As a corollary, for a morphism already known to
be smooth, relative dimension `n` gives a locally free differential sheaf of
rank `n`.

This is a statement about the scheme differential sheaf and the finite-module
criterion for local freeness; it is not definitionally the modern Mathlib
smoothness predicate.

## Depends on

- [The relative differential sheaf](../../../schemes/differentials/scheme-differentials/relative-differentials.md)
- [Locally free module sheaves](../../../schemes/modules-and-quasicoherent/locally-free-and-invertible.md)

## Proof depends on

- The finite-presentation criterion that a coherent module on an integral
  Noetherian scheme is locally free of rank `n` exactly when every fibre has
  dimension `n`.
- For the smooth corollary,
  `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` in
  pinned Mathlib.

## Sources

- [Hartshorne III.10, Example 10.0.2, p.268](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
- [Stacks Project, smooth morphisms, tag 01V4](../../../../sources/hartshorne-iii-10.md#smoothness-and-geometric-fibres-pp268270)
