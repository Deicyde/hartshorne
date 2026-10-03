---
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Cohomology after tensor is a delta functor

Let `A` be Noetherian, `Y = Spec A`, `f : X -> Y` projective, and `F` a
coherent `O_X`-module flat over `Y`. For an `A`-module `M`, set

`T^i(M) = H^i(X, F tensor_A M)`.

Here `M` is first associated to a quasicoherent module on `Y`, pulled back to
`X`, and tensored with `F`. Each `T^i` is additive and covariant, every short
exact sequence of `A`-modules gives the natural long exact cohomology
sequence, and the collection `(T^i)_(i >= 0)` is a covariant delta functor.
In particular, every `T^i` is exact in the middle.

## Depends on

- [A module sheaf flat over a base](../../flat-families/flatness/module-sheaf-flat-over-base.md)
- [Tensor products of module sheaves](../../../schemes/modules-and-quasicoherent/module-tensor-product.md)
- [The affine quasicoherent equivalence](../../../schemes/modules-and-quasicoherent/affine-quasicoherent-equivalence.md)
- [The long exact sequence of right-derived functors](../../derived-functors/right-derived-long-exact-sequence.md)

## Proof depends on

- Flatness of `F` over `Y` makes tensoring the associated short exact sequence
  of module sheaves exact.

## Sources

- [Hartshorne III.12, Proposition 12.1, p.282](../../../../sources/hartshorne-iii-11-12.md#cohomology-after-tensor-and-finite-free-models-pp281287)
