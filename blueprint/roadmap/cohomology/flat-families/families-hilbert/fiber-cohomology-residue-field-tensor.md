---
article_id: af_2433bcfab3883a7e0a8e38b4
declaration: isomorphism
origin: cited
source_units: [chapter-iii-sections-8-9]
---

# Fibre cohomology as residue-field tensor cohomology

Let `f : X -> Y` be a separated finite-type morphism of Noetherian schemes,
with `Y=Spec A`, and let `F` be quasicoherent. For every point `y : Y` and
every `i`, there is a natural isomorphism

`H^i(X_y,F_y) ≅ H^i(X,F tensor_{O_Y} k(y))`.

On the right, regard `k(y)` as an `A`-module, take its associated
quasicoherent module on `Y`, pull that module sheaf back along `f`, and tensor
it with `F` on `X`. It is not an unrelated constant sheaf on `X`.

## Depends on

- [The fibre of a morphism](../../../schemes/fiber-products/scheme-fiber.md)
- [Tensor products of module sheaves](../../../schemes/modules-and-quasicoherent/module-tensor-product.md)
- [The affine quasicoherent equivalence](../../../schemes/modules-and-quasicoherent/affine-quasicoherent-equivalence.md)

## Proof depends on

- Reduction to the reduced closure of `y`, followed by flat base change to
  its generic point.
- [Flat base change for higher direct images](flat-base-change-higher-direct-images.md).

## Sources

- [Hartshorne III.9, Corollary 9.4, pp.255–256](../../../../sources/hartshorne-iii-9.md#cohomology-and-flat-base-change-pp255256)
