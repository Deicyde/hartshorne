---
article_id: af_9689cb7a25365808cbe4da45
declaration: isomorphism
origin: background
source_units: [appendix-b-sections-1-2]
not_ready: true
---

# Coherent analytification is analytic scalar extension

For every coherent algebraic sheaf `F` on `X`, there is a natural isomorphism

`F^h ~= phi^*F`

of coherent analytic sheaves, where pullback uses
`phi^(-1)O_X->O_(X^h)`.

This node is not ready pending exactness/coherence of analytic extension of
scalars and independence from a finite free presentation.

## Depends on

- [Analytification of a coherent algebraic sheaf](coherent-sheaf-analytification.md)
- [The analytification locally ringed-space morphism](analytification-locally-ringed-space-map.md)
- [Inverse image of a sheaf](../../schemes/sheaf-functors/inverse-image.md)
- [Tensor products of module sheaves](../../schemes/modules-and-quasicoherent/module-tensor-product.md)

## Proof depends on

- Form `phi^-1 F tensor_[phi^-1 O_X] O_(X^h)` using the analytic ring map;
  compare its local finite-presentation cokernel with `F^h`.

## Sources

- [Hartshorne Appendix B.1, `F^h ~= phi^*F`, p.439](../../../sources/hartshorne-appendix-b-1-2.md)
