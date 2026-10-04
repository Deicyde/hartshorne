---
article_id: af_765c0204b1db21f247c49009
declaration: def
origin: cited
source_units: [chapter-iii-sections-11-12]
---

# Infinitesimal fibres

Let `f : X -> Y` be a morphism of Noetherian schemes, let `F` be a coherent
`O_X`-module, and let `y : Y`. For `n : Nat`, define

`X_n = X times_Y Spec(O_(Y,y) / m_y^(n+1))`

and define `F_n` as the module pullback of `F` to `X_n`. Construct the
transition morphisms `X_(n+1) -> X_n`, their compatible maps of module
sheaves, and the natural morphisms `X_n -> X`.

Prove that `X_0` is canonically the scheme-theoretic fibre `X_y` and every
`X_n` has the same underlying topological space as `X_y`. These are fibre
thickenings over the local scheme at `y`; they are not silently identified
with powers of a globally defined closed-subscheme ideal when `y` is not
closed.

## Depends on

- [The fibre of a morphism](../../../schemes/fiber-products/scheme-fiber.md)
- [Base extension](../../../schemes/fiber-products/base-extension.md)
- [Infinitesimal neighbourhoods](../../../schemes/formal-schemes/formal-neighborhoods/infinitesimal-neighborhoods.md)
- [Pullback preserves quasi-coherence](../../../schemes/modules-and-quasicoherent/pullback-quasicoherent.md)

## Proof depends on

- The spectrum of `O_(Y,y)/m_y^(n+1)` has one point and reduction modulo the
  maximal ideal gives `Spec k(y)`.
- Pullback pasting for the local morphism `Spec O_(Y,y) -> Y`.

## Sources

- [Hartshorne III.11, infinitesimal-fibre construction, pp.276–277](../../../../sources/hartshorne-iii-11-12.md#infinitesimal-fibres-and-formal-functions-pp276279)
