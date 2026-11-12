---
article_id: af_db0c348bdcc039a837b2f8b9
declaration: def
origin: cited
lean: Hartshorne.QuasicoherentIdealSubsheaf.pullbackIsoModuleCompletion Hartshorne.QuasicoherentIdealSubsheaf.isIso_pullbackToModuleCompletion
statement: formalized
proof: formalized
---

# Completion and ordinary sheaf tensor product

Let $X$ be Noetherian, let $\widehat{X}$ be its completion along a closed subscheme,
and let $F$ be coherent. Construct the canonical isomorphism

$\widehat{F}\cong\left.F\right|_{|\widehat{X}|}\otimes_{\left.\mathcal{O}_X\right|_{|\widehat{X}|}}\mathcal{O}_{\widehat{X}}$.

The tensor product is the ordinary tensor product of module sheaves.
The isomorphism holds more generally for $X$ locally Noetherian; the Noetherian hypothesis is kept because it is Hartshorne's setting.

## Depends on

- [Completion of a coherent module](completed-coherent-module.md)
- [Coherent modules on a Noetherian formal scheme](coherent-formal-module.md)
- [Tensor products of module sheaves](../../modules-and-quasicoherent/module-tensor-product.md)

## Proof depends on

- [Affine completed modules and ordinary tensor product](affine-formal-module-tensor.md)
- Locality on a finite affine cover.

## Sources

- [Hartshorne II.9, Corollary 9.8 (p.198)](../../../../sources/hartshorne-ii-9.md#coherent-modules-on-formal-schemes)
