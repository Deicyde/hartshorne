---
article_id: af_caaa3e08a63e0c689b006588
declaration: def
origin: cited
lean: Hartshorne.tildePullbackIsoModuleCompletion Hartshorne.isIso_tildePullbackToModuleCompletion Hartshorne.tildePullbackToModuleCompletion Hartshorne.QuasicoherentIdealSubsheaf.pullbackToModuleCompletion
statement: formalized
proof: formalized
---

# Affine completed modules and ordinary tensor product

Let $A$ be Noetherian, $I$ an ideal, $M$ a finite $A$-module, and
$\widehat{X} = \operatorname{Spf} _I(A)$. The completed sheaf associated to $M$ is canonically
isomorphic to

$\left.\widetilde{M}\right|_{V(I)}\otimes_{\left.\mathcal{O}_{\operatorname{Spec}A}\right|_{V(I)}}\mathcal{O}_{\widehat{X}}$.

This is the ordinary tensor product of sheaves of modules. No completed tensor product is
involved.

## Depends on

- [Completion of a coherent module](completed-coherent-module.md)
- [Coherent modules on a Noetherian formal scheme](coherent-formal-module.md)
- [Affine formal schemes](../formal-neighborhoods/formal-spectrum.md)
- [Tensor products of module sheaves](../../modules-and-quasicoherent/module-tensor-product.md)
- [Pushforward, pullback, and their adjunction](../../modules-and-quasicoherent/module-push-pull-adjunction.md)

## Proof depends on

- [Finite-module completion as tensor product](../adic-completion/finite-module-completion-tensor.md)
- [Affine sections of a formal completion](../formal-neighborhoods/formal-completion-affine-sections.md)
- [Exactness of affine module completion](affine-formal-module-exact.md)
- Comparison on an affine basis followed by sheaf isomorphism extensionality.

## Sources

- [Hartshorne II.9, Proposition 9.4(b) (pp.195–196)](../../../../sources/hartshorne-ii-9.md#affine-formal-schemes-and-ideals-of-definition)
