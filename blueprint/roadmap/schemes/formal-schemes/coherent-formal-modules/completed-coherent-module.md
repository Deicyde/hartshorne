---
article_id: af_be595eb6efbe593de0abb2cf
declaration: def
origin: cited
lean: Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletion Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionDiagram Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionMap Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionObj Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionNeighborhood Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionQuotient Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionπ Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletionπ_comp_moduleCompletionMap Hartshorne.QuasicoherentIdealSubsheaf.isLimitModuleCompletionSections Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionRingCatSheaf
statement: formalized
proof: formalized
---

# Completion of a coherent module

Let $X$ be Noetherian, let $Y \hookrightarrow X$ have module ideal sheaf $I$, and let $F$
be a coherent $\mathcal{O}_X$-module. Define its completion along $Y$ by

$\widehat{F}=\varprojlim_n\left(F/I^{n+1}F\right)|_{|Y|}$.

The quotients and their transition maps give the completion its
natural module structure over the completed structure sheaf. Powers
are taken in the ideal sheaf of $Y$.
The construction uses neither that $X$ is Noetherian nor that $F$ is coherent; both hypotheses are kept because they are Hartshorne's setting.

## Depends on

- [Formal completion as a locally ringed space](../formal-neighborhoods/formal-completion.md)
- [Sheaves of modules](../../modules-and-quasicoherent/sheaves-of-modules.md)
- [Module ideal sheaves and ideal data](../../coherent-sheaves/module-ideal-sheaf-data.md)
- [Product of an ideal sheaf with a submodule sheaf](../../coherent-sheaves/ideal-power-product.md)

## Proof depends on

- Limits of sheaves of modules and compatibility of scalar actions with the
  quotient transition maps.
- [Coherent affine-local criterion](../../modules-and-quasicoherent/coherent-affine-local-criterion.md)

## Sources

- [Hartshorne II.9, completion of a coherent sheaf (p.194)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
