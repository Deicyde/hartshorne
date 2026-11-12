---
article_id: af_fd3f8843d61d7ea77d575edd
declaration: theorem
origin: cited
lean: Hartshorne.QuasicoherentIdealSubsheaf.isIso_powQuotientToModuleCompletionObj Hartshorne.QuasicoherentIdealSubsheaf.powQuotientToModuleCompletionObj Hartshorne.QuasicoherentIdealSubsheaf.powQuotientπ_powQuotientToModuleCompletionObj
statement: formalized
proof: formalized
---

# Quotients of completed coherent modules

Let $X$ be Noetherian, let $I$ define a closed subscheme, let $J$ be its
completed ideal, and let $F$ be coherent. For every nonnegative integer $n$, the canonical
map induces an isomorphism

$\widehat{F} / J^{n+1} \widehat{F} \cong F / I^{n+1} F$

on the common closed support.
The isomorphism holds more generally for $X$ locally Noetherian and $F$ quasi-coherent; the Noetherian and coherence hypotheses are kept because they are Hartshorne's setting.

## Depends on

- [Completion of a coherent module](completed-coherent-module.md)
- [Coherent modules on a Noetherian formal scheme](coherent-formal-module.md)
- [Product of an ideal sheaf with a submodule sheaf](../../coherent-sheaves/ideal-power-product.md)

## Proof depends on

- [Thickenings of an affine formal scheme](../formal-neighborhoods/affine-formal-thickenings.md)
- [Reconstruction from infinitesimal reductions](coherent-formal-module-reconstruction.md)
- Locality on a finite affine cover.

## Sources

- [Hartshorne II.9, Corollary 9.8 (p.198)](../../../../sources/hartshorne-ii-9.md#coherent-modules-on-formal-schemes)
