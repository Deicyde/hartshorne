---
article_id: af_eb929e5a457734c167168974
declaration: def
origin: cited
lean: Hartshorne.IsCoherentFormalModule Hartshorne.IsCoherentFormalModule.of_iso Hartshorne.IsCoherentFormalModule.iso_iff Hartshorne.structureModuleRestrict Hartshorne.structureModulePushforward Hartshorne.structureRingCatSheafHom Hartshorne.structureRingCatSheaf
statement: formalized
proof: formalized
---

# Coherent modules on a Noetherian formal scheme

Let $\widehat{X}$ be a Noetherian formal scheme. Define an $\mathcal{O}_{\widehat{X}}$-module $F$ to be
coherent when there is a finite open cover $\{U_i\}$ of $\widehat{X}$ with $U_i \cong \widehat{X_i}$, the
completion of a Noetherian scheme $X_i$ along a closed subscheme, and for each $i$ a
coherent $\mathcal{O}_{X_i}$-module $F_i$ with $F|_{U_i} \cong \widehat{F_i}$. The schemes $X_i$
need not be affine.

## Depends on

- [Noetherian formal schemes](../formal-neighborhoods/noetherian-formal-scheme.md)
- [Sheaves of modules](../../modules-and-quasicoherent/sheaves-of-modules.md)
- [Completion of a coherent module](completed-coherent-module.md)

## Proof depends on

- Independence of the chosen finite formal-affine refinement.

## Sources

- [Hartshorne II.9, definition of coherent formal modules (p.194)](../../../../sources/hartshorne-ii-9.md#formal-completions-and-formal-schemes)
