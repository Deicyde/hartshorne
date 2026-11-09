# Tensor-dual compatibility for sheaf Ext

## Ringed-space generalization plan

III.6 works on a ringed space, so the Lean for Proposition 6.7 (sheaf Ext) is general.
Setting: `{X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}`, modules `SheafOfModules.{u} (ringCatSheafOf R)`, new general declarations in namespace `Hartshorne.Ringed` under `src/Hartshorne/RingedSpace/`. Schemes are the case `R := X.sheaf`, for which `SheafOfModules (ringCatSheafOf X.sheaf)` is definitionally `X.Modules`. It uses the general dual `Ringed.moduleSheafDual`, the hypothesis
`Ringed.IsFiniteLocallyFree L`, sheaf Ext built on the general left-exact functor
`Ringed.moduleSheafHomFunctor` (module-sheaf-hom-left-exact, then sheaf-ext), and the general
Lemma 6.6 `Ringed.moduleSheafTensor_injective` (stage 4). It becomes ready after stage 4, once
sheaf-ext and derived-functor-universality are formalized.

## Second isomorphism (faithfulness item 3)

The article now states both sheaf-Ext isomorphisms of Proposition III.6.7:
`𝓔xt^i(F ⊗ L, G) ≅ 𝓔xt^i(F, L^∨ ⊗ G)` and `𝓔xt^i(F, L^∨ ⊗ G) ≅ 𝓔xt^i(F, G) ⊗ L^∨`.
No Lean exists for either yet. The Lean for the second isomorphism is still to be written: a
natural isomorphism, for each `i`, between `Ringed` sheaf Ext of `(F, moduleSheafTensor
(moduleSheafDual L) G)` and `moduleSheafTensor (moduleSheafDual L) (sheaf Ext (F, G))` (order of
the tensor factors up to the symmetric-monoidal braiding), natural in `F` and `G`. Route: both
sides are universal δ-functors in `G` (tensoring by the finite locally free `L^∨` is exact, and
the right side vanishes on injective `G` in positive degree), agreeing in degree zero by
the natural map `𝓗om(F, G) ⊗ L^∨ → 𝓗om(F, L^∨ ⊗ G)`, an isomorphism because it is one on an
open cover trivializing `L` (the same local check as `moduleSheafDualTensorMap_isIso`). Like the first isomorphism, it becomes ready once sheaf-ext and
derived-functor-universality are formalized.

The full staged plan (setting, route, all stages, claim sets) is in the implementation note of the Modules and quasi-coherent sheaves container (`af_cef7a5b34bf9a0c78dc51155`).
