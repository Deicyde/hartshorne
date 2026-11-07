# Tensor-dual compatibility for sheaf Ext

## Ringed-space generalization plan

III.6 works on a ringed space, so the Lean for Proposition 6.7 (sheaf Ext) is general.
Setting: `{X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}`, modules `SheafOfModules.{u} (ringCatSheafOf R)`, new general declarations in namespace `Hartshorne.Ringed` under `src/Hartshorne/RingedSpace/`. Schemes are the case `R := X.sheaf`, for which `SheafOfModules (ringCatSheafOf X.sheaf)` is definitionally `X.Modules`. It uses the general dual `Ringed.moduleSheafDual`, the hypothesis
`Ringed.IsFiniteLocallyFree L`, sheaf Ext built on the general left-exact functor
`Ringed.moduleSheafHomFunctor` (module-sheaf-hom-left-exact, then sheaf-ext), and the general
Lemma 6.6 `Ringed.moduleSheafTensor_injective` (stage 4). It becomes ready after stage 4, once
sheaf-ext and derived-functor-universality are formalized.

The full staged plan (setting, route, all stages, claim sets) is in the implementation note of the Modules and quasi-coherent sheaves container (`af_cef7a5b34bf9a0c78dc51155`).
