# Completion of a coherent module

## Lean

Module `Hartshorne.Scheme.FormalCompletionModule`, namespace `Hartshorne.QuasicoherentIdealSubsheaf`.

- `formalCompletionRingCatSheaf I`: `formalCompletionSheaf I` composed with `forget₂ CommRingCat RingCat`,
  the ring sheaf over which the completed module is a `SheafOfModules`.
- `formalCompletionRingCatSheafπ I n`: the projection to `𝒪_{Y_(n+1)}`, transported to `|Y|` along the
  open-embedding functor of `infinitesimalNeighborhoodFromOne n` (continuity instance
  `isContinuous_functor_infinitesimalNeighborhoodFromOne`).
- `moduleCompletionQuotient I F n`: `cokernel (powSmulι I F n)`, with `powSmulι` the inclusion of
  `powSmul (quasicoherentIdealSubsheafEquiv I) (n + 1) ⊤` (the ideal-power-product sheaf `I^(n+1) F`).
- `moduleCompletionNeighborhood I F n`: `Scheme.Modules.pullback (infinitesimalNeighborhoodι (n + 1))` of the
  quotient. Mathematically `ι^*(F/I^(n+1)F) = ι^{-1}(F/I^(n+1)F)` because the quotient is killed by
  `I^(n+1)`; this identification is not proved in Lean (see remaining goals).
- `moduleCompletionObj I F n`: `SheafOfModules.pushforward (formalCompletionRingCatSheafπ I n)` of it.
- `moduleCompletionMap I F n`: pushforward of `moduleCompletionNeighborhoodMap` (pullback of the quotient
  map, unit of `pullbackPushforwardAdjunction` along `infinitesimalNeighborhoodSucc n`, `pullbackComp`,
  `pullbackCongr`), followed by `Hartshorne.sheafOfModulesPushforwardCompRestrict`, a generic
  restriction map `pushforward φ₂ (pushforward ψ M) ⟶ pushforward φ₁ M` along `α : F₁ ⟶ F₂ ⋙ G`.
- `moduleCompletionDiagram`, `moduleCompletion` (the limit in `SheafOfModules`), `moduleCompletionπ`,
  `moduleCompletionπ_comp_moduleCompletionMap`, `isLimitModuleCompletionSections` (sections over each
  open are the limit of the sections).

No Noetherian or coherence hypothesis is used.

## Friction

- Stating an equality of ring-sheaf morphisms whose middle object is
  `F.sheafPushforwardContinuous.obj (G.sheafPushforwardContinuous.obj S)` against
  `(F ⋙ G).sheafPushforwardContinuous.obj S` makes the kernel time out on the concrete schemes `Y_n`
  (it unfolds the subscheme structure sheaf). Hence `SheafOfModules.pushforwardComp` /
  `pushforwardNatTrans` / `pushforwardCongr` were avoided in favour of the generic
  `sheafOfModulesPushforwardCompRestrict`, whose compatibility hypothesis is elementwise.
- `rw` fails on composites in `X.Modules` built from `ArtinReesKernelSheaf.toModules` ("not type-correct
  at implicit transparency", `TopCat.Sheaf` vs `Sheaf` mismatch); term-mode `trans`/`congrArg` works.
- `rfl` for `inclusion ≫ powSmulι = powSmulι` timed out in the kernel; `SheafOfModules.Hom.ext` with
  `PresheafOfModules.Submodule.homOfLE_ι` works.

## Remaining goals (not part of this statement)

- `F = 𝒪_X` recovers `𝒪_{X̂_Y}`: needs `ι^* (𝒪_X / I^(n+1)) ≅ 𝒪_{Y_(n+1)}` (pullback of the unit module
  and of a cokernel), compatible with the transition maps.
- Bridge `ι_* ι^* G ≅ G` for an `𝒪_X`-module `G` killed by `I^(n+1)` (the unit of the pullback-pushforward
  adjunction is an isomorphism), which identifies `moduleCompletionNeighborhood` with the restriction
  of `F / I^(n+1) F` to `|Y|` as a sheaf of abelian groups.
