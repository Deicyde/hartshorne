/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.NoetherianFormalScheme
import Hartshorne.Scheme.FormalCompletionModule
import Hartshorne.Scheme.CoherentAffineLocalCriterion

/-!
# Coherent modules on a Noetherian formal scheme

Hartshorne, *Algebraic Geometry*, II.9, definition of coherent modules on a Noetherian formal
scheme (p. 194).

Let `𝔛` be a Noetherian formal scheme, a locally ringed space with structure sheaf `𝒪_𝔛`. An
`𝒪_𝔛`-module `F` is *coherent* when there is a finite open cover `𝔛 = ⋃ Uᵢ` together with
isomorphisms of locally ringed spaces `Uᵢ ≅ X̂ᵢ` onto formal completions of Noetherian schemes
`Xᵢ` along closed subschemes, such that for each `i` the restriction `F|_{Uᵢ}` is isomorphic to
the completion `F̂ᵢ` of a coherent `𝒪_{Xᵢ}`-module `Fᵢ`, transported to `Uᵢ` along the chart.

As for Noetherian formal schemes, the ambient schemes `Xᵢ` need not be affine, the structure sheaf
is a plain sheaf of rings and `F` is a plain sheaf of modules; no topology is put on sections.

* `Hartshorne.structureRingCatSheaf X`: the structure sheaf of a locally ringed space `X`, as a
  sheaf of rings in `RingCat`, over which `𝒪_X`-modules are sheaves of modules.
* `Hartshorne.structureRingCatSheafHom f`: for a morphism `f : X ⟶ Y` of locally ringed spaces,
  the map `𝒪_Y ⟶ f_* 𝒪_X`.
* `Hartshorne.structureModulePushforward f`: the pushforward `f_*` of `𝒪_X`-modules along `f`,
  an `𝒪_Y`-module through `𝒪_Y ⟶ f_* 𝒪_X`.
* `Hartshorne.structureModuleRestrict X h`: the restriction `F|_U` of an `𝒪_X`-module to an open
  subspace `U` (given by an open embedding `h`), a module over the structure sheaf of
  `X.restrict h`.
* `Hartshorne.IsCoherentFormalModule F`: `F` is a coherent module on the Noetherian formal
  scheme.
* `Hartshorne.IsCoherentFormalModule.of_iso`: coherence is invariant under isomorphisms of
  modules.

The transport of the completion `F̂ᵢ`, a module over the structure sheaf of `X̂ᵢ`, to `Uᵢ` along a
chart `eᵢ : Uᵢ ≅ X̂ᵢ` is its pushforward along the inverse isomorphism `eᵢ⁻¹ : X̂ᵢ ⟶ Uᵢ`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Hartshorne

universe u

/-- The structure sheaf of a locally ringed space `X`, as a sheaf of rings in `RingCat`: the form
in which it carries sheaves of `𝒪_X`-modules. -/
abbrev structureRingCatSheaf (X : LocallyRingedSpace.{u}) :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- For a morphism `f : X ⟶ Y` of locally ringed spaces, the map of structure sheaves
`𝒪_Y ⟶ f_* 𝒪_X`, as sheaves of rings in `RingCat`. -/
def structureRingCatSheafHom {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    structureRingCatSheaf Y ⟶ ((Opens.map f.base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)).obj
        (structureRingCatSheaf X) where
  hom := Functor.whiskerRight f.c _

/-- The pushforward `f_*` of `𝒪_X`-modules along a morphism `f : X ⟶ Y` of locally ringed spaces:
its sections over an open `V` of `Y` are the sections over `f⁻¹ V`, with `𝒪_Y(V)` acting through
`𝒪_Y(V) ⟶ 𝒪_X(f⁻¹ V)`. -/
def structureModulePushforward {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules.{u} (structureRingCatSheaf X) ⥤ SheafOfModules.{u} (structureRingCatSheaf Y) :=
  SheafOfModules.pushforward.{u} (structureRingCatSheafHom f)

/-- The restriction `F|_U` of an `𝒪_X`-module to an open subspace `U` of a locally ringed space,
given by an open embedding `h : U ⟶ X`: its sections over an open `V` of `U` are the sections of
`F` over the image of `V`, a module over the structure sheaf of `X.restrict h`. -/
def structureModuleRestrict (X : LocallyRingedSpace.{u}) {U : TopCat.{u}} {f : U ⟶ X.carrier}
    (h : Topology.IsOpenEmbedding f) :
    SheafOfModules.{u} (structureRingCatSheaf X) ⥤
      SheafOfModules.{u} (structureRingCatSheaf (X.restrict h)) :=
  letI : h.functor.IsContinuous (Opens.grothendieckTopology (X.restrict h).carrier)
      (Opens.grothendieckTopology X.carrier) := h.functor_isContinuous
  SheafOfModules.pushforward.{u}
    (F := h.functor) (R := structureRingCatSheaf X) (𝟙 (structureRingCatSheaf (X.restrict h)))

/-- **Coherent modules on a Noetherian formal scheme** (Hartshorne II.9, p. 194): an
`𝒪_𝔛`-module `F` on a Noetherian formal scheme `𝔛` is coherent when there is a finite open cover
`𝔛 = ⋃ Uᵢ` with, for each `i`, a Noetherian scheme `Xᵢ`, a closed subscheme of `Xᵢ` (given by a
quasi-coherent ideal subsheaf `Iᵢ`), an isomorphism of locally ringed spaces `eᵢ : Uᵢ ≅ X̂ᵢ` onto
the formal completion of `Xᵢ` along it, and a coherent `𝒪_{Xᵢ}`-module `Fᵢ` such that `F|_{Uᵢ}`
is isomorphic, as a module over the structure sheaf of `Uᵢ`, to the completion `F̂ᵢ` transported
along `eᵢ`. The ambient schemes need not be affine. -/
def IsCoherentFormalModule {X : NoetherianFormalScheme.{u}}
    (F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (U : ι → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i, ∃ (Y : Scheme.{u}) (_ : IsNoetherian Y) (I : QuasicoherentIdealSubsheaf Y)
      (e : X.restrict (U i).isOpenEmbedding ≅ I.formalCompletion) (G : Y.Modules),
      IsCoherent G ∧
        Nonempty ((structureModuleRestrict X.toLocallyRingedSpace (U i).isOpenEmbedding).obj F ≅
          (structureModulePushforward e.inv).obj (I.moduleCompletion G))

/-- Coherence of a module on a Noetherian formal scheme is invariant under isomorphisms of
modules. -/
theorem IsCoherentFormalModule.of_iso {X : NoetherianFormalScheme.{u}}
    {F F' : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)} (φ : F ≅ F')
    (hF : IsCoherentFormalModule F) : IsCoherentFormalModule F' := by
  obtain ⟨ι, hι, U, hU, hchart⟩ := hF
  refine ⟨ι, hι, U, hU, fun i => ?_⟩
  obtain ⟨Y, hY, I, e, G, hG, ⟨ψ⟩⟩ := hchart i
  exact ⟨Y, hY, I, e, G, hG,
    ⟨((structureModuleRestrict X.toLocallyRingedSpace (U i).isOpenEmbedding).mapIso φ).symm ≪≫ ψ⟩⟩

/-- Coherence of a module on a Noetherian formal scheme is invariant under isomorphisms of
modules. -/
theorem IsCoherentFormalModule.iso_iff {X : NoetherianFormalScheme.{u}}
    {F F' : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)} (φ : F ≅ F') :
    IsCoherentFormalModule F ↔ IsCoherentFormalModule F' :=
  ⟨fun h => h.of_iso φ, fun h => h.of_iso φ.symm⟩

end Hartshorne
