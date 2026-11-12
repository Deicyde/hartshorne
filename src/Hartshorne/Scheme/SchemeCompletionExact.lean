/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AffineFormalModuleExact
import Hartshorne.Scheme.AffineGlobalSectionsExact
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.CoherentFormalModule
import Hartshorne.Scheme.AlgebraizableFormalScheme

/-!
# Exactness of completion along a closed subscheme

Hartshorne, *Algebraic Geometry*, II, Corollary 9.8 (p. 198): for a Noetherian scheme `X` and a
closed subscheme `Y` with ideal sheaf `I`, the functor `F ↦ F̂` from coherent `𝒪_X`-modules to
coherent `𝒪_{X̂_Y}`-modules is exact. Exactness is proved here among all `𝒪_{X̂_Y}`-modules.

Exactness of a complex of sheaves is local, and is checked here on the basis of `|Y|` formed by
the traces of the affine opens `U` of `X`. Over such a `U`, the sections of an exact sequence of
quasi-coherent modules form an exact sequence of modules over the Noetherian ring `Γ(U, 𝒪_X)`,
finite for coherent modules, and the affine computation of
`Hartshorne.Scheme.AffineFormalModuleExact` (completion of finite modules over a Noetherian ring
is exact) applies.

* `Hartshorne.modules_app_exact_of_isAffineOpen`: over an affine open `U`, the sections of an
  exact sequence `F' ⟶ F ⟶ F''` of quasi-coherent `𝒪_X`-modules form an exact sequence.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletion_exact`: the main result. On a locally
  Noetherian scheme, for an exact sequence `F' ⟶ F ⟶ F''` of `𝒪_X`-modules with `F'`
  quasi-coherent and `F`, `F''` coherent, the completions `F̂' ⟶ F̂ ⟶ F̂''` form an exact sequence
  of modules over the structure sheaf of `X̂_Y`.
* `Hartshorne.QuasicoherentIdealSubsheaf.moduleCompletion_shortExact`: the short exact form, for
  short exact sequences of coherent modules.
* `Hartshorne.QuasicoherentIdealSubsheaf.isCoherentFormalModule_moduleCompletion`: on a
  Noetherian scheme, the completion `F̂` of a coherent module is a coherent module on the
  Noetherian formal scheme `X̂_Y`, so the functor lands in coherent formal modules. The proof uses
  the one-chart cover of `X̂_Y` by itself, with `F` as the coherent module on the chart.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

/-- **Sections over an affine open are exact on quasi-coherent modules.** For an exact sequence
`F' ⟶ F ⟶ F''` of quasi-coherent `𝒪_X`-modules and an affine open `U ⊆ X`, the sequence of
sections `Γ(U, F') ⟶ Γ(U, F) ⟶ Γ(U, F'')` is exact. The kernel `K` of `F ⟶ F''` is
quasi-coherent, sections over `U` are left exact, and `Γ(U, F') ⟶ Γ(U, K)` is onto because the
kernel of the epimorphism `F' ⟶ K` is quasi-coherent and `U` is affine. -/
theorem modules_app_exact_of_isAffineOpen {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.Exact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (U : X.affineOpens) :
    Function.Exact (S.f.app U) (S.g.app U) := by
  have : S.cycles.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso S.cyclesIsoKernel.symm
      (isQuasicoherent_kernel S.g)
  have : (kernel S.toCycles).IsQuasicoherent := isQuasicoherent_kernel S.toCycles
  have : Epi S.toCycles := hS.epi_toCycles
  let T := ShortComplex.mk (kernel.ι S.toCycles) S.toCycles (kernel.condition _)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel T (kernelIsKernel _) }
  have : IsAffine (U : X.Opens) := U.2
  let Φ := Scheme.Modules.restrictFunctor (U : X.Opens).ι
  have hT' : (T.map Φ).ShortExact := hT.map_of_exact Φ
  have : (T.map Φ).X₁.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor _ (kernel S.toCycles)
  have hsurj : Function.Surjective (S.toCycles.app ((U : X.Opens).ι ''ᵁ ⊤)) := by
    have h := (ModuleCat.epi_iff_surjective _).1 (affine_globalSections_shortExact _ hT').epi_g
    exact h
  rw [Scheme.Opens.ι_image_top] at hsurj
  have hC : (ShortComplex.mk S.iCycles S.g S.iCycles_g).Exact :=
    ShortComplex.exact_of_f_is_kernel _ S.cyclesIsKernel
  intro x
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := modules_sections_exact hC (U := (U : X.Opens)) x hx
    obtain ⟨y, rfl⟩ := hsurj c
    refine ⟨y, ?_⟩
    rw [← S.toCycles_i]
    rfl
  · rintro ⟨y, rfl⟩
    change (S.f ≫ S.g).app U y = 0
    rw [S.zero]
    rfl

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- **Hartshorne II, Corollary 9.8** (exactness): on a locally Noetherian scheme `X` (Hartshorne:
Noetherian), completion along the closed subscheme with ideal sheaf `I` carries an exact sequence
`F' ⟶ F ⟶ F''` of `𝒪_X`-modules with `F'` quasi-coherent and `F`, `F''` coherent to an exact
sequence `F̂' ⟶ F̂ ⟶ F̂''` of modules over the structure sheaf of the formal completion. -/
theorem moduleCompletion_exact [IsLocallyNoetherian X] (S : ShortComplex X.Modules)
    (hS : S.Exact) [S.X₁.IsQuasicoherent] (h₂ : IsCoherent S.X₂) (h₃ : IsCoherent S.X₃) :
    (S.map I.moduleCompletionFunctor).Exact := by
  have : S.X₂.IsQuasicoherent := h₂.isQuasicoherent
  have : S.X₃.IsQuasicoherent := h₃.isQuasicoherent
  have hB : Opens.IsBasis ((Opens.map (I.infinitesimalNeighborhoodι 1).base).obj ''
      ((fun U : X.affineOpens => (U : X.Opens)) '' Set.univ)) := by
    rw [Set.image_univ, Subtype.range_coe]
    exact opens_isBasis_map_image _ (I.infinitesimalNeighborhoodι 1).isClosedEmbedding.isInducing
      X.isBasis_affineOpens
  refine I.moduleCompletionHom_exact_of_isBasis S.f S.g _ Set.univ hB ?_
  intro U _
  exact ⟨IsLocallyNoetherian.component_noetherian U,
    (forall_affine_finite_of_isCoherent S.X₂ h₂ U).1,
    (forall_affine_finite_of_isCoherent S.X₃ h₃ U).1,
    modules_app_exact_of_isAffineOpen hS U⟩

open ZeroObject in
/-- **Hartshorne II, Corollary 9.8**, short exact form: on a locally Noetherian scheme (Hartshorne:
Noetherian), completion along a closed subscheme carries a short exact sequence of coherent
`𝒪_X`-modules to a short exact sequence of modules over the structure sheaf of the formal
completion. -/
theorem moduleCompletion_shortExact [IsLocallyNoetherian X] (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₁ : IsCoherent S.X₁) (h₂ : IsCoherent S.X₂) (h₃ : IsCoherent S.X₃) :
    (S.map I.moduleCompletionFunctor).ShortExact := by
  let Φ := I.moduleCompletionFunctor
  have : S.X₁.IsQuasicoherent := h₁.isQuasicoherent
  have : S.X₂.IsQuasicoherent := h₂.isQuasicoherent
  let Z : X.Modules := 0
  have hZ : IsZero Z := isZero_zero _
  have : Z.IsQuasicoherent := isQuasicoherent_of_isZero hZ
  let T := ShortComplex.mk (0 : Z ⟶ S.X₁) S.f zero_comp
  let T' := ShortComplex.mk S.g (0 : S.X₃ ⟶ Z) comp_zero
  have hT : T.Exact := (ShortComplex.exact_iff_mono T rfl).2 hS.mono_f
  have hT' : T'.Exact := (ShortComplex.exact_iff_epi T' rfl).2 hS.epi_g
  have : T.X₁.IsQuasicoherent := isQuasicoherent_of_isZero hZ
  have : T'.X₁.IsQuasicoherent := h₂.isQuasicoherent
  have h1 := I.moduleCompletion_exact T hT h₁ h₂
  have h2 := I.moduleCompletion_exact T' hT' h₃ (isCoherent_of_isZero hZ)
  refine ShortComplex.ShortExact.mk' (I.moduleCompletion_exact S hS.exact h₂ h₃) ?_ ?_
  · exact (ShortComplex.exact_iff_mono (T.map Φ) (Φ.map_zero _ _)).1 h1
  · exact (ShortComplex.exact_iff_epi (T'.map Φ) (Φ.map_zero _ _)).1 h2

/-- **The completion of a coherent module is coherent** (Hartshorne II.9, p. 194, for the target
of Corollary 9.8): on a Noetherian scheme, `F̂` is a coherent module on `X̂_Y`. Here `X̂_Y` is
covered by the single chart `X̂_Y` itself, the completion of `X` along `Y`, on which `F̂` is the
completion of the coherent module `F`; the remaining isomorphism identifies the restriction of
`F̂` to the whole space with its pushforward along the canonical isomorphism. -/
theorem isCoherentFormalModule_moduleCompletion [IsNoetherian X] (F : X.Modules)
    (hF : IsCoherent F) :
    IsCoherentFormalModule (X := I.toNoetherianFormalScheme) (I.moduleCompletion F) := by
  refine ⟨Unit, inferInstance, fun _ => ⊤, by simp, fun _ => ⟨X, inferInstance, I,
    LocallyRingedSpace.restrictTopIso _, F, hF, ⟨?_⟩⟩⟩
  dsimp only [structureModuleRestrict, structureModulePushforward]
  have e := @SheafOfModules.pushforwardCongr₂ _ _ _ _ (Opens.grothendieckTopology _)
    (Opens.grothendieckTopology _)
    (Opens.map (LocallyRingedSpace.restrictTopIso I.formalCompletion).inv.base)
    (@Opens.isOpenEmbedding I.formalCompletion.carrier ⊤).functor
    (structureRingCatSheaf (I.formalCompletion.restrict
      (@Opens.isOpenEmbedding I.formalCompletion.carrier ⊤)))
    (structureRingCatSheaf I.formalCompletion) inferInstance
    (@Opens.isOpenEmbedding I.formalCompletion.carrier ⊤).functor_isContinuous
    (𝟙 _) (structureRingCatSheafHom (LocallyRingedSpace.restrictTopIso I.formalCompletion).inv)
    (eqToIso (Opens.inclusion'_top_functor I.formalCompletion.carrier).symm) ?_
  · exact e.app _
  have hc : (LocallyRingedSpace.restrictTopIso I.formalCompletion).inv.c =
      eqToHom (PresheafedSpace.restrict_top_presheaf _) := rfl
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  erw [Category.id_comp]
  simp only [Functor.sheafPushforwardContinuousNatTrans, ObjectProperty.ι_obj,
    Functor.whiskerRight_app, Functor.op_obj, structureRingCatSheafHom, hc]
  have key : ∀ {A B : (Opens I.formalCompletion.carrier)ᵒᵖ} (f : A ⟶ B) (hAB : A = B),
      (structureRingCatSheaf I.formalCompletion).obj.map f =
        eqToHom (congrArg (structureRingCatSheaf I.formalCompletion).obj.obj hAB) := by
    intro A B f hAB
    subst hAB
    rw [show f = 𝟙 A from Quiver.Hom.unop_inj (Subsingleton.elim _ _),
      CategoryTheory.Functor.map_id]
    rfl
  have key2 : ∀ {C : Type u} [Category.{u} C] {F₁ F₂ : C ⥤ CommRingCat.{u}} (h : F₁ = F₂)
      (V : C), (Functor.whiskerRight (eqToHom h) (forget₂ CommRingCat RingCat.{u})).app V =
        eqToHom (by rw [h]) := by
    intro C _ F₁ F₂ h V
    subst h
    simp
  refine (key _ ?_).trans
    (key2 (PresheafedSpace.restrict_top_presheaf I.formalCompletion.toPresheafedSpace) U).symm
  exact congrArg (fun G => op (G.obj (unop U)))
    (Opens.inclusion'_top_functor I.formalCompletion.carrier)

end QuasicoherentIdealSubsheaf

end Hartshorne
