/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModuleChart
import Hartshorne.Scheme.SchemeCompletionTensor
import Hartshorne.Scheme.PullbackQuasicoherent

/-!
# Coherence of the reductions of a coherent formal module

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.6(a) (pp. 197–198): for a Noetherian formal
scheme `X`, an ideal of definition `J` and a coherent `𝒪_X`-module `F`, every
`F_n = F / J ^ (n + 1) F` is a coherent module on the scheme `(X, 𝒪_X / J ^ (n + 1))`, and the
canonical map `F ⟶ lim_n F_n` is an isomorphism
(`Hartshorne.IsIdealOfDefinition.reconstruction`).

Pullback of modules along a morphism `f : A ⟶ B` of locally ringed spaces:

* `Hartshorne.structureModulePullback f`: the left adjoint `f^*` of the pushforward `f_*`, with
  `structureModulePullbackComp` (`(f ≫ g)^* ≅ f^* ∘ g^*`), `structureModulePullbackCongr`,
  `structureModulePullbackIsoPushforward` (`e^* ≅ (e⁻¹)_*` for an isomorphism `e`),
  `structureModuleRestrictIsoPullback` (restriction to an open subspace is the pullback along the
  inclusion) and `schemeModulesPullbackIso` (for schemes it is `Scheme.Modules.pullback`).
* `Hartshorne.IsIdealOfDefinition.quotientLRSHom`: the morphism of locally ringed spaces
  `(X, 𝒪_X / J) ⟶ X`; `IsIdealOfDefinition.quotientPullbackIso` identifies the pullback along it
  with `quotientPullback`.
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionLRSHom`: the morphism of locally ringed
  spaces `Ŷ ⟶ Y` from the completion of a scheme along a closed subscheme;
  `QuasicoherentIdealSubsheaf.pullbackFormalCompletionIso` identifies the pullback along it with
  the module pullback of Corollary 9.8.

Coherence:

* `Hartshorne.IsIdealOfDefinition.reductionIso`: `F_n ≅ i^* F` for
  `i : (X, 𝒪_X / J ^ (n + 1)) ⟶ X`, since the pullback is right exact and kills `J ^ (n + 1) F`.
* `Hartshorne.isCoherent_of_isCoherent_restrict`: on a locally Noetherian scheme, coherence is
  local.
* `Hartshorne.IsIdealOfDefinition.isCoherent_restrict_pullback_chart`: on a chart `U ≅ Ŷ` of `F`,
  `(i^* F)|_U` is the pullback of a coherent module along a morphism of schemes
  `(U, 𝒪_U / J ^ (n + 1)) ⟶ Y`, hence coherent (Proposition 5.8(b)); this uses
  `Ĝ ≅ f^* G` (Corollary 9.8).
* `Hartshorne.IsIdealOfDefinition.isCoherent_reduction`: `F_n` is coherent.
-/

noncomputable section
open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne
universe u

section StructureModulePullback

variable {A B C : LocallyRingedSpace.{u}}

/-- The pushforward of presheaves of modules along a morphism of locally ringed spaces has a left
adjoint. -/
instance (f : A ⟶ B) :
    (PresheafOfModules.pushforward.{u} (structureRingCatSheafHom f).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top _)

/-- The pushforward of sheaves of modules along a morphism of locally ringed spaces has a left
adjoint. -/
instance (f : A ⟶ B) : (structureModulePushforward f).IsRightAdjoint :=
  (SheafOfModules.PullbackConstruction.adjunction.{u} (structureRingCatSheafHom f)).isRightAdjoint

/-- The pullback `f^*` of modules along a morphism `f : A ⟶ B` of locally ringed spaces, the left
adjoint of the pushforward `f_*`. -/
def structureModulePullback (f : A ⟶ B) :
    SheafOfModules.{u} (structureRingCatSheaf B) ⥤ SheafOfModules.{u} (structureRingCatSheaf A) :=
  SheafOfModules.pullback.{u} (structureRingCatSheafHom f)

/-- The adjunction `f^* ⊣ f_*`. -/
def structureModulePullbackAdjunction (f : A ⟶ B) :
    structureModulePullback f ⊣ structureModulePushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} _

/-- Pushforward along a composite is the composite of the pushforwards. -/
def structureModulePushforwardComp (f : A ⟶ B) (g : B ⟶ C) :
    structureModulePushforward (f ≫ g) ≅
      structureModulePushforward f ⋙ structureModulePushforward g :=
  Iso.refl _

/-- Pullback along a composite is the composite of the pullbacks. -/
def structureModulePullbackComp (f : A ⟶ B) (g : B ⟶ C) :
    structureModulePullback (f ≫ g) ≅ structureModulePullback g ⋙ structureModulePullback f :=
  (structureModulePullbackAdjunction (f ≫ g)).leftAdjointUniq
    ((structureModulePullbackAdjunction g).comp (structureModulePullbackAdjunction f))

/-- Pullbacks along equal morphisms agree. -/
def structureModulePullbackCongr {f g : A ⟶ B} (h : f = g) :
    structureModulePullback f ≅ structureModulePullback g :=
  eqToIso (by rw [h])

/-- Pushforward along the identity is the identity. -/
def structureModulePushforwardId (A : LocallyRingedSpace.{u}) :
    structureModulePushforward (𝟙 A) ≅ 𝟭 _ :=
  Iso.refl _

/-- Pushforwards along equal morphisms agree. -/
def structureModulePushforwardCongr {f g : A ⟶ B} (h : f = g) :
    structureModulePushforward f ≅ structureModulePushforward g :=
  eqToIso (by rw [h])

/-- For an isomorphism `e : A ≅ B` of locally ringed spaces, the pushforwards along `e⁻¹` and `e`
are inverse equivalences. -/
def structureModulePushforwardEquivalence (e : A ≅ B) :
    SheafOfModules.{u} (structureRingCatSheaf B) ≌ SheafOfModules.{u} (structureRingCatSheaf A) :=
  CategoryTheory.Equivalence.mk (structureModulePushforward e.inv)
    (structureModulePushforward e.hom)
    ((structureModulePushforwardId B).symm ≪≫ structureModulePushforwardCongr e.inv_hom_id.symm ≪≫
      structureModulePushforwardComp e.inv e.hom)
    ((structureModulePushforwardComp e.hom e.inv).symm ≪≫
      structureModulePushforwardCongr e.hom_inv_id ≪≫ structureModulePushforwardId A)

/-- For an isomorphism `e : A ≅ B` of locally ringed spaces, the pullback along `e` is the
pushforward along `e⁻¹`. -/
def structureModulePullbackIsoPushforward (e : A ≅ B) :
    structureModulePullback e.hom ≅ structureModulePushforward e.inv :=
  (structureModulePullbackAdjunction e.hom).leftAdjointUniq
    (structureModulePushforwardEquivalence e).toAdjunction

/-- For a morphism of schemes, the pullback of modules is the pullback along the underlying
morphism of locally ringed spaces. -/
def schemeModulesPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pullback f ≅ structureModulePullback f.toLRSHom :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjointUniq
    (structureModulePullbackAdjunction f.toLRSHom)

/-- Restriction to an open subspace is left adjoint to the pushforward along the inclusion. -/
def structureModuleRestrictAdjunction (X : LocallyRingedSpace.{u}) {U : TopCat.{u}}
    {f : U ⟶ X.carrier} (h : Topology.IsOpenEmbedding f) :
    structureModuleRestrict X h ⊣ structureModulePushforward (X.ofRestrict h) := by
  letI : h.functor.IsContinuous (Opens.grothendieckTopology (X.restrict h).carrier)
      (Opens.grothendieckTopology X.carrier) := h.functor_isContinuous
  letI : (Opens.map f).IsContinuous (Opens.grothendieckTopology X.carrier)
      (Opens.grothendieckTopology (X.restrict h).carrier) :=
    inferInstanceAs ((Opens.map (X.ofRestrict h).base).IsContinuous _ _)
  refine SheafOfModules.pushforwardPushforwardAdj h.isOpenMap.adjunction _ _ ?_ ?_
  · ext V x
    rfl
  · ext V x
    change (X.presheaf.map _ ≫ X.presheaf.map _) x = x
    rw [← Functor.map_comp, Subsingleton.elim (_ ≫ _) (𝟙 _), X.presheaf.map_id]
    rfl

/-- Restriction to an open subspace is the pullback along the inclusion. -/
def structureModuleRestrictIsoPullback (X : LocallyRingedSpace.{u}) {U : TopCat.{u}}
    {f : U ⟶ X.carrier} (h : Topology.IsOpenEmbedding f) :
    structureModuleRestrict X h ≅ structureModulePullback (X.ofRestrict h) :=
  (structureModuleRestrictAdjunction X h).leftAdjointUniq (structureModulePullbackAdjunction _)

end StructureModulePullback

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)

/-- The morphism of ringed spaces `(X, 𝒪_X / J) ⟶ X`: the identity on spaces and the projection
`𝒪_X ⟶ 𝒪_X / J` on sheaves. -/
def quotientPresheafedSpaceHom :
    h.quotientScheme.toPresheafedSpace ⟶ X.toLocallyRingedSpace.toPresheafedSpace where
  base := 𝟙 X.toLocallyRingedSpace.toTopCat
  c := J.quotientπ.hom

/-- The stalk maps of `(X, 𝒪_X / J) ⟶ X` are surjective, since `𝒪_X ⟶ 𝒪_X / J` is locally
surjective. -/
lemma surjective_stalkMap_quotientPresheafedSpaceHom (x : X.toLocallyRingedSpace) :
    Function.Surjective ((quotientPresheafedSpaceHom h).stalkMap x) := by
  intro b
  obtain ⟨V, hxV, t, rfl⟩ := J.quotient.presheaf.exists_germ_eq b
  obtain ⟨V', hV'V, ⟨s, hs⟩, hxV'⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp
    J.isLocallySurjective_quotientπ V t x hxV
  refine ⟨X.toLocallyRingedSpace.presheaf.germ V' x hxV' s, ?_⟩
  refine (PresheafedSpace.stalkMap_germ_apply (quotientPresheafedSpaceHom h) V' x hxV' s).trans ?_
  exact (congrArg (J.quotient.presheaf.germ V' x hxV') hs).trans
    (J.quotient.presheaf.germ_res_apply (homOfLE hV'V) x hxV' t)

/-- The morphism of locally ringed spaces `(X, 𝒪_X / J) ⟶ X`. -/
def quotientLRSHom : h.quotientScheme.toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  ⟨quotientPresheafedSpaceHom h, fun x =>
    haveI : IsLocalRing (X.toLocallyRingedSpace.presheaf.stalk x) :=
      X.toLocallyRingedSpace.isLocalRing x
    IsLocalHom.of_surjective _ (surjective_stalkMap_quotientPresheafedSpaceHom h x)⟩

/-- The pullback along `𝒪_X ⟶ 𝒪_X / J` is the pullback along `(X, 𝒪_X / J) ⟶ X`. -/
def quotientPullbackIso : h.quotientPullback ≅ structureModulePullback (quotientLRSHom h) :=
  h.quotientAdjunction.leftAdjointUniq (structureModulePullbackAdjunction _)

end IsIdealOfDefinition

namespace QuasicoherentIdealSubsheaf

variable {Y : Scheme.{u}} (I : QuasicoherentIdealSubsheaf Y)

/-- The morphism of ringed spaces `f : (|Y_1|, 𝒪_Ŷ) ⟶ (Y, 𝒪_Y)`, with `𝒪_Y ⟶ f_* 𝒪_Ŷ` the
canonical map. -/
def formalCompletionPresheafedSpaceHom :
    I.formalCompletion.toPresheafedSpace ⟶ Y.toPresheafedSpace where
  base := (I.infinitesimalNeighborhoodι 1).base
  c := I.structureSheafToFormalCompletion.hom

/-- The stalk maps of `(|Y_1|, 𝒪_Ŷ) ⟶ (Y, 𝒪_Y)` are local: if the image in `𝒪_Ŷ` of a section
`s` of `𝒪_Y` near `y` has a unit germ, then near `y` its image in `𝒪_{Y_1}` is a unit, so the germ
of `s` is a unit because `Y_1 ⟶ Y` is a morphism of schemes. -/
lemma isLocalHom_stalkMap_formalCompletionPresheafedSpaceHom (y : I.formalCompletion) :
    IsLocalHom ((I.formalCompletionPresheafedSpaceHom).stalkMap y).hom := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨V, hyV, s, rfl⟩ := Y.presheaf.exists_germ_eq a
  rw [PresheafedSpace.stalkMap_germ_apply] at ha
  obtain ⟨W, i, hyW, hW⟩ := I.formalCompletion.toRingedSpace.isUnit_res_of_isUnit_germ _ _ y hyV ha
  have h1 := (I.isUnit_formalCompletionSheaf_iff W _).mp hW
  have hj := I.isOpenEmbedding_infinitesimalNeighborhoodFromOne 0
  have h2 := NatTrans.naturality_apply (limit.π I.formalCompletionDiagram (op 0)).hom i.op
    (I.structureSheafToFormalCompletion.hom.app (op V) s)
  have h3 : (limit.π I.formalCompletionDiagram (op 0)).hom.app
      (op ((I.infinitesimalNeighborhoodι 1) ⁻¹ᵁ V))
      (I.structureSheafToFormalCompletion.hom.app (op V) s) =
        I.formalCompletionSheafObjSectionsMap 0 V s :=
    congrArg (fun g => g.hom s) (I.formalCompletionSectionsMap_π V 0)
  have hle : hj.functor.obj W ≤ I.infinitesimalNeighborhoodι (0 + 1) ⁻¹ᵁ V :=
    (hj.functor.monotone i.le).trans (I.functor_obj_preimage_infinitesimalNeighborhoodι 0 V).le
  have h4 : IsUnit ((I.infinitesimalNeighborhoodι (0 + 1)).appLE V (hj.functor.obj W) hle s) := by
    erw [h2, h3] at h1
    have h6 : IsUnit (((I.infinitesimalNeighborhoodι (0 + 1)).appLE V
        (hj.functor.obj ((I.infinitesimalNeighborhoodι 1) ⁻¹ᵁ V))
        (I.functor_obj_preimage_infinitesimalNeighborhoodι 0 V).le ≫
        (I.infinitesimalNeighborhood (0 + 1)).presheaf.map (hj.functor.map i).op) s) := h1
    exact (congrArg IsUnit (congrArg (fun g => g.hom s)
      (Scheme.Hom.appLE_map (I.infinitesimalNeighborhoodι (0 + 1))
        (I.functor_obj_preimage_infinitesimalNeighborhoodι 0 V).le (hj.functor.map i).op))).mp h6
  let y' : I.infinitesimalNeighborhood 1 := y
  have hjy : I.infinitesimalNeighborhoodFromOne 0 y' ∈ hj.functor.obj W := ⟨y, hyW, rfl⟩
  have h7 := h4.map ((I.infinitesimalNeighborhood (0 + 1)).presheaf.germ _ _ hjy).hom
  have h8 : (I.infinitesimalNeighborhood (0 + 1)).presheaf.germ _ _ hjy
      ((I.infinitesimalNeighborhoodι (0 + 1)).appLE V (hj.functor.obj W) hle s) =
        (I.infinitesimalNeighborhoodι (0 + 1)).stalkMap (I.infinitesimalNeighborhoodFromOne 0 y')
          (Y.presheaf.germ V _ (hle hjy) s) := by
    rw [Scheme.Hom.germ_stalkMap_apply (I.infinitesimalNeighborhoodι (0 + 1)) V
      (I.infinitesimalNeighborhoodFromOne 0 y') (hle hjy) s, Scheme.Hom.appLE,
      CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  rw [h8] at h7
  have h9 := (isUnit_map_iff ((I.infinitesimalNeighborhoodι (0 + 1)).stalkMap
    (I.infinitesimalNeighborhoodFromOne 0 y')).hom _).mp h7
  have hpt : I.infinitesimalNeighborhoodι (0 + 1) (I.infinitesimalNeighborhoodFromOne 0 y') =
      (I.infinitesimalNeighborhoodι 1).base y := by
    rw [← Scheme.Hom.comp_apply, infinitesimalNeighborhoodFromOne_comp_ι]
  have key : ∀ z (hz : z ∈ V), z = (I.infinitesimalNeighborhoodι 1).base y →
      IsUnit (Y.presheaf.germ V z hz s) → IsUnit (Y.presheaf.germ V _ hyV s) := by
    rintro z hz rfl h
    exact h
  exact key _ _ hpt h9

/-- **The morphism of locally ringed spaces `Ŷ ⟶ Y`**: the inclusion of `|Y_1|` with the
canonical map `𝒪_Y ⟶ f_* 𝒪_Ŷ`. -/
def formalCompletionLRSHom : I.formalCompletion ⟶ Y.toLocallyRingedSpace :=
  ⟨I.formalCompletionPresheafedSpaceHom, I.isLocalHom_stalkMap_formalCompletionPresheafedSpaceHom⟩

/-- The pullback along `𝒪_Y ⟶ f_* 𝒪_Ŷ` is the pullback along `Ŷ ⟶ Y`. -/
def pullbackFormalCompletionIso :
    SheafOfModules.pullback.{u} I.structureSheafToFormalCompletionRingCat ≅
      structureModulePullback I.formalCompletionLRSHom :=
  (SheafOfModules.pullbackPushforwardAdjunction.{u} _).leftAdjointUniq
    (structureModulePullbackAdjunction _)

end QuasicoherentIdealSubsheaf

namespace IdealSubsheaf

variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} (J : IdealSubsheaf R)

/-- A section of `J` maps to zero in `R / J`. -/
lemma quotientπ_app_eq_zero_of_mem {U : Opens T} {s : R.presheaf.obj (op U)}
    (hs : s ∈ J.ideal U) : J.quotientπ.hom.app (op U) s = 0 := by
  have h : J.quotientπ.hom = J.quotientPresheafπ ≫ toSheafify (Opens.grothendieckTopology T)
      (idealQuotientPresheaf R J.ideal J.ideal_le_comap) := by
    rw [toSheafify_naturality]
    rfl
  rw [h]
  change (toSheafify (Opens.grothendieckTopology T)
    (idealQuotientPresheaf R J.ideal J.ideal_le_comap)).app (op U)
      (Ideal.Quotient.mk (J.ideal U) s) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs]
  exact map_zero _

end IdealSubsheaf

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)
  (F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace))

/-- The pullback along `𝒪_X ⟶ 𝒪_X / J` kills the inclusion `J F ⟶ F`: its adjoint, the
composite of `J F ⟶ F` with the unit `F ⟶ i_* i^* F`, vanishes since `J` acts by zero on
`i_* i^* F`. -/
lemma quotientPullback_map_smulι : h.quotientPullback.map (J.smulι F) = 0 := by
  let K : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace) := J.smulModules F
  let ι : K ⟶ F := J.smulι F
  have h0 : ι ≫ h.quotientAdjunction.unit.app F = 0 := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    ext ⟨s, hs⟩
    change (h.quotientAdjunction.unit.app F).val.app V s = 0
    induction V using Opposite.rec with | op V => ?_
    refine sheafOfModules_eq_zero_of_locally
      (A := h.quotientPushforward.obj (h.quotientPullback.obj F)) _ fun x hx => ?_
    obtain ⟨W, hWV, hxW, hsW⟩ := hs x hx
    refine ⟨W, hWV, hxW, ?_⟩
    refine (PresheafOfModules.naturality_apply (h.quotientAdjunction.unit.app F).val
      (homOfLE hWV).op s).symm.trans ?_
    let F' : SheafOfModules.{u} (ringCatSheafOf X.toLocallyRingedSpace.sheaf) := F
    have key : ∀ t : F'.val.obj (op W), t ∈ J.sectionsSmul F' W →
        (h.quotientAdjunction.unit.app F).val.app (op W) t = 0 := by
      intro t ht
      refine Submodule.smul_induction_on ht (fun r hr m _ => ?_) (fun a b ha hb => ?_)
      · refine (((h.quotientAdjunction.unit.app F).val.app (op W)).hom.map_smul r m).trans ?_
        have hr0 : (show h.quotientScheme.ringCatSheaf.obj.obj (op W) from
            (h.quotientRingCatSheafHom.hom.app (op W)).hom r) = 0 :=
          J.quotientπ_app_eq_zero_of_mem hr
        have e : (show (structureRingCatSheaf X.toLocallyRingedSpace).obj.obj (op W) from r) •
            (show (h.quotientPushforward.obj (h.quotientPullback.obj F)).val.obj (op W) from
              ((h.quotientAdjunction.unit.app F).val.app (op W)).hom m) =
            (show h.quotientScheme.ringCatSheaf.obj.obj (op W) from
              (h.quotientRingCatSheafHom.hom.app (op W)).hom r) •
              (show (h.quotientPullback.obj F).val.obj (op W) from
                ((h.quotientAdjunction.unit.app F).val.app (op W)).hom m) := rfl
        have z : (0 : h.quotientScheme.ringCatSheaf.obj.obj (op W)) •
            (show (h.quotientPullback.obj F).val.obj (op W) from
              ((h.quotientAdjunction.unit.app F).val.app (op W)).hom m) = 0 := zero_smul _ _
        exact e.trans ((congrArg (· • _) hr0).trans z)
      · rw [map_add, ha, hb, add_zero]
    exact key _ hsW
  calc h.quotientPullback.map (J.smulι F) =
        h.quotientPullback.map ι ≫ (h.quotientPullback.map (h.quotientAdjunction.unit.app F) ≫
          h.quotientAdjunction.counit.app (h.quotientPullback.obj F)) := by
        rw [h.quotientAdjunction.left_triangle_components F, Category.comp_id]
    _ = h.quotientPullback.map (ι ≫ h.quotientAdjunction.unit.app F) ≫
          h.quotientAdjunction.counit.app (h.quotientPullback.obj F) := by
        rw [Functor.map_comp, Category.assoc]
    _ = 0 := by
        have := h.quotientAdjunction.isLeftAdjoint
        rw [h0, Functor.map_zero, zero_comp]

/-- The pullback to `(X, 𝒪_X / J)` of `F / J F` is the pullback of `F`: the pullback is right
exact and kills `J F ⟶ F`. -/
def quotientPullbackCokernelIso :
    h.quotientPullback.obj (cokernel (J.smulι F)) ≅ h.quotientPullback.obj F := by
  haveI := h.quotientAdjunction.leftAdjoint_preservesColimits
  let K : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace) := J.smulModules F
  let ι : K ⟶ F := J.smulι F
  exact PreservesCokernel.iso h.quotientPullback ι ≪≫
    cokernelIsoOfEq (h.quotientPullback_map_smulι F) ≪≫ cokernelZeroIsoTarget

/-- **`F_n` is the pullback of `F`**: `F_n = i^* (F / J ^ (n + 1) F) ≅ i^* F` along
`i : (X, 𝒪_X / J ^ (n + 1)) ⟶ X`. -/
def reductionIso (n : ℕ) : h.reduction F n ≅ (h.pow_succ n).quotientPullback.obj F :=
  (h.pow_succ n).quotientPullbackCokernelIso F

end IsIdealOfDefinition

section CoherentLocality

/-- A presentation of the restriction `M|_W` of a module on a scheme to an open `W` gives a
presentation of `M` over `W`, with the same generators and relations. -/
def presentationOverOfRestrict {Z : Scheme.{u}} (M : Z.Modules) (W : Z.Opens)
    (P : (M.restrict W.ι).Presentation) : (M.over W).Presentation := by
  let Q := @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (Scheme.Modules.overEquiv W).inverse
    ((Scheme.Modules.overEquiv W).symm.toAdjunction.leftAdjoint_preservesColimits)
    (W.sheafOfModulesEquivOverInverseUnit Z.ringCatSheaf).symm
  let e : M.over W ≅ (Scheme.Modules.overEquiv W).inverse.obj (M.restrict W.ι) :=
    (Scheme.Modules.overEquiv W).unitIso.app (M.over W) ≪≫
      (Scheme.Modules.overEquiv W).inverse.mapIso ((Scheme.Modules.overFunctorEquiv W).app M)
  letI : IsIso e.inv := e.isIso_inv
  exact SheafOfModules.Presentation.ofIsIso e.inv Q

set_option backward.isDefEq.respectTransparency false in
/-- `presentationOverOfRestrict` keeps the generators and relations, so it preserves
finiteness. -/
private lemma isFinite_presentationOverOfRestrict {Z : Scheme.{u}} (M : Z.Modules) (W : Z.Opens)
    (P : (M.restrict W.ι).Presentation) [P.IsFinite] :
    (presentationOverOfRestrict M W P).IsFinite where
  isFiniteType_generators :=
    ⟨(SheafOfModules.Presentation.IsFinite.isFiniteType_generators (p := P)).finite⟩
  isFiniteType_relations :=
    ⟨(SheafOfModules.Presentation.IsFinite.isFiniteType_relations (p := P)).finite⟩

/-- Transporting a presentation along an isomorphism preserves finiteness. -/
private lemma isFinite_ofIsIso {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [IsIso f] (P : M.Presentation) [P.IsFinite] : (P.ofIsIso f).IsFinite :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- `Scheme.Modules.presentationRestrict` keeps the generators and relations, so it preserves
finiteness. -/
private lemma isFinite_presentationRestrict {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    {M : X.Modules} (P : M.Presentation) [P.IsFinite] :
    (Scheme.Modules.presentationRestrict f P).IsFinite where
  isFiniteType_generators :=
    ⟨(SheafOfModules.Presentation.IsFinite.isFiniteType_generators (p := P)).finite⟩
  isFiniteType_relations :=
    ⟨(SheafOfModules.Presentation.IsFinite.isFiniteType_relations (p := P)).finite⟩

set_option backward.isDefEq.respectTransparency false in
/-- A module on a scheme which near every point has a finite presentation is of finite
presentation. -/
theorem isFinitePresentation_of_forall_exists {Z : Scheme.{u}} (M : Z.Modules)
    (h : ∀ x : Z, ∃ (W : Z.Opens) (_ : x ∈ W) (P : (M.restrict W.ι).Presentation), P.IsFinite) :
    M.IsFinitePresentation := by
  choose W hxW P hP using h
  have hcov : (Opens.grothendieckTopology Z).CoversTop W := by
    rw [Opens.coversTop_iff, IsOpenCover]
    exact eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩
  let σ : M.QuasicoherentData :=
    SheafOfModules.QuasicoherentData.mk.{u, u, u, u} Z W hcov
      (fun x => presentationOverOfRestrict M (W x) (P x))
  have hσ : σ.IsFinitePresentation := by
    constructor
    intro x
    have := hP x
    exact isFinite_presentationOverOfRestrict M (W x) (P x)
  exact SheafOfModules.IsFinitePresentation.mk.{u, u, u} ⟨σ, hσ⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the restriction of `M` along an open immersion `o : V ⟶ Z` from a locally Noetherian
scheme is coherent, then near every point of the image `M` has a finite presentation. -/
theorem exists_presentation_of_isCoherent_restrict {Z V : Scheme.{u}} [IsLocallyNoetherian V]
    (o : V ⟶ Z) [IsOpenImmersion o] (M : Z.Modules) (hM : IsCoherent (M.restrict o)) (v : V) :
    ∃ (W : Z.Opens) (_ : o v ∈ W) (P : (M.restrict W.ι).Presentation), P.IsFinite := by
  obtain ⟨W₀, hW₀, hvW₀, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := v) trivial
  have h3 := (coherent_affine_local_tfae (M.restrict o)).out 0 2 |>.mp hM
  obtain ⟨N, hN, ⟨φ⟩⟩ := h3 ⟨W₀, hW₀⟩
  have : IsNoetherianRing Γ(V, W₀) := IsLocallyNoetherian.component_noetherian ⟨W₀, hW₀⟩
  obtain ⟨P₀, hP₀⟩ := CoherentAux.exists_finite_presentation_tilde N
  have : IsOpenImmersion hW₀.fromSpec := hW₀.isOpenImmersion_fromSpec
  let j := hW₀.fromSpec ≫ o
  let P₁ : ((M.restrict o).restrict hW₀.fromSpec).Presentation := P₀.ofIsIso φ.hom
  let P₂ : (M.restrict j).Presentation :=
    P₁.ofIsIso ((Scheme.Modules.restrictFunctorComp hW₀.fromSpec o).app M).inv
  let P₃ := Scheme.Modules.presentationRestrict j.isoOpensRange.inv P₂
  let P₄ : (M.restrict j.opensRange.ι).Presentation :=
    P₃.ofIsIso (((Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).app M).inv ≫
      (Scheme.Modules.restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp j)).hom.app M)
  have hP₁ : P₁.IsFinite := isFinite_ofIsIso _ P₀
  have hP₂ : P₂.IsFinite := isFinite_ofIsIso _ P₁
  have hP₃ : P₃.IsFinite := isFinite_presentationRestrict _ P₂
  have hP₄ : P₄.IsFinite := isFinite_ofIsIso _ P₃
  have hv : v ∈ Set.range hW₀.fromSpec := by rw [hW₀.range_fromSpec]; exact hvW₀
  obtain ⟨w, hw⟩ := hv
  refine ⟨j.opensRange, ⟨w, ?_⟩, P₄, hP₄⟩
  simp [j, hw]

/-- **Coherence is local**: a module on a locally Noetherian scheme whose restrictions to the
members of an open cover are coherent is coherent. -/
theorem isCoherent_of_isCoherent_restrict {Z : Scheme.{u}} [IsLocallyNoetherian Z] (M : Z.Modules)
    {ι : Type*} (U : ι → Z.Opens) (hU : ⨆ i, U i = ⊤) (h : ∀ i, IsCoherent (M.restrict (U i).ι)) :
    IsCoherent M := by
  have : M.IsFinitePresentation := isFinitePresentation_of_forall_exists M fun x => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    obtain ⟨W, hW, P, hP⟩ := exists_presentation_of_isCoherent_restrict (U i).ι M (h i) ⟨x, hi⟩
    exact ⟨W, hW, P, hP⟩
  exact isCoherent_of_isFinitePresentation M

end CoherentLocality

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)

/-- **The pullback of a coherent formal module is coherent on a chart.** Let `U` be an open of
`X` with a chart `e : U ≅ Ŷ` onto the completion of a locally Noetherian scheme `Y`, on which
`F|_U` is the transport of the completion `Ĝ` of a coherent `𝒪_Y`-module `G`. Then the pullback
of `F` to `(X, 𝒪_X / J)`, restricted to `U`, is the pullback of `G` along the morphism of schemes
`(U, 𝒪_U / J|_U) ⟶ U ≅ Ŷ ⟶ Y`, since `Ĝ` is the pullback of `G` along `Ŷ ⟶ Y`; it is coherent. -/
theorem isCoherent_restrict_pullback_chart
    (F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace))
    (U : Opens X.carrier) {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (I : QuasicoherentIdealSubsheaf Y) (e : X.restrict U.isOpenEmbedding ≅ I.formalCompletion)
    (G : Y.Modules) (hG : IsCoherent G)
    (ψ : (structureModuleRestrict X.toLocallyRingedSpace U.isOpenEmbedding).obj F ≅
      (structureModulePushforward e.inv).obj (I.moduleCompletion G)) :
    IsCoherent (Scheme.Modules.restrict
      (show h.quotientScheme.Modules from (structureModulePullback h.quotientLRSHom).obj F)
      (Scheme.Opens.ι (X := h.quotientScheme) ((Opens.map h.quotientLRSHom.base).obj U))) := by
  let p := h.quotientLRSHom
  let U' : h.quotientScheme.Opens := (Opens.map p.base).obj U
  have H : Set.range (U'.ι.toLRSHom ≫ p).base ⊆
      Set.range (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x.1, x.2⟩, rfl⟩
  let q := LocallyRingedSpace.IsOpenImmersion.lift
    (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding) (U'.ι.toLRSHom ≫ p) H
  have hq : q ≫ X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding = U'.ι.toLRSHom ≫ p :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  let g : U'.toScheme ⟶ Y := Scheme.Hom.mk (q ≫ e.hom ≫ I.formalCompletionLRSHom)
  let M : h.quotientScheme.Modules := (structureModulePullback p).obj F
  let χ : M.restrict U'.ι ≅ (Scheme.Modules.pullback g).obj G :=
    (Scheme.Modules.restrictFunctorIsoPullback U'.ι).app M ≪≫
    (schemeModulesPullbackIso U'.ι).app M ≪≫
    ((structureModulePullbackComp U'.ι.toLRSHom p).app F).symm ≪≫
    (structureModulePullbackCongr hq.symm).app F ≪≫
    (structureModulePullbackComp q _).app F ≪≫
    (structureModulePullback q).mapIso
      (((structureModuleRestrictIsoPullback _ U.isOpenEmbedding).app F).symm ≪≫ ψ ≪≫
        ((structureModulePullbackIsoPushforward e).app _).symm ≪≫
        (structureModulePullback e.hom).mapIso
          ((I.pullbackIsoModuleCompletion G hG).symm ≪≫ I.pullbackFormalCompletionIso.app G) ≪≫
        ((structureModulePullbackComp e.hom I.formalCompletionLRSHom).app G).symm) ≪≫
    ((structureModulePullbackComp q (e.hom ≫ I.formalCompletionLRSHom)).app G).symm ≪≫
    ((schemeModulesPullbackIso g).app G).symm
  exact isCoherent_of_iso χ.symm (isCoherent_pullback g hG)

/-- **`F_n` is coherent**: for a coherent `𝒪_X`-module `F` on a Noetherian formal scheme and an
ideal of definition `J`, the reduction `F_n = F / J ^ (n + 1) F` is a coherent module on the
Noetherian scheme `(X, 𝒪_X / J ^ (n + 1))`. It is the pullback of `F`
(`IsIdealOfDefinition.reductionIso`), coherence is local, and on each chart of `F` the pullback is
coherent (`IsIdealOfDefinition.isCoherent_restrict_pullback_chart`). -/
theorem isCoherent_reduction {F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)}
    (hF : IsCoherentFormalModule F) (n : ℕ) : IsCoherent (h.reduction F n) := by
  let h' := h.pow_succ n
  obtain ⟨ι, -, U, hU, hchart⟩ := hF
  have key : IsCoherent (show h'.quotientScheme.Modules from
      (structureModulePullback h'.quotientLRSHom).obj F) := by
    refine isCoherent_of_isCoherent_restrict _
      (fun i => (Opens.map h'.quotientLRSHom.base).obj (U i)) ?_ fun i => ?_
    · exact (Opens.map_iSup h'.quotientLRSHom.base U).symm.trans
        ((congrArg (Opens.map h'.quotientLRSHom.base).obj hU).trans rfl)
    · obtain ⟨Y, hY, I, e, G, hG, ⟨ψ⟩⟩ := hchart i
      exact h'.isCoherent_restrict_pullback_chart F (U i) I e G hG ψ
  exact isCoherent_of_iso (h.reductionIso F n ≪≫ h'.quotientPullbackIso.app F).symm key

end IsIdealOfDefinition

/-- **Reconstruction from infinitesimal reductions** (Hartshorne II.9, Proposition 9.6(a)). Let
`X` be a Noetherian formal scheme, `J` an ideal of definition and `F` a coherent `𝒪_X`-module, and
let `F_n` be `F / J ^ (n + 1) F` as a module on the scheme `(X, 𝒪_X / J ^ (n + 1))`. Then every
`F_n` is coherent, the canonical map `F / J ^ (n + 1) F ⟶ F_n` (with `F_n` pushed forward to `X`)
is an isomorphism, and the canonical map `F ⟶ lim_n F / J ^ (n + 1) F` is an isomorphism. -/
theorem IsIdealOfDefinition.reconstruction {X : NoetherianFormalScheme.{u}}
    {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf} (h : IsIdealOfDefinition X J)
    {F : SheafOfModules.{u} (structureRingCatSheaf X.toLocallyRingedSpace)}
    (hF : IsCoherentFormalModule F) :
    (∀ n, IsCoherent (h.reduction F n)) ∧ (∀ n, IsIso (h.toReduction F n)) ∧
      IsIso (J.toLimitPowQuotient F) :=
  ⟨h.isCoherent_reduction hF, h.isIso_toReduction F, h.isIso_toLimitPowQuotient hF⟩

end Hartshorne
