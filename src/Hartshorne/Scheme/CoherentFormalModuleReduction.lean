/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFormalModuleChart
import Hartshorne.Scheme.SchemeCompletionTensor
import Hartshorne.Scheme.PullbackQuasicoherent

noncomputable section
open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne
universe u

section StructureModulePullback

variable {A B C : LocallyRingedSpace.{u}}

instance (f : A ⟶ B) :
    (PresheafOfModules.pushforward.{u} (structureRingCatSheafHom f).hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top _)

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
    structureModulePushforward (f ≫ g) ≅ structureModulePushforward f ⋙ structureModulePushforward g :=
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
  CategoryTheory.Equivalence.mk (structureModulePushforward e.inv) (structureModulePushforward e.hom)
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

end Hartshorne
