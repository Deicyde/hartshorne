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

end Hartshorne
