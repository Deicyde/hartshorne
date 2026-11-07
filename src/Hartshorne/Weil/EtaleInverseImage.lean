/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.GlobalSections
import Mathlib.CategoryTheory.Sites.Point.Comap
import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Inverse image of abelian sheaves on small étale sites

Let `f : X ⟶ Y` be a morphism of schemes.  Base change `V ↦ V ×_Y X` is a functor
`Y.Etale ⥤ X.Etale` between the small étale sites.  This file shows that it is a
morphism of sites and studies the induced functors on abelian sheaves.

## Main declarations

- `AlgebraicGeometry.Scheme.etaleBaseChange f`: the base change functor
  `Y.Etale ⥤ X.Etale`; it preserves finite limits, is representably flat and continuous.
- `AlgebraicGeometry.Scheme.etalePushforward f`: the direct image
  `Sheaf X.smallEtaleTopology Ab ⥤ Sheaf Y.smallEtaleTopology Ab`.
- `AlgebraicGeometry.Scheme.etaleInverseImage f`: the inverse image, a left adjoint of the
  direct image.  It exists because the direct image factors, up to the equivalence given by
  the essentially small affine étale site of `Y`, through a pushforward along a functor out of
  that affine site, for which the left Kan extension exists.
- `AlgebraicGeometry.Scheme.etalePushforwardCompΓ f`: global sections of the direct image are
  the global sections on `X`.
- `AlgebraicGeometry.Scheme.constantSheafCompEtaleInverseImageIso f`: the inverse image of a
  constant sheaf is the constant sheaf.
- The inverse image preserves monomorphisms.  This is checked on the conservative family of
  geometric points of the small étale site of `X`: the stalk of the inverse image at a geometric
  point `s` of `X` is the stalk at the geometric point `s ≫ f` of `Y`.

## Universes

For `X : Scheme.{u}`, the sheaves take values in `Ab.{u}`.
-/

open CategoryTheory Limits MorphismProperty

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance hasPullbacksAlong_etale :
    MorphismProperty.HasPullbacksAlong (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- Base change along `f : X ⟶ Y`, as a functor from the small étale site of `Y` to the small
étale site of `X`: an étale `Y`-scheme `V` goes to `V ×_Y X`. -/
noncomputable def etaleBaseChange : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f

instance : PreservesFiniteLimits (etaleBaseChange f) :=
  inferInstanceAs
    (PreservesFiniteLimits (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f))

instance : RepresentablyFlat (etaleBaseChange f) := by
  have : HasFiniteLimits Y.Etale :=
    inferInstanceAs (HasFiniteLimits (MorphismProperty.Over @AlgebraicGeometry.Etale ⊤ Y))
  exact flat_of_preservesFiniteLimits _

/-- Base change sends étale coverings to étale coverings. -/
lemma coverPreserving_etaleBaseChange :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (etaleBaseChange f) where
  cover_preserve {W} R hR := by
    obtain ⟨𝒰, _, h, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hR
    let V : 𝒰.I₀ → Y.Etale := fun i ↦ (𝒰.X i).asOverProp Y (h i)
    let a : ∀ i, V i ⟶ W := fun i ↦ (𝒰.f i).asOverProp Y
    refine X.smallEtaleTopology.superset_covering (S := Sieve.ofArrows _
      (fun i ↦ (etaleBaseChange f).map (a i))) ?_ ?_
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact ⟨V i, a i, 𝟙 _, hle _ (a i) (Presieve.ofArrows.mk i), (Category.id_comp _).symm⟩
    · rw [ofArrows_mem_smallEtaleTopology_iff]
      refine Set.eq_univ_of_forall fun z ↦ ?_
      let p := pullback.fst W.hom f
      obtain ⟨i, v, hv⟩ := 𝒰.exists_eq (p z)
      have hw : pullback.snd p (𝒰.f i) ≫ (V i).hom =
          (pullback.fst p (𝒰.f i) ≫ pullback.snd W.hom f) ≫ f := by
        have e1 : 𝒰.f i ≫ W.hom = (V i).hom := comp_over (𝒰.f i) Y
        rw [← e1, ← pullback.condition_assoc, Category.assoc, pullback.condition]
      have key : pullback.lift (pullback.snd p (𝒰.f i))
          (pullback.fst p (𝒰.f i) ≫ pullback.snd W.hom f) hw ≫
            ((etaleBaseChange f).map (a i)).left = pullback.fst p (𝒰.f i) := by
        apply pullback.hom_ext
        · simp only [etaleBaseChange, a, p, Category.assoc,
            MorphismProperty.Over.pullback_map_left, pullback.lift_fst, pullback.lift_fst_assoc]
          exact (pullback.condition (f := p) (g := 𝒰.f i)).symm
        · simp only [etaleBaseChange, a, p, Category.assoc,
            MorphismProperty.Over.pullback_map_left, pullback.lift_snd]
      have hsub : Set.range (pullback.fst p (𝒰.f i)) ⊆
          Set.range ((etaleBaseChange f).map (a i)).left := by
        rw [← key]
        rintro _ ⟨x, rfl⟩
        exact ⟨_, (Scheme.Hom.comp_apply _ _ x).symm⟩
      refine Set.mem_iUnion.2 ⟨i, hsub ?_⟩
      rw [Scheme.Pullback.range_fst]
      exact ⟨v, hv⟩

instance isContinuous_etaleBaseChange :
    (etaleBaseChange f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_iff_coverPreserving.2 (coverPreserving_etaleBaseChange f)

/-- The direct image `f_*` of abelian sheaves on small étale sites. -/
noncomputable abbrev etalePushforward :
    Sheaf X.smallEtaleTopology Ab.{u} ⥤ Sheaf Y.smallEtaleTopology Ab.{u} :=
  (etaleBaseChange f).sheafPushforwardContinuous Ab.{u} _ _

/-- Base change restricted to the affine étale site of `Y`. -/
noncomputable def affineEtaleBaseChange : Y.AffineEtale ⥤ X.Etale :=
  AffineEtale.Spec Y ⋙ etaleBaseChange f

instance : (affineEtaleBaseChange f).IsContinuous (AffineEtale.topology Y)
    X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

instance (F : (Y.AffineEtale)ᵒᵖ ⥤ Ab.{u}) :
    (affineEtaleBaseChange f).op.HasLeftKanExtension F := by
  have : ∀ V, HasColimitsOfShape (CostructuredArrow (affineEtaleBaseChange f).op V) Ab.{u} :=
    fun V ↦ hasColimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

instance : ((affineEtaleBaseChange f).sheafPushforwardContinuous Ab.{u}
    (AffineEtale.topology Y) X.smallEtaleTopology).IsRightAdjoint := inferInstance

instance : (etalePushforward f).IsRightAdjoint := by
  let ι := (AffineEtale.Spec Y).sheafPushforwardContinuous Ab.{u}
    (AffineEtale.topology Y) Y.smallEtaleTopology
  let e : etalePushforward f ≅ (affineEtaleBaseChange f).sheafPushforwardContinuous Ab.{u}
      (AffineEtale.topology Y) X.smallEtaleTopology ⋙ ι.inv :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ ι.asEquivalence.unitIso ≪≫
      (Iso.refl _)
  exact Functor.isRightAdjoint_of_iso e.symm

/-- The inverse image `f⁻¹` of abelian sheaves on small étale sites, the left adjoint of the
direct image `etalePushforward f`. -/
noncomputable abbrev etaleInverseImage :
    Sheaf Y.smallEtaleTopology Ab.{u} ⥤ Sheaf X.smallEtaleTopology Ab.{u} :=
  (etaleBaseChange f).sheafPullback Ab.{u} _ _

/-- Base change sends the terminal object `Y` of `Y.Etale` to a terminal object of `X.Etale`. -/
noncomputable def isTerminalEtaleBaseChangeObj :
    IsTerminal ((etaleBaseChange f).obj (MorphismProperty.Over.mk ⊤ (𝟙 Y)
      (MorphismProperty.id_mem (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) Y))) :=
  IsTerminal.isTerminalObj _ _ (MorphismProperty.Over.mkIdTerminal _ Y)

/-- Global sections of a direct image are the global sections on `X`. -/
noncomputable def etalePushforwardCompΓ :
    etalePushforward f ⋙ Sheaf.Γ Y.smallEtaleTopology Ab.{u} ≅
      Sheaf.Γ X.smallEtaleTopology Ab.{u} :=
  Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections _ _ (MorphismProperty.Over.mkIdTerminal _ Y)) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleBaseChangeObj f)).symm

/-- The inverse image of a constant sheaf is the constant sheaf with the same value: both are
left adjoint to global sections on `X`. -/
noncomputable def constantSheafCompEtaleInverseImageIso :
    constantSheaf Y.smallEtaleTopology Ab.{u} ⋙ etaleInverseImage f ≅
      constantSheaf X.smallEtaleTopology Ab.{u} :=
  Adjunction.leftAdjointUniq
    (((constantSheafΓAdj _ _).comp (Functor.sheafAdjunctionContinuous _ _ _ _)).ofNatIsoRight
      (etalePushforwardCompΓ f))
    (constantSheafΓAdj _ _)

section Points

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- The fiber functor of the geometric point `s ≫ f` of `Y` is the fiber functor of the
geometric point `s` of `X` composed with base change. -/
noncomputable def pointSmallEtaleFiberIso :
    (pointSmallEtale (s ≫ f)).fiber ≅ etaleBaseChange f ⋙ (pointSmallEtale s).fiber :=
  Functor.isoWhiskerLeft (Etale.forget Y)
    ((CategoryTheory.Over.mapPullbackAdj f).compCoyonedaIso.app
      (Opposite.op (CategoryTheory.Over.mk s)))

instance : InitiallySmall.{u} (etaleBaseChange f ⋙ (pointSmallEtale s).fiber).Elements :=
  haveI : InitiallySmall.{u} (Functor.elementsFunctor.obj (pointSmallEtale (s ≫ f)).fiber) :=
    (pointSmallEtale (s ≫ f)).initiallySmall
  initiallySmall_of_initial_of_initiallySmall
    (Cat.equivOfIso (Functor.elementsFunctor.mapIso (pointSmallEtaleFiberIso f s))).functor

/-- At a geometric point of `X`, the stalk of the inverse image of a monomorphism is a
monomorphism. -/
lemma mono_sheafFiber_map_etaleInverseImage_map {F G : Sheaf Y.smallEtaleTopology Ab.{u}}
    (g : F ⟶ G) [Mono g] :
    Mono ((pointSmallEtale s).sheafFiber.map ((etaleInverseImage f).map g)) := by
  let e := (pointSmallEtale s).sheafFiberComapIso (etaleBaseChange f)
    (coverPreserving_etaleBaseChange f) Ab.{u}
  exact ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso e).app (Arrow.mk g))).1
      (inferInstanceAs (Mono (((pointSmallEtale s).comap (etaleBaseChange f)
        (coverPreserving_etaleBaseChange f)).sheafFiber.map g)))

end Points

/-- The inverse image of abelian sheaves on small étale sites preserves monomorphisms. -/
instance : (etaleInverseImage f).PreservesMonomorphisms where
  preserves {F G} g _ := by
    exact @JointlyReflectMonomorphisms.mono _ _ _ _ _ _
      ((isConservativeFamilyOfPoints_pointSmallEtale' X).jointlyReflectMonomorphisms Ab.{u})
      _ _ _ (by
        rintro ⟨_, ⟨x⟩⟩
        exact mono_sheafFiber_map_etaleInverseImage_map f _ g)

instance : (etaleInverseImage f).IsLeftAdjoint :=
  (Functor.sheafAdjunctionContinuous _ _ _ _).isLeftAdjoint

instance : (etaleInverseImage f).Additive := by
  have : PreservesBinaryBiproducts (etaleInverseImage f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

instance : (etalePushforward f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse image is exact: it preserves monomorphisms and, as a left adjoint, cokernels. -/
instance : (etaleInverseImage f).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

end AlgebraicGeometry.Scheme
