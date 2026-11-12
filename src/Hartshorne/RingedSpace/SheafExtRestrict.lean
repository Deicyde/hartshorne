/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtLocallyFreeResolution
import Hartshorne.RingedSpace.ModuleGluing
import Mathlib.Topology.Sheaves.Module

/-!
# Sheaf Ext restricts to open subsets

Hartshorne, *Algebraic Geometry*, III.6, Proposition 6.2 (p. 234).

Let `(X, 𝒪_X)` be a ringed space, given by a sheaf `R` of commutative rings on a topological
space `X`, and let `U` be an open subset. The restricted structure sheaf `𝒪_U`
(`Hartshorne.Ringed.restrictRingSheaf`) is a sheaf of commutative rings on the subspace `U`, and
restriction `F ↦ F|_U` (`Hartshorne.Ringed.moduleRestrict`) sends `𝒪_X`-modules to
`𝒪_U`-modules. For `𝒪_X`-modules `F` and `G` we construct isomorphisms

`ℋom_X(F, G)|_U ≅ ℋom_U(F|_U, G|_U)`, natural in `G` (`Hartshorne.Ringed.homRestrictIso`),

`ℰxtⁿ_X(F, G)|_U ≅ ℰxtⁿ_U(F|_U, G|_U)` (`Hartshorne.Ringed.sheafExtRestrictIso`).

## Proof

For an open `W ⊆ U`, the opens of `U` contained in `W` and the opens of `X` contained in `W`
form equivalent sites, so module sheaves over them are equivalent; on sections over `W` this
identifies the morphisms `F|_W ⟶ G|_W` computed in `X` and in `U`, compatibly with restriction
and with the module structures. This gives the isomorphism of sheaf Homs.

Restriction to `U` is exact, being both a left adjoint (of the pushforward along the inclusion)
and a right adjoint (of the extension by zero), and it preserves injectives (Hartshorne III.6,
Lemma 6.1, `Hartshorne.injective_moduleSheafRestrict_obj`). Hence it carries an injective
resolution `G ⟶ I^•` to an injective resolution of `G|_U`, and commutes with taking cohomology
sheaves, so that `ℰxtⁿ_X(F, G)|_U = hⁿ(ℋom_X(F, I^•))|_U ≅ hⁿ(ℋom_U(F|_U, I^•|_U)) ≅
ℰxtⁿ_U(F|_U, G|_U)`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace Ringed

namespace SheafExtRestrict

variable {X : TopCat.{u}} (U : Opens X)

/-- The inclusion of the opens of `U` into the opens of `X`. -/
abbrev incl : Opens ((Opens.toTopCat X).obj U) ⥤ Opens X :=
  U.overEquivalence.inverse ⋙ Over.forget U

/-- The inclusion of the opens of `U` preserves covers. -/
lemma incl_coverPreserving :
    CoverPreserving (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      (Opens.grothendieckTopology X) (incl U) :=
  CoverPreserving.comp _ _ (Functor.IsDenseSubsite.coverPreserving
    (Opens.grothendieckTopology U)
    ((Opens.grothendieckTopology X).over U) U.overEquivalence.inverse)
    (GrothendieckTopology.over_forget_coverPreserving (Opens.grothendieckTopology X) U)

/-- The inclusion of the opens of `U` is cocontinuous. -/
instance : (incl U).IsCocontinuous (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    (Opens.grothendieckTopology X) where
  cover_lift hS := U.overEquivalence.inverse.cover_lift (Opens.grothendieckTopology U)
    ((Opens.grothendieckTopology X).over U)
    ((Over.forget U).cover_lift ((Opens.grothendieckTopology X).over U) _ hS)

/-- The inclusion of the opens of `U` is faithful. -/
instance : (incl U).Faithful := ⟨fun _ => Subsingleton.elim _ _⟩

/-- The inclusion of the opens of `U` is full. -/
instance : (incl U).Full where
  map_surjective {V V'} f := ⟨homOfLE (fun x hx => by
    obtain ⟨y, hy, hyx⟩ := leOfHom f ⟨x, hx, rfl⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy), Subsingleton.elim _ _⟩

variable {U} (W : Opens ((Opens.toTopCat X).obj U))

/-- The preimage in `U` of an open of `X` contained in the image of `W`. -/
def back : Over ((incl U).obj W) ⥤ Over W where
  obj B := Over.mk (Y := (Opens.map (TopCat.ofHom ⟨_, continuous_subtype_val⟩)).obj B.left)
    (homOfLE (fun x hx => by
      obtain ⟨y, hy, hyx⟩ := leOfHom B.hom hx
      have : y = x := Subtype.ext hyx
      exact this ▸ hy))
  map f := Over.homMk (homOfLE (fun x hx => leOfHom f.left hx))

/-- Every open of `X` contained in `W` is the image of an open of `U`. -/
instance : (Over.post (X := W) (incl U)).EssSurj where
  mem_essImage B := ⟨(back W).obj B, ⟨Over.isoMk (eqToIso (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx
      exact ⟨⟨x, ((leOfHom B.hom).trans (leOfHom (U.overEquivalence.inverse.obj W).hom)) hx⟩,
        hx, rfl⟩))⟩⟩

/-- The opens of `U` and of `X` contained in `W` correspond. -/
instance : (Over.post (X := W) (incl U)).IsEquivalence where

/-- The correspondence of opens contained in `W` identifies the two sites. -/
instance : (Over.post (X := W) (incl U)).IsDenseSubsite
    ((Opens.grothendieckTopology ((Opens.toTopCat X).obj U)).over W)
    ((Opens.grothendieckTopology X).over ((incl U).obj W)) where
  functorPushforward_mem_iff {A S} := by
    constructor
    · intro H
      refine GrothendieckTopology.superset_covering _ ?_
        ((Over.post (X := W) (incl U)).cover_lift _ _ H)
      rw [(Sieve.fullyFaithfulFunctorGaloisCoinsertion (Over.post (X := W) (incl U)) A).u_l_eq S]
    · intro H
      exact ((incl_coverPreserving U).overPost W).cover_preserve H

/-- The equivalence between the opens of `U` contained in `W` and the opens of `X` contained in
`W`. -/
noncomputable abbrev overEquiv : Over W ≌ Over ((incl U).obj W) :=
  (Over.post (X := W) (incl U)).asEquivalence

/-- The forward functor of `overEquiv` is continuous. -/
instance : (overEquiv W).functor.IsContinuous
    ((Opens.grothendieckTopology ((Opens.toTopCat X).obj U)).over W)
    ((Opens.grothendieckTopology X).over ((incl U).obj W)) :=
  inferInstanceAs ((Over.post (X := W) (incl U)).IsContinuous _ _)

/-- The inverse functor of `overEquiv` is continuous. -/
instance : (overEquiv W).inverse.IsContinuous
    ((Opens.grothendieckTopology X).over ((incl U).obj W))
    ((Opens.grothendieckTopology ((Opens.toTopCat X).obj U)).over W) := by
  have : (overEquiv W).symm.inverse.IsDenseSubsite
      ((Opens.grothendieckTopology ((Opens.toTopCat X).obj U)).over W)
      ((Opens.grothendieckTopology X).over ((incl U).obj W)) :=
    inferInstanceAs ((Over.post (X := W) (incl U)).IsDenseSubsite _ _)
  exact inferInstanceAs ((overEquiv W).symm.functor.IsContinuous _ _)

end SheafExtRestrict

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) (U : Opens X)

/-- The restriction `𝒪_U` of the structure sheaf to an open subset `U`, a sheaf of commutative
rings on the subspace `U`: its sections over an open of `U` are those of `𝒪_X` over the same
open. -/
noncomputable abbrev restrictRingSheaf :
    Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) CommRingCat.{u} :=
  (U.isOpenEmbedding.functor.sheafPushforwardContinuous CommRingCat.{u} _ _).obj R

namespace SheafExtRestrict

variable {U} (W : Opens ((Opens.toTopCat X).obj U))

open Functor in
/-- Module sheaves on the opens of `X` contained in an open `W ⊆ U` are module sheaves on the
opens of `U` contained in `W`. -/
noncomputable def overModuleEquiv :
    SheafOfModules.{u} ((ringCatSheafOf R).over ((incl U).obj W)) ≌
      SheafOfModules.{u} ((ringCatSheafOf (restrictRingSheaf R U)).over W) :=
  SheafOfModules.pushforwardPushforwardEquivalence (overEquiv W)
    (𝟙 ((ringCatSheafOf (restrictRingSheaf R U)).over W) : _ ⟶
      ((overEquiv W).functor.sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ((Opens.toTopCat X).obj U)).over W)
        ((Opens.grothendieckTopology X).over ((incl U).obj W))).obj
          ((ringCatSheafOf R).over ((incl U).obj W)))
    ⟨whiskerRight (NatTrans.op (overEquiv W).counit)
      ((ringCatSheafOf R).over ((incl U).obj W)).obj⟩
    (by ext : 2; rfl) (by
      ext A : 2
      refine (Category.id_comp _).trans ?_
      refine ((ringCatSheafOf R).obj.map_comp _ _).symm.trans ?_
      exact (ringCatSheafOf R).obj.map_id _)

end SheafExtRestrict

open SheafExtRestrict

variable {R}

/-- Restriction `F ↦ F|_U` of `𝒪_X`-modules to `𝒪_U`-modules on the subspace `U`. -/
noncomputable abbrev moduleRestrict :
    SheafOfModules.{u} (ringCatSheafOf R) ⥤
      SheafOfModules.{u} (ringCatSheafOf (restrictRingSheaf R U)) :=
  moduleSheafRestrict U (ringCatSheafOf R)

variable {U}

/-- On sections over an open `W ⊆ U`: a morphism `F|_W ⟶ G|_W` over the opens of `X` contained
in `W`, regarded as a morphism over the opens of `U` contained in `W`. -/
noncomputable def homRestrictApp (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (W : Opens ((Opens.toTopCat X).obj U)) :
    (F.over ((incl U).obj W) ⟶ G.over ((incl U).obj W)) →
      (((moduleRestrict U).obj F).over W ⟶ ((moduleRestrict U).obj G).over W) :=
  fun σ => (overModuleEquiv R W).functor.map σ

/-- On sections, `Hartshorne.Ringed.homRestrictApp` evaluates the morphism at the
corresponding open of `X`. -/
lemma homRestrictApp_app (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (W : Opens ((Opens.toTopCat X).obj U))
    (σ : F.over ((incl U).obj W) ⟶ G.over ((incl U).obj W))
    (A : (Over W)ᵒᵖ) (x : F.val.obj (op ((incl U).obj A.unop.left))) :
    (homRestrictApp F G W σ).val.app A x =
      σ.val.app (op ((Over.post (X := W) (incl U)).obj A.unop)) x := rfl

/-- `Hartshorne.Ringed.homRestrictApp` is bijective. -/
lemma homRestrictApp_bijective (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (W : Opens ((Opens.toTopCat X).obj U)) : Function.Bijective (homRestrictApp F G W) :=
  (overModuleEquiv R W).fullyFaithfulFunctor.map_bijective _ _

/-- The morphism `ℋom_X(F, G)|_U ⟶ ℋom_U(F|_U, G|_U)`: on sections over `W ⊆ U`, a morphism
`F|_W ⟶ G|_W` is regarded over the opens of `U`. -/
noncomputable def homRestrict (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    (moduleRestrict U).obj (moduleSheafHom F G) ⟶
      moduleSheafHom ((moduleRestrict U).obj F) ((moduleRestrict U).obj G) where
  val := PresheafOfModules.homMk
    { app W := AddCommGrpCat.ofHom
        { toFun := homRestrictApp F G W.unop
          map_zero' := by
            apply SheafOfModules.hom_ext
            ext A x
            rfl
          map_add' σ τ := by
            apply SheafOfModules.hom_ext
            ext A x
            rfl }
      naturality W W' i := by
        ext σ
        apply SheafOfModules.hom_ext
        ext A x
        rfl }
    (fun W r σ => by
      apply SheafOfModules.hom_ext
      ext A x
      exact (moduleSheafHomOver_smul_app F G _ r σ
          (op ((Over.post (X := W.unop) (incl U)).obj A.unop)) x).trans
        (moduleSheafHomOver_smul_app _ _ W.unop r (homRestrictApp F G W.unop σ) A x).symm)

/-- On sections over `W`, the comparison morphism is `Hartshorne.Ringed.homRestrictApp`. -/
lemma homRestrict_app_apply (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (W : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ)
    (σ : F.over ((incl U).obj W.unop) ⟶ G.over ((incl U).obj W.unop)) :
    (homRestrict F G).val.app W σ = homRestrictApp F G W.unop σ := rfl

/-- The comparison morphism `ℋom_X(F, G)|_U ⟶ ℋom_U(F|_U, G|_U)` is an isomorphism. -/
lemma isIso_homRestrict (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    IsIso (homRestrict (U := U) F G) := by
  refine ModuleGluing.isIso_of_bijective _ (fun W => ?_)
  have h : ⇑((homRestrict F G).val.app W) = homRestrictApp F G W.unop :=
    funext (homRestrict_app_apply F G W)
  rw [h]
  exact homRestrictApp_bijective F G W.unop

/-- The comparison morphism is natural in `G`. -/
lemma homRestrict_naturality (F : SheafOfModules.{u} (ringCatSheafOf R))
    {G G' : SheafOfModules.{u} (ringCatSheafOf R)} (g : G ⟶ G') :
    (moduleRestrict U).map ((moduleSheafHomFunctor F).map g) ≫ homRestrict F G' =
      homRestrict F G ≫ (moduleSheafHomFunctor ((moduleRestrict U).obj F)).map
        ((moduleRestrict U).map g) := by
  apply SheafOfModules.hom_ext
  ext W σ : 3
  apply SheafOfModules.hom_ext
  ext A x
  rfl

variable (U) in
/-- **Sheaf Hom commutes with restriction to an open subset**:
`ℋom_X(F, -)|_U ≅ ℋom_U(F|_U, (-)|_U)`. -/
noncomputable def homRestrictIso (F : SheafOfModules.{u} (ringCatSheafOf R)) :
    moduleSheafHomFunctor F ⋙ moduleRestrict U ≅
      moduleRestrict U ⋙ moduleSheafHomFunctor ((moduleRestrict U).obj F) :=
  NatIso.ofComponents
    (fun G => @asIso _ _ _ _ (homRestrict (U := U) F G) (isIso_homRestrict F G))
    (fun g => homRestrict_naturality (U := U) F g)

variable (U)

/-- Restriction to an open subset is left adjoint to the pushforward along the inclusion. -/
noncomputable def moduleRestrictAdjunction :
    moduleRestrict U ⊣ (U.sheafOfModulesEquivOver (ringCatSheafOf R)).inverse ⋙
      openPushforward (R := R) U :=
  (restrictionAdjunction U).comp (U.sheafOfModulesEquivOver (ringCatSheafOf R)).toAdjunction

/-- Restriction to an open subset preserves finite limits (it is a right adjoint). -/
instance : PreservesFiniteLimits (moduleRestrict (R := R) U) := by
  have : PreservesLimitsOfSize.{u, u} (moduleRestrict (R := R) U) :=
    (SheafOfModules.PullbackConstruction.adjunction.{u}
      (restrictedRingHom U (ringCatSheafOf R))).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits _

/-- Restriction to an open subset preserves finite colimits (it is a left adjoint). -/
instance : PreservesFiniteColimits (moduleRestrict (R := R) U) := by
  have : PreservesColimitsOfSize.{u, u} (moduleRestrict (R := R) U) :=
    (moduleRestrictAdjunction (R := R) U).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- Restriction to an open subset is additive. -/
instance : (moduleRestrict (R := R) U).Additive :=
  Functor.additive_of_preserves_binary_products _

section Ext

attribute [local instance 2000] Abelian.toPreadditive

variable {U}

/-- The restriction to `U` of an injective resolution of `G` is an injective resolution of
`G|_U`. -/
noncomputable abbrev restrictInjectiveResolution {G : SheafOfModules.{u} (ringCatSheafOf R)}
    (I : InjectiveResolution G) : InjectiveResolution ((moduleRestrict U).obj G) where
  cocomplex := ((moduleRestrict U).mapHomologicalComplex _).obj I.cocomplex
  injective n := injective_moduleSheafRestrict_obj U (ringCatSheafOf R) (I.cocomplex.X n)
  ι := (HomologicalComplex.singleMapHomologicalComplex (moduleRestrict U) _ 0).inv.app G ≫
    ((moduleRestrict U).mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

variable (U)

/-- **Sheaf Ext restricts to open subsets** (Hartshorne III.6, Proposition 6.2):
`ℰxtⁿ_X(F, G)|_U ≅ ℰxtⁿ_U(F|_U, G|_U)`. -/
noncomputable def sheafExtRestrictIso (F G : SheafOfModules.{u} (ringCatSheafOf R)) (n : ℕ) :
    (moduleRestrict U).obj ((sheafExt F n).obj G) ≅
      (sheafExt ((moduleRestrict U).obj F) n).obj ((moduleRestrict U).obj G) :=
  let I := injectiveResolution G
  let K := ((moduleSheafHomFunctor F).mapHomologicalComplex _).obj I.cocomplex
  (moduleRestrict U).mapIso (sheafExtIsoHomology F I n) ≪≫
    ((K.sc n).mapHomologyIso (moduleRestrict U)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).app I.cocomplex ≪≫
        (NatIso.mapHomologicalComplex (homRestrictIso U F) _).app I.cocomplex ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl _) _).app I.cocomplex).symm) ≪≫
    (sheafExtIsoHomology _ (restrictInjectiveResolution I) n).symm

end Ext

end Ringed

end Hartshorne
