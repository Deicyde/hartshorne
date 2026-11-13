/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtRestrict

/-!
# Right derived functors and exact functors: computation with any injective resolution

Let `Φ : C ⥤ D` be an exact functor between abelian categories preserving injective objects, and
`e : H ⋙ Φ ≅ Φ ⋙ H'`. The isomorphism `Φ(RⁿH(G)) ≅ RⁿH'(Φ(G))` of
`Hartshorne.RightDerivedComp.rightDerivedCompIso` is built from the chosen injective resolution of
`G`. Here it is computed from an arbitrary injective resolution `I` of `G`
(`Hartshorne.RightDerivedComp.rightDerivedCompIso_eq_ofResolution`): it is
`Φ(RⁿH(G)) ≅ Φ(hⁿ(H(I))) ≅ hⁿ(H'(Φ(I))) ≅ RⁿH'(Φ(G))`, where `Φ(I)` is the image injective
resolution of `Φ(G)`. In particular this applies to `Hartshorne.Ringed.sheafExtRestrictIso`
(`Hartshorne.Ringed.sheafExtRestrictIso_eq_ofResolution`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace RightDerivedComp

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {Φ : C ⥤ D} [Φ.Additive] [Φ.PreservesHomology]
  (hΦ : ∀ I : C, Injective I → Injective (Φ.obj I))
  [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  {H : C ⥤ C} [H.Additive] {H' : D ⥤ D} [H'.Additive] (e : H ⋙ Φ ≅ Φ ⋙ H')

/-- The isomorphism `Φ(RⁿH(G)) ≅ RⁿH'(Φ(G))` computed from an injective resolution `I` of `G`:
`Φ(RⁿH(G)) ≅ Φ(hⁿ(H(I))) ≅ hⁿ(H'(Φ(I))) ≅ RⁿH'(Φ(G))`. -/
noncomputable def rightDerivedCompIsoOfResolution {G : C} (I : InjectiveResolution G) (n : ℕ) :
    Φ.obj ((H.rightDerived n).obj G) ≅ (H'.rightDerived n).obj (Φ.obj G) :=
  Φ.mapIso (I.isoRightDerivedObj H n) ≪≫ (homologyCompIso e n).app I.cocomplex ≪≫
    ((mapInjectiveResolution hΦ I).isoRightDerivedObj H' n).symm

/-- Naturality of `rightDerivedCompIsoOfResolution`, for a chain map of injective resolutions over
a morphism `g : G ⟶ G'`. -/
lemma rightDerivedCompIsoOfResolution_hom_naturality {G G' : C} (g : G ⟶ G')
    (I : InjectiveResolution G) (I' : InjectiveResolution G') (φ : I.cocomplex ⟶ I'.cocomplex)
    (comm : I.ι.f 0 ≫ φ.f 0 = g ≫ I'.ι.f 0) (n : ℕ) :
    Φ.map ((H.rightDerived n).map g) ≫ (rightDerivedCompIsoOfResolution hΦ e I' n).hom =
      (rightDerivedCompIsoOfResolution hΦ e I n).hom ≫ (H'.rightDerived n).map (Φ.map g) := by
  have h1 := InjectiveResolution.isoRightDerivedObj_hom_naturality g I I' φ comm H n
  have h2 := (homologyCompIso e n).hom.naturality φ
  have hcc : (mapInjectiveResolution hΦ I).ι ≫ (Φ.mapHomologicalComplex _).map φ =
      (CochainComplex.single₀ D).map (Φ.map g) ≫ (mapInjectiveResolution hΦ I').ι := by
    have hφ : I.ι ≫ φ = (CochainComplex.single₀ C).map g ≫ I'.ι := by
      ext
      simpa using comm
    simp only [mapInjectiveResolution, Category.assoc, ← Functor.map_comp, hφ]
    rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _)
      ((HomologicalComplex.singleMapHomologicalComplex Φ _ 0).inv.naturality g).symm
  have hc : (mapInjectiveResolution hΦ I).ι.f 0 ≫ ((Φ.mapHomologicalComplex _).map φ).f 0 =
      Φ.map g ≫ (mapInjectiveResolution hΦ I').ι.f 0 := by
    rw [← HomologicalComplex.comp_f, hcc, HomologicalComplex.comp_f,
      CochainComplex.single₀_map_f_zero]
    rfl
  have h4 := InjectiveResolution.isoRightDerivedObj_hom_naturality (Φ.map g)
    (mapInjectiveResolution hΦ I) (mapInjectiveResolution hΦ I')
    ((Φ.mapHomologicalComplex _).map φ) hc H' n
  have h4' := (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 h4).trans (Category.assoc _ _ _))
  simp only [rightDerivedCompIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc]
  refine congrArg (_ ≫ ·) ?_
  rw [← Category.assoc]
  erw [h2]
  rw [Category.assoc]
  exact congrArg (_ ≫ ·) h4'.symm

/-- `rightDerivedCompIsoOfResolution` does not depend on the injective resolution. -/
lemma rightDerivedCompIsoOfResolution_eq {G : C} (I I' : InjectiveResolution G) (n : ℕ) :
    rightDerivedCompIsoOfResolution hΦ e I n = rightDerivedCompIsoOfResolution hΦ e I' n := by
  ext
  have h := rightDerivedCompIsoOfResolution_hom_naturality hΦ e (𝟙 G) I I'
    (InjectiveResolution.desc (𝟙 G) I' I) (InjectiveResolution.desc_commutes_zero _ _ _) n
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- **`rightDerivedCompIso` from any injective resolution.** -/
lemma rightDerivedCompIso_eq_ofResolution {G : C} (I : InjectiveResolution G) (n : ℕ) :
    rightDerivedCompIso hΦ e G n = rightDerivedCompIsoOfResolution hΦ e I n :=
  rightDerivedCompIsoOfResolution_eq hΦ e (injectiveResolution G) I n

end RightDerivedComp

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (U : Opens X)

attribute [local instance 2000] Abelian.toPreadditive

/-- `ℰxtⁿ_X(F, G)|_U ≅ ℰxtⁿ_U(F|_U, G|_U)` is the isomorphism of right derived functors given by
restriction to `U`. -/
lemma sheafExtRestrictIso_eq_rightDerivedCompIso (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (n : ℕ) :
    sheafExtRestrictIso U F G n = RightDerivedComp.rightDerivedCompIso (Φ := moduleRestrict U)
      (H := moduleSheafHomFunctor F) (H' := moduleSheafHomFunctor ((moduleRestrict U).obj F))
      (fun I _ => injective_moduleSheafRestrict_obj U (ringCatSheafOf R) I)
      (homRestrictIso U F) G n :=
  rfl

/-- **`ℰxtⁿ_X(F, G)|_U ≅ ℰxtⁿ_U(F|_U, G|_U)` from any injective resolution** `G ⟶ I^•`: it is
`ℰxtⁿ_X(F, G)|_U ≅ hⁿ(ℋom_X(F, I^•))|_U ≅ hⁿ(ℋom_U(F|_U, I^•|_U)) ≅ ℰxtⁿ_U(F|_U, G|_U)`. -/
lemma sheafExtRestrictIso_eq_ofResolution (F : SheafOfModules.{u} (ringCatSheafOf R))
    {G : SheafOfModules.{u} (ringCatSheafOf R)} (I : InjectiveResolution G) (n : ℕ) :
    sheafExtRestrictIso U F G n = RightDerivedComp.rightDerivedCompIsoOfResolution
      (Φ := moduleRestrict U) (H := moduleSheafHomFunctor F)
      (H' := moduleSheafHomFunctor ((moduleRestrict U).obj F))
      (fun I _ => injective_moduleSheafRestrict_obj U (ringCatSheafOf R) I)
      (homRestrictIso U F) I n :=
  RightDerivedComp.rightDerivedCompIso_eq_ofResolution _ _ I n

end Ringed

end Hartshorne
