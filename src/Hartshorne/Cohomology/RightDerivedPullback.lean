/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ResolutionToInjectiveComplex
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Maps of right derived functors along a direct image

This file packages the homological algebra behind the pullback maps of sheaf cohomology.
Let `P : D ⥤ C` be an additive functor between abelian categories with enough injectives which
preserves injective objects (a direct image functor `f_*`), and let `ΓC : C ⥤ A`, `ΓD : D ⥤ A`
be additive functors with an isomorphism `e : P ⋙ ΓC ≅ ΓD` (global sections of a direct image
are global sections).  For objects `F : C`, `G : D` and a morphism `α : F ⟶ P G`, choose
injective resolutions `F ⟶ I•` and `G ⟶ J•`.  Since `P J•` is a complex of injectives, `α`
extends to a cochain map `I• ⟶ P J•`, unique up to homotopy, and applying `ΓC` and `e` gives a
cochain map `ΓC I• ⟶ ΓD J•`.  Its effect on cohomology is

`pullback e α n : R^n ΓC F ⟶ R^n ΓD G`.

We show that it does not depend on the extension, that it is natural in `F` and in `G`, that it
is compatible with composition of direct images, and that for a direct image isomorphic to the
identity it is the map induced by `α` itself.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne.RightDerivedPullback

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
  {A : Type u₃} [Category.{v₃} A] [Abelian A]

section Basic

variable (P : D ⥤ C) [P.Additive] [P.PreservesInjectiveObjects]

instance injective_mapHomologicalComplex_obj_X {G : D} (I : InjectiveResolution G) (n : ℕ) :
    Injective (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).X n) :=
  P.injective_obj_of_injective (I.injective n)

/-- A chosen cochain map from the injective resolution of `F` to the image under `P` of the
injective resolution of `G`, extending `α : F ⟶ P G` in degree `0`. -/
def pullbackCochainMap {F : C} {G : D} (α : F ⟶ P.obj G) :
    (injectiveResolution F).cocomplex ⟶
      (P.mapHomologicalComplex _).obj (injectiveResolution G).cocomplex :=
  ResolutionToInjectiveComplex.extend (injectiveResolution F).ι
    ((CochainComplex.fromSingle₀Equiv _ F).symm
      ⟨α ≫ P.map ((injectiveResolution G).ι.f 0), by
        rw [Functor.mapHomologicalComplex_obj_d, Category.assoc, ← P.map_comp,
          InjectiveResolution.ι_f_zero_comp_complex_d, P.map_zero, comp_zero]⟩)

@[reassoc (attr := simp)]
theorem ι_f_zero_comp_pullbackCochainMap_f_zero {F : C} {G : D} (α : F ⟶ P.obj G) :
    (injectiveResolution F).ι.f 0 ≫ (pullbackCochainMap P α).f 0 =
      α ≫ P.map ((injectiveResolution G).ι.f 0) := by
  unfold pullbackCochainMap
  rw [← HomologicalComplex.comp_f, ResolutionToInjectiveComplex.comp_extend]
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

variable {P} {ΓC : C ⥤ A} {ΓD : D ⥤ A} [ΓC.Additive] [ΓD.Additive] (e : P ⋙ ΓC ≅ ΓD)

/-- The cochain map `ΓC I• ⟶ ΓD J•` obtained from a cochain map `I• ⟶ P J•`. -/
abbrev globalCochainMap {K : CochainComplex C ℕ} {L : CochainComplex D ℕ}
    (ψ : K ⟶ (P.mapHomologicalComplex _).obj L) :
    (ΓC.mapHomologicalComplex _).obj K ⟶ (ΓD.mapHomologicalComplex _).obj L :=
  (ΓC.mapHomologicalComplex _).map ψ ≫ (Functor.mapHomologicalComplexCompIso e _).hom.app L

/-- The map `R^n ΓC F ⟶ R^n ΓD G` induced by `α : F ⟶ P G`. -/
def pullback {F : C} {G : D} (α : F ⟶ P.obj G) (n : ℕ) :
    (ΓC.rightDerived n).obj F ⟶ (ΓD.rightDerived n).obj G :=
  ((injectiveResolution F).isoRightDerivedObj ΓC n).hom ≫
    (HomologicalComplex.homologyFunctor _ _ n).map (globalCochainMap e (pullbackCochainMap P α)) ≫
    ((injectiveResolution G).isoRightDerivedObj ΓD n).inv

/-- The map `pullback e α n` may be computed with any cochain map extending `α`. -/
theorem pullback_eq {F : C} {G : D} (α : F ⟶ P.obj G) (n : ℕ)
    (ψ : (injectiveResolution F).cocomplex ⟶
      (P.mapHomologicalComplex _).obj (injectiveResolution G).cocomplex)
    (hψ : (injectiveResolution F).ι.f 0 ≫ ψ.f 0 = α ≫ P.map ((injectiveResolution G).ι.f 0)) :
    pullback e α n =
      ((injectiveResolution F).isoRightDerivedObj ΓC n).hom ≫
        (HomologicalComplex.homologyFunctor _ _ n).map (globalCochainMap e ψ) ≫
        ((injectiveResolution G).isoRightDerivedObj ΓD n).inv := by
  have h : Homotopy (pullbackCochainMap P α) ψ :=
    ResolutionToInjectiveComplex.homotopy (injectiveResolution F).ι _ _ (by
      ext
      simp only [HomologicalComplex.comp_f, ι_f_zero_comp_pullbackCochainMap_f_zero, hψ])
  unfold pullback
  congr 2
  simpa only [HomologicalComplex.homologyFunctor_map] using
    ((ΓC.mapHomotopy h).compRight _).homologyMap_eq n

/-- Naturality of `pullback` in the source object. -/
theorem rightDerived_map_comp_pullback {F' F : C} {G : D} (u : F' ⟶ F) (α : F ⟶ P.obj G)
    (n : ℕ) :
    (ΓC.rightDerived n).map u ≫ pullback e α n = pullback e (u ≫ α) n := by
  rw [ΓC.rightDerived_map_eq n u (P := injectiveResolution F') (Q := injectiveResolution F)
      (InjectiveResolution.desc u _ _) (InjectiveResolution.desc_commutes _ _ _),
    pullback_eq e (u ≫ α) n (InjectiveResolution.desc u _ _ ≫ pullbackCochainMap P α)
      (by simp [reassoc_of% InjectiveResolution.desc_commutes_zero])]
  unfold pullback
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.comp_map, globalCochainMap,
    Functor.map_comp]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] [P.PreservesInjectiveObjects] in
theorem globalCochainMap_comp_map {K : CochainComplex C ℕ} {L L' : CochainComplex D ℕ}
    (ψ : K ⟶ (P.mapHomologicalComplex _).obj L) (φ : L ⟶ L') :
    globalCochainMap e ψ ≫ (ΓD.mapHomologicalComplex _).map φ =
      globalCochainMap e (ψ ≫ (P.mapHomologicalComplex _).map φ) := by
  ext k
  have h := e.hom.naturality (φ.f k)
  simp only [Functor.comp_map] at h
  simp [h]

/-- Naturality of `pullback` in the target object. -/
theorem pullback_comp_rightDerived_map {F : C} {G G' : D} (α : F ⟶ P.obj G) (v : G ⟶ G')
    (n : ℕ) :
    pullback e α n ≫ (ΓD.rightDerived n).map v = pullback e (α ≫ P.map v) n := by
  rw [ΓD.rightDerived_map_eq n v (P := injectiveResolution G) (Q := injectiveResolution G')
      (InjectiveResolution.desc v _ _) (InjectiveResolution.desc_commutes _ _ _),
    pullback_eq e (α ≫ P.map v) n
      (pullbackCochainMap P α ≫ (P.mapHomologicalComplex _).map (InjectiveResolution.desc v _ _))
      (by simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
            ι_f_zero_comp_pullbackCochainMap_f_zero_assoc, Category.assoc, ← P.map_comp,
            InjectiveResolution.desc_commutes_zero])]
  unfold pullback
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.comp_map]
  rw [← Functor.map_comp_assoc, globalCochainMap_comp_map]

end Basic

section Composition

variable {B : Type u₄} [Category.{v₄} B] [Abelian B] [HasInjectiveResolutions B]
  {P : D ⥤ C} [P.Additive] [P.PreservesInjectiveObjects]
  {P' : C ⥤ B} [P'.Additive] [P'.PreservesInjectiveObjects]
  {P'' : D ⥤ B} [P''.Additive] [P''.PreservesInjectiveObjects]
  {ΓB : B ⥤ A} {ΓC : C ⥤ A} {ΓD : D ⥤ A} [ΓB.Additive] [ΓC.Additive] [ΓD.Additive]
  (e : P ⋙ ΓC ≅ ΓD) (e' : P' ⋙ ΓB ≅ ΓC) (e'' : P'' ⋙ ΓB ≅ ΓD) (m : P ⋙ P' ≅ P'')

/-- Composition law: if the isomorphism `m : P ⋙ P' ≅ P''` of direct images is compatible with
the identifications of global sections, then the composite of the maps induced by
`β : H ⟶ P' F` and `α : F ⟶ P G` is the map induced by `β ≫ P' α ≫ m`. -/
theorem pullback_comp_pullback
    (hm : ∀ J : D, e'.hom.app (P.obj J) ≫ e.hom.app J = ΓB.map (m.hom.app J) ≫ e''.hom.app J)
    {H : B} {F : C} {G : D} (β : H ⟶ P'.obj F) (α : F ⟶ P.obj G) (n : ℕ) :
    pullback e' β n ≫ pullback e α n = pullback e'' (β ≫ P'.map α ≫ m.hom.app G) n := by
  have hcomp : (injectiveResolution H).ι.f 0 ≫ (pullbackCochainMap P' β ≫
      (P'.mapHomologicalComplex _).map (pullbackCochainMap P α) ≫
        (Functor.mapHomologicalComplexCompIso m _).hom.app _).f 0 =
      (β ≫ P'.map α ≫ m.hom.app G) ≫ P''.map ((injectiveResolution G).ι.f 0) := by
    have h := m.hom.naturality ((injectiveResolution G).ι.f 0)
    simp only [Functor.comp_map] at h
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f,
      ι_f_zero_comp_pullbackCochainMap_f_zero_assoc, Category.assoc]
    rw [← P'.map_comp_assoc, ι_f_zero_comp_pullbackCochainMap_f_zero, P'.map_comp,
      Category.assoc, h]
    rfl
  have key : globalCochainMap e' (pullbackCochainMap P' β) ≫
      globalCochainMap e (pullbackCochainMap P α) =
      globalCochainMap e'' (pullbackCochainMap P' β ≫
        (P'.mapHomologicalComplex _).map (pullbackCochainMap P α) ≫
          (Functor.mapHomologicalComplexCompIso m _).hom.app _) := by
    ext k
    have h1 := e'.hom.naturality ((pullbackCochainMap P α).f k)
    have h2 := hm ((injectiveResolution G).cocomplex.X k)
    simp only [Functor.comp_map, Functor.comp_obj] at h1 h2
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f, Category.assoc, ΓB.map_comp]
    rw [← reassoc_of% h1]
    exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) h2)
  rw [pullback_eq e'' _ n _ hcomp]
  unfold pullback
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, key]

end Composition

section Identity

variable {P : C ⥤ C} [P.Additive] [P.PreservesInjectiveObjects] {ΓC : C ⥤ A} [ΓC.Additive]
  (e : P ⋙ ΓC ≅ ΓC) (m : P ≅ 𝟭 C)

/-- Identity law: for a direct image isomorphic to the identity, compatibly with the
identification of global sections, the map induced by `α : F ⟶ P G` is the map of right
derived functors induced by `α` followed by the isomorphism `P G ≅ G`. -/
theorem pullback_eq_rightDerived_map (hm : ∀ J : C, e.hom.app J = ΓC.map (m.hom.app J))
    {F G : C} (α : F ⟶ P.obj G) (n : ℕ) :
    pullback e α n = (ΓC.rightDerived n).map (α ≫ m.hom.app G) := by
  let g : (injectiveResolution F).cocomplex ⟶ (injectiveResolution G).cocomplex :=
    pullbackCochainMap P α ≫ (NatTrans.mapHomologicalComplex m.hom _).app _ ≫
      (Functor.mapHomologicalComplexIdIso C _).hom.app _
  have hg : (injectiveResolution F).ι ≫ g =
      (CochainComplex.single₀ C).map (α ≫ m.hom.app G) ≫ (injectiveResolution G).ι := by
    ext
    simp [g]
  have key : globalCochainMap e (pullbackCochainMap P α) = (ΓC.mapHomologicalComplex _).map g := by
    ext k
    simp [g, hm]
    erw [ΓC.map_id, Category.comp_id]
  rw [ΓC.rightDerived_map_eq n _ g hg]
  unfold pullback
  rw [key]
  rfl

end Identity

end Hartshorne.RightDerivedPullback
