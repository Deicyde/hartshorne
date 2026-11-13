/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulRegularImmersionTopExt
import Hartshorne.RingedSpace.SheafExtResolutionExactFunctor

/-!
# Restricting the sheafified Koszul resolution to an open subspace

Let `(X, 𝒪_X)` be a ringed space, `φ : A → 𝒪_X(X)` a ring map, `f₁, …, f_r ∈ A`, and `U ⊆ X` an
open subset. The restriction to `U` of the sheafified Koszul complex `𝒪_X ⊗_A K_•(f; A)` is the
sheafified Koszul complex `𝒪_U ⊗_A K_•(f; A)` of the subspace
(`Hartshorne.Ringed.KoszulSheaf.restrictComplexIso`). An augmentation `𝒪_X ⊗_A K_0 ⟶ F₀`
restricts to an augmentation of the latter (`Hartshorne.Ringed.KoszulSheaf.restrictAugmentation`),
which is a quasi-isomorphism when the original one is
(`Hartshorne.Ringed.KoszulSheaf.quasiIso_restrictAugmentation`). Hence the identification
`ℰxtⁱ(F₀, G) ≅ hⁱ(ℋom(𝒪_X ⊗_A K_•, G))` of Hartshorne III.6, Proposition 6.5, restricts to `U` as
the one computed with `𝒪_U ⊗_A K_•`
(`Hartshorne.Ringed.KoszulSheaf.sheafExtIsoHomology_restrict`).
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

/- The objects of `Φ(K)` for a complex `K` are only definitionally (not reducibly) the images of
the objects of `K`; rewriting along such identifications needs the default transparency. -/
set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Ringed

namespace KoszulSheaf

open Koszul ScalarExtension LocallyFreeResolutionExt

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {A : Type u} [CommRing A] (φ : A →+* R.obj.obj (op ⊤)) {r : ℕ} (f : Fin r → A)
  (U : Opens X)

/-- **The restricted Koszul complex**: `(𝒪_X ⊗_A K_•(f; A))|_U ≅ 𝒪_U ⊗_A K_•(f; A)`. -/
noncomputable def restrictComplexIso :
    complex (restrictBase φ U) f ≅
      ((moduleRestrict U).mapHomologicalComplex _).obj (complex φ f) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => @asIso _ _ _ _ (restrictSheafHom φ U ((K f).X p)) (isIso_restrictSheafHom φ U _))
    (fun i j _ => restrictSheafHom_naturality φ U ((K f).d i j))

@[simp]
lemma restrictComplexIso_hom_f (p : ℕ) :
    (restrictComplexIso φ f U).hom.f p = restrictSheafHom φ U ((K f).X p) := rfl

variable {F₀ : SheafOfModules.{u} (ringCatSheafOf R)} (ε : (complex φ f).X 0 ⟶ F₀)
  (hε : (complex φ f).d 1 0 ≫ ε = 0)

include hε in
lemma restrict_d_comp_ε :
    (complex (restrictBase φ U) f).d 1 0 ≫ restrictSheafHom φ U ((K f).X 0) ≫
      (moduleRestrict U).map ε = 0 := by
  have h := (restrictComplexIso φ f U).hom.comm 1 0
  calc _ = ((complex (restrictBase φ U) f).d 1 0 ≫ (restrictComplexIso φ f U).hom.f 0) ≫
        (moduleRestrict U).map ε := (Category.assoc _ _ _).symm
    _ = ((restrictComplexIso φ f U).hom.f 1 ≫ (moduleRestrict U).map ((complex φ f).d 1 0)) ≫
        (moduleRestrict U).map ε := by rw [← h]; rfl
    _ = 0 := by rw [Category.assoc, ← Functor.map_comp, hε, Functor.map_zero, comp_zero]

/-- The restricted augmentation `𝒪_U ⊗_A K_•(f; A) ⟶ F₀|_U[0]`. -/
noncomputable abbrev restrictAugmentation :
    complex (restrictBase φ U) f ⟶ (ChainComplex.single₀ _).obj ((moduleRestrict U).obj F₀) :=
  augmentation (restrictBase φ U) f (restrictSheafHom φ U ((K f).X 0) ≫ (moduleRestrict U).map ε)
    (restrict_d_comp_ε φ f U ε hε)

lemma restrictAugmentation_eq :
    restrictAugmentation φ f U ε hε = (restrictComplexIso φ f U).hom ≫
      ((moduleRestrict U).mapHomologicalComplex _).map (augmentation φ f ε hε) ≫
        (HomologicalComplex.singleMapHomologicalComplex (moduleRestrict U) _ 0).hom.app F₀ := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  rw [ChainComplex.toSingle₀Equiv_apply_coe, ChainComplex.toSingle₀Equiv_apply_coe,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  simp only [HomologicalComplex.comp_f, restrictComplexIso_hom_f,
    Functor.mapHomologicalComplex_map_f, ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  exact (congrArg (_ ≫ ·) (Category.comp_id _)).symm.trans (Category.assoc _ _ _).symm

instance quasiIso_restrictAugmentation [QuasiIso (augmentation φ f ε hε)] :
    QuasiIso (restrictAugmentation φ f U ε hε) := by
  rw [restrictAugmentation_eq]
  infer_instance

/-- **The Koszul resolution isomorphism restricted to an open subset.** For an augmentation
`𝒪_X ⊗_A K_•(f; A) ⟶ F₀[0]` that is a quasi-isomorphism, the restriction to `U` of
`ℰxtⁱ(F₀, G) ≅ hⁱ(ℋom(𝒪_X ⊗_A K_•, G))` is, through `ℰxtⁱ_X(F₀, G)|_U ≅ ℰxtⁱ_U(F₀|_U, G|_U)` and
`ℋom_X(-, G)|_U ≅ ℋom_U(-|_U, G|_U)`, the isomorphism computed with `𝒪_U ⊗_A K_•` followed by the
identification of the two complexes. -/
theorem sheafExtIsoHomology_restrict [QuasiIso (augmentation φ f ε hε)] (i : ℕ)
    (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    (sheafExtRestrictIso U F₀ G i).inv ≫
        (moduleRestrict U).map ((sheafExtIsoHomologyOfLocallyFreeResolution (complex φ f)
          (augmentation φ f ε hε) (isFiniteLocallyFree_complex φ f) i).hom.app G) ≫
          (homologyHomComplexRestrictIso U (complex φ f) G i).hom =
      (sheafExtIsoHomologyOfLocallyFreeResolution (complex (restrictBase φ U) f)
          (restrictAugmentation φ f U ε hε) (isFiniteLocallyFree_complex _ f) i).hom.app
          ((moduleRestrict U).obj G) ≫
        HomologicalComplex.homologyMap
          ((moduleSheafHomComplexMap (restrictComplexIso φ f U).inv).app _) i :=
  sheafExtIsoHomologyOfLocallyFreeResolution_restrict U _ _ _ _ _ _ (restrictComplexIso φ f U).inv
    (by
      change (restrictComplexIso φ f U).inv.f 0 ≫ (restrictComplexIso φ f U).hom.f 0 ≫
        (moduleRestrict U).map ε = (moduleRestrict U).map ε
      rw [← Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f,
        Category.id_comp]) i G

end KoszulSheaf

end Ringed

end Hartshorne
