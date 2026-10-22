/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.OpenExtensionByZeroAdjunction
import Hartshorne.Scheme.RestrictionStalk
import Batteries.Tactic.OpenPrivate

/-!
# Restriction, stalks, and compatible uniqueness of open extension by zero

The objects are the original conditional-presheaf/sheafification construction of
Hartshorne II.1, Exercise 1.19(b). The restriction comparison is fixed by the
canonical adjunction unit before any candidate or restriction marking is chosen.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hartshorne

universe u

set_option backward.isDefEq.respectTransparency false in
/-- Restriction to image opens preserves stalks naturally in the entire presheaf. -/
private noncomputable def openRestrictionStalkNatIso {X : TopCat.{u}} (U : Opens X)
    (x : U) :
    (Functor.whiskeringLeft (Opens (TopCat.of U))ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
        U.isOpenEmbedding.functor.op ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x ≅
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X) := by
  letI := Functor.initial_of_adjunction
    (U.isOpenEmbedding.adjunctionNhds (f := U.inclusion') x)
  exact Functor.isoWhiskerLeft
    ((Functor.whiskeringLeft (OpenNhds (x : X))ᵒᵖ (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj
      (OpenNhds.inclusion (x : X)).op)
    (Functor.Final.colimIso (U.isOpenEmbedding.functorNhds x).op)

set_option backward.isDefEq.respectTransparency false in
/-- The general sheafification unit stays invertible on stalks after open restriction. -/
private theorem openWhisker_stalkUnit_isIso {X : TopCat.{u}} (U : Opens X)
    (P : X.Presheaf AddCommGrpCat.{u}) (x : U) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (Functor.whiskerLeft U.isOpenEmbedding.functor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P))) := by
  let e := openRestrictionStalkNatIso U x
  let η := CategoryTheory.toSheafify (Opens.grothendieckTopology X) P
  let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (x : X) AddCommGrpCat.{u} P
  have h : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (Functor.whiskerLeft U.isOpenEmbedding.functor.op η) =
      (e.app P).hom ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map η ≫
        (e.app (CategoryTheory.sheafify (Opens.grothendieckTopology X) P)).inv := by
    apply (cancel_mono
      (e.app (CategoryTheory.sheafify (Opens.grothendieckTopology X) P)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact e.hom.naturality η
  rw [h]
  infer_instance

/-- The fixed canonical map, expressed in image-open restriction rather than native pullback. -/
private noncomputable def openZeroNaiveUnit {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    F ⟶ (U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj
      (openExtensionByZero U F) :=
  openExtensionByZeroCanonicalRestriction U F (openExtensionByZero U F) (𝟙 _) ≫
    ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app
      (openExtensionByZero U F)).hom

open private openZeroSeedIso from Hartshorne.Scheme.OpenExtensionByZeroAdjunction

set_option backward.isDefEq.respectTransparency false in
/-- The fixed naive-restriction unit is invertible by the sheaf-only stalk criterion. -/
private theorem openZeroNaiveUnit_isIso {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) : IsIso (openZeroNaiveUnit U F) := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso (openZeroNaiveUnit U F)).2
  intro x
  simp only [openZeroNaiveUnit, openExtensionByZeroCanonicalRestriction,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((openZeroSeedIso U F).hom ≫ Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (openExtensionByZeroPresheaf U F))))
  rw [CategoryTheory.Functor.map_comp]
  let := openWhisker_stalkUnit_isIso U (openExtensionByZeroPresheaf U F) x
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The ACTUAL canonical adjunction unit is invertible, using the proved naive unit. -/
private theorem openZero_unit_isIso {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    IsIso ((openExtensionByZeroAdjunction U).unit.app F) := by
  have h : openZeroNaiveUnit U F = (openExtensionByZeroAdjunction U).unit.app F ≫
      ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app
        (openExtensionByZero U F)).hom := by
    unfold openZeroNaiveUnit
    rw [← openExtensionByZeroAdjunction_homEquiv U F (openExtensionByZero U F) (𝟙 _)]
    erw [(openExtensionByZeroAdjunction U).homEquiv_id F]
  have h' : (openExtensionByZeroAdjunction U).unit.app F = openZeroNaiveUnit U F ≫
      ((U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app
        (openExtensionByZero U F)).inv := by
    rw [h]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let := openZeroNaiveUnit_isIso U F
  rw [h']
  infer_instance

/-- Canonical open restriction is the inverse of the proved canonical adjunction unit.
Its choice is independent of any candidate sheaf or restriction marking. -/
noncomputable def openExtensionByZeroRestrictionIso {X : TopCat.{u}} (U : Opens X) :
    openExtensionByZeroFunctor U ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion' ≅
      𝟭 ((TopCat.of U).Sheaf AddCommGrpCat.{u}) := by
  letI : ∀ F, IsIso ((openExtensionByZeroAdjunction U).unit.app F) :=
    fun F => openZero_unit_isIso U F
  letI : IsIso (openExtensionByZeroAdjunction U).unit :=
    NatIso.isIso_of_isIso_app _
  exact (asIso (openExtensionByZeroAdjunction U).unit).symm

/-- The inverse restriction map is the fixed original canonical adjunction unit. -/
theorem openExtensionByZeroRestrictionIso_inv_app {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    (openExtensionByZeroRestrictionIso U).inv.app F =
      (openExtensionByZeroAdjunction U).unit.app F := rfl

/-- On the open subspace, the original extension-by-zero stalk is canonically the source stalk. -/
noncomputable def openExtensionByZeroStalkIso {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (x : U) :
    (openExtensionByZero U F).presheaf.stalk (x : X) ≅ F.presheaf.stalk x :=
  (restrictionStalkIso U.inclusion' (openExtensionByZero U F) x).symm ≪≫
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of U) AddCommGrpCat.{u} x).mapIso
      ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).mapIso
        ((openExtensionByZeroRestrictionIso U).app F))

open private openZeroOutside_eq_zero from Hartshorne.Scheme.OpenExtensionByZeroAdjunction

/-- Every actual germ of the original conditional presheaf is zero outside the open. -/
private theorem openZeroRawStalk_eq_zero {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∉ U)
    (t : (openExtensionByZeroPresheaf U F).stalk x) : t = 0 := by
  obtain ⟨V, hV, s, rfl⟩ := (openExtensionByZeroPresheaf U F).exists_germ_eq t
  have hs : s = 0 := openZeroOutside_eq_zero U F V (fun h => hx (h hV)) s
  rw [hs, map_zero]

/-- The original sheafified extension has a genuine zero stalk outside the open. -/
theorem openExtensionByZero_stalk_isZero_of_not_mem {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∉ U) :
    IsZero ((openExtensionByZero U F).presheaf.stalk x) := by
  let P := openExtensionByZeroPresheaf U F
  let : Subsingleton (P.stalk x) :=
    ⟨fun a b => (openZeroRawStalk_eq_zero U F x hx a).trans
      (openZeroRawStalk_eq_zero U F x hx b).symm⟩
  have hP : IsZero (P.stalk x) := by
    rw [IsZero.iff_id_eq_zero]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro t
    exact Subsingleton.elim _ _
  let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P
  exact hP.of_iso
    (asIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P))).symm

set_option backward.isDefEq.respectTransparency false in
/-- An invertible native restriction map gives invertible stalk maps at inside points,
by the proved natural comparisons, not by global faithfulness of restriction. -/
private theorem openStalk_map_isIso_of_pullback_map_isIso {X : TopCat.{u}} (U : Opens X)
    {G H : X.Sheaf AddCommGrpCat.{u}} (φ : G ⟶ H) (x : U)
    [IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map φ)] :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (x : X)).map φ.hom) := by
  let : IsIso ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).map φ) :=
    (NatIso.isIso_map_iff (U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}) φ).mp
      inferInstance
  apply (NatIso.isIso_map_iff (openRestrictionStalkNatIso U x) φ.hom).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor (X := TopCat.of U) AddCommGrpCat.{u} x).map
    (((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).map φ).hom))
  infer_instance

/-- Invertible restriction detects maps from old extension by zero into a sheaf
whose actual stalks vanish outside the open. -/
private theorem openZeroHom_isIso_of_restriction {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
    (hG : ∀ x : X, x ∉ U → IsZero (G.presheaf.stalk x))
    (φ : openExtensionByZero U F ⟶ G)
    [IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map φ)] : IsIso φ := by
  apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso φ).2
  intro x
  by_cases hx : x ∈ U
  · exact openStalk_map_isIso_of_pullback_map_isIso U φ ⟨x, hx⟩
  · exact (openExtensionByZero_stalk_isZero_of_not_mem U F x hx).isIso (hG x hx)
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom)

/-- The actual morphism determined by a fixed native restriction marking. -/
private noncomputable def openZeroMarkedHom {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
    (ρ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj G ≅ F) :
    openExtensionByZero U F ⟶ G :=
  ((openExtensionByZeroAdjunction U).homEquiv F G).symm ρ.inv

set_option backward.isDefEq.respectTransparency false in
/-- The marked morphism satisfies the exact fixed-marking compatibility. -/
private theorem openZeroMarkedHom_comp {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
    (ρ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj G ≅ F) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map (openZeroMarkedHom U F G ρ) ≫
        ρ.hom = (openExtensionByZeroRestrictionIso U).hom.app F := by
  have h : (openExtensionByZeroAdjunction U).unit.app F ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map
        (openZeroMarkedHom U F G ρ) = ρ.inv := by
    simpa only [openZeroMarkedHom, Adjunction.homEquiv_apply] using
      ((openExtensionByZeroAdjunction U).homEquiv F G).apply_symm_apply ρ.inv
  let := openZero_unit_isIso U F
  apply (cancel_epi ((openExtensionByZeroAdjunction U).unit.app F)).1
  change (openExtensionByZeroAdjunction U).unit.app F ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map
        (openZeroMarkedHom U F G ρ) ≫ ρ.hom =
      ((openExtensionByZeroRestrictionIso U).app F).inv ≫
        ((openExtensionByZeroRestrictionIso U).app F).hom
  erw [← Category.assoc, h]
  exact ρ.inv_hom_id.trans ((openExtensionByZeroRestrictionIso U).app F).inv_hom_id.symm

set_option backward.isDefEq.respectTransparency false in
/-- The marked morphism is an isomorphism for every target with zero outside stalks. -/
private theorem openZeroMarkedHom_isIso {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
    (hG : ∀ x : X, x ∉ U → IsZero (G.presheaf.stalk x))
    (ρ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj G ≅ F) :
    IsIso (openZeroMarkedHom U F G ρ) := by
  have h : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map
      (openZeroMarkedHom U F G ρ) = (openExtensionByZeroRestrictionIso U).hom.app F ≫
        ρ.inv := by
    apply (cancel_mono ρ.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact openZeroMarkedHom_comp U F G ρ
  let : IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map
      (openZeroMarkedHom U F G ρ)) := by
    rw [h]
    infer_instance
  exact openZeroHom_isIso_of_restriction U F G hG (openZeroMarkedHom U F G ρ)

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-marking compatibility determines the morphism by the genuine Hom equivalence. -/
private theorem openZeroHom_eq_marked_of_comp {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
    (ρ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj G ≅ F)
    (φ : openExtensionByZero U F ⟶ G)
    (hφ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map φ ≫ ρ.hom =
      (openExtensionByZeroRestrictionIso U).hom.app F) : φ = openZeroMarkedHom U F G ρ := by
  apply ((openExtensionByZeroAdjunction U).homEquiv F G).injective
  change (openExtensionByZeroAdjunction U).homEquiv F G φ =
    ((openExtensionByZeroAdjunction U).homEquiv F G)
      (((openExtensionByZeroAdjunction U).homEquiv F G).symm ρ.inv)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_apply]
  apply (cancel_mono ρ.hom).1
  erw [Category.assoc, hφ]
  change ((openExtensionByZeroRestrictionIso U).app F).inv ≫
      ((openExtensionByZeroRestrictionIso U).app F).hom = ρ.inv ≫ ρ.hom
  exact ((openExtensionByZeroRestrictionIso U).app F).inv_hom_id.trans ρ.inv_hom_id.symm

/-- A fixed native restriction marking determines a unique compatible isomorphism
from the original extension by zero, for every sheaf with zero outside stalks. -/
theorem existsUnique_openExtensionByZeroIso {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) (G : X.Sheaf AddCommGrpCat.{u})
    (hG : ∀ x : X, x ∉ U → IsZero (G.presheaf.stalk x))
    (ρ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj G ≅ F) :
    ∃! e : openExtensionByZero U F ≅ G,
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map e.hom ≫ ρ.hom =
        (openExtensionByZeroRestrictionIso U).hom.app F := by
  let := openZeroMarkedHom_isIso U F G hG ρ
  refine ⟨asIso (openZeroMarkedHom U F G ρ), openZeroMarkedHom_comp U F G ρ, ?_⟩
  intro e he
  apply Iso.ext
  exact openZeroHom_eq_marked_of_comp U F G ρ e.hom he

/-- All restriction, stalk, and fixed-marking characterization properties of the
original extension by zero. The restriction is fixed by the canonical unit. -/
theorem openExtensionByZero_properties {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) :
    ∃ r : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj
        (openExtensionByZero U F) ≅ F,
      r.inv = (openExtensionByZeroAdjunction U).unit.app F ∧
      (∀ x : U, Nonempty ((openExtensionByZero U F).presheaf.stalk (x : X) ≅
        F.presheaf.stalk x)) ∧
      (∀ x : X, x ∉ U → IsZero ((openExtensionByZero U F).presheaf.stalk x)) ∧
      ∀ (G : X.Sheaf AddCommGrpCat.{u}),
        (∀ x : X, x ∉ U → IsZero (G.presheaf.stalk x)) →
        ∀ (ρ : (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').obj G ≅ F),
        ∃! e : openExtensionByZero U F ≅ G,
          (TopCat.Sheaf.pullback AddCommGrpCat.{u} U.inclusion').map e.hom ≫ ρ.hom = r.hom := by
  refine ⟨(openExtensionByZeroRestrictionIso U).app F,
    openExtensionByZeroRestrictionIso_inv_app U F, ?_, ?_, ?_⟩
  · exact fun x => ⟨openExtensionByZeroStalkIso U F x⟩
  · exact openExtensionByZero_stalk_isZero_of_not_mem U F
  · exact fun G hG ρ => existsUnique_openExtensionByZeroIso U F G hG ρ

end Hartshorne
