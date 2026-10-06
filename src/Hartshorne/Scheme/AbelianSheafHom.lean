/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Forget

/-!
# The additive sheaf of local morphisms

For sheaves of abelian groups `F` and `G` on a topological space, this file
bundles the local morphism types `Hom(F|U, G|U)` as abelian groups. Forgetting
the additive structure recovers `CategoryTheory.sheafHom F G`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

private def abelianPresheafHom
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of
    (((Opens.grothendieckTopology X).overPullback AddCommGrpCat U.unop).obj F ⟶
      ((Opens.grothendieckTopology X).overPullback AddCommGrpCat U.unop).obj G)
  map f := AddCommGrpCat.ofHom
    { toFun := ((Opens.grothendieckTopology X).overMapPullback
        AddCommGrpCat f.unop).map
      map_zero' := by ext : 3; rfl
      map_add' := by intros; ext : 3; rfl }
  map_id U := by
    ext φ : 2
    exact ConcreteCategory.congr_hom
      ((CategoryTheory.sheafHom' F G).map_id U) φ
  map_comp f g := by
    ext φ : 2
    exact ConcreteCategory.congr_hom
      ((CategoryTheory.sheafHom' F G).map_comp f g) φ

private def abelianPresheafHomForgetIso
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    abelianPresheafHom F G ⋙ CategoryTheory.forget AddCommGrpCat ≅
      CategoryTheory.sheafHom' F G :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The sheaf of local additive morphisms between two sheaves of abelian
groups. Its sections on `U` are the additive group of morphisms between the
restrictions of `F` and `G` to `U`. -/
def abelianSheafHom
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    TopCat.Sheaf AddCommGrpCat.{u} X where
  obj := abelianPresheafHom F G
  property := by
    change TopCat.Presheaf.IsSheaf (abelianPresheafHom F G)
    rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (CategoryTheory.forget AddCommGrpCat) (abelianPresheafHom F G)]
    rw [TopCat.Presheaf.isSheaf_iso_iff
      (abelianPresheafHomForgetIso F G)]
    exact (CategoryTheory.sheafHom F G).property

/-- Forgetting the additive structure on `abelianSheafHom F G` recovers
Mathlib's Type-valued sheaf of local morphisms. -/
def abelianSheafHomForgetIso
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (sheafCompose (Opens.grothendieckTopology X)
      (CategoryTheory.forget AddCommGrpCat)).obj (abelianSheafHom F G) ≅
      CategoryTheory.sheafHom F G :=
  ObjectProperty.isoMk _ (abelianPresheafHomForgetIso F G)

end TopCat.Sheaf
