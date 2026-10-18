/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Open extension by zero for abelian sheaves

For the inclusion of an open subspace U, the conditional presheaf consists of sections in
F(j⁻¹V) satisfying V ⊆ U or s = 0. When V ⊆ U, j⁻¹V is V regarded as an open of U, so
F(j⁻¹V) is precisely the source's F(V), and the subgroup contains every section. Otherwise
it is the zero subgroup. Restrictions are inherited from F, and sheafification gives j_!F.

This is the ordinary construction in Hartshorne II.1, Exercise 1.19(b), printed p. 68.
Adjunction, restriction, stalk, and uniqueness properties are separate results.
-/

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

universe u

/-- The full group of sections when V is contained in U, and the zero subgroup otherwise. -/
private def openZeroSections {X : TopCat.{u}} (U : Opens X)
    (P : TopCat.Presheaf AddCommGrpCat.{u} X) (V : Opens X) :
    AddSubgroup (P.obj (op V)) where
  carrier := {s | V ≤ U ∨ s = 0}
  zero_mem' := Or.inr rfl
  add_mem' := by
    intro a b ha hb
    rcases ha with h | ha
    · exact Or.inl h
    rcases hb with h | hb
    · exact Or.inl h
    exact Or.inr (by simp [ha, hb])
  neg_mem' := by
    intro a ha
    rcases ha with h | ha
    · exact Or.inl h
    exact Or.inr (by simp [ha])

/-- Inherited restriction homomorphisms preserve the conditional groups of sections. -/
private def openZeroMap {X : TopCat.{u}} (U : Opens X)
    (P : TopCat.Presheaf AddCommGrpCat.{u} X) {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    AddCommGrpCat.of (openZeroSections U P V.unop) ⟶
      AddCommGrpCat.of (openZeroSections U P W.unop) :=
  AddCommGrpCat.ofHom
    (((P.map f).hom.comp (openZeroSections U P V.unop).subtype).codRestrict
      (openZeroSections U P W.unop) (by
        intro s
        rcases s.property with h | hs
        · exact Or.inl ((leOfHom f.unop).trans h)
        · right
          change (P.map f).hom s.val = 0
          rw [hs, map_zero]))

/-- The conditional groups and their inherited restrictions form a genuine presheaf. -/
private def openZeroPresheaf {X : TopCat.{u}} (U : Opens X)
    (P : TopCat.Presheaf AddCommGrpCat.{u} X) : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj V := AddCommGrpCat.of (openZeroSections U P V.unop)
  map f := openZeroMap U P f
  map_id V := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply Subtype.ext
    change (P.map (𝟙 V)).hom s.val = s.val
    simp
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply Subtype.ext
    change (P.map (f ≫ g)).hom s.val = (P.map g).hom ((P.map f).hom s.val)
    simp

/-- The source's conditional presheaf. For V ⊆ U, the inverse-image open j⁻¹V is V viewed
as an open of U, so its sections are F(V); otherwise only the zero section is retained. -/
def openExtensionByZeroPresheaf {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) : TopCat.Presheaf AddCommGrpCat.{u} X :=
  openZeroPresheaf U ((Opens.map U.inclusion').op ⋙ F.presheaf)

/-- Ordinary extension by zero of an abelian sheaf along an open-subspace inclusion,
obtained by sheafifying the conditional presheaf of Hartshorne II.1, Exercise 1.19(b). -/
noncomputable def openExtensionByZero {X : TopCat.{u}} (U : Opens X)
    (F : (TopCat.of U).Sheaf AddCommGrpCat.{u}) : X.Sheaf AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (openExtensionByZeroPresheaf U F)

end Hartshorne
