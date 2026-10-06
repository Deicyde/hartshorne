/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
# Closed extension by zero

Hartshorne, *Algebraic Geometry*, II.1, Exercise 1.19(a) (p. 68).

For the inclusion of a closed subspace, direct image of a sheaf of abelian groups preserves
stalks on the subspace and has zero stalks on its complement.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject

namespace Hartshorne

universe u

/-- The inclusion of a subspace into its ambient topological space. -/
def closedSubspaceInclusion (X : TopCat.{u}) (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

private theorem closedSubspaceInclusion_isInducing (X : TopCat.{u}) (Z : Set X) :
    Topology.IsInducing (closedSubspaceInclusion X Z) :=
  Topology.IsEmbedding.subtypeVal.isInducing

/-- On the closed subspace, the stalk of direct image is canonically isomorphic to the original
stalk. Its forward map is Mathlib's canonical stalk-pushforward morphism. -/
noncomputable def closedExtensionByZeroOnImageStalkIso
    {X : TopCat.{u}} (Z : Set X) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) (z : Z) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F).presheaf.stalk
        (z : X) ≅
      F.presheaf.stalk z := by
  let f := F.presheaf.stalkPushforward AddCommGrpCat.{u}
    (closedSubspaceInclusion X Z) z
  have hf : IsIso f :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat.{u} (closedSubspaceInclusion_isInducing X Z) F.presheaf z
  exact @asIso _ _ _ _ f hf

private theorem closedExtensionByZeroOffImageStalk_isZero
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∉ Z) :
    IsZero
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F).presheaf.stalk
        x) := by
  let P :=
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F).presheaf
  rw [IsZero.iff_id_eq_zero]
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hxU
  simp only [Category.comp_id, comp_zero]
  let V : Opens X := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  have hxV : x ∈ V := ⟨hxU, hx⟩
  let iVU : V ⟶ U := homOfLE inf_le_left
  have hpreimage : (Opens.map (closedSubspaceInclusion X Z)).obj V = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    change (z : X) ∈ U ∧ (z : X) ∈ Zᶜ at hz
    exact (hz.2 z.2).elim
  have hzero : IsZero (P.obj (op V)) := by
    change IsZero (F.presheaf.obj (op ((Opens.map (closedSubspaceInclusion X Z)).obj V)))
    exact (F.isTerminalOfEqEmpty hpreimage).isZero
  calc
    P.germ U x hxU = P.map iVU.op ≫ P.germ V x hxV :=
      (P.germ_res iVU x hxV).symm
    _ = 0 := by rw [hzero.eq_of_tgt (P.map iVU.op) 0, zero_comp]

/-- Off the closed subspace, the stalk of direct image is canonically isomorphic to the zero
abelian group. -/
noncomputable def closedExtensionByZeroOffImageStalkIso
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∉ Z) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (closedSubspaceInclusion X Z)).obj F).presheaf.stalk
        x ≅
      0 :=
  (closedExtensionByZeroOffImageStalk_isZero Z hZ F x hx).isoZero

/-- **Hartshorne II.1, Exercise 1.19(a).** Direct image along a closed-subspace inclusion is
extension by zero: the canonical stalk-pushforward map gives the on-image isomorphism, and every
stalk off the subspace is isomorphic to the zero abelian group. -/
theorem exists_closedExtensionByZeroStalkIsos
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (∀ z : Z,
      ∃ e :
          ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
            (closedSubspaceInclusion X Z)).obj F).presheaf.stalk (z : X) ≅
            F.presheaf.stalk z,
        e.hom = F.presheaf.stalkPushforward AddCommGrpCat.{u}
          (closedSubspaceInclusion X Z) z) ∧
      ∀ x : X, x ∉ Z →
        Nonempty
          (((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
            (closedSubspaceInclusion X Z)).obj F).presheaf.stalk x ≅ 0) := by
  constructor
  · intro z
    exact ⟨closedExtensionByZeroOnImageStalkIso Z F z, rfl⟩
  · intro x hx
    exact ⟨closedExtensionByZeroOffImageStalkIso Z hZ F x hx⟩

end Hartshorne
