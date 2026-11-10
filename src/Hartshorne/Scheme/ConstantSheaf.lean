/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Flasque

/-!
# The constant sheaf

Hartshorne, *Algebraic Geometry*, Example II.1.0.3 (p. 62).

For an abelian group `A`, the sections of the constant sheaf over an open set `U` are the
continuous maps from `U` to `A` with its discrete topology. We present these as locally constant
maps, with pointwise addition and restriction by precomposition.
-/

namespace Hartshorne

open CategoryTheory TopologicalSpace Opposite

universe u

private def constantPresheaf (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (LocallyConstant U.unop A)
  map {_ _} i := AddCommGrpCat.ofHom <|
    LocallyConstant.comapAddMonoidHom ((Opens.toTopCat X).map i.unop).hom
  map_id _ := by
    ext f x
    rfl
  map_comp _ _ := by
    ext f x
    rfl

private def locallyConstantEquivContinuous (X : TopCat.{u}) (A : AddCommGrpCat.{u})
    (U : (Opens X)ᵒᵖ) :
    LocallyConstant U.unop A ≃
      ((Opens.toTopCat X).obj U.unop ⟶ TopCat.discrete.obj A) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact
    { toFun := fun f ↦ TopCat.ofHom ⟨f, f.continuous⟩
      invFun := fun f ↦ ⟨f, (IsLocallyConstant.iff_continuous f).2 f.hom.continuous⟩
      left_inv := fun f ↦ by ext; rfl
      right_inv := fun f ↦ by ext; rfl }

private def constantPresheafForgetIso (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    constantPresheaf X A ⋙ forget AddCommGrpCat ≅
      TopCat.presheafToTop X (TopCat.discrete.obj A) :=
  NatIso.ofComponents (fun U ↦ (locallyConstantEquivContinuous X A U).toIso)
    (fun i ↦ by
      ext f
      apply TopCat.ext
      intro x
      rfl)

/-- **Hartshorne II.1.0.3.** The constant sheaf associated to an abelian group `A`: its sections
over `U` are the continuous maps from `U` to `A` with the discrete topology. -/
noncomputable def constantSheaf (X : TopCat.{u}) (A : AddCommGrpCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨constantPresheaf X A,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (forget AddCommGrpCat) (constantPresheaf X A)).2
      ((TopCat.Presheaf.isSheaf_iso_iff (constantPresheafForgetIso X A)).2
        (TopCat.sheafToTop (X := X) (TopCat.discrete.obj A)).2)⟩

/-- The constant sheaf on an irreducible space is flasque: on a nonempty open set its sections are
constant. -/
theorem isFlasque_constantSheaf_of_irreducibleSpace (X : TopCat.{u}) [IrreducibleSpace X]
    (A : AddCommGrpCat.{u}) : (constantSheaf X A).IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    change LocallyConstant V.unop A at t
    by_cases hV : (V.unop : Set X).Nonempty
    · obtain ⟨x, hx⟩ := hV
      have hpre : IsPreconnected (V.unop : Set X) :=
        ((IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset V.unop.isOpen
          (Set.subset_univ _)).isPreconnected
      have : PreconnectedSpace V.unop := Subtype.preconnectedSpace hpre
      refine ⟨(LocallyConstant.const U.unop (t ⟨x, hx⟩) : LocallyConstant U.unop A), ?_⟩
      change LocallyConstant.comap _ (LocallyConstant.const U.unop (t ⟨x, hx⟩)) = t
      ext y
      exact (t.apply_eq_of_preconnectedSpace y ⟨x, hx⟩).symm
    · refine ⟨(0 : LocallyConstant U.unop A), ?_⟩
      change LocallyConstant.comap _ (0 : LocallyConstant U.unop A) = t
      ext y
      exact absurd ⟨y.1, y.2⟩ hV

end Hartshorne
