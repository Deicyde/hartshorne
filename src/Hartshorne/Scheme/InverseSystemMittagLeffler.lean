/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.RingTheory.Artinian.Module

/-!
# The Mittag--Leffler condition for inverse systems

Hartshorne, *Algebraic Geometry*, II.9 (pp. 190--192).

We specialize Mathlib's Mittag--Leffler predicate to inverse systems of abelian groups indexed by
the natural numbers. The condition is imposed on the underlying sets, as in Mathlib: at every
stage, one transition image is contained in every transition image into that stage.
-/

namespace Hartshorne

open CategoryTheory

universe u

namespace InverseSystem

/-- A sequential inverse system of abelian groups satisfies the Mittag--Leffler condition when
the underlying Type-valued functor does. -/
def IsMittagLeffler (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : Prop :=
  (A ⋙ forget AddCommGrpCat).IsMittagLeffler

/-- An inverse system with surjective transition maps is Mittag--Leffler. -/
theorem isMittagLeffler_of_surjective (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : ∀ ⦃i j⦄ (f : i ⟶ j), Function.Surjective (A.map f)) :
    IsMittagLeffler A := by
  apply CategoryTheory.Functor.isMittagLeffler_of_surjective
  intro i j f
  exact hA f

/-- If every term of an inverse system satisfies the descending chain condition on subgroups,
then the system is Mittag--Leffler. -/
theorem isMittagLeffler_of_isArtinian (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u})
    (hA : ∀ j, IsArtinian ℤ (A.obj j)) : IsMittagLeffler A := by
  intro j
  let : IsArtinian ℤ (A.obj j) := hA j
  let ranges : Set (Submodule ℤ (A.obj j)) :=
    { R | ∃ (i : ℕᵒᵖ) (f : i ⟶ j),
        R = LinearMap.range (A.map f).hom.toIntLinearMap }
  have ranges_nonempty : ranges.Nonempty := by
    refine ⟨LinearMap.range (A.map (𝟙 j)).hom.toIntLinearMap, ?_⟩
    exact ⟨j, 𝟙 j, rfl⟩
  obtain ⟨R, hR_mem, hR_min⟩ := IsArtinian.set_has_minimal ranges ranges_nonempty
  obtain ⟨i, f, rfl⟩ := hR_mem
  refine ⟨i, f, fun k g ↦ ?_⟩
  obtain ⟨l, p, q, hpq⟩ := CategoryTheory.IsCofiltered.cospan f g
  let S : Submodule ℤ (A.obj j) :=
    LinearMap.range (A.map (p ≫ f)).hom.toIntLinearMap
  have hS_mem : S ∈ ranges := ⟨l, p ≫ f, rfl⟩
  have hS_le_f : S ≤ LinearMap.range (A.map f).hom.toIntLinearMap := by
    rintro x ⟨y, rfl⟩
    refine ⟨A.map p y, ?_⟩
    change A.map f (A.map p y) = A.map (p ≫ f) y
    rw [← AddCommGrpCat.comp_apply, ← A.map_comp]
  have hS_eq_f : S = LinearMap.range (A.map f).hom.toIntLinearMap :=
    eq_of_le_of_not_lt hS_le_f (hR_min S hS_mem)
  have hf_le_g : LinearMap.range (A.map f).hom.toIntLinearMap ≤
      LinearMap.range (A.map g).hom.toIntLinearMap := by
    rw [← hS_eq_f]
    rintro x ⟨y, rfl⟩
    refine ⟨A.map q y, ?_⟩
    change A.map g (A.map q y) = A.map (p ≫ f) y
    rw [← AddCommGrpCat.comp_apply, ← A.map_comp, ← hpq]
  intro x hx
  change x ∈ LinearMap.range (A.map f).hom.toIntLinearMap at hx
  change x ∈ LinearMap.range (A.map g).hom.toIntLinearMap
  exact hf_le_g hx

end InverseSystem

end Hartshorne
