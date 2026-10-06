/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.InverseSystemMittagLeffler
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Stable images of Mittag--Leffler inverse systems

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.1 (pp. 191--192).

The stable images of a Mittag--Leffler inverse system form a new inverse system with surjective
transition maps. Componentwise inclusion induces an additive equivalence on inverse-limit
sections.
-/

noncomputable section

open CategoryTheory Set

namespace Hartshorne.InverseSystem

universe u

private abbrev underlying (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : ℕᵒᵖ ⥤ Type u :=
  A ⋙ forget AddCommGrpCat

/-- The stable image at one stage of an inverse system. -/
def stableImage (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (j : ℕᵒᵖ) : AddSubgroup (A.obj j) where
  carrier := (underlying A).eventualRange j
  zero_mem' := by
    rw [Functor.mem_eventualRange_iff]
    intro i f
    exact ⟨0, (A.map f).hom.map_zero⟩
  add_mem' := by
    intro x y hx hy
    rw [Functor.mem_eventualRange_iff] at hx hy ⊢
    intro i f
    obtain ⟨x', rfl⟩ := hx f
    obtain ⟨y', rfl⟩ := hy f
    exact ⟨x' + y', (A.map f).hom.map_add x' y'⟩
  neg_mem' := by
    intro x hx
    rw [Functor.mem_eventualRange_iff] at hx ⊢
    intro i f
    obtain ⟨x', rfl⟩ := hx f
    exact ⟨-x', (A.map f).hom.map_neg x'⟩

/-- The inverse system obtained by restricting every term to its stable image. -/
def stableImageSystem (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) : ℕᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj j := AddCommGrpCat.of (stableImage A j)
  map {i j} f := AddCommGrpCat.ofHom
    { toFun := fun x =>
        ⟨A.map f x, (underlying A).eventualRange_mapsTo f x.2⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        simp }
  map_id j := by
    ext x
    change A.map (𝟙 j) x.1 = x.1
    simp
  map_comp f g := by
    ext x
    change A.map (f ≫ g) x.1 = A.map g (A.map f x.1)
    rw [A.map_comp]
    rfl

/-- A Mittag--Leffler system has surjective transition maps after restricting to stable images. -/
theorem stableImageSystem_map_surjective
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (hA : IsMittagLeffler A)
    ⦃i j⦄ (f : i ⟶ j) : Function.Surjective ((stableImageSystem A).map f) := by
  exact Functor.surjective_toEventualRanges (F := underlying A) hA f

private def sectionsAddSubgroup (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    AddSubgroup (∀ j, A.obj j) where
  carrier := (A ⋙ forget AddCommGrpCat).sections
  zero_mem' := by
    intro i j f
    exact (A.map f).hom.map_zero
  add_mem' := by
    intro x y hx hy i j f
    change A.map f (x i + y i) = x j + y j
    rw [(A.map f).hom.map_add]
    have hxf := hx f
    have hyf := hy f
    change A.map f (x i) = x j at hxf
    change A.map f (y i) = y j at hyf
    rw [hxf, hyf]
  neg_mem' := by
    intro x hx i j f
    change A.map f (-x i) = -x j
    rw [(A.map f).hom.map_neg]
    have hxf := hx f
    change A.map f (x i) = x j at hxf
    rw [hxf]

/-- The compatible sections of an inverse system of additive commutative groups form an additive
commutative group under pointwise operations. -/
noncomputable instance sectionsAddCommGroup (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    AddCommGroup ((A ⋙ forget AddCommGrpCat).sections) :=
  (sectionsAddSubgroup A).toAddCommGroup

/-- Componentwise inclusion of stable images is an additive equivalence on inverse-limit
sections. -/
noncomputable def stableImageSectionsAddEquiv (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((stableImageSystem A ⋙ forget AddCommGrpCat).sections) ≃+
      ((A ⋙ forget AddCommGrpCat).sections) :=
  { (underlying A).toEventualRangesSectionsEquiv with
    map_add' := fun _ _ => rfl }

/-- **Hartshorne II.9, stable-image replacement.** A Mittag--Leffler inverse system may be
replaced by its stable-image system: all transition maps become surjective, and componentwise
inclusion induces an additive equivalence on inverse-limit sections. -/
theorem exists_stableImageSectionsAddEquiv
    (A : ℕᵒᵖ ⥤ AddCommGrpCat.{u}) (hA : IsMittagLeffler A) :
    ∃ e : ((stableImageSystem A ⋙ forget AddCommGrpCat).sections) ≃+
        ((A ⋙ forget AddCommGrpCat).sections),
      (∀ s j, (e s).1 j = (s.1 j).1) ∧
        (∀ ⦃i j⦄ (f : i ⟶ j), Function.Surjective ((stableImageSystem A).map f)) := by
  refine ⟨stableImageSectionsAddEquiv A, ?_, ?_⟩
  · intro s j
    rfl
  · exact stableImageSystem_map_surjective A hA

end Hartshorne.InverseSystem
