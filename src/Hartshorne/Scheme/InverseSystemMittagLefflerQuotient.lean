/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.InverseSystemMittagLeffler
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Mittag--Leffler descends to quotients

Hartshorne, *Algebraic Geometry*, Proposition II.9.1(a) (p. 192).

In a levelwise short exact sequence of sequential inverse systems of abelian groups, the quotient
system is Mittag--Leffler whenever the middle system is.
-/

namespace Hartshorne

open CategoryTheory

universe u

namespace InverseSystem

/-- **Hartshorne II.9.1(a).** In a levelwise short exact sequence of sequential inverse systems of
abelian groups, the quotient of a Mittag--Leffler system is Mittag--Leffler. -/
theorem isMittagLeffler_quotient
    (S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hS : ∀ n : ℕᵒᵖ,
      (S.map ((evaluation ℕᵒᵖ AddCommGrpCat.{u}).obj n)).ShortExact)
    (hB : IsMittagLeffler S.X₂) : IsMittagLeffler S.X₃ := by
  have hsurj (n : ℕᵒᵖ) : Function.Surjective (S.g.app n) := by
    change Function.Surjective
      ((S.map ((evaluation ℕᵒᵖ AddCommGrpCat.{u}).obj n)).g)
    exact (hS n).ab_surjective_g
  have range_eq_image (i j : ℕᵒᵖ) (f : i ⟶ j) :
      Set.range (S.X₃.map f) = S.g.app j '' Set.range (S.X₂.map f) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨b, rfl⟩ := hsurj i c
      refine ⟨S.X₂.map f b, ⟨b, rfl⟩, ?_⟩
      simpa only [AddCommGrpCat.comp_apply] using
        congrArg (fun h : S.X₂.obj i ⟶ S.X₃.obj j ↦ h b) (S.g.naturality f)
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      refine ⟨S.g.app i b, ?_⟩
      simpa only [AddCommGrpCat.comp_apply] using
        (congrArg (fun h : S.X₂.obj i ⟶ S.X₃.obj j ↦ h b) (S.g.naturality f)).symm
  intro j
  obtain ⟨i, f, hf⟩ := hB j
  refine ⟨i, f, fun k g ↦ ?_⟩
  change Set.range (S.X₃.map f) ⊆ Set.range (S.X₃.map g)
  rw [range_eq_image i j f, range_eq_image k j g]
  exact Set.image_mono (hf g)

end InverseSystem

end Hartshorne
