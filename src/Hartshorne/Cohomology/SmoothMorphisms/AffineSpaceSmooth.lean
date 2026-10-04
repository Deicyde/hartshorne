/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smoothness of affine space

Hartshorne, *Algebraic Geometry*, III.10, Example 10.0.1 (p. 268).

Affine space over an arbitrary scheme is smooth of relative dimension equal
to the number of coordinates. The algebraic input is the zero-relation
submersive presentation of a multivariable polynomial algebra.
-/

open CategoryTheory
open AlgebraicGeometry
open MvPolynomial

universe u

namespace Hartshorne

/-- The zero-relation submersive presentation of a multivariable polynomial algebra. -/
noncomputable def mvPolynomialSubmersivePresentation
    (R : Type u) [CommRing R] (ι : Type u) :
    Algebra.SubmersivePresentation R (MvPolynomial ι R) ι Empty where
  toPreSubmersivePresentation :=
    { toPresentation :=
        { toGenerators := Algebra.Generators.mvPolynomial R ι
          relation := Empty.elim
          span_range_relation_eq_ker := by
            simp [Algebra.Generators.ker_mvPolynomial] }
      map := Empty.elim
      map_inj := fun a => Empty.elim a }
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
    simp

/-- A polynomial algebra in finitely many variables is standard smooth of relative dimension
equal to the number of variables. -/
theorem mvPolynomial_isStandardSmoothOfRelativeDimension
    (R : Type u) [CommRing R] (ι : Type u) [Finite ι] :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) R (MvPolynomial ι R) := by
  apply (mvPolynomialSubmersivePresentation R ι).isStandardSmoothOfRelativeDimension
  simp [Algebra.Presentation.dimension]

/-- Affine space over an affine scheme is smooth of relative dimension equal to the number of
coordinates. -/
theorem affineSpace_overSpec_smoothOfRelativeDimension
    (R : CommRingCat.{u}) (ι : Type u) [Finite ι] :
    SmoothOfRelativeDimension (Nat.card ι)
      (𝔸(ι; Spec R) ↘ Spec R) := by
  let _ : MorphismProperty.RespectsIso
      (@SmoothOfRelativeDimension (Nat.card ι)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange
      (n := Nat.card ι)).respectsIso
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension (Nat.card ι))
    (AffineSpace.SpecIso ι R).inv, AffineSpace.SpecIso_inv_over]
  rw [HasRingHomProperty.Spec_iff
    (P := @SmoothOfRelativeDimension (Nat.card ι))]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  convert
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap
      (n := Nat.card ι) (R := R) (S := MvPolynomial ι R)).mpr
        (mvPolynomial_isStandardSmoothOfRelativeDimension R ι) using 1 <;> rfl

/-- **Hartshorne III.10, Example 10.0.1.** Affine space over any scheme is smooth of relative
dimension equal to the number of coordinates. -/
theorem affineSpace_smoothOfRelativeDimension
    (S : Scheme.{u}) (ι : Type u) [Finite ι] :
    SmoothOfRelativeDimension (Nat.card ι) (𝔸(ι; S) ↘ S) := by
  let _ : MorphismProperty.RespectsIso
      (@SmoothOfRelativeDimension (Nat.card ι)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange
      (n := Nat.card ι)).respectsIso
  let _ : IsZariskiLocalAtTarget
      (@SmoothOfRelativeDimension (Nat.card ι)) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (@SmoothOfRelativeDimension (Nat.card ι))
      (Q := RingHom.Locally
        (RingHom.IsStandardSmoothOfRelativeDimension (Nat.card ι)))
  wlog hS : ∃ R, S = Spec R generalizing S
  · refine (IsZariskiLocalAtTarget.iff_of_openCover
      (P := @SmoothOfRelativeDimension (Nat.card ι)) S.affineCover).mpr ?_
    intro i
    have h := this (S.affineCover.X i) ⟨_, rfl⟩
    rwa [← (AffineSpace.isPullback_map
      (n := ι) (S.affineCover.f i)).isoPullback_hom_snd,
      MorphismProperty.cancel_left_of_respectsIso
        (P := @SmoothOfRelativeDimension (Nat.card ι))] at h
  obtain ⟨R, rfl⟩ := hS
  exact affineSpace_overSpec_smoothOfRelativeDimension R ι

/-- Affine space over any scheme is smooth. -/
theorem affineSpace_smooth
    (S : Scheme.{u}) (ι : Type u) [Finite ι] :
    Smooth (𝔸(ι; S) ↘ S) := by
  let _ := affineSpace_smoothOfRelativeDimension S ι
  exact SmoothOfRelativeDimension.smooth (Nat.card ι) _

end Hartshorne
