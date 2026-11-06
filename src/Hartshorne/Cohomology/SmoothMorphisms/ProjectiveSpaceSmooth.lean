/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.AffineSpaceSmooth
import Hartshorne.Scheme.ProjectiveSpaceChart
import Hartshorne.Scheme.ProjectiveSpaceOverScheme
import Hartshorne.Scheme.SmoothRelativeDimensionCalculus

/-!
# Smoothness of projective space

Hartshorne, *Algebraic Geometry*, III.10, Example 10.0.1 (p. 268).

Projective `n`-space over an arbitrary scheme is smooth of relative dimension
`n`. Over the integers, the coordinate charts `D₊(xᵢ)` cover projective space and
dehomogenization identifies each with affine `n`-space, so smoothness of
relative dimension `n` follows from the affine case by locality on the source.
Relative projective space is a base change of projective space over the
integers.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open MvPolynomial

universe u

namespace Hartshorne

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate chart `D₊(xᵢ)` of projective space over the integers is
affine `n`-space over the integers. -/
private def projectiveChartAffineSpaceIso (n : ℕ) (i : Fin (n + 1)) :
    Spec (CommRingCat.of (HomogeneousLocalization.Away
        (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X i))) ≅
      𝔸(ULift.{u} {j : Fin (n + 1) // j ≠ i}; Spec (CommRingCat.of (ULift.{u} ℤ))) :=
  let e : HomogeneousLocalization.Away
        (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X i) ≃+*
      MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ) :=
    (chartAwayEquiv (ULift.{u} ℤ) i).trans
      (MvPolynomial.renameEquiv (ULift.{u} ℤ) Equiv.ulift.symm).toRingEquiv
  (Scheme.Spec.mapIso e.toCommRingCatIso.op).symm ≪≫ (AffineSpace.SpecIso _ _).symm

/-- Projective `n`-space over the integers is smooth of relative dimension `n`. -/
theorem projectiveSpaceOverIntegersMap_smoothOfRelativeDimension (n : ℕ) :
    SmoothOfRelativeDimension n (projectiveSpaceOverIntegersMap.{u} n) := by
  let _ : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension n) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).respectsIso
  let _ : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension n)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @SmoothOfRelativeDimension n)
    (projCoordinateAffineOpenCover (ULift.{u} ℤ) (σ := Fin (n + 1))).openCover).mpr ?_
  intro (i : Fin (n + 1))
  have hcard : Nat.card (ULift.{u} {j : Fin (n + 1) // j ≠ i}) = n := by
    rw [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_fin, Fintype.card_subtype_eq, Nat.add_sub_cancel]
  have h := affineSpace_smoothOfRelativeDimension
    (Spec (CommRingCat.of (ULift.{u} ℤ))) (ULift.{u} {j : Fin (n + 1) // j ≠ i})
  rw [hcard] at h
  have heq : (projCoordinateAffineOpenCover (ULift.{u} ℤ) (σ := Fin (n + 1))).openCover.f i ≫
      projectiveSpaceOverIntegersMap.{u} n =
      (projectiveChartAffineSpaceIso n i).hom ≫
        (𝔸(ULift.{u} {j : Fin (n + 1) // j ≠ i}; Spec (CommRingCat.of (ULift.{u} ℤ))) ↘
          Spec (CommRingCat.of (ULift.{u} ℤ))) :=
    specULiftZIsTerminal.{u}.hom_ext _ _
  rw [heq]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension n)
    (projectiveChartAffineSpaceIso n i).hom _).mpr h

/-- **Projective space is smooth over an arbitrary base.** For every scheme `Y`,
the projection `ℙⁿ_Y ⟶ Y` is smooth of relative dimension `n`. -/
theorem projectiveSpaceOverSchemeProjection_smoothOfRelativeDimension
    (n : ℕ) (Y : Scheme.{u}) :
    SmoothOfRelativeDimension n (projectiveSpaceOverSchemeProjection n Y) := by
  have := projectiveSpaceOverIntegersMap_smoothOfRelativeDimension.{u} n
  exact smoothOfRelativeDimension_baseChange (IsPullback.of_hasPullback _ _)

end Hartshorne
