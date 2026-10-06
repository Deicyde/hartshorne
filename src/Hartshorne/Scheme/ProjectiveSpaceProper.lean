/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceOverScheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Properness of projective space

Hartshorne, *Algebraic Geometry*, II.4, Theorem 4.9.

Projective space over the integers is proper by Mathlib's properness theorem
for `Proj`. Relative projective space is its base change, so its projection is
proper over every scheme; no Noetherian hypothesis on the base is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- Projective space over the universe-lifted integers is proper over
`Spec ℤ`. -/
theorem projectiveSpaceOverIntegersMap_isProper (n : ℕ) :
    IsProper
      (projectiveSpaceOverIntegersMap n :
        projectiveSpaceScheme (ULift.{u} ℤ) n ⟶
          Spec (CommRingCat.of (ULift.{u} ℤ))) := by
  let R := ULift.{u} ℤ
  let σ := Fin (n + 1)
  let 𝒜 := MvPolynomial.homogeneousSubmodule σ R
  let _ := MvPolynomial.gradedAlgebra (σ := σ) (R := R)
  change IsProper (specULiftZIsTerminal.from (Proj 𝒜))
  let _ : IsScalarTower R (𝒜 0) (MvPolynomial σ R) :=
    IsScalarTower.of_algebraMap_eq
      (R := R) (S := 𝒜 0) (A := MvPolynomial σ R) (fun _ ↦ rfl)
  let _ : Algebra.FiniteType (𝒜 0) (MvPolynomial σ R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType
      (R := R) (S := 𝒜 0) (A := MvPolynomial σ R)
  have hsur : Function.Surjective (algebraMap R (𝒜 0)) := by
    intro x
    have hx : (x.1 : MvPolynomial σ R) ∈
        (1 : Submodule R (MvPolynomial σ R)) := by
      rw [← MvPolynomial.homogeneousSubmodule_zero]
      exact x.2
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx
    refine ⟨r, ?_⟩
    apply Subtype.ext
    exact hr
  let a : CommRingCat.of R ⟶ CommRingCat.of (𝒜 0) :=
    CommRingCat.ofHom (algebraMap R (𝒜 0))
  have ha : Function.Surjective a := by
    simpa [a] using hsur
  let _ : IsClosedImmersion (Spec.map a) :=
    IsClosedImmersion.spec_of_surjective a ha
  have heq : Proj.toSpecZero 𝒜 ≫ Spec.map a =
      specULiftZIsTerminal.from (Proj 𝒜) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [← heq]
  infer_instance

/-- For every scheme `Y`, relative projective `n`-space is proper over `Y`.
This strengthens Hartshorne's stated Noetherian-base version. -/
theorem projectiveSpaceOverSchemeProjection_isProper (n : ℕ) (Y : Scheme.{u}) :
    IsProper (projectiveSpaceOverSchemeProjection n Y) := by
  let _ : IsProper
      (projectiveSpaceOverIntegersMap n :
        projectiveSpaceScheme (ULift.{u} ℤ) n ⟶
          Spec (CommRingCat.of (ULift.{u} ℤ))) :=
    projectiveSpaceOverIntegersMap_isProper n
  infer_instance

end Hartshorne
