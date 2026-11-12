/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Hartshorne.Scheme.ProjectiveSpace
import Hartshorne.Scheme.ProjectiveSpaceChart

/-!
# Projective space over a Noetherian ring is a Noetherian scheme

Hartshorne, *Algebraic Geometry*, II.2, Example 2.5.1 (p. 77) sets up `ℙⁿ_A = Proj A[x₀, …, xₙ]`
with its standard affine charts; II.3, Proposition 3.2 (pp. 83–84) characterizes Noetherian
schemes by finite covers by spectra of Noetherian rings. Together they give the fact proved
here, which supplements the book's text.

## Proof

The coordinate charts `D₊(xᵢ) ≅ Spec A[x]_(xᵢ)` cover `Proj A[x_j : j ∈ σ]`, and there are
finitely many of them when `σ` is finite. Dehomogenization identifies `A[x]_(xᵢ)` with the
polynomial ring `A[x_j : j ≠ i]` in finitely many variables, which is Noetherian by the Hilbert
basis theorem when `A` is. A scheme with a finite cover by spectra of Noetherian rings is
Noetherian.

## Main results

* `Hartshorne.isNoetherian_proj_homogeneousSubmodule`: `Proj A[x_j : j ∈ σ]` is Noetherian for a
  Noetherian ring `A` and a finite type `σ`.
* `Hartshorne.projectiveSpaceScheme_isNoetherian`: `ℙⁿ_A` is Noetherian for a Noetherian ring
  `A`.
-/

namespace Hartshorne

open AlgebraicGeometry MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Projective space over a Noetherian ring is Noetherian.** For a Noetherian ring `A` and a
finite type `σ`, the scheme `Proj A[x_j : j ∈ σ]` (total-degree grading) is Noetherian: it is
covered by the finitely many charts `Spec A[x]_(xᵢ)`, and each `A[x]_(xᵢ) ≅ A[x_j : j ≠ i]` is a
Noetherian ring. -/
instance isNoetherian_proj_homogeneousSubmodule (A : Type u) (σ : Type*) [CommRing A]
    [IsNoetherianRing A] [Finite σ] : IsNoetherian (Proj (homogeneousSubmodule σ A)) := by
  classical
  let 𝒰 := (projCoordinateAffineOpenCover A (σ := σ)).openCover
  have : Finite 𝒰.I₀ := ‹Finite σ›
  have : ∀ i, IsAffine (𝒰.X i) := fun i ↦ inferInstanceAs (IsAffine (Spec _))
  refine (isNoetherian_iff_of_finite_affine_openCover (𝒰 := 𝒰)).mpr fun i ↦ ?_
  let R := HomogeneousLocalization.Away (homogeneousSubmodule σ A) (X i : MvPolynomial σ A)
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ (chartAwayEquiv A i).symm
  exact isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm

/-- **`ℙⁿ_A` is Noetherian** for a Noetherian ring `A`. -/
instance projectiveSpaceScheme_isNoetherian (A : Type u) [CommRing A] [IsNoetherianRing A]
    (n : ℕ) : IsNoetherian (projectiveSpaceScheme A n) :=
  isNoetherian_proj_homogeneousSubmodule A (Fin (n + 1))

end Hartshorne
