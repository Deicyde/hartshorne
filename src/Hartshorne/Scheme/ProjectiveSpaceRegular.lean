/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpace
import Hartshorne.Scheme.ProjectiveSpaceChart
import Hartshorne.Scheme.Regular
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Projective space over a regular ring is regular

Hartshorne, *Algebraic Geometry*, II.8, the projective-space case in the proof of
Theorem 8.18 (pp. 179–180), regularity input.

A point of a scheme lying in an affine open `U` whose ring of sections is a regular
ring is a regular point, because its local ring is a localization of `Γ(X, U)` at a
prime. Projective space `ℙⁿ_A` over a regular ring `A` is covered by the coordinate
charts `D₊(xⱼ)`, whose rings of sections are polynomial rings in `n` variables over
`A`, and polynomial rings in finitely many variables over a regular ring are
regular. Hence `ℙⁿ_A` is a regular scheme; in particular `ℙⁿ_k` is regular for every
field `k`.

## Main results

* `Hartshorne.isRegularAt_of_isAffineOpen`: points of an affine open with regular
  ring of sections are regular.
* `Hartshorne.projectiveSpaceScheme_isRegular`: `ℙⁿ_A` is regular when `A` is a
  regular ring.
-/

open AlgebraicGeometry CategoryTheory

namespace Hartshorne

universe u

/-- A point lying in an affine open whose ring of sections is a regular ring is a
regular point: its local ring is a localization of that ring at a prime. -/
theorem isRegularAt_of_isAffineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    [IsRegularRing Γ(X, U)] (x : X) (hx : x ∈ U) : X.IsRegularAt x := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (X.presheaf.stalk x)).toRingEquiv

/-- Projective space `ℙⁿ_A` over a regular ring `A` is a regular scheme. Its
coordinate charts are polynomial rings in `n` variables over `A`. -/
theorem projectiveSpaceScheme_isRegular (A : Type u) [CommRing A] [IsRegularRing A] (n : ℕ) :
    (projectiveSpaceScheme A n).IsRegular := by
  let := MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := A)
  change (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IsRegular
  have hreg (j : Fin (n + 1)) : IsRegularRing
      Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j)) :=
    IsRegularRing.of_ringEquiv ((chartAwayEquiv A j).symm.trans
      (Proj.basicOpenIsoAway _ _ (X_mem_homogeneousSubmodule_one A j)
        Nat.one_pos).commRingCatIsoToRingEquiv)
  have hcov := iSup_proj_basicOpen_X_eq_top (σ := Fin (n + 1)) A
  have haff (j : Fin (n + 1)) := Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j)
    (X_mem_homogeneousSubmodule_one A j) Nat.one_pos
  refine ⟨isLocallyNoetherian_of_affine_cover (S := fun j => ⟨_, haff j⟩) hcov
    fun j => by have := hreg j; infer_instance, fun x => ?_⟩
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov.symm ▸ trivial :
    x ∈ ⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
      (MvPolynomial.X j))
  exact isRegularAt_of_isAffineOpen (haff j) x hj

end Hartshorne
