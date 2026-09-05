/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.ProjFunctionField
import Hartshorne.Projective.AwayAtPrime
import Hartshorne.Projective.CoordAwayChart
import Hartshorne.Projective.ChartIdeal

/-!
# Theorem 3.4(c)

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(c) (pp. 18-19).

For `Y` a projective variety meeting the chart `Uᵢ`,

`K(Y) ≅ S(Y)_((0))`.

Everything it is assembled from is already proved. `K(Y)` is the fraction field
of `A(Yᵢ)`, which is the geometric half; `A(Yᵢ) ≅ S(Y)_(xᵢ)`; and `S(Y)_((0))`
is the fraction field of `S(Y)_(xᵢ)`, which is the `𝔭 = (0)` case of the
comparison between graded localisations. A fraction field is determined by its
ring up to isomorphism, so the three compose.

The `(0)` case is the easy half of Theorem 3.4. The ideal needs no construction,
and the prime lying under the maximal ideal of `S(Y)_((0))` is `(0)` itself,
because that ring is a field and the comparison map is injective. Part (b) needs
`𝔪_P`, which has to be built.

## Main results

* `Hartshorne.projFunctionFieldEquivGraded`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace HomogeneousLocalization

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ] [DecidableEq σ]
  [Nonempty σ] {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) (i : σ)
  (hne : (Y ∩ standardChart i).Nonempty)

omit [DecidableEq σ] [Nonempty σ] in
include hY in
/-- `S(Y)` is a domain, `J(Y)` being prime for an irreducible `Y`. -/
theorem isDomain_homogeneousCoordinateRing : IsDomain (homogeneousCoordinateRing Y) := by
  have : (homogeneousVanishingIdeal Y).IsPrime :=
    (isIrreducible_iff_isPrime_homogeneousVanishingIdeal hY.isProjAlgebraicSet).1 hY.1
  exact Ideal.Quotient.isDomain _

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
include hne in
/-- The class of `xᵢ` is nonzero in `S(Y)`: it does not vanish at a point of `Y`
in the chart. -/
theorem mk_X_ne_zero :
    (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)) ≠ 0 := by
  intro h
  obtain ⟨P, hPY, hPc⟩ := hne
  rw [Ideal.Quotient.eq_zero_iff_mem] at h
  have hvan : HomogeneousVanish (X i : MvPolynomial σ k) P :=
    homogeneousVanish_of_mem_homogeneousVanishingIdeal h hPY
  simp only [HomogeneousVanish, eval_X] at hvan
  exact rep_ne_zero_of_mem_standardChart hPc hvan

omit [DecidableEq σ] [Nonempty σ] in
include hY hne in
/-- **`S(Y)_((0))` is the fraction field of `S(Y)_(xᵢ)`.** -/
theorem isFractionRing_projAtPrimeBot :
    letI := isDomain_homogeneousCoordinateRing hY
    letI := (awayToAtPrime (𝒜 := projCoordGrading Y)
      (f := Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)) ⊥
      (ne_bot_notMem (mk_X_ne_zero i hne))).toAlgebra
    IsFractionRing
      (Away (projCoordGrading Y) (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)))
      (AtPrime (projCoordGrading Y) (⊥ : Ideal (homogeneousCoordinateRing Y))) :=
  letI := isDomain_homogeneousCoordinateRing hY
  isFractionRing_atPrime_bot (mk_X_mem_projCoordGrading i Y) (mk_X_ne_zero i hne)

include hY hne in
/-- **Theorem 3.4(c)**: `K(Y) ≅ S(Y)_((0))`.

Three isomorphisms of fraction fields. `K(Y)` is the fraction field of `A(Yᵢ)`;
`A(Yᵢ) ≅ S(Y)_(xᵢ)`; and `S(Y)_((0))` is the fraction field of `S(Y)_(xᵢ)`. A
fraction field is determined by its ring, so transporting along the middle
isomorphism joins the two ends. -/
noncomputable def projFunctionFieldEquivGraded :
    letI := isDomain_homogeneousCoordinateRing hY
    Variety.FunctionField (Variety.ofQuasiProjective hY.isQuasiProjVariety)
      ≃+* AtPrime (projCoordGrading Y) (⊥ : Ideal (homogeneousCoordinateRing Y)) :=
  letI := isDomain_homogeneousCoordinateRing hY
  letI := (awayToAtPrime (𝒜 := projCoordGrading Y)
    (f := Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)) ⊥
    (ne_bot_notMem (mk_X_ne_zero i hne))).toAlgebra
  haveI := isFractionRing_projAtPrimeBot hY i hne
  haveI : IsDomain (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
    isDomain_coordinateRing (isAffineVariety_chartMap_image i hY hne)
  (projFunctionFieldEquivFractionRing hY i hne).trans
    (IsFractionRing.ringEquivOfRingEquiv (coordAwayChartEquiv i Y).symm)

end Hartshorne
