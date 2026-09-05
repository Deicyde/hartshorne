/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.ProjLocalRing
import Hartshorne.Projective.AwayAtPrime
import Hartshorne.Projective.PointIdeal
import Hartshorne.Projective.ChartIdeal

/-!
# Theorem 3.4(b)

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(b) (pp. 18-19).

For `Y` a projective variety and `P ∈ Y` in the chart `Uᵢ`,

`𝒪_P ≅ S(Y)_(𝔪_P)`.

Both halves are already proved, and this file matches them up. The geometric
half is `𝒪_P ≅ A(Yᵢ)_𝔪`; the algebraic half is that `S(Y)_(𝔪_P)` is the
localisation of `S(Y)_(xᵢ)` at the prime lying under its maximal ideal. What
joins them is that `S(Y)_(xᵢ) ≅ A(Yᵢ)` carries the one prime to the other.

## The ideal match

That last point is where the chart dictionary does its work, and it is short
because every step of it is already available. An element of `S(Y)_(xᵢ)` is
`g/xᵢⁿ` with `g` homogeneous; it lies in the contracted prime exactly when
`g ∈ 𝔪_P`, which is exactly when `g` vanishes at `P`, which by the
dehomogenisation dictionary is exactly when `α(g)` vanishes at `φᵢ(P)` — that
is, when its image lies in the maximal ideal of `A(Yᵢ)` at `φᵢ(P)`.

Recognising the contracted prime by numerators is what makes this possible;
`𝔮` was defined as a contraction so that primality would be free, and the
numerator criterion is what pays that back.

## Main results

* `Hartshorne.projLocalRingEquivGraded`
-/

namespace Hartshorne

open MvPolynomial HomogeneousLocalization

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ] [DecidableEq σ]
  [Nonempty σ] {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) (i : σ)
  (Q : (Variety.ofQuasiProjective hY.isQuasiProjVariety).carrier)
  (hQc : Q.1 ∈ standardChart i)

/-- `φᵢ(P)`, as a point of the affine chart image. -/
noncomputable abbrev chartImagePoint :
    (chartMap i '' (Y ∩ standardChart i) : Set ({j : σ // j ≠ i} → k)) :=
  ⟨chartMap i Q.1, Q.1, ⟨Q.2, hQc⟩, rfl⟩

omit [IsAlgClosed k] [Finite σ] [Nonempty σ] in
include hQc in
/-- **The chart isomorphism carries the contracted prime to the maximal ideal.**

The chain is: in the contracted prime, iff the numerator is in `𝔪_P`, iff it
vanishes at `P`, iff its dehomogenisation vanishes at `φᵢ(P)`, iff the image is
in the maximal ideal there. -/
theorem mem_awayPrime_iff_mem_maximalIdealAt
    (z : Away (projCoordGrading Y)
      (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i))) :
    letI := isPrime_projPointIdeal Q.2
    z ∈ awayPrime (𝒜 := projCoordGrading Y) (projPointIdeal Y Q.1)
        (mk_X_notMem_projPointIdeal Q.2 i hQc)
      ↔ coordAwayChartEquiv i Y z ∈ maximalIdealAt _ (chartImagePoint hY i Q hQc) := by
  have := isPrime_projPointIdeal Q.2
  obtain ⟨n, a, ha, rfl⟩ :=
    Away.mk_surjective _ (mk_X_mem_projCoordGrading i Y) z
  obtain ⟨g, hg, rfl⟩ := id ha
  rw [mem_awayPrime_iff (mk_X_mem_projCoordGrading i Y) (projPointIdeal Y Q.1)
    (mk_X_notMem_projPointIdeal Q.2 i hQc) n _ ha]
  show (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g) ∈ projPointIdeal Y Q.1 ↔ _
  rw [mem_projPointIdeal_iff Q.2,
    mem_homogeneousVanishingIdeal_singleton_iff ((mem_homogeneousSubmodule _ _).1 hg)]
  show HomogeneousVanish g Q.1 ↔ _
  rw [homogeneousVanish_iff_eval_dehomogenize ((mem_homogeneousSubmodule _ _).1 hg) hQc]
  show _ ↔ coordAwayToPoly i Y _ ∈ _
  rw [coordAwayToPoly_mk]
  show _ ↔ coordChartHom i Y (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g) ∈ _
  rw [coordChartHom_mk, mem_maximalIdealAt, evalAt_mk]
  simp

omit [IsAlgClosed k] [Finite σ] [Nonempty σ] in
include hQc in
/-- The two spellings of the maximal ideal at `φᵢ(P)` agree. -/
theorem chartMaximalIdeal_eq :
    chartMaximalIdeal hY i Q hQc = maximalIdealAt _ (chartImagePoint hY i Q hQc) := rfl

omit [IsAlgClosed k] [Finite σ] [Nonempty σ] in
include hQc in
/-- The chart isomorphism carries the complement of the contracted prime onto
the complement of the maximal ideal. -/
theorem map_primeCompl_awayPrime :
    letI := isPrime_projPointIdeal Q.2
    Submonoid.map (coordAwayChartEquiv i Y : _ ≃* _)
        (awayPrime (𝒜 := projCoordGrading Y) (projPointIdeal Y Q.1)
          (mk_X_notMem_projPointIdeal Q.2 i hQc)).primeCompl
      = (maximalIdealAt _ (chartImagePoint hY i Q hQc)).primeCompl := by
  have := isPrime_projPointIdeal Q.2
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact fun hx => hz ((mem_awayPrime_iff_mem_maximalIdealAt hY i Q hQc z).2 hx)
  · intro hx
    refine ⟨(coordAwayChartEquiv i Y).symm x, ?_, by simp⟩
    intro hmem
    exact hx (by
      simpa using (mem_awayPrime_iff_mem_maximalIdealAt hY i Q hQc _).1 hmem)

include hQc in
/-- **Theorem 3.4(b)**: `𝒪_P ≅ S(Y)_(𝔪_P)`.

The geometric half gives `𝒪_P ≅ A(Yᵢ)_𝔪`; the algebraic half gives that
`S(Y)_(𝔪_P)` is a localisation of `S(Y)_(xᵢ)`; and the chart isomorphism carries
one prime to the other, so both are localisations of `A(Yᵢ)` at the same
submonoid. -/
noncomputable def projLocalRingEquivGraded :
    letI := isPrime_projPointIdeal Q.2
    Variety.LocalRingAt (Variety.ofQuasiProjective hY.isQuasiProjVariety) Q
      ≃+* AtPrime (projCoordGrading Y) (projPointIdeal Y Q.1) :=
  letI := isPrime_projPointIdeal Q.2
  letI := (awayToAtPrime (𝒜 := projCoordGrading Y) (projPointIdeal Y Q.1)
    (mk_X_notMem_projPointIdeal Q.2 i hQc)).toAlgebra
  haveI := isLocalization_awayPrime (mk_X_mem_projCoordGrading i Y) (projPointIdeal Y Q.1)
    (mk_X_notMem_projPointIdeal Q.2 i hQc) (isHomogeneous_projPointIdeal)
  letI := ((algebraMap (Away (projCoordGrading Y)
      (Ideal.Quotient.mk (projVanishingIdeal Y).toIdeal (X i)))
      (AtPrime (projCoordGrading Y) (projPointIdeal Y Q.1))).comp
    (coordAwayChartEquiv i Y).symm.toRingHom).toAlgebra
  haveI : IsLocalization (maximalIdealAt _ (chartImagePoint hY i Q hQc)).primeCompl
      (AtPrime (projCoordGrading Y) (projPointIdeal Y Q.1)) := by
    rw [← map_primeCompl_awayPrime hY i Q hQc]
    exact IsLocalization.isLocalization_of_base_ringEquiv _ _ (coordAwayChartEquiv i Y)
  (projLocalRingEquiv hY i Q hQc).trans
    (IsLocalization.algEquiv (maximalIdealAt _ (chartImagePoint hY i Q hQc)).primeCompl
      (Localization.AtPrime (maximalIdealAt _ (chartImagePoint hY i Q hQc)))
      (AtPrime (projCoordGrading Y) (projPointIdeal Y Q.1))).toRingEquiv

end Hartshorne
