/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.DedekindSubringLocalization
import Hartshorne.Curve.SeparableNormalizationCharts
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Finiteness of poles in a function field

Hartshorne, *Algebraic Geometry*, I.6, Lemma 6.5 (p. 41).

A rational function on a one-dimensional function field has a pole at only
finitely many function-field DVRs.  The proof uses the two normalization
charts associated to a separating parameter.  On either chart, a DVR is
determined by its center, and poles map into the finite support of the rational
function on the Dedekind normalization.
-/

namespace Hartshorne

open IsDedekindDomain

noncomputable section

universe u v

namespace FunctionFieldDVR

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- On one Dedekind normalization chart, only finitely many containing DVRs
have a pole at a fixed rational function. -/
private theorem finite_hasPoleAt_on_chart
    (C : SeparableNormalizationChart k K) (x : K) :
    {R : FunctionFieldDVR k K |
      C.normalization.toSubring ≤ R.toValuationSubring.toSubring ∧
        R.HasPoleAt x}.Finite := by
  let S : Set (FunctionFieldDVR k K) :=
    {R | C.normalization.toSubring ≤ R.toValuationSubring.toSubring ∧
      R.HasPoleAt x}
  let contains (R : S) :
      ∀ b : C.normalization,
        algebraMap C.normalization K b ∈ R.1.toValuationSubring := by
    intro b
    simpa using R.2.1 b.2
  let centerMap (R : S) : HeightOneSpectrum C.normalization :=
    R.1.centerHeightOne (contains R)
  let supportMap (R : S) :
      {v : HeightOneSpectrum C.normalization |
        v ∈ HeightOneSpectrum.Support C.normalization x} :=
    ⟨centerMap R, by
      change 1 < (centerMap R).valuation K x
      have hnot :
          x ∉ HeightOneSpectrum.valuationSubringAtPrime K (centerMap R) := by
        rw [show HeightOneSpectrum.valuationSubringAtPrime K (centerMap R) =
            R.1.toValuationSubring from R.1.localizationAtCenter_eq (contains R)]
        exact R.2.2
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hnot
      change ¬ (centerMap R).valuation K x ≤ 1 at hnot
      exact lt_of_not_ge hnot⟩
  have hcenterMap_injective : Function.Injective centerMap := by
    intro R T hRT
    apply Subtype.ext
    apply FunctionFieldDVR.center_injective (contains R) (contains T)
    exact congrArg HeightOneSpectrum.asIdeal hRT
  have hsupportMap_injective : Function.Injective supportMap := by
    intro R T hRT
    apply hcenterMap_injective
    exact congrArg Subtype.val hRT
  let _ : Finite
      {v : HeightOneSpectrum C.normalization |
        v ∈ HeightOneSpectrum.Support C.normalization x} :=
    Set.finite_coe_iff.mpr (HeightOneSpectrum.Support.finite C.normalization x)
  let _ : Finite S := Finite.of_injective supportMap hsupportMap_injective
  exact Set.toFinite S

/-- **Hartshorne I.6, Lemma 6.5.** A rational function on a
one-dimensional function field has a pole at only finitely many
function-field DVRs. -/
theorem finite_hasPoleAt [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (x : K) :
    {R : FunctionFieldDVR k K | R.HasPoleAt x}.Finite := by
  let C := separableNormalizationCharts k K htrdeg
  refine ((finite_hasPoleAt_on_chart C.atZero x).union
    (finite_hasPoleAt_on_chart C.atInfinity x)).subset ?_
  intro R hR
  rcases C.normalization_cover R with hzero | hinfinity
  · exact Or.inl ⟨hzero, hR⟩
  · exact Or.inr ⟨hinfinity, hR⟩

/-- A nonzero rational function vanishes at only finitely many
function-field DVRs. -/
theorem finite_vanishesAt [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) {x : K} (hx : x ≠ 0) :
    {R : FunctionFieldDVR k K | R.VanishesAt x}.Finite := by
  refine (finite_hasPoleAt htrdeg x⁻¹).subset ?_
  intro R hR
  change R.HasPoleAt x⁻¹
  change R.VanishesAt x at hR
  rw [hasPoleAt_iff_valuation_one_lt]
  rw [vanishesAt_iff_valuation_lt_one] at hR
  exact (R.toValuationSubring.valuation.val_lt_one_iff hx).mp hR

/-- Equivalently, a nonzero rational function belongs to the maximal ideal
of only finitely many function-field DVRs. -/
theorem finite_mem_maximalIdeal [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) {x : K} (hx : x ≠ 0) :
    {R : FunctionFieldDVR k K |
      ∃ hxR : x ∈ R.toValuationSubring,
        (⟨x, hxR⟩ : R.toValuationSubring) ∈
          IsLocalRing.maximalIdeal R.toValuationSubring}.Finite := by
  have heq :
      {R : FunctionFieldDVR k K |
        ∃ hxR : x ∈ R.toValuationSubring,
          (⟨x, hxR⟩ : R.toValuationSubring) ∈
            IsLocalRing.maximalIdeal R.toValuationSubring} =
        {R : FunctionFieldDVR k K | R.VanishesAt x} := by
    ext R
    change (∃ hxR : x ∈ R.toValuationSubring,
      (⟨x, hxR⟩ : R.toValuationSubring) ∈
        IsLocalRing.maximalIdeal R.toValuationSubring) ↔ R.VanishesAt x
    exact (R.vanishesAt_iff_exists_mem_maximalIdeal x).symm
  rw [heq]
  exact finite_vanishesAt htrdeg hx

end FunctionFieldDVR

end

end Hartshorne
