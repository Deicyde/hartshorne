/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.DVR
import Hartshorne.Curve.FunctionFieldDVR
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Centers of function-field DVRs on Dedekind subrings

Hartshorne, *Algebraic Geometry*, I.6, proof of Lemma 6.5 (p. 41).

A function-field DVR containing a Dedekind subring of its fraction field is the
localization of that subring at the contraction of the DVR's maximal ideal.
-/

namespace Hartshorne

open IsDedekindDomain IsLocalRing

universe u v w

namespace FunctionFieldDVR

variable {k : Type u} {B : Type v} {K : Type w}
variable [Field k] [CommRing B] [Field K] [Algebra k K] [Algebra B K]

/-- The center on `B` of a function-field DVR of `K` which contains `B`. -/
def center (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) : Ideal B :=
  (maximalIdeal R.toValuationSubring).comap
    ((algebraMap B K).codRestrict R.toValuationSubring.toSubring hB)

/-- Membership in the center is membership of the image in the DVR's maximal
ideal. -/
theorem mem_center_iff (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) (b : B) :
    b ∈ R.center hB ↔
      (⟨algebraMap B K b, hB b⟩ : R.toValuationSubring) ∈
        maximalIdeal R.toValuationSubring :=
  Iff.rfl

instance center_isPrime (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) :
    (R.center hB).IsPrime :=
  Ideal.comap_isPrime _ _

/-- The underlying valuation subring of a function-field DVR is proper in its
ambient field. -/
theorem toValuationSubring_ne_top (R : FunctionFieldDVR k K) :
    R.toValuationSubring ≠ ⊤ := by
  intro hR
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (IsDiscreteValuationRing.not_a_field R.toValuationSubring)
  have hπK : (π : K) ≠ 0 := by
    intro h
    apply hπ0
    exact Subtype.ext h
  have hinv : (π : K)⁻¹ ∈ R.toValuationSubring := by
    change (π : K)⁻¹ ∈ (R.toValuationSubring : Set K)
    have hset : (R.toValuationSubring : Set K) = Set.univ :=
      congrArg SetLike.coe hR
    rw [hset]
    exact Set.mem_univ _
  let πinv : R.toValuationSubring := ⟨(π : K)⁻¹, hinv⟩
  have hprod : πinv * π ∈ maximalIdeal R.toValuationSubring :=
    (maximalIdeal R.toValuationSubring).mul_mem_left πinv hπ
  have hprod_eq : πinv * π = 1 := by
    apply Subtype.ext
    simp [πinv, hπK]
  have hone : (1 : R.toValuationSubring) ∈ maximalIdeal R.toValuationSubring := by
    rwa [hprod_eq] at hprod
  exact (maximalIdeal.isMaximal R.toValuationSubring).ne_top
    ((Ideal.eq_top_iff_one _).mpr hone)

/-- The center of a function-field DVR on a fraction subring is nonzero. -/
theorem center_ne_bot [IsDomain B] [IsFractionRing B K]
    (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) :
    R.center hB ≠ ⊥ := by
  intro hcenter
  apply R.toValuationSubring_ne_top
  apply top_unique
  intro x _
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective B x
  have hb0 : algebraMap B K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hb_center : b ∉ R.center hB := by
    intro hb'
    have : b ∈ (⊥ : Ideal B) := hcenter ▸ hb'
    exact (nonZeroDivisors.ne_zero hb) (by simpa using this)
  have hb_unit : IsUnit (⟨algebraMap B K b, hB b⟩ : R.toValuationSubring) := by
    simpa [mem_center_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hb_center
  have hb_val : R.toValuationSubring.valuation (algebraMap B K b) = 1 :=
    (R.toValuationSubring.valuation_eq_one_iff
      (⟨algebraMap B K b, hB b⟩ : R.toValuationSubring)).mp hb_unit
  have hb_inv : (algebraMap B K b)⁻¹ ∈ R.toValuationSubring := by
    rw [← R.toValuationSubring.valuation_le_one_iff,
      map_inv₀, hb_val, inv_one]
  rw [← hab, div_eq_mul_inv]
  exact R.toValuationSubring.mul_mem _ _ (hB a) hb_inv

/-- The center, packaged as a height-one prime of the Dedekind subring. -/
def centerHeightOne [IsDedekindDomain B] [IsFractionRing B K]
    (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) :
    HeightOneSpectrum B where
  asIdeal := R.center hB
  isPrime := inferInstance
  ne_bot := R.center_ne_bot hB

/-- The center of a function-field DVR on a Dedekind subring is maximal. -/
theorem center_isMaximal [IsDedekindDomain B] [IsFractionRing B K]
    (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) :
    (R.center hB).IsMaximal :=
  (R.centerHeightOne hB).isMaximal

/-- The localization of a Dedekind subring at the center of a containing DVR,
realized inside the common fraction field, is exactly that DVR. -/
theorem localizationAtCenter_eq [IsDedekindDomain B] [IsFractionRing B K]
    (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
      (R.centerHeightOne hB) =
      R.toValuationSubring := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ R.toValuationSubring_ne_top
  rintro x ⟨a, s, hs, rfl⟩
  have hs_center : s ∉ R.center hB := by
    simpa [Ideal.primeCompl, centerHeightOne] using hs
  have hs_unit : IsUnit (⟨algebraMap B K s, hB s⟩ : R.toValuationSubring) := by
    simpa [mem_center_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hs_center
  have hs_val : R.toValuationSubring.valuation (algebraMap B K s) = 1 :=
    (R.toValuationSubring.valuation_eq_one_iff
      (⟨algebraMap B K s, hB s⟩ : R.toValuationSubring)).mp hs_unit
  have hs_inv : (algebraMap B K s)⁻¹ ∈ R.toValuationSubring := by
    rw [← R.toValuationSubring.valuation_le_one_iff,
      map_inv₀, hs_val, inv_one]
  exact R.toValuationSubring.mul_mem _ _ (hB a) hs_inv

/-- The abstract localization at the center is canonically ring-equivalent to
the containing DVR. -/
noncomputable def localizationAtCenterEquiv
    [IsDedekindDomain B] [IsFractionRing B K]
    (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) :
    Localization.AtPrime (R.center hB) ≃+* R.toValuationSubring := by
  change Localization.AtPrime (R.centerHeightOne hB).asIdeal ≃+*
    R.toValuationSubring
  rw [← R.localizationAtCenter_eq hB]
  exact (IsLocalization.algEquiv (R.centerHeightOne hB).asIdeal.primeCompl
    (Localization.AtPrime (R.centerHeightOne hB).asIdeal)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
      (R.centerHeightOne hB))).toRingEquiv

/-- Two function-field DVRs containing the same Dedekind subring and having the
same center are equal. -/
theorem center_injective [IsDedekindDomain B] [IsFractionRing B K]
    {R S : FunctionFieldDVR k K}
    (hR : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring)
    (hS : ∀ b : B, algebraMap B K b ∈ S.toValuationSubring)
    (hcenter : R.center hR = S.center hS) : R = S := by
  have hheight : R.centerHeightOne hR = S.centerHeightOne hS := by
    apply HeightOneSpectrum.ext
    exact hcenter
  have hvaluation : R.toValuationSubring = S.toValuationSubring := by
    calc
      R.toValuationSubring =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
            (R.centerHeightOne hR) :=
        (R.localizationAtCenter_eq hR).symm
      _ = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
          (S.centerHeightOne hS) := by rw [hheight]
      _ = S.toValuationSubring := S.localizationAtCenter_eq hS
  apply FunctionFieldDVR.ext
  intro x
  rw [hvaluation]

end FunctionFieldDVR

end Hartshorne
