/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.DedekindAffineModel
import Hartshorne.Curve.DedekindSubringLocalization
import Hartshorne.Curve.SeparableNormalizationCharts

/-!
# Affine models of function-field DVRs

Hartshorne, *Algebraic Geometry*, I.6, Corollary 6.6 (p. 42).

Every function-field DVR is the local ring of a point on a nonsingular affine
curve.  The identifications constructed here commute with the embeddings of
the local rings into the common function field.
-/

namespace Hartshorne

noncomputable section

universe u v w

namespace FunctionFieldDVR

variable {k : Type u} {B : Type v} {K : Type w}
variable [Field k] [CommRing B] [Field K] [Algebra k B] [Algebra B K]
variable [Algebra k K] [IsScalarTower k B K]

/-- The localization equivalence at the center of a function-field DVR can be
promoted to a `k`-algebra equivalence that commutes with the inclusions into
the ambient function field. -/
private theorem exists_localizationAtCenterAlgEquiv
    [IsDedekindDomain B] [IsFractionRing B K]
    (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) :
    ∃ e : Localization.AtPrime (R.center hB) ≃ₐ[k]
        R.toValuationSubring,
      ∀ z : Localization.AtPrime (R.center hB),
        ((e z : R.toValuationSubring) : K) =
          localizationAtPrimeToFractionField (k := k) B K
            (R.center hB) z := by
  let eVR :
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
          (R.centerHeightOne hB) ≃+* R.toValuationSubring :=
    RingEquiv.subringCongr (congrArg
      (fun A : ValuationSubring K ↦ A.toSubring)
      (R.localizationAtCenter_eq hB))
  let _ : Algebra B R.toValuationSubring :=
    (eVR.toRingHom.comp (algebraMap B
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
        (R.centerHeightOne hB)))).toAlgebra
  have hloc : IsLocalization (R.center hB).primeCompl
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
        (R.centerHeightOne hB)) := by
    change IsLocalization (R.centerHeightOne hB).asIdeal.primeCompl
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
        (R.centerHeightOne hB))
    infer_instance
  let _ : IsLocalization (R.center hB).primeCompl R.toValuationSubring :=
    (IsLocalization.isLocalization_iff_of_ringEquiv
      (R.center hB).primeCompl eVR).mp hloc
  let eB : Localization.AtPrime (R.center hB) ≃ₐ[B]
      R.toValuationSubring :=
    IsLocalization.algEquiv (R.center hB).primeCompl _ _
  let e : Localization.AtPrime (R.center hB) ≃ₐ[k]
      R.toValuationSubring :=
    AlgEquiv.ofRingEquiv (f := eB.toRingEquiv) fun c ↦ by
      apply Subtype.ext
      change ((eB (algebraMap k (Localization.AtPrime (R.center hB)) c) :
          R.toValuationSubring) : K) = algebraMap k K c
      have hsource : algebraMap k (Localization.AtPrime (R.center hB)) c =
          algebraMap B (Localization.AtPrime (R.center hB))
            (algebraMap k B c) := by
        rfl
      rw [hsource, eB.commutes]
      change algebraMap B K (algebraMap k B c) = algebraMap k K c
      exact (IsScalarTower.algebraMap_apply k B K c).symm
  refine ⟨e, ?_⟩
  let f : Localization.AtPrime (R.center hB) →+* K :=
    R.toValuationSubring.subtype.comp e.toRingEquiv.toRingHom
  let g : Localization.AtPrime (R.center hB) →+* K :=
    (localizationAtPrimeToFractionField (k := k) B K
      (R.center hB)).toRingHom
  have hfg : f = g := by
    apply IsLocalization.ringHom_ext (R.center hB).primeCompl
    ext b
    change ((e
        (algebraMap B (Localization.AtPrime (R.center hB)) b) :
          R.toValuationSubring) : K) =
      localizationAtPrimeToFractionField (k := k) B K (R.center hB)
        (algebraMap B (Localization.AtPrime (R.center hB)) b)
    rw [localizationAtPrimeToFractionField_algebraMap]
    change ((eB (algebraMap B
      (Localization.AtPrime (R.center hB)) b) :
        R.toValuationSubring) : K) = algebraMap B K b
    rw [eB.commutes]
    change ((eVR (algebraMap B
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K
        (R.centerHeightOne hB)) b) : R.toValuationSubring) : K) =
      algebraMap B K b
    rfl
  intro z
  exact DFunLike.congr_fun hfg z

/-- A function-field DVR containing a finite-type Dedekind subring of
dimension one is the local ring of a point on a nonsingular affine curve. -/
private theorem exists_nonsingular_affine_model_of_dedekind_subring
    [IsAlgClosed k] [IsDedekindDomain B] [Algebra.FiniteType k B]
    [IsFractionRing B K]
    (hdim : ringKrullDim B = 1)
    (R : FunctionFieldDVR k K)
    (hB : ∀ b : B, algebraMap B K b ∈ R.toValuationSubring) :
    ∃ (n : ℕ) (Y : Set (Fin n → k)) (hY : IsAffineVariety Y) (P : Y)
      (eK : FunctionField hY.isIrreducible ≃ₐ[k] K)
      (eR : LocalRingAt hY.isIrreducible P ≃ₐ[k]
        R.toValuationSubring),
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).IsCurve ∧
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).Nonsingular ∧
      ∀ z : LocalRingAt hY.isIrreducible P,
        eK (localToFunctionField hY.isIrreducible P z) =
          (eR z : K) := by
  let _ : (R.center hB).IsMaximal := R.center_isMaximal hB
  obtain ⟨n, Y, hY, P, eB, eK, eP, hcurve, hnonsingular, _, _, hlocal⟩ :=
    exists_dedekind_affine_model (k := k) B K hdim (R.center hB)
  obtain ⟨eCenter, hCenter⟩ :=
    exists_localizationAtCenterAlgEquiv R hB
  let eR : LocalRingAt hY.isIrreducible P ≃ₐ[k]
      R.toValuationSubring :=
    eP.trans eCenter
  refine ⟨n, Y, hY, P, eK, eR, hcurve, hnonsingular, ?_⟩
  intro z
  change eK (localToFunctionField hY.isIrreducible P z) =
    ((eCenter (eP z) :
      R.toValuationSubring) : K)
  rw [hCenter]
  exact hlocal z

/-- **Hartshorne I.6, Corollary 6.6.** Every discrete valuation ring of a
one-dimensional function field is the local ring of a point on a nonsingular
affine curve, compatibly with both rings' embeddings into the function field.
-/
theorem exists_nonsingular_affine_model
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (R : FunctionFieldDVR k K) :
    ∃ (n : ℕ) (Y : Set (Fin n → k)) (hY : IsAffineVariety Y) (P : Y)
      (eK : FunctionField hY.isIrreducible ≃ₐ[k] K)
      (eR : LocalRingAt hY.isIrreducible P ≃ₐ[k]
        R.toValuationSubring),
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).IsCurve ∧
      (Variety.ofQuasiAffine hY.isQuasiAffineVariety).Nonsingular ∧
      ∀ z : LocalRingAt hY.isIrreducible P,
        eK (localToFunctionField hY.isIrreducible P z) =
          (eR z : K) := by
  let C := separableNormalizationCharts k K htrdeg
  rcases C.normalization_cover R with hzero | hinfinity
  · have hB : ∀ b : C.atZero.normalization,
        algebraMap C.atZero.normalization K b ∈ R.toValuationSubring := by
      intro b
      change (b : K) ∈ R.toValuationSubring
      exact hzero b.2
    exact exists_nonsingular_affine_model_of_dedekind_subring
      C.atZero.ringKrullDim_normalization R hB
  · have hB : ∀ b : C.atInfinity.normalization,
        algebraMap C.atInfinity.normalization K b ∈ R.toValuationSubring := by
      intro b
      change (b : K) ∈ R.toValuationSubring
      exact hinfinity b.2
    exact exists_nonsingular_affine_model_of_dedekind_subring
      C.atInfinity.ringKrullDim_normalization R hB

end FunctionFieldDVR

end

end Hartshorne
