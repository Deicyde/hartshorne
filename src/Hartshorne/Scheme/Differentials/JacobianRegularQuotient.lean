/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RegularQuotientCotangentIndependent
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Elements with independent differentials cut out a regular local ring

Let `P` be a `k`-algebra, `Q` a prime of `P` with `P_Q` a regular local ring, and let
`f₁, …, f_c ∈ Q` have `κ(Q)`-linearly independent differentials `1 ⊗ d fᵢ` in
`κ(Q) ⊗_P Ω_{P/k}`. Then the classes of the `fᵢ` in the cotangent space of `P_Q` are linearly
independent (the conormal map `𝔪/𝔪² → κ ⊗ Ω` sends them to the `1 ⊗ d fᵢ`), so `P_Q ⧸ (f)` is a
regular local ring of dimension `ht Q - c`.

The main application is to a polynomial ring `P = k[x₁, …, x_N]` over a field, all of whose
localizations at primes are regular: this is the local computation behind the dimension of a
smooth scheme over a field and the differential criterion for smoothness over a field, used to
compare Hartshorne's definition of a smooth morphism (III.10, p. 268) with the standard smooth
predicate.

## Main results

* `Hartshorne.linearIndependent_toCotangent_localization_of_linearIndependent_D`
* `Hartshorne.isRegularLocalRing_localization_quotient_of_linearIndependent_D`
* `Hartshorne.ringKrullDim_localization_quotient_add_card_of_linearIndependent_D`
-/

namespace Hartshorne

open IsLocalRing Ideal Module KaehlerDifferential TensorProduct

variable {k P : Type*} [CommRing k] [CommRing P] [Algebra k P] (Q : Ideal P) [Q.IsPrime]

/-- The element `f / 1` of the maximal ideal of `P_Q`, for `f ∈ Q`. -/
noncomputable def localizationMaximalIdealMk (f : P) (hf : f ∈ Q) :
    maximalIdeal (Localization.AtPrime Q) :=
  ⟨algebraMap P (Localization.AtPrime Q) f, by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hf⟩

/-- The conormal map from the cotangent space of `P_Q` to `κ(Q) ⊗_P Ω_{P/k}`, sending the class
of `f / 1` to `1 ⊗ d f`. -/
theorem exists_cotangentSpace_localization_toTensor :
    ∃ ψ : CotangentSpace (Localization.AtPrime Q) →ₗ[Q.ResidueField] Q.ResidueField ⊗[P] Ω[P⁄k],
      ∀ (f : P) (hf : f ∈ Q),
        ψ ((maximalIdeal _).toCotangent (localizationMaximalIdealMk Q f hf)) =
          (1 : Q.ResidueField) ⊗ₜ D k P f := by
  let B := Localization.AtPrime Q
  let κ := Q.ResidueField
  have : Algebra.FormallyEtale P B := .of_isLocalization Q.primeCompl
  let e := tensorKaehlerEquivOfFormallyEtale k P B
  have hker : maximalIdeal B = RingHom.ker (algebraMap B κ) :=
    (IsLocalRing.ker_residue (R := B)).symm
  let ψB : CotangentSpace B →ₗ[B] κ ⊗[P] Ω[P⁄k] :=
    ((AlgebraTensorModule.cancelBaseChange P B κ κ Ω[P⁄k]).restrictScalars B).toLinearMap ∘ₗ
      (e.symm.toLinearMap.lTensor κ) ∘ₗ kerCotangentToTensor k B κ ∘ₗ
      (Cotangent.equivOfEq _ _ hker).toLinearMap
  refine ⟨ψB.extendScalarsOfSurjective IsLocalRing.residue_surjective, fun f hf => ?_⟩
  change ψB _ = _
  change AlgebraTensorModule.cancelBaseChange P B κ κ Ω[P⁄k]
    (1 ⊗ₜ e.symm (D k B (algebraMap P B f))) = _
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- If `f₁, …, f_c ∈ Q` have linearly independent differentials `1 ⊗ d fᵢ` in `κ(Q) ⊗_P Ω_{P/k}`,
then the classes of the `fᵢ / 1` in the cotangent space of `P_Q` are linearly independent. -/
theorem linearIndependent_toCotangent_localization_of_linearIndependent_D {ι : Type*}
    (f : ι → P) (hf : ∀ i, f i ∈ Q)
    (hli : LinearIndependent Q.ResidueField
      (fun i => (1 : Q.ResidueField) ⊗ₜ[P] D k P (f i))) :
    LinearIndependent Q.ResidueField (fun i =>
      ((maximalIdeal _).toCotangent (localizationMaximalIdealMk Q (f i) (hf i)) :
        CotangentSpace (Localization.AtPrime Q))) := by
  obtain ⟨ψ, hψ⟩ := exists_cotangentSpace_localization_toTensor (k := k) Q
  apply LinearIndependent.of_comp ψ
  convert hli using 1
  ext i
  exact hψ (f i) (hf i)

variable [IsRegularLocalRing (Localization.AtPrime Q)]

/-- Let `P_Q` be a regular local ring and let `f₁, …, f_c ∈ Q` have linearly independent
differentials in `κ(Q) ⊗_P Ω_{P/k}`. Then `P_Q ⧸ (f₁, …, f_c)` is a regular local ring. -/
theorem isRegularLocalRing_localization_quotient_of_linearIndependent_D {ι : Type*} [Fintype ι]
    (f : ι → P) (hf : ∀ i, f i ∈ Q)
    (hli : LinearIndependent Q.ResidueField
      (fun i => (1 : Q.ResidueField) ⊗ₜ[P] D k P (f i))) :
    IsRegularLocalRing (Localization.AtPrime Q ⧸
      span (Set.range fun i => algebraMap P (Localization.AtPrime Q) (f i))) :=
  isRegularLocalRing_quotient_span_range_of_linearIndependent
    (fun i => localizationMaximalIdealMk Q (f i) (hf i))
    (linearIndependent_toCotangent_localization_of_linearIndependent_D Q f hf hli)

/-- Let `P_Q` be a regular local ring and let `f₁, …, f_c ∈ Q` have linearly independent
differentials in `κ(Q) ⊗_P Ω_{P/k}`. Then `dim P_Q ⧸ (f₁, …, f_c) + c = ht Q`. -/
theorem ringKrullDim_localization_quotient_add_card_of_linearIndependent_D {ι : Type*}
    [Fintype ι] (f : ι → P) (hf : ∀ i, f i ∈ Q)
    (hli : LinearIndependent Q.ResidueField
      (fun i => (1 : Q.ResidueField) ⊗ₜ[P] D k P (f i))) :
    ringKrullDim (Localization.AtPrime Q ⧸
        span (Set.range fun i => algebraMap P (Localization.AtPrime Q) (f i))) +
      Fintype.card ι = Q.height := by
  rw [← IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
  exact ringKrullDim_quotient_span_range_add_card_of_linearIndependent
    (fun i => localizationMaximalIdealMk Q (f i) (hf i))
    (linearIndependent_toCotangent_localization_of_linearIndependent_D Q f hf hli)

end Hartshorne
