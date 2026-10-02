/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.PrimeFiltrationSupport
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Multiplicity in a graded prime filtration

Hartshorne, *Algebraic Geometry*, Proposition I.7.4(b) (p. 51).
-/

namespace Hartshorne

noncomputable section

variable {R A M : Type*}
  [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (𝓐 : ℤ → Submodule R A) [GradedAlgebra 𝓐]
  (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul 𝓐 ℳ]

local instance : DecidableEq (PrimeSpectrum A) := Classical.decEq _

/-- The length of a module after localization at a prime. -/
noncomputable def gradedMultiplicity
    (A M : Type*) [CommRing A] [AddCommGroup M] [Module A M]
    (p : PrimeSpectrum A) : ℕ∞ :=
  Module.length (Localization.AtPrime p.1)
    (LocalizedModule p.1.primeCompl M)

private theorem localizedModuleMap_exact
    {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module A X] [Module A Y] [Module A Z]
    (S : Submonoid A) (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z)
    (h : Function.Exact f g) :
    Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) := by
  have hloc := LocalizedModule.map_exact S f g h
  have hf :
      ⇑(LocalizedModule.map S f) =
        ⇑((IsLocalizedModule.map S
          (LocalizedModule.mkLinearMap S X)
          (LocalizedModule.mkLinearMap S Y)) f) := by
    funext x
    have hx := congrFun
      (LocalizedModule.coe_map_eq
        (R := A) (S := S)
        (LocalizedModule.mkLinearMap S X)
        (LocalizedModule.mkLinearMap S Y) f) x
    simpa [IsLocalizedModule.iso_localizedModule_eq_refl] using hx
  have hg :
      ⇑(LocalizedModule.map S g) =
        ⇑((IsLocalizedModule.map S
          (LocalizedModule.mkLinearMap S Y)
          (LocalizedModule.mkLinearMap S Z)) g) := by
    funext x
    have hx := congrFun
      (LocalizedModule.coe_map_eq
        (R := A) (S := S)
        (LocalizedModule.mkLinearMap S Y)
        (LocalizedModule.mkLinearMap S Z) g) x
    simpa [IsLocalizedModule.iso_localizedModule_eq_refl] using hx
  rw [hf, hg]
  exact hloc

private noncomputable def localizedLinearEquiv
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y]
    (S : Submonoid A) (e : X ≃ₗ[A] Y) :
    LocalizedModule S X ≃ₗ[Localization S] LocalizedModule S Y :=
  IsLocalizedModule.mapEquiv S
    (LocalizedModule.mkLinearMap S X)
    (LocalizedModule.mkLinearMap S Y) (Localization S) e

/-- Length is additive after localizing one inclusion/quotient step. -/
private theorem length_localized_step_eq_add
    {N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ} (P : PrimeSpectrum A)
    (h : N₁ ≤ N₂) :
    Module.length (Localization.AtPrime P.1)
        (LocalizedModule P.1.primeCompl N₂) =
      Module.length (Localization.AtPrime P.1)
          (LocalizedModule P.1.primeCompl N₁) +
        Module.length (Localization.AtPrime P.1)
          (LocalizedModule P.1.primeCompl
            (N₂ ⧸ (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule)) := by
  let Q := (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h).toSubmodule
  let S := P.1.primeCompl
  let f := LocalizedModule.map S Q.subtype
  let g := LocalizedModule.map S Q.mkQ
  have hf : Function.Injective f :=
    LocalizedModule.map_injective S Q.subtype
      (Submodule.injective_subtype Q)
  have hg : Function.Surjective g :=
    LocalizedModule.map_surjective S Q.mkQ
      (Submodule.mkQ_surjective Q)
  have hex : Function.Exact f g :=
    localizedModuleMap_exact S Q.subtype Q.mkQ
      (LinearMap.exact_subtype_mkQ Q)
  have hlen :
      Module.length (Localization S) (LocalizedModule S N₂) =
        Module.length (Localization S) (LocalizedModule S Q) +
          Module.length (Localization S) (LocalizedModule S (N₂ ⧸ Q)) :=
    Module.length_eq_add_of_exact
      (R := Localization S) (M := LocalizedModule S N₂)
      (N := LocalizedModule S Q) (P := LocalizedModule S (N₂ ⧸ Q))
      f g hf hg hex
  let e : LocalizedModule S Q ≃ₗ[Localization S]
      LocalizedModule S N₁ :=
    localizedLinearEquiv S (Submodule.submoduleOfEquivOfLe h)
  have he : Module.length (Localization S) (LocalizedModule S Q) =
      Module.length (Localization S) (LocalizedModule S N₁) :=
    e.length_eq
  rw [he] at hlen
  exact hlen

/-- The localization of `A / P` at `P` is the residue field of the local
ring `A_P`. -/
private noncomputable def localizedQuotientAtPrimeEquivResidue
    (P : PrimeSpectrum A) :
    LocalizedModule P.1.primeCompl (A ⧸ P.1) ≃ₗ[Localization.AtPrime P.1]
      (Localization.AtPrime P.1 ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P.1)) :=
  (localizedQuotientEquiv P.1.primeCompl P.1).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by
      change Submodule.localized' (Localization.AtPrime P.1)
        P.1.primeCompl (Algebra.linearMap A (Localization.AtPrime P.1)) P.1 = _
      rw [Ideal.localized'_eq_map,
        Localization.AtPrime.map_eq_maximalIdeal])

private theorem length_localized_quotient_atPrime_eq_one
    (P : PrimeSpectrum A) :
    Module.length (Localization.AtPrime P.1)
        (LocalizedModule P.1.primeCompl (A ⧸ P.1)) = 1 := by
  rw [(localizedQuotientAtPrimeEquivResidue P).length_eq,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def]
  exact IsLocalRing.maximalIdeal.isMaximal _

/-- At a minimal factor prime, a localized filtration factor has length one
exactly when its selected prime is that prime, and otherwise has length zero. -/
private theorem length_localized_factor_eq_ite
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (P : PrimeSpectrum A)
    (hmin : Minimal (IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s) P)
    (i : Fin s.length) :
    let d := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
    Module.length (Localization.AtPrime P.1)
        (LocalizedModule P.1.primeCompl
          (s i.succ ⧸
            (gradedSubmoduleOf 𝓐 ℳ
              (s (Fin.castSucc i)) (s i.succ) d.le).toSubmodule)) =
      if gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i = P then 1 else 0 := by
  dsimp only
  let d := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
  let q := gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i
  have hfactor : IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s q :=
    ⟨i, gradedPrimeFiltrationFactorPrime_spec 𝓐 ℳ s i⟩
  by_cases hq : q = P
  · subst P
    rw [if_pos rfl]
    let e : LocalizedModule q.1.primeCompl (A ⧸ q.1) ≃ₗ[Localization.AtPrime q.1]
        LocalizedModule q.1.primeCompl
          (s i.succ ⧸
            (gradedSubmoduleOf 𝓐 ℳ
              (s (Fin.castSucc i)) (s i.succ) d.le).toSubmodule) :=
      localizedLinearEquiv q.1.primeCompl d.equiv.toLinearEquiv
    have he : Module.length (Localization.AtPrime q.1)
        (LocalizedModule q.1.primeCompl (A ⧸ q.1)) =
      Module.length (Localization.AtPrime q.1)
        (LocalizedModule q.1.primeCompl
          (s i.succ ⧸
            (gradedSubmoduleOf 𝓐 ℳ
              (s (Fin.castSucc i)) (s i.succ) d.le).toSubmodule)) :=
      e.length_eq
    rw [← he]
    exact length_localized_quotient_atPrime_eq_one q
  · rw [if_neg hq]
    have hnle : ¬ q ≤ P := by
      intro hqP
      exact hq (le_antisymm hqP (hmin.2 hfactor hqP))
    have hnle' : ¬ q.1 ≤ P.1 := hnle
    obtain ⟨a, haq, haP⟩ := SetLike.not_le_iff_exists.mp hnle'
    have hann :
        Module.annihilator A
            (s i.succ ⧸
              (gradedSubmoduleOf 𝓐 ℳ
                (s (Fin.castSucc i)) (s i.succ) d.le).toSubmodule) =
          q.1 :=
      annihilator_gradedFactorPiece_eq 𝓐 ℳ d.le
        (gradedPrimeFiltrationFactorPrime_spec 𝓐 ℳ s i)
    have haann : a ∈ Module.annihilator A
        (s i.succ ⧸
          (gradedSubmoduleOf 𝓐 ℳ
            (s (Fin.castSucc i)) (s i.succ) d.le).toSubmodule) :=
      hann.symm ▸ haq
    have hsub : Subsingleton
        (LocalizedModule P.1.primeCompl
          (s i.succ ⧸
            (gradedSubmoduleOf 𝓐 ℳ
              (s (Fin.castSucc i)) (s i.succ) d.le).toSubmodule)) := by
      rw [LocalizedModule.subsingleton_iff]
      intro m
      refine ⟨a, ?_, Module.mem_annihilator.mp haann m⟩
      simpa [Ideal.primeCompl] using haP
    exact Module.length_eq_zero

private theorem length_localized_series_eq_sum
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (P : PrimeSpectrum A)
    (hmin : Minimal (IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s) P) :
    ∀ (n : ℕ) (hn : n ≤ s.length),
      Module.length (Localization.AtPrime P.1)
          (LocalizedModule P.1.primeCompl
            (s ⟨n, Nat.lt_succ_of_le hn⟩)) =
        Module.length (Localization.AtPrime P.1)
            (LocalizedModule P.1.primeCompl s.head) +
          ∑ j : Fin n,
            if gradedPrimeFiltrationFactorPrime 𝓐 ℳ s
                (Fin.castLE hn j) = P then 1 else 0 := by
  intro n hn
  induction n with
  | zero =>
      rw [show s ⟨0, Nat.lt_succ_of_le hn⟩ = s.head from rfl]
      simp
  | succ n ih =>
      have hnlt : n < s.length := Nat.lt_of_succ_le hn
      have hnle : n ≤ s.length := Nat.le_trans (Nat.le_succ n) hn
      let i : Fin s.length := ⟨n, hnlt⟩
      let d := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
      have hstep := length_localized_step_eq_add 𝓐 ℳ P d.le
      have hfactor := length_localized_factor_eq_ite 𝓐 ℳ s P hmin i
      have hfactor' :
          Module.length (Localization.AtPrime P.1)
              (LocalizedModule P.1.primeCompl
                (s i.succ ⧸
                  (gradedSubmoduleOf 𝓐 ℳ
                    (s (Fin.castSucc i)) (s i.succ) d.le).toSubmodule)) =
            if gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i = P
              then 1 else 0 := by
        simpa [d] using hfactor
      have hprev :
          Module.length (Localization.AtPrime P.1)
              (LocalizedModule P.1.primeCompl (s (Fin.castSucc i))) =
            Module.length (Localization.AtPrime P.1)
                (LocalizedModule P.1.primeCompl s.head) +
              ∑ j : Fin n,
                if gradedPrimeFiltrationFactorPrime 𝓐 ℳ s
                    (Fin.castLE hnle j) = P then 1 else 0 := by
        simpa [i] using ih hnle
      have hcast (j : Fin n) :
          Fin.castLE hn j.castSucc = Fin.castLE hnle j := by
        apply Fin.ext
        rfl
      have hlast : Fin.castLE hn (Fin.last n) = i := by
        apply Fin.ext
        rfl
      calc
        Module.length (Localization.AtPrime P.1)
            (LocalizedModule P.1.primeCompl
              (s ⟨n + 1, Nat.lt_succ_of_le hn⟩)) =
            Module.length (Localization.AtPrime P.1)
                (LocalizedModule P.1.primeCompl (s (Fin.castSucc i))) +
              Module.length (Localization.AtPrime P.1)
                (LocalizedModule P.1.primeCompl
                  (s i.succ ⧸
                    (gradedSubmoduleOf 𝓐 ℳ
                      (s (Fin.castSucc i)) (s i.succ) d.le).toSubmodule)) := by
          simpa [i, d] using hstep
        _ =
            (Module.length (Localization.AtPrime P.1)
                (LocalizedModule P.1.primeCompl s.head) +
              ∑ j : Fin n,
                if gradedPrimeFiltrationFactorPrime 𝓐 ℳ s
                    (Fin.castLE hnle j) = P then 1 else 0) +
              (if gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i = P
                then 1 else 0) := by
          rw [hprev, hfactor']
        _ =
            Module.length (Localization.AtPrime P.1)
                (LocalizedModule P.1.primeCompl s.head) +
              ∑ j : Fin (n + 1),
                if gradedPrimeFiltrationFactorPrime 𝓐 ℳ s
                    (Fin.castLE hn j) = P then 1 else 0 := by
          rw [Fin.sum_univ_castSucc]
          simp_rw [hcast]
          rw [hlast, add_assoc]

/-- At a prime minimal over the annihilator, the localized length of a module
is the number of occurrences of that prime in any graded prime filtration. -/
theorem gradedPrimeFiltration_multiplicity_eq_count
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (P : PrimeSpectrum A)
    (hP : (Module.annihilator A M).IsMinimalPrime P.1) :
    gradedMultiplicity A M P =
      ((Finset.filter
        (fun i : Fin s.length =>
          gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i = P)
        Finset.univ).card : ℕ∞) := by
  have hmin : Minimal (IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s) P :=
    (gradedPrimeFiltration_minimal_factor_iff
      𝓐 ℳ s hshead hslast P).2 hP
  have hsum := length_localized_series_eq_sum
    𝓐 ℳ s P hmin s.length le_rfl
  have hhead : Module.length (Localization.AtPrime P.1)
      (LocalizedModule P.1.primeCompl s.head) = 0 := by
    rw [hshead]
    change Module.length (Localization.AtPrime P.1)
      (LocalizedModule P.1.primeCompl (⊥ : Submodule A M)) = 0
    exact Module.length_eq_zero
  have hlast : Module.length (Localization.AtPrime P.1)
      (LocalizedModule P.1.primeCompl s.last) = gradedMultiplicity A M P := by
    rw [hslast]
    change Module.length (Localization.AtPrime P.1)
      (LocalizedModule P.1.primeCompl (⊤ : Submodule A M)) =
        Module.length (Localization.AtPrime P.1)
          (LocalizedModule P.1.primeCompl M)
    exact (localizedLinearEquiv P.1.primeCompl
      (Submodule.topEquiv : (⊤ : Submodule A M) ≃ₗ[A] M)).length_eq
  rw [show s ⟨s.length, Nat.lt_succ_self s.length⟩ = s.last from rfl,
    hlast, hhead, zero_add] at hsum
  calc
    gradedMultiplicity A M P =
        ∑ i : Fin s.length,
          if gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i = P
          then 1 else 0 := by simpa using hsum
    _ = ((Finset.filter
          (fun i : Fin s.length =>
            gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i = P)
          Finset.univ).card : ℕ∞) := by
      simp

/-- In particular, the multiplicity at a minimal prime is finite. -/
theorem gradedPrimeFiltration_multiplicity_ne_top
    (s : RelSeries
      {q : HomogeneousSubmodule 𝓐 ℳ × HomogeneousSubmodule 𝓐 ℳ |
        IsGradedPrimeFiltrationStep 𝓐 ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (P : PrimeSpectrum A)
    (hP : (Module.annihilator A M).IsMinimalPrime P.1) :
    gradedMultiplicity A M P ≠ ⊤ := by
  rw [gradedPrimeFiltration_multiplicity_eq_count
    𝓐 ℳ s hshead hslast P hP]
  simp

end

end Hartshorne
