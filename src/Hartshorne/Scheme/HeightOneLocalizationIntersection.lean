/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Intersection of height-one localizations

Hartshorne, *Algebraic Geometry*, II, Proposition 6.3A (p. 132), citing Matsumura,
*Commutative Algebra*, Theorem 38 (p. 124).

Let `A` be an integrally closed Noetherian domain with fraction field `K`. Inside `K`, the
image of `A` is the intersection of the localizations `A_𝔭` over the primes `𝔭` of height one.

The proof follows Matsumura. Write `x = c / a`. If `c ∉ aA`, the annihilator of the class of `c`
in `A ⧸ aA` lies in an associated prime `𝔭 = (aA : y)` of `A ⧸ aA`. In the localization `A_𝔭`
the maximal ideal is `(a A_𝔭 : y)`, and integral closedness forces it to be principal (the
argument of `maximalIdeal_isPrincipal_of_isDedekindDomain`), so `A_𝔭` is a discrete valuation
ring and `𝔭` has height one. Then `x ∈ A_𝔭` puts an element outside `𝔭` into `(aA : c) ⊆ 𝔭`.

## Main results

* `Hartshorne.iInf_localization_height_one_eq_bot`: the intersection form.
* `Hartshorne.exists_algebraMap_eq_of_forall_height_one`: an element of `K` lying in `A_𝔭` for
  every height-one prime `𝔭` lies in `A`.
-/

namespace Hartshorne

open IsLocalRing

section Local

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
  [IsIntegrallyClosed R]

/-- In an integrally closed Noetherian local domain, if the maximal ideal is `(a : b)` for some
`a ≠ 0` in the maximal ideal and `b ∉ (a)`, then the maximal ideal is principal. This is the
second half of the proof of `maximalIdeal_isPrincipal_of_isDedekindDomain`. -/
theorem maximalIdeal_isPrincipal_of_colon {a b : R} (ha₁ : a ∈ maximalIdeal R) (ha₂ : a ≠ 0)
    (hb₂ : b ∉ Ideal.span {a}) (hb₃ : ∀ m ∈ maximalIdeal R, ∃ k : R, k * a = b * m) :
    (maximalIdeal R).IsPrincipal := by
  have hb₄ : b ≠ 0 := by rintro rfl; apply hb₂; exact zero_mem _
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have ha₃ : algebraMap R K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha₂
  by_cases hx : ∀ y ∈ M, x * y ∈ M
  · have := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral this
      refine (hb₂ (Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul, e, div_mul_cancel₀ _ ha₃]
    · rw [Submodule.ne_bot_iff]; refine ⟨_, ⟨a, ha₁, rfl⟩, ?_⟩
      exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr ha₂
    · apply Submodule.FG.map; exact IsNoetherian.noetherian _
  · have :
        (M.map (DistribSMul.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
      contrapose! hx with h
      rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hb₃ m hm
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel_right₀ _ ha₃]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ maximalIdeal R, b * y = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at this
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := this
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq ha₃, ← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine ⟨⟨y, ?_⟩⟩
    apply le_antisymm
    · intro m hm; obtain ⟨k, hk⟩ := hb₃ m hm; rw [← hy₂, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb₄ hk, mul_comm]; exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rwa [Submodule.span_le, Set.singleton_subset_iff]

end Local

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

/-- In an integrally closed Noetherian domain, a prime of the form `(aA : y)` with `a ≠ 0` has
height one. -/
theorem height_eq_one_of_eq_colon {a y : A} (ha : a ≠ 0) (P : Ideal A) [P.IsPrime]
    (hP : ∀ r, r ∈ P ↔ r * y ∈ Ideal.span {a}) : P.height = 1 := by
  let R := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap A R) :=
    IsLocalization.injective R P.primeCompl_le_nonZeroDivisors
  have : IsIntegrallyClosed R := isIntegrallyClosed_of_isLocalization (R := A) R P.primeCompl
    P.primeCompl_le_nonZeroDivisors
  have haP : a ∈ P := (hP a).mpr (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a))
  have ha₁ : algebraMap A R a ∈ maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ haP
  have ha₂ : algebraMap A R a ≠ 0 := by
    rwa [Ne, ← map_zero (algebraMap A R), hinj.eq_iff]
  have hb₂ : algebraMap A R y ∉ Ideal.span {algebraMap A R a} := by
    intro h
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
    obtain ⟨⟨u, s⟩, hus⟩ := IsLocalization.surj P.primeCompl r
    have : algebraMap A R (s * y) = algebraMap A R (u * a) := by
      rw [map_mul, map_mul, ← hr, ← hus]; ring
    have hsP : (s : A) ∈ P :=
      (hP s).mpr (Ideal.mem_span_singleton'.mpr ⟨u, (hinj this).symm⟩)
    exact s.2 hsP
  have hb₃ : ∀ m ∈ maximalIdeal R, ∃ k : R, k * algebraMap A R a = algebraMap A R y * m := by
    intro m hm
    obtain ⟨⟨q, s⟩, hqs⟩ := IsLocalization.surj P.primeCompl m
    simp only at hqs
    have hq : q ∈ P := by
      have : algebraMap A R q ∈ maximalIdeal R := by
        rw [← hqs]; exact Ideal.mul_mem_right _ _ hm
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff R P q).mp this
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp ((hP q).mp hq)
    have hs1 : algebraMap A R s * IsLocalization.mk' R (1 : A) s = 1 := by
      rw [mul_comm, IsLocalization.mk'_spec, map_one]
    refine ⟨algebraMap A R t * IsLocalization.mk' R (1 : A) s, ?_⟩
    calc algebraMap A R t * IsLocalization.mk' R (1 : A) s * algebraMap A R a
        = algebraMap A R (t * a) * IsLocalization.mk' R (1 : A) s := by rw [map_mul]; ring
      _ = algebraMap A R y * (m * algebraMap A R s) * IsLocalization.mk' R (1 : A) s := by
        rw [ht, hqs, map_mul]; ring
      _ = algebraMap A R y * m * (algebraMap A R s * IsLocalization.mk' R (1 : A) s) := by ring
      _ = algebraMap A R y * m := by rw [hs1, mul_one]
  have hprinc := maximalIdeal_isPrincipal_of_colon ha₁ ha₂ hb₂ hb₃
  have hnf : ¬ IsField R := by
    intro hf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at ha₁
    exact ha₂ ha₁
  have : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 0 4).mpr hprinc
  have hPR : P.height = (maximalIdeal R).height := by
    rw [← IsLocalization.height_under P.primeCompl (maximalIdeal R),
      IsLocalization.AtPrime.under_maximalIdeal R P]
  have h1 : ((maximalIdeal R).height : WithBot ℕ∞) = 1 := by
    rw [maximalIdeal_height_eq_ringKrullDim, IsDiscreteValuationRing.ringKrullDim_eq_one]
  rw [hPR]
  exact_mod_cast h1

/-- **Hartshorne, Proposition II.6.3A** (pointwise form). Let `A` be an integrally closed
Noetherian domain with fraction field `K`. An element of `K` that lies in the image of `A_𝔭` for
every prime `𝔭` of height one lies in the image of `A`. -/
theorem exists_algebraMap_eq_of_forall_height_one (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (x : K)
    (hx : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      x ∈ Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors) :
    ∃ a : A, algebraMap A K a = x := by
  obtain ⟨c, a, ha, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have haK : algebraMap A K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
  by_cases hc : c ∈ Ideal.span {a}
  · obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hc
    exact ⟨r, by rw [← hr, map_mul, mul_div_cancel_right₀ _ haK]⟩
  exfalso
  let M := A ⧸ Ideal.span {a}
  have hcolon : ∀ r z : A,
      r ∈ (⊥ : Submodule A M).colon {Ideal.Quotient.mk _ z} ↔ r * z ∈ Ideal.span {a} := by
    intro r z
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have hc0 : (Ideal.Quotient.mk (Ideal.span {a}) c : M) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hc0
  obtain ⟨hPprime, yb, hPy⟩ := isAssociatedPrime_iff.mp hPass
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  have hP : ∀ r, r ∈ P ↔ r * y ∈ Ideal.span {a} := fun r ↦ by rw [hPy, hcolon]
  obtain ⟨u, s, hs, hus⟩ := hx P (height_eq_one_of_eq_colon ha0 P hP)
  have hsK : algebraMap A K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (P.primeCompl_le_nonZeroDivisors hs)
  have hsc : s * c = u * a := by
    apply IsFractionRing.injective A K
    rw [map_mul, map_mul]
    rw [div_eq_iff haK, mul_assoc, mul_comm _ (algebraMap A K a), ← mul_assoc,
      eq_mul_inv_iff_mul_eq₀ hsK] at hus
    rw [mul_comm, hus]
  exact hs (hle ((hcolon s c).mpr (Ideal.mem_span_singleton'.mpr ⟨u, hsc.symm⟩)))

/-- **Hartshorne, Proposition II.6.3A**. Let `A` be an integrally closed Noetherian domain with
fraction field `K`. Inside `K`, the image of `A` is the intersection of the images of the
localizations `A_𝔭` over the primes `𝔭` of height one. -/
theorem iInf_localization_height_one_eq_bot (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] :
    (⨅ P : {P : PrimeSpectrum A // P.asIdeal.height = 1},
      Localization.subalgebra.ofField K _ P.1.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_iInf, Algebra.mem_bot]
  constructor
  · intro hx
    exact exists_algebraMap_eq_of_forall_height_one K x fun P _ hP ↦ hx ⟨⟨P, ‹_›⟩, hP⟩
  · rintro ⟨a, rfl⟩ P
    exact Subalgebra.algebraMap_mem _ a

end Hartshorne
