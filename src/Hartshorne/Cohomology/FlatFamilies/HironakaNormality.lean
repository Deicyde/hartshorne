/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.DimFormula
import Hartshorne.Dimension.AdjoinRootTrdeg
import Hartshorne.Scheme.SerreNormalityCriterion
import Hartshorne.Scheme.FiniteIntegralClosureField
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Hironaka's normality lemma

Hartshorne, *Algebraic Geometry*, III.9, Lemma 9.12 (pp. 264–265).

Let `A` be a local Noetherian domain essentially of finite type over a field, and let `t ∈ A`.
Assume that `tA` has a unique minimal associated prime `p`, that `t` generates the maximal ideal
of `A_p`, and that `A ⧸ p` is normal. Then `p = tA` and `A` is normal.

"Minimal associated prime of `tA`" is read literally: a minimal element of the set of
associated primes of the `A`-module `A ⧸ tA`. In a Noetherian ring these are exactly the minimal
primes of `tA` (`Hartshorne.Hironaka.minimal_associatedPrimes_eq_minimalPrimes`), which is the
form the proof uses. "Normal" for a domain is `IsIntegrallyClosed`.

## Proof

Let `Ā` be the integral closure of `A` in its fraction field `K`.

* `Ā` is a finite `A`-module: `A` is a localization of a finitely generated `k`-subalgebra `B`,
  whose normalization is finite, and every element of `Ā` has a multiple by a denominator
  lying in the normalization of `B`.
* `A_p` has principal maximal ideal, so it is a discrete valuation ring (or a field) and in
  particular normal; hence every `x ∈ Ā` lies in `A_p`. Its residue class in
  `κ(p) = Frac(A ⧸ p)` is integral over the normal ring `A ⧸ p`, so it comes from some `a ∈ A`,
  and `x - a ∈ t A_p`: there are `b ∈ A`, `s ∉ p` with `s (x - a) = t b`.
* The colon step: if `s ∉ p` and `s z ∈ t Ā` with `z ∈ Ā`, then `z ∈ t Ā`. Otherwise
  some associated prime `Q` of `Ā ⧸ t Ā` contains `s` and `t`, so `q = Q ∩ A` strictly contains
  `p ⊋ 0` and has height at least two. Heights of primes are preserved by contraction along the
  finite birational extension `A ⊆ Ā` (both are essentially of finite type over `k`, so this
  follows from the dimension formula `trdeg K = trdeg κ(P) + ht P`). Thus `Ā_Q` is a normal
  local domain of dimension at least two, which has a regular pair in its maximal ideal (the
  depth half of Serre's criterion), and this forces `t ∣ w` for the element `w` with
  `Q = (t Ā : w)`, a contradiction.
* Hence `Ā = A + t Ā`, and Nakayama's lemma (with `t` in the maximal ideal) gives `Ā = A`, so
  `A` is normal. Finally if `a ∈ p` then `a ∈ t A_p`, so `s a = t b` with `s ∉ p`; the colon step
  in `Ā = A` gives `a ∈ tA`.

## Main results

* `Hartshorne.hironaka_normality_lemma`: Lemma 9.12.
-/

open IsLocalRing

namespace Hartshorne.Hironaka

universe u

section Dimension

/-- Transcendence degree is unchanged along an injective algebraic extension. -/
theorem trdeg_eq_of_isAlgebraic (k S T : Type u) [Field k] [CommRing S] [CommRing T]
    [IsDomain T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    [FaithfulSMul S T] [Algebra.IsAlgebraic S T] :
    Algebra.trdeg k S = Algebra.trdeg k T := by
  have : Nontrivial S := (algebraMap S T).domain_nontrivial
  have h := trdeg_add_eq k S (A := T)
  rw [trdeg_eq_zero (R := S) (A := T), add_zero] at h
  exact h

/-- The dimension formula for a domain essentially of finite type over a field, in
transcendence-degree form. -/
theorem exists_trdeg_eq_trdeg_quotient_add_height (k R : Type u) [Field k] [CommRing R]
    [IsDomain R] [Algebra k R] [Algebra.EssFiniteType k R] (P : Ideal R) [P.IsPrime] :
    ∃ e h : ℕ, Algebra.trdeg k (R ⧸ P) = e ∧ P.height = h ∧ Algebra.trdeg k R = e + h := by
  let C := Algebra.EssFiniteType.subalgebra k R
  let M := Algebra.EssFiniteType.submonoid k R
  let PC := P.comap (algebraMap C R)
  have : FiniteRingKrullDim C := finiteRingKrullDim_of_finiteType k C
  have hht : PC.height = P.height := IsLocalization.height_under M P
  obtain ⟨h, hh⟩ : ∃ h : ℕ, PC.height = h :=
    ENat.ne_top_iff_exists.mp (PC.height_ne_top (Ideal.IsPrime.ne_top inferInstance))
      |>.imp fun _ e => e.symm
  obtain ⟨e, -, he⟩ := exists_ringKrullDim_quotient_eq_trdeg k C PC
  have hform := trdeg_eq_trdeg_quotient_add_height k h C PC inferInstance hh
  rw [trdeg_fractionRing, trdeg_fractionRing] at hform
  rw [trdeg_fractionRing] at he
  -- `C → R` is algebraic and injective.
  have hCR : Algebra.trdeg k C = Algebra.trdeg k R := by
    have : Algebra.IsAlgebraic C R := IsLocalization.isAlgebraic R M
    exact trdeg_eq_of_isAlgebraic k C R
  -- `C/PC → R/P` is algebraic and injective.
  have : P.LiesOver PC := ⟨rfl⟩
  have : Algebra.IsAlgebraic (C ⧸ PC) (R ⧸ P) := by
    constructor
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨c, m⟩, hcm⟩ := IsLocalization.mk'_surjective M r
    have hm : (Ideal.Quotient.mk PC (m : C)) ≠ 0 := by
      rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
      intro hmem
      exact (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.eq_top_of_isUnit_mem P (Ideal.mem_comap.mp hmem) (IsLocalization.map_units R m))
    refine IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hm) ?_
    have hsm : (Ideal.Quotient.mk PC (m : C)) • (Ideal.Quotient.mk P r) =
        algebraMap (C ⧸ PC) (R ⧸ P) (Ideal.Quotient.mk PC c) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_mk_of_liesOver,
        Ideal.Quotient.algebraMap_mk_of_liesOver, ← map_mul, ← hcm, mul_comm,
        IsLocalization.mk'_spec]
    rw [hsm]
    exact isAlgebraic_algebraMap _
  have hquot : Algebra.trdeg k (C ⧸ PC) = Algebra.trdeg k (R ⧸ P) :=
    trdeg_eq_of_isAlgebraic k (C ⧸ PC) (R ⧸ P)
  refine ⟨e, h, hquot ▸ he, hht ▸ hh, ?_⟩
  rw [← hCR, hform, he]

/-- Along an injective integral extension of domains essentially of finite type over a field,
contraction preserves the height of a prime. -/
theorem height_comap_eq_of_isIntegral (k R S : Type u) [Field k] [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    [Algebra.EssFiniteType k R] [Algebra.EssFiniteType k S] [Algebra.IsIntegral R S]
    [FaithfulSMul R S] (Q : Ideal S) [Q.IsPrime] :
    (Q.comap (algebraMap R S)).height = Q.height := by
  obtain ⟨eS, hS, heS, hhS, htS⟩ := exists_trdeg_eq_trdeg_quotient_add_height k S Q
  obtain ⟨eR, hR, heR, hhR, htR⟩ :=
    exists_trdeg_eq_trdeg_quotient_add_height k R (Q.comap (algebraMap R S))
  have h1 : Algebra.trdeg k R = Algebra.trdeg k S := trdeg_eq_of_isAlgebraic k R S
  have : Q.LiesOver (Q.comap (algebraMap R S)) := ⟨rfl⟩
  have h2 : Algebra.trdeg k (R ⧸ Q.comap (algebraMap R S)) = Algebra.trdeg k (S ⧸ Q) :=
    trdeg_eq_of_isAlgebraic k _ _
  rw [hhS, hhR]
  rw [heR, heS] at h2
  rw [htR, htS, h2] at h1
  norm_cast at h1 h2
  congr 1
  omega

end Dimension

section Normalization

/-- A domain essentially of finite type over a field has finite normalization. -/
theorem moduleFinite_integralClosure_of_essFiniteType (k A : Type*) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.EssFiniteType k A] :
    Module.Finite A (integralClosure A (FractionRing A)) := by
  let B := Algebra.EssFiniteType.subalgebra k A
  let M := Algebra.EssFiniteType.submonoid k A
  let K := FractionRing A
  have hBK : Function.Injective (algebraMap B K) := by
    rw [IsScalarTower.algebraMap_eq B A K]
    exact (IsFractionRing.injective A K).comp Subtype.val_injective
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective B K).2 hBK
  have hmk : ∀ (b : B) (m : M), algebraMap A K (IsLocalization.mk' A b m) =
      algebraMap B K b / algebraMap B K m := by
    intro b m
    have hm : algebraMap B K m ≠ 0 :=
      (map_ne_zero_iff _ hBK).2 fun h => by
        have := IsLocalization.map_units A m
        rw [h, map_zero] at this
        exact not_isUnit_zero this
    rw [eq_div_iff hm, IsScalarTower.algebraMap_apply B A K m, ← map_mul,
      IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
  have : IsFractionRing B K := by
    refine IsFractionRing.of_field B K fun z => ?_
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨⟨b₁, m₁⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    obtain ⟨⟨b₂, m₂⟩, rfl⟩ := IsLocalization.mk'_surjective M y
    refine ⟨b₁ * m₂, b₂ * m₁, ?_⟩
    rw [hmk, hmk, map_mul, map_mul]
    rw [div_div_div_eq, mul_comm (algebraMap B K (m₁ : B))]
  have hfin : Module.Finite B (integralClosure B K) :=
    moduleFinite_integralClosure_of_finiteType_of_field k B K K
  obtain ⟨g, hg⟩ := hfin.fg_top
  classical
  have hfg : (integralClosure A K).toSubmodule.FG := by
    refine ⟨g.image (fun x : integralClosure B K => (x : K)), le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro y hy
      simp only [Finset.coe_image] at hy
      obtain ⟨x, -, rfl⟩ := hy
      exact (x.2 : IsIntegral B (x : K)).tower_top
    · intro x hx
      obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M x
        (show IsIntegral A x from hx)
      have h1 : (⟨m • x, hm⟩ : integralClosure B K) ∈
          Submodule.span B (g : Set (integralClosure B K)) := hg ▸ Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := (integralClosure B K).val.toLinearMap) h1
      rw [Submodule.map_span] at h2
      have h3 := Submodule.span_le_restrictScalars B A _ h2
      rw [Finset.coe_image]
      obtain ⟨u, hu⟩ := IsLocalization.map_units A m
      have hx' : x = ((u⁻¹ : Aˣ) : A) • (m • x) := by
        rw [Submonoid.smul_def, ← algebraMap_smul A (m : B) x, smul_smul, ← hu, Units.inv_mul,
          one_smul]
      rw [hx']
      exact Submodule.smul_mem _ _ h3
  exact Module.Finite.iff_fg.mpr hfg

/-- In a Noetherian integrally closed local domain of dimension at least two, a nonzero `t`
which divides `x * w` for every `x` in the maximal ideal divides `w`. -/
theorem dvd_of_forall_dvd_mul {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] [IsIntegrallyClosed R] (hdim : 2 ≤ ringKrullDim R) {t w : R} (ht : t ≠ 0)
    (h : ∀ x ∈ maximalIdeal R, t ∣ x * w) : t ∣ w := by
  obtain ⟨x, y, hx, hy, hxy⟩ := SerreNormality.exists_isRegularPair_of_isIntegrallyClosed hdim
  exact hxy.dvd_of_dvd_mul (fun a b hab => mul_left_cancel₀ ht hab) (h x hx) (h y hy)

/-- The colon step: if `tA` has the single minimal prime `p`, `S` is a Noetherian integrally
closed domain finite over `A` (essentially of finite type over `k`), and `s ∉ p` with
`s z ∈ t S`, then `z ∈ t S`. -/
theorem exists_eq_mul_of_mul_eq {k A : Type u} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.EssFiniteType k A] (S : Type u) [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [IsIntegrallyClosed S] [Algebra k S] [Algebra A S] [IsScalarTower k A S]
    [Algebra.EssFiniteType k S] [Algebra.IsIntegral A S] [FaithfulSMul A S]
    {t : A} {p : Ideal A} (hp : (Ideal.span {t}).minimalPrimes = {p}) {s : A} (hs : s ∉ p)
    {z b : S} (hzb : algebraMap A S s * z = algebraMap A S t * b) :
    ∃ w, z = algebraMap A S t * w := by
  have hpmin : p ∈ (Ideal.span {t}).minimalPrimes := hp ▸ rfl
  have hpprime : p.IsPrime := hpmin.1.1
  have htp : t ∈ p := hpmin.1.2 (Ideal.mem_span_singleton_self t)
  have hinj := FaithfulSMul.algebraMap_injective A S
  have hs0 : algebraMap A S s ≠ 0 := by
    intro h
    have : s = 0 := hinj (h.trans (map_zero _).symm)
    exact hs (this ▸ p.zero_mem)
  by_cases ht : t = 0
  · refine ⟨0, ?_⟩
    rw [ht, map_zero, zero_mul] at hzb
    rw [mul_zero]
    exact (mul_eq_zero.mp hzb).resolve_left hs0
  by_contra hne
  push Not at hne
  set T := algebraMap A S t with hT
  have hT0 : T ≠ 0 := fun h => ht (hinj (h.trans (map_zero _).symm))
  set J : Ideal S := Ideal.span {T}
  have hmem : ∀ a v : S, a ∈ (⊥ : Submodule S (S ⧸ J)).colon {Ideal.Quotient.mk J v} ↔
      T ∣ a * v := by
    intro a v
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk J (a * v) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hz : (Ideal.Quotient.mk J z) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    rintro ⟨w, hw⟩
    exact hne w (by rw [← hw, mul_comm])
  obtain ⟨Q, hQ, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing S _ hz
  obtain ⟨hQp, x, rfl⟩ := isAssociatedPrime_iff.mp hQ
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hsQ := hle ((hmem _ z).2 ⟨b, hzb⟩)
  have hTQ := (hmem T w).2 (dvd_mul_right T w)
  set Q := (⊥ : Submodule S (S ⧸ J)).colon {Ideal.Quotient.mk J w} with hQdef
  set q := Q.comap (algebraMap A S)
  have hsq : s ∈ q := hsQ
  have htq : t ∈ q := hTQ
  obtain ⟨p', hp', hp'q⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem q).2 htq)
  rw [hp, Set.mem_singleton_iff] at hp'
  subst hp'
  have hpq : p' < q := lt_of_le_of_ne hp'q fun h => hs (h ▸ hsq)
  have hbp : (⊥ : Ideal A) < p' := bot_lt_iff_ne_bot.2 fun h => ht (by
    rw [h] at htp
    exact htp)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbp
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hpq
  rw [Ideal.height_bot, zero_add] at h1
  have hq2 : (2 : ℕ∞) ≤ q.height := by
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ p'.height + 1 := by gcongr
      _ ≤ q.height := h2
  rw [height_comap_eq_of_isIntegral k A S Q] at hq2
  -- Pass to the local ring at `Q`.
  let R := Localization.AtPrime Q
  have hRdim : 2 ≤ ringKrullDim R := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q R]
    exact WithBot.coe_le_coe.mpr hq2
  have : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R Q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors Q)
  have hRinj : Function.Injective (algebraMap S R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors Q)
  have hdvd : algebraMap S R T ∣ algebraMap S R w := by
    refine dvd_of_forall_dvd_mul hRdim
      (fun h => hT0 (hRinj (h.trans (map_zero _).symm))) fun y hy => ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal] at hy
    have hle' : Q.map (algebraMap S R) ≤
        (Ideal.span {algebraMap S R T} : Submodule R R).colon {algebraMap S R w} := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul,
        Ideal.mem_span_singleton]
      obtain ⟨c, hc⟩ := (hmem a w).1 ha
      exact ⟨algebraMap S R c, by rw [← map_mul, hc, map_mul]⟩
    have := hle' hy
    rwa [Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton] at this
  obtain ⟨r, hr⟩ := hdvd
  obtain ⟨⟨c, u⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl r
  have hwu : algebraMap S R (u * w) = algebraMap S R (T * c) := by
    rw [map_mul, map_mul, hr, ← IsLocalization.mk'_spec R c u]
    ring
  have huQ : (u : S) ∈ Q := (hmem u w).2 ⟨c, hRinj hwu⟩
  exact u.2 huQ

/-- In a Noetherian ring, the minimal elements of the associated primes of `A ⧸ I` are exactly
the minimal primes of `I`. -/
theorem minimal_associatedPrimes_eq_minimalPrimes {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) :
    {q | Minimal (· ∈ associatedPrimes A (A ⧸ I)) q} = I.minimalPrimes := by
  have hsub : ∀ q ∈ associatedPrimes A (A ⧸ I), q.IsPrime ∧ I ≤ q := by
    intro q hq
    obtain ⟨hqp, x, rfl⟩ := isAssociatedPrime_iff.mp hq
    refine ⟨hqp, fun i hi => ?_⟩
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I (i * y) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact I.mul_mem_right y hi
  have hsup : I.minimalPrimes ⊆ associatedPrimes A (A ⧸ I) := by
    have h := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A (A ⧸ I)
    rwa [Ideal.annihilator_quotient] at h
  ext q
  constructor
  · intro hq
    have := (hsub q hq.1).1
    obtain ⟨q', hq', hq'q⟩ := Ideal.exists_minimalPrimes_le (hsub q hq.1).2
    have := hq.2 (hsup hq') hq'q
    rwa [← le_antisymm hq'q this]
  · intro hq
    exact ⟨hsup hq, fun r hr hrq => hq.2 (hsub r hr) hrq⟩

/-- Hironaka's lemma, with the field in the universe of `A`. -/
theorem hironaka_normality_aux (k : Type u) {A : Type u} [Field k] [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.EssFiniteType k A]
    (t : A) (p : Ideal A)
    [p.IsPrime] (hp : (Ideal.span {t}).minimalPrimes = {p})
    (hmax : maximalIdeal (Localization.AtPrime p) =
      Ideal.span {algebraMap A (Localization.AtPrime p) t})
    (hnorm : IsIntegrallyClosed (A ⧸ p)) :
    p = Ideal.span {t} ∧ IsIntegrallyClosed A := by
  let K := FractionRing A
  let Ab := integralClosure A K
  have : Module.Finite A Ab := moduleFinite_integralClosure_of_essFiniteType k A
  have : IsNoetherianRing Ab := IsNoetherianRing.of_finite A Ab
  have : IsIntegrallyClosed Ab := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have : Algebra.EssFiniteType k Ab := Algebra.EssFiniteType.comp k A Ab
  have hAbinj : Function.Injective (algebraMap A Ab) := by
    intro x y hxy
    exact IsFractionRing.injective A K (congrArg Subtype.val hxy)
  have : FaithfulSMul A Ab := (faithfulSMul_iff_algebraMap_injective A Ab).2 hAbinj
  have key : ∀ {s : A}, s ∉ p → ∀ {z b : Ab},
      algebraMap A Ab s * z = algebraMap A Ab t * b → ∃ w, z = algebraMap A Ab t * w :=
    fun hs _ _ h => exists_eq_mul_of_mul_eq (k := k) Ab hp hs h
  have hpmin : p ∈ (Ideal.span {t}).minimalPrimes := hp ▸ rfl
  have htp : t ∈ p := hpmin.1.2 (Ideal.mem_span_singleton_self t)
  let L := Localization.AtPrime p
  have hL : (maximalIdeal L).IsPrincipal ↔ (IsIntegrallyClosed L ∧
      ∀ P : Ideal L, P ≠ ⊥ → P.IsPrime → P = maximalIdeal L) :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain L).out 4 3
  have hLint : IsIntegrallyClosed L := (hL.mp ⟨⟨_, hmax⟩⟩).1
  have : IsFractionRing L K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl L K
  have hLinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors p)
  -- Elements of the maximal ideal of `A_p` are multiples of `t`.
  have hmaxL : ∀ l ∈ maximalIdeal L, ∃ b : A, ∃ s : A, s ∉ p ∧
      algebraMap A L s * l = algebraMap A L (t * b) := by
    intro l hl
    rw [hmax, Ideal.mem_span_singleton'] at hl
    obtain ⟨l', rfl⟩ := hl
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl l'
    refine ⟨b, s, s.2, ?_⟩
    rw [map_mul, ← IsLocalization.mk'_spec L b s]
    ring
  -- Step 1: every element of the normalization is `a + t w`.
  have hdecomp : ∀ x : Ab, ∃ a : A, ∃ w : Ab,
      x = algebraMap A Ab a + algebraMap A Ab t * w := by
    intro x
    have hxA : IsIntegral A (x : K) := x.2
    obtain ⟨l, hl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hxA.tower_top (A := L))
    have hlA : IsIntegral A l := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom A L K)
        (IsFractionRing.injective L K)]
      simpa [hl] using hxA
    have hres : IsIntegral (A ⧸ p) (algebraMap L p.ResidueField l) :=
      (hlA.map (IsScalarTower.toAlgHom A L p.ResidueField)).tower_top
    obtain ⟨abar, habar⟩ := IsIntegrallyClosed.isIntegral_iff.mp hres
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective abar
    have hmem : l - algebraMap A L a ∈ maximalIdeal L := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      change algebraMap L p.ResidueField l = algebraMap L p.ResidueField (algebraMap A L a)
      rw [← habar, ← IsScalarTower.algebraMap_apply A L,
        IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField]
      rfl
    obtain ⟨b, s, hs, hsb⟩ := hmaxL _ hmem
    have hK : algebraMap A K s * ((x : K) - algebraMap A K a) = algebraMap A K (t * b) := by
      rw [← hl, IsScalarTower.algebraMap_apply A L K, IsScalarTower.algebraMap_apply A L K a,
        IsScalarTower.algebraMap_apply A L K (t * b), ← map_sub, ← map_mul, hsb]
    obtain ⟨w, hw⟩ := key hs (z := x - algebraMap A Ab a) (b := algebraMap A Ab b) (by
      apply Subtype.ext
      simpa [map_mul] using hK)
    exact ⟨a, w, by rw [← hw]; ring⟩
  -- Step 2: Nakayama.
  have htm : t ∈ maximalIdeal A := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) htp
  have hN : (⊤ : Submodule A Ab) ≤ LinearMap.range (Algebra.linearMap A Ab) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (maximalIdeal_le_jacobson ⊥) fun x _ => ?_
    obtain ⟨a, w, rfl⟩ := hdecomp x
    refine Submodule.mem_sup.mpr ⟨algebraMap A Ab a, ⟨a, rfl⟩, algebraMap A Ab t * w, ?_, rfl⟩
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul htm trivial
  have hrange : ∀ x : Ab, ∃ a : A, algebraMap A Ab a = x := fun x => hN trivial
  refine ⟨le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).2 htp), ?_⟩
  · intro a ha
    have haL : algebraMap A L a ∈ maximalIdeal L := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ ha
    obtain ⟨b, s, hs, hsb⟩ := hmaxL _ haL
    rw [← map_mul] at hsb
    have hsb' := hLinj hsb
    obtain ⟨w, hw⟩ := key hs (z := algebraMap A Ab a) (b := algebraMap A Ab b) (by
      rw [← map_mul, ← map_mul, hsb'])
    obtain ⟨c, rfl⟩ := hrange w
    rw [← map_mul] at hw
    rw [hAbinj hw]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t)
  · refine (isIntegrallyClosed_iff K).mpr fun {x} hx => ?_
    obtain ⟨a, ha⟩ := hrange ⟨x, hx⟩
    exact ⟨a, congrArg Subtype.val ha⟩

end Normalization

end Hartshorne.Hironaka

namespace Hartshorne

universe u v

/-- **Hartshorne III, Lemma 9.12 (Hironaka).** Let `A` be a local Noetherian domain essentially
of finite type over a field `k`, and let `t ∈ A`. Assume that `tA` has a unique minimal
associated prime `p` (the minimal elements of the associated primes of `A ⧸ tA` are exactly
`p`), that `t` generates the maximal ideal of `A_p`, and that `A ⧸ p` is normal. Then `p = tA`
and `A` is normal. -/
theorem hironaka_normality_lemma {k : Type v} {A : Type u} [Field k] [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.EssFiniteType k A]
    (t : A) (p : Ideal A) [p.IsPrime]
    (hp : {q | Minimal (· ∈ associatedPrimes A (A ⧸ Ideal.span {t})) q} = {p})
    (hmax : maximalIdeal (Localization.AtPrime p) =
      Ideal.span {algebraMap A (Localization.AtPrime p) t})
    (hnorm : IsIntegrallyClosed (A ⧸ p)) :
    p = Ideal.span {t} ∧ IsIntegrallyClosed A := by
  rw [Hironaka.minimal_associatedPrimes_eq_minimalPrimes] at hp
  -- Replace `k` by its image in `A`, a field in the universe of `A`.
  let k₀ := (algebraMap k A).range
  let e : k ≃+* k₀ := RingEquiv.ofBijective (algebraMap k A).rangeRestrict
    ⟨fun x y h => (algebraMap k A).injective (congrArg Subtype.val h),
      (algebraMap k A).rangeRestrict_surjective⟩
  let hk₀ : Field k₀ := (e.symm.toMulEquiv.isField (Field.toIsField k)).toField
  let hkk₀ : Algebra k k₀ := (algebraMap k A).rangeRestrict.toAlgebra
  have : IsScalarTower k k₀ A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.EssFiniteType k₀ A := Algebra.EssFiniteType.of_comp k k₀ A
  exact Hironaka.hironaka_normality_aux k₀ t p hp hmax hnorm

end Hartshorne
