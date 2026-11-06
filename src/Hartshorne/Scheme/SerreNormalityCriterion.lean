/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CohenMacaulay
import Hartshorne.Scheme.RegularLocalCohenMacaulay
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Support

/-!
# Serre's criterion for normality

Hartshorne, *Algebraic Geometry*, II, Theorem 8.22A (p. 185); Matsumura, *Commutative Ring
Theory*, Theorem 23.8; Stacks, tag 031S.

A Noetherian ring `R` is normal (every localization at a prime is an integrally closed domain)
if and only if it satisfies

* `(R1)`: `R_𝔭` is a regular local ring for every prime `𝔭` of height at most one, and
* `(S2)`: `R_𝔭` has depth at least two for every prime `𝔭` of height at least two.

Depth is the notion `Module.depth` used for Cohen--Macaulay local rings.

## Main result

* `Hartshorne.SerreNormality.normal_iff_R1_and_S2`

## Proof outline

Everything reduces to local statements about a *regular pair* `x, y` in the maximal ideal `𝔪`
of a local ring `A`: `x` is a non-zero-divisor and `y` is a non-zero-divisor modulo `x`. Depth
at least two is the same as the existence of such a pair.

* Powers of a regular pair form a regular pair. Hence if an ideal `C` is contained in no
  non-maximal prime, then (as `𝔪 ⊆ √C`) `C` contains a regular pair.
* If `x', y'` is a regular pair and `b` is a non-zero-divisor with `b ∣ x' z` and `b ∣ y' z`,
  then `b ∣ z`.
* If `x', y' ∈ I + J` form a regular pair in a local ring and `I J = 0`, then `I = 0` or `J = 0`.

For `(R1) ∧ (S2) ⇒` normal, argue by induction on the height of `𝔭`. Primes of height at most
one are handled by `(R1)` (a regular local ring of dimension at most one is a field or a DVR).
Otherwise `A = R_𝔭` has a regular pair, and all localizations of `A` at non-maximal primes are
integrally closed domains by induction. Taking `I = ann b`, `J = ann I` for `a b = 0` shows that
`A` is a domain; taking `C = (b : a)` for an integral element `a / b` shows that `A` is
integrally closed.

For normal `⇒ (R1) ∧ (S2)`: a normal local ring of dimension at most one is a Dedekind domain,
hence regular. If `A` is a normal local domain of dimension at least two and `0 ≠ x ∈ 𝔪`, then
`𝔪` is not an associated prime of `A / x A`: otherwise `𝔪 = (x : z)` with `z ∉ x A`, and either
`(z / x) 𝔪 ⊆ 𝔪`, making `z / x` integral, or `(z / x) 𝔪 = A`, making `𝔪` principal and
contradicting Krull's principal ideal theorem. Prime avoidance then produces `y ∈ 𝔪` regular
modulo `x`.
-/

open IsLocalRing Pointwise RingTheory.Sequence

universe u v

namespace Hartshorne.SerreNormality

section RegularPair

variable {A : Type u} [CommRing A]

/-- A regular pair in `A`: `x` is a non-zero-divisor on `A` and `y` is a non-zero-divisor on
`A / x A`. -/
def IsRegularPair (x y : A) : Prop :=
  IsSMulRegular A x ∧ ∀ z : A, x ∣ y * z → x ∣ z

/-- Membership in `x • A` is divisibility by `x`. -/
theorem mem_smul_top_iff_dvd (x z : A) : z ∈ x • (⊤ : Submodule A A) ↔ x ∣ z := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, -, hw⟩
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, trivial, rfl⟩

/-- `y` is regular on `A / x A` exactly when `x ∣ y z` implies `x ∣ z`. -/
theorem isSMulRegular_quotSMulTop_iff (x y : A) :
    IsSMulRegular (QuotSMulTop x A) y ↔ ∀ z : A, x ∣ y * z → x ∣ z := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  constructor
  · intro h z hz
    have h0 := h (Submodule.Quotient.mk z) (by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_dvd]
      exact hz)
    rwa [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_dvd] at h0
  · intro h m hm
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_dvd] at hm
    rw [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_dvd]
    exact h z hm

/-- Powers of a regular pair form a regular pair. -/
theorem IsRegularPair.pow {x y : A} (h : IsRegularPair x y) (n k : ℕ) :
    IsRegularPair (x ^ n) (y ^ k) := by
  have hx : ∀ n : ℕ, ∀ z, x ^ n ∣ y * z → x ^ n ∣ z := by
    intro n
    induction n with
    | zero => intro z _; simp
    | succ n ih =>
      intro z hz
      obtain ⟨w, rfl⟩ := h.2 z (dvd_trans (dvd_pow_self x n.succ_ne_zero) hz)
      obtain ⟨c, hc⟩ := hz
      have hyw : y * w = x ^ n * c := h.1 (by
        simp only [smul_eq_mul]
        linear_combination hc)
      obtain ⟨d, rfl⟩ := ih w ⟨c, hyw⟩
      exact ⟨d, by ring⟩
  refine ⟨h.1.pow n, ?_⟩
  induction k with
  | zero => intro z hz; simpa using hz
  | succ k ih =>
    intro z hz
    exact ih z (hx n _ (by rwa [pow_succ', mul_assoc] at hz))

/-- If `x, y` is a regular pair and `b` is a non-zero-divisor dividing both `x z` and `y z`,
then `b` divides `z`. -/
theorem IsRegularPair.dvd_of_dvd_mul {x y b z : A} (h : IsRegularPair x y)
    (hb : IsSMulRegular A b) (hxz : b ∣ x * z) (hyz : b ∣ y * z) : b ∣ z := by
  obtain ⟨w, hw⟩ := hxz
  obtain ⟨v, hv⟩ := hyz
  have h1 : y * w = x * v := hb (by
    simp only [smul_eq_mul]
    linear_combination x * hv - y * hw)
  obtain ⟨w', rfl⟩ := h.2 w ⟨v, h1⟩
  exact ⟨w', h.1 (by
    simp only [smul_eq_mul]
    linear_combination hw)⟩

/-- In a local ring, if a regular pair lies in `I + J` and `I J = 0`, then `I = 0` or `J = 0`. -/
theorem IsRegularPair.eq_bot_or_eq_bot [IsLocalRing A] {x y : A} (h : IsRegularPair x y)
    {I J : Ideal A} (hIJ : ∀ i ∈ I, ∀ j ∈ J, i * j = 0) (hx : x ∈ I ⊔ J) (hy : y ∈ I ⊔ J) :
    I = ⊥ ∨ J = ⊥ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
  have key : (a + b) ∣ (c + d) * a := ⟨c, by
    have h1 := hIJ a ha d hd
    have h2 := hIJ c hc b hb
    linear_combination h1 - h2⟩
  obtain ⟨t, ht⟩ := h.2 a key
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self t with ht' | ht'
  · right
    obtain ⟨s, hs⟩ := ht'.exists_right_inv
    have hab : a + b = a * s := by linear_combination -(a + b) * hs - s * ht
    refine eq_bot_iff.mpr fun j hj => ?_
    rw [Submodule.mem_bot]
    apply h.1
    simp only [smul_eq_mul, mul_zero]
    rw [hab, mul_assoc, mul_comm s, ← mul_assoc, hIJ a ha j hj, zero_mul]
  · left
    obtain ⟨s, hs⟩ := ht'.exists_right_inv
    have hab : a + b = b * s := by linear_combination -(a + b) * hs + s * ht
    refine eq_bot_iff.mpr fun i hi => ?_
    rw [Submodule.mem_bot]
    apply h.1
    simp only [smul_eq_mul, mul_zero]
    rw [hab, mul_assoc, mul_comm s, ← mul_assoc, mul_comm b, hIJ i hi b hb, zero_mul]

/-- In a local ring, an ideal contained in no non-maximal prime contains a power of every
element of the maximal ideal. -/
theorem exists_pow_mem_of_forall_not_le [IsLocalRing A] {C : Ideal A}
    (hC : ∀ Q : Ideal A, Q.IsPrime → Q ≠ maximalIdeal A → ¬ C ≤ Q) {x : A}
    (hx : x ∈ maximalIdeal A) : ∃ n : ℕ, x ^ n ∈ C := by
  have hrad : x ∈ C.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hCQ, hQ⟩
    by_contra hxQ
    exact hC Q hQ (fun h => hxQ (h ▸ hx)) hCQ
  exact hrad

/-- In a local ring with a regular pair in the maximal ideal, an ideal contained in no
non-maximal prime contains a regular pair. -/
theorem exists_isRegularPair_mem [IsLocalRing A] {x y : A} (h : IsRegularPair x y)
    (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A) {C : Ideal A}
    (hC : ∀ Q : Ideal A, Q.IsPrime → Q ≠ maximalIdeal A → ¬ C ≤ Q) :
    ∃ x' y' : A, x' ∈ C ∧ y' ∈ C ∧ IsRegularPair x' y' := by
  obtain ⟨n, hn⟩ := exists_pow_mem_of_forall_not_le hC hx
  obtain ⟨k, hk⟩ := exists_pow_mem_of_forall_not_le hC hy
  exact ⟨x ^ n, y ^ k, hn, hk, h.pow n k⟩

/-- A Noetherian local ring with a regular pair in its maximal ideal, all of whose
localizations at non-maximal primes are domains, is a domain. -/
theorem isDomain_of_isRegularPair [IsLocalRing A] [IsNoetherianRing A] {x y : A}
    (h : IsRegularPair x y) (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A)
    (hQ : ∀ (Q : Ideal A) [Q.IsPrime], Q ≠ maximalIdeal A → IsDomain (Localization.AtPrime Q)) :
    IsDomain A := by
  refine @NoZeroDivisors.to_isDomain A _ _ ⟨fun {a b} hab => ?_⟩
  let I : Ideal A := Submodule.annihilator (Ideal.span {b})
  let J : Ideal A := Module.annihilator A I
  have hI : ∀ r, r ∈ I ↔ r * b = 0 := fun r => by
    simp [I]
  have hJ : ∀ r, r ∈ J ↔ ∀ i ∈ I, r * i = 0 := fun r => by
    simp only [J, Module.mem_annihilator, Subtype.forall]
    refine forall₂_congr fun i hi => ?_
    rw [← Subtype.coe_inj]
    rfl
  have hIJ : ∀ i ∈ I, ∀ j ∈ J, i * j = 0 := fun i hi j hj => by
    rw [mul_comm]
    exact (hJ j).1 hj i hi
  have hC : ∀ Q : Ideal A, Q.IsPrime → Q ≠ maximalIdeal A → ¬ I ⊔ J ≤ Q := by
    intro Q hQp hQm hle
    have := hQ Q hQm
    by_cases hb : algebraMap A (Localization.AtPrime Q) b = 0
    · obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ b).mp hb
      exact hs (hle (Ideal.mem_sup_left ((hI s).2 hsb)))
    · have hsupp : (⟨Q, hQp⟩ : PrimeSpectrum A) ∉ Module.support A I := by
        rw [Module.notMem_support_iff']
        rintro ⟨i, hi⟩
        have hi0 : algebraMap A (Localization.AtPrime Q) i = 0 := by
          have h0 : algebraMap A (Localization.AtPrime Q) i *
              algebraMap A (Localization.AtPrime Q) b = 0 := by
            rw [← map_mul, (hI i).1 hi, map_zero]
          exact (mul_eq_zero.mp h0).resolve_right hb
        obtain ⟨⟨s, hs⟩, hsi⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ i).mp hi0
        exact ⟨s, hs, Subtype.ext hsi⟩
      rw [Module.mem_support_iff_of_finite] at hsupp
      exact hsupp (le_sup_right.trans hle)
  obtain ⟨x', y', hx', hy', h'⟩ := exists_isRegularPair_mem h hx hy hC
  rcases h'.eq_bot_or_eq_bot hIJ hx' hy' with hI0 | hJ0
  · left
    have ha : a ∈ I := (hI a).2 hab
    rwa [hI0, Submodule.mem_bot] at ha
  · right
    have hb : b ∈ J := (hJ b).2 fun i hi => by rw [mul_comm]; exact (hI i).1 hi
    rwa [hJ0, Submodule.mem_bot] at hb

/-- A local domain with a regular pair in its maximal ideal, all of whose localizations at
non-maximal primes are integrally closed, is integrally closed. -/
theorem isIntegrallyClosed_of_isRegularPair [IsLocalRing A] [IsDomain A] {x y : A}
    (h : IsRegularPair x y) (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A)
    (hQ : ∀ (Q : Ideal A) [Q.IsPrime], Q ≠ maximalIdeal A →
      IsIntegrallyClosed (Localization.AtPrime Q)) :
    IsIntegrallyClosed A := by
  refine IsIntegrallyClosed.of_localization {Q : PrimeSpectrum A | Q.asIdeal ≠ maximalIdeal A}
    (fun Q hQm => hQ Q.asIdeal hQm) ?_
  refine eq_bot_iff.mpr fun f hf => ?_
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) f
  let C : Ideal A := (Ideal.span {b}).colon {a}
  have hC : ∀ Q : Ideal A, Q.IsPrime → Q ≠ maximalIdeal A → ¬ C ≤ Q := by
    intro Q hQ hQm hle
    have hfQ := Algebra.mem_iInf.mp (Algebra.mem_iInf.mp hf ⟨Q, hQ⟩) hQm
    obtain ⟨c, t, ht, hct⟩ := hfQ
    rw [IsLocalization.mk'_eq_iff_eq] at hct
    have hct' := IsFractionRing.injective A (FractionRing A) hct
    refine ht (hle (Submodule.mem_colon_singleton.mpr (Ideal.mem_span_singleton.mpr ⟨c, ?_⟩)))
    simp only [smul_eq_mul]
    linear_combination hct'
  obtain ⟨x', y', hx', hy', h'⟩ := exists_isRegularPair_mem h hx hy hC
  have hbreg : IsSMulRegular A b := fun u v huv =>
    mul_left_cancel₀ (nonZeroDivisors.ne_zero hb) huv
  have hxa : b ∣ x' * a := Ideal.mem_span_singleton.mp (Submodule.mem_colon_singleton.mp hx')
  have hya : b ∣ y' * a := Ideal.mem_span_singleton.mp (Submodule.mem_colon_singleton.mp hy')
  obtain ⟨c, hc⟩ := h'.dvd_of_dvd_mul hbreg hxa hya
  rw [Algebra.mem_bot]
  refine ⟨c, ?_⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, hc, map_mul, mul_comm]

/-- A local ring has depth at least two exactly when its maximal ideal contains a regular
pair. -/
theorem two_le_depth_iff [IsLocalRing A] :
    2 ≤ Module.depth A A ↔
      ∃ x y : A, x ∈ maximalIdeal A ∧ y ∈ maximalIdeal A ∧ IsRegularPair x y := by
  have hne : ¬ maximalIdeal A • (⊤ : Submodule A A) = ⊤ := by
    rw [smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal A).ne_top
  rw [Module.depth, if_neg hne]
  constructor
  · intro h2
    obtain ⟨⟨rs, hreg, hmem⟩, hlt⟩ :=
      lt_iSup_iff.mp (lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) h2)
    match rs, hreg, hmem, hlt with
    | [], _, _, hlt => simp at hlt
    | [_], _, _, hlt => simp at hlt
    | x :: y :: rest, hreg, hmem, _ =>
      have hw := hreg.toIsWeaklyRegular
      rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff] at hw
      exact ⟨x, y, hmem x (by simp), hmem y (by simp), hw.1,
        (isSMulRegular_quotSMulTop_iff x y).mp hw.2.1⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hmem : ∀ r ∈ [x, y], r ∈ maximalIdeal A := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> assumption
    have hw : IsWeaklyRegular A [x, y] :=
      (isWeaklyRegular_cons_iff A x [y]).mpr ⟨hxy.1, (isWeaklyRegular_singleton_iff _ y).mpr
        ((isSMulRegular_quotSMulTop_iff x y).mpr hxy.2)⟩
    refine le_iSup_of_le ⟨[x, y], IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal A hmem hw,
      hmem⟩ ?_
    simp

end RegularPair

section Local

variable {A : Type u} [CommRing A]

/-- A regular local ring of dimension at most one is an integrally closed domain. -/
theorem isDomain_isIntegrallyClosed_of_isRegularLocalRing [IsRegularLocalRing A]
    (hdim : ringKrullDim A ≤ 1) : IsDomain A ∧ IsIntegrallyClosed A := by
  have := RegularLocal.isDomain A
  refine ⟨this, ?_⟩
  have h := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp inferInstance
  have hle : Module.finrank (ResidueField A) (CotangentSpace A) ≤ 1 := by
    rw [← h] at hdim
    exact_mod_cast hdim
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · exact (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp h0).toField.instIsIntegrallyClosed
  · have := IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp h1
    infer_instance

/-- A Noetherian integrally closed local domain of dimension at most one is regular. -/
theorem isRegularLocalRing_of_isIntegrallyClosed [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A] (hdim : ringKrullDim A ≤ 1) : IsRegularLocalRing A := by
  have : Ring.DimensionLEOne A := ⟨fun {Q} hQ hQprime =>
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp (Ring.krullDimLE_iff.mpr hdim) Q hQ hQprime⟩
  have : IsDedekindDomain A :=
    { toIsDomain := inferInstance
      toIsDedekindRing := {} }
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing A

/-- A Noetherian integrally closed local domain of dimension at least two has a regular pair
in its maximal ideal. -/
theorem exists_isRegularPair_of_isIntegrallyClosed [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A] (hdim : 2 ≤ ringKrullDim A) :
    ∃ x y : A, x ∈ maximalIdeal A ∧ y ∈ maximalIdeal A ∧ IsRegularPair x y := by
  have hm : maximalIdeal A ≠ ⊥ := by
    intro h
    rw [ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr h)] at hdim
    exact absurd hdim (by decide)
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hxreg : IsSMulRegular A x := fun a b hab => mul_left_cancel₀ hx0 hab
  by_contra hcon
  have hsub : (maximalIdeal A : Set A) ⊆
      ⋃ P ∈ associatedPrimes A (QuotSMulTop x A), (P : Set A) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    intro y hy hreg
    exact hcon ⟨x, y, hxm, hy, hxreg, (isSMulRegular_quotSMulTop_iff x y).mp hreg⟩
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite A _) ⊥ ⊥
    (fun P hP _ _ => (isAssociatedPrime_iff.mp hP).1)).mp hsub
  obtain ⟨hPprime, zbar, hz⟩ := isAssociatedPrime_iff.mp hP
  have hPm : maximalIdeal A = P := (maximalIdeal.isMaximal A).eq_of_le hPprime.ne_top hmP
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ zbar
  have hmem : ∀ r : A, r ∈ maximalIdeal A ↔ x ∣ r * z := by
    intro r
    rw [hPm, hz, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_dvd, smul_eq_mul]
  have hxz : ¬ x ∣ z := fun hd =>
    (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr ((hmem 1).mpr (by simpa)))
  have hz0 : z ≠ 0 := fun h0 => hxz (h0 ▸ dvd_zero x)
  by_cases hcase : ∃ r ∈ maximalIdeal A, ∃ u : A, IsUnit u ∧ r * z = x * u
  · obtain ⟨r, hrm, u, hu, hru⟩ := hcase
    obtain ⟨s, hs⟩ := hu.exists_right_inv
    have hle : maximalIdeal A ≤ Ideal.span {r} := by
      intro v hv
      obtain ⟨w, hw⟩ := (hmem v).mp hv
      have hvu : v * u = r * w := by
        apply mul_left_cancel₀ hz0
        linear_combination u * hw - w * hru
      refine Ideal.mem_span_singleton'.mpr ⟨w * s, ?_⟩
      linear_combination s * hvu.symm + v * hs
    have hr : ¬ IsUnit r := (IsLocalRing.mem_maximalIdeal r).mp hrm
    have h1 : (maximalIdeal A).height ≤ 1 :=
      (Ideal.height_mono hle).trans (Ideal.height_span_singleton_le_one hr)
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hdim
    have h2 : (2 : ℕ∞) ≤ (maximalIdeal A).height := WithBot.coe_le_coe.mp hdim
    exact absurd (h2.trans h1) (by decide)
  · push Not at hcase
    let K := FractionRing A
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) (maximalIdeal A)
    have hN : N ≠ ⊥ := by
      intro h
      have hxN : algebraMap A K x ∈ N := Submodule.mem_map_of_mem (f := Algebra.linearMap A K) hxm
      rw [h, Submodule.mem_bot] at hxN
      exact hx0 (IsFractionRing.injective A K (by rw [hxN, map_zero]))
    have hNfg : N.FG :=
      Submodule.FG.map (f := Algebra.linearMap A K) (maximalIdeal A).fg_of_isNoetherianRing
    let f : K := algebraMap A K z / algebraMap A K x
    have hxK : algebraMap A K x ≠ 0 := fun h0 =>
      hx0 (IsFractionRing.injective A K (by rw [h0, map_zero]))
    have hf : ∀ n ∈ N, f • n ∈ N := by
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hn
      obtain ⟨u, hu⟩ := (hmem r).mp hr
      have hum : u ∈ maximalIdeal A := by
        by_contra hnot
        exact hcase r hr u ((IsLocalRing.notMem_maximalIdeal).mp hnot) hu
      refine ⟨u, hum, ?_⟩
      have hfu : f * algebraMap A K r = algebraMap A K u := by
        simp only [f]
        rw [div_mul_eq_mul_div, div_eq_iff hxK, ← map_mul, ← map_mul, mul_comm z, hu, mul_comm]
      simpa [Algebra.linearMap_apply, smul_eq_mul] using hfu.symm
    have hint : IsIntegral A f := isIntegral_of_smul_mem_submodule N hN hNfg f hf
    obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hint
    apply hxz
    refine ⟨c, IsFractionRing.injective A K ?_⟩
    rw [map_mul, hc, mul_comm]
    exact (div_mul_cancel₀ _ hxK).symm

end Local

section Transfer

variable {R : Type u} [CommRing R]

/-- A non-maximal prime of `R_𝔭` contracts to a prime of `R` strictly contained in `𝔭`. -/
theorem comap_lt_of_ne_maximalIdeal (p : Ideal R) [p.IsPrime]
    (Q : Ideal (Localization.AtPrime p)) [Q.IsPrime] (hQ : Q ≠ maximalIdeal _) :
    Q.comap (algebraMap R (Localization.AtPrime p)) < p := by
  refine lt_of_le_of_ne ?_ fun heq => hQ ?_
  · exact (Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›))).trans
      (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p).le
  · rw [← IsLocalization.map_under p.primeCompl (Localization.AtPrime p) Q]
    change Ideal.map _ (Q.comap _) = _
    rw [heq]
    exact IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)

/-- The localization of `R_𝔭` at a prime `Q` is the localization of `R` at the contraction
of `Q`. -/
noncomputable def localizationAtPrimeEquiv (p : Ideal R) [p.IsPrime]
    (Q : Ideal (Localization.AtPrime p)) [Q.IsPrime] :
    Localization.AtPrime Q ≃+*
      Localization.AtPrime (Q.comap (algebraMap R (Localization.AtPrime p))) :=
  (IsLocalization.localizationLocalizationAtPrimeIsoLocalization p.primeCompl Q).symm.toRingEquiv

end Transfer

/-- **Serre's criterion for normality** (Hartshorne II, Theorem 8.22A). A Noetherian ring `R` is
normal, meaning that every localization at a prime is an integrally closed domain, if and only
if it satisfies `(R1)`: every localization at a prime of height at most one is a regular local
ring, and `(S2)`: every localization at a prime of height at least two has depth at least two. -/
theorem normal_iff_R1_and_S2 (R : Type u) [CommRing R] [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
      (∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
          IsRegularLocalRing (Localization.AtPrime p)) ∧
        (∀ (p : Ideal R) [p.IsPrime], 2 ≤ p.height →
          2 ≤ Module.depth (Localization.AtPrime p) (Localization.AtPrime p)) := by
  constructor
  · intro hN
    refine ⟨fun p _ hp => ?_, fun p _ hp => ?_⟩
    · obtain ⟨_, _⟩ := hN p
      refine isRegularLocalRing_of_isIntegrallyClosed ?_
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
      exact_mod_cast hp
    · obtain ⟨_, _⟩ := hN p
      refine two_le_depth_iff.mpr (exists_isRegularPair_of_isIntegrallyClosed ?_)
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
      exact WithBot.coe_le_coe.mpr hp
  · rintro ⟨hR1, hS2⟩
    have hbase : ∀ (p : Ideal R) [p.IsPrime], p.height ≤ 1 →
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
      intro p _ hp
      have := hR1 p hp
      refine isDomain_isIntegrallyClosed_of_isRegularLocalRing ?_
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
      exact_mod_cast hp
    suffices H : ∀ n : ℕ, ∀ (p : Ideal R) [p.IsPrime], p.height ≤ n →
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) by
      intro p _
      exact H _ p (ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := p))).symm.le
    intro n
    induction n with
    | zero => exact fun p _ hp => hbase p (hp.trans (by norm_num))
    | succ n ih =>
      intro p _ hp
      by_cases h1 : p.height ≤ 1
      · exact hbase p h1
      have h2 : 2 ≤ p.height := Order.add_one_le_of_lt (not_le.mp h1)
      obtain ⟨x, y, hx, hy, hxy⟩ := two_le_depth_iff.mp (hS2 p h2)
      have hQ : ∀ (Q : Ideal (Localization.AtPrime p)) [Q.IsPrime], Q ≠ maximalIdeal _ →
          IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
        intro Q _ hQm
        have hlt := comap_lt_of_ne_maximalIdeal p Q hQm
        have hq : (Q.comap (algebraMap R (Localization.AtPrime p))).height ≤ n := by
          have h3 := (Ideal.height_add_one_le_of_lt_of_isPrime hlt).trans hp
          push_cast at h3
          exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h3
        obtain ⟨_, _⟩ := ih _ hq
        let e := localizationAtPrimeEquiv p Q
        exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩
      have hdom := isDomain_of_isRegularPair hxy hx hy fun Q _ hQm => (hQ Q hQm).1
      exact ⟨hdom, isIntegrallyClosed_of_isRegularPair hxy hx hy fun Q _ hQm => (hQ Q hQm).2⟩

end Hartshorne.SerreNormality
