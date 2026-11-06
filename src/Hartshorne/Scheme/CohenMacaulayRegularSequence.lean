/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.KrullDimension.Regular
import Hartshorne.Scheme.CohenMacaulay

/-!
# Regular sequences and Cohen--Macaulay quotients

Hartshorne, *Algebraic Geometry*, II, Theorem 8.21A(c), pp. 184--185 (Stacks, tag 02JN).

Let `A` be a Noetherian Cohen--Macaulay local ring and let `x₁, …, xᵣ` lie in its maximal
ideal. The sequence is regular if and only if `dim A/(x₁, …, xᵣ) = dim A - r` (stated additively
as `dim A/(x₁, …, xᵣ) + r = dim A`), and in that case `A/(x₁, …, xᵣ)` is Cohen--Macaulay.

## Main results

* `IsCohenMacaulayLocalRing.isRegular_iff_ringKrullDim_quotient_ofList_add_length`
* `IsCohenMacaulayLocalRing.isWeaklyRegular_iff_ringKrullDim_quotient_ofList_add_length`
  (Hartshorne's formulation: each `xᵢ` is a non-zero-divisor modulo the previous ones)
* `IsCohenMacaulayLocalRing.quotient_ofList`

## Proof outline

The forward implication is Mathlib's `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`.
For the converse and the quotient clause we work with finite modules over the fixed ring `A`:

* depth drops by at most one modulo a regular element in the maximal ideal, which follows from
  the Rees theorem (`ModuleCat.exists_isRegular_tfae`) and the long exact `Ext` sequence;
* if `M` has a regular sequence of length `n` in the maximal ideal, then `n ≤ dim A/p` for every
  associated prime `p` of `M` (an induction using Krull's intersection theorem);
* hence, in the Cohen--Macaulay case, an element of the maximal ideal that lowers the dimension
  avoids every associated prime and is therefore a non-zero-divisor, and one inducts on `r`.
-/

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise Module

universe u

namespace Hartshorne.CohenMacaulay

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- A finite nontrivial module over a Noetherian local ring has finite support dimension. -/
lemma exists_supportDim_eq_natCast (M : Type*) [AddCommGroup M] [Module A M]
    [Nontrivial M] : ∃ k : ℕ, supportDim A M = k := by
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp (supportDim_ne_bot_of_nontrivial A M)
  have hlt : supportDim A M < ⊤ := (supportDim_le_ringKrullDim A M).trans_lt ringKrullDim_lt_top
  have he' : e ≠ ⊤ := by
    rintro rfl
    simp [← he] at hlt
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp he'
  exact ⟨k, he.symm⟩


/-- Depth drops by at most one modulo a regular element: if `M` has a regular sequence of length
`n + 1` in the maximal ideal and `x` in the maximal ideal is `M`-regular, then `M / xM` has a
regular sequence of length `n` in the maximal ideal. This is deduced from the Rees theorem. -/
lemma exists_isRegular_quotSMulTop (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] {x : A} (hx : x ∈ maximalIdeal A) (reg : IsSMulRegular M x) (n : ℕ)
    (rs : List A) (hlen : rs.length = n + 1) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal A)
    (hrs : IsRegular M rs) :
    ∃ rs' : List A, rs'.length = n ∧ (∀ r ∈ rs', r ∈ maximalIdeal A) ∧
      IsRegular (QuotSMulTop x M) rs' := by
  have : Nontrivial M := hrs.nontrivial
  have : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  let N : ModuleCat.{u} A := ModuleCat.of A (A ⧸ maximalIdeal A)
  have hsupp : Module.support A N = PrimeSpectrum.zeroLocus (maximalIdeal A) := by
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have smul_lt : ∀ (L : Type u) [AddCommGroup L] [Module A L] [Module.Finite A L] [Nontrivial L],
      maximalIdeal A • (⊤ : Submodule A L) < ⊤ := fun L _ _ _ _ =>
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson _)).symm.lt_top
  have h_ext := ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal A) N hsupp.le
    (ModuleCat.of A M) (smul_lt M) rs hmem hrs
  have h_ext' : ∀ i < n, Subsingleton (Ext N (ModuleCat.of A (QuotSMulTop x M)) i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext i (by omega))
    have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (h_ext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' N
        (IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of A M) reg)) i (i + 1) rfl)
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  exact ModuleCat.exists_isRegular_of_exists_subsingleton_ext (maximalIdeal A) n
    (ModuleCat.of A (QuotSMulTop x M)) (smul_lt _) N hsupp h_ext'

/-- Iterated form of `exists_isRegular_quotSMulTop`: modulo a regular sequence `xs` of length
`r` in the maximal ideal, a regular sequence of length `n + r` yields one of length `n`. -/
lemma exists_isRegular_quotient_ofList (xs : List A) (hxm : ∀ x ∈ xs, x ∈ maximalIdeal A) :
    ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M], IsRegular M xs →
    ∀ (n : ℕ) (rs : List A), rs.length = n + xs.length → (∀ r ∈ rs, r ∈ maximalIdeal A) →
      IsRegular M rs →
    ∃ rs' : List A, rs'.length = n ∧ (∀ r ∈ rs', r ∈ maximalIdeal A) ∧
      IsRegular (M ⧸ (Ideal.ofList xs • ⊤ : Submodule A M)) rs' := by
  induction xs with
  | nil =>
    intro M _ _ _ _ n rs hlen hmem hrs
    refine ⟨rs, by simpa using hlen, hmem, ?_⟩
    exact (LinearEquiv.isRegular_congr
      (Submodule.quotEquivOfEqBot _ (by simp)).symm rs).mp hrs
  | cons x xs ih =>
    intro M _ _ _ hxs n rs hlen hmem hrs
    rw [isRegular_cons_iff] at hxs
    have hx : x ∈ maximalIdeal A := hxm x List.mem_cons_self
    obtain ⟨rs₁, hlen₁, hmem₁, hrs₁⟩ := exists_isRegular_quotSMulTop M hx hxs.1
      (n + xs.length) rs (by simpa [← add_assoc] using hlen) hmem hrs
    obtain ⟨rs', hlen', hmem', hrs'⟩ := ih (fun y hy => hxm y (List.mem_cons_of_mem _ hy))
      (QuotSMulTop x M) hxs.2 n rs₁ hlen₁ hmem₁ hrs₁
    exact ⟨rs', hlen', hmem', (LinearEquiv.isRegular_congr
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs) rs').mpr hrs'⟩

/-- Cutting by `r` elements of the maximal ideal lowers the support dimension by at most `r`. -/
lemma supportDim_le_supportDim_quotient_ofList_add_length (xs : List A)
    (hxm : ∀ x ∈ xs, x ∈ maximalIdeal A) :
    ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
      supportDim A M ≤
        supportDim A (M ⧸ (Ideal.ofList xs • ⊤ : Submodule A M)) + xs.length := by
  induction xs with
  | nil =>
    intro M _ _ _
    rw [supportDim_eq_of_equiv (Submodule.quotEquivOfEqBot (Ideal.ofList [] • ⊤ :
      Submodule A M) (by rw [Ideal.ofList_nil, Submodule.bot_smul]))]
    simp
  | cons x xs ih =>
    intro M _ _ _
    have hx : x ∈ maximalIdeal A := hxm x List.mem_cons_self
    rw [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs)]
    calc supportDim A M ≤ supportDim A (QuotSMulTop x M) + 1 :=
          supportDim_le_supportDim_quotSMulTop_succ hx
      _ ≤ supportDim A (QuotSMulTop x M ⧸
            (Ideal.ofList xs • ⊤ : Submodule A (QuotSMulTop x M))) + xs.length + 1 := by
          gcongr
          exact ih (fun y hy => hxm y (List.mem_cons_of_mem _ hy)) _
      _ = _ := by simp [add_assoc]

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- If `p` lies in the support of `M`, then `dim A/p ≤ dim Supp M`. -/
lemma ringKrullDim_quotient_le_supportDim (M : Type*) [AddCommGroup M] [Module A M]
    (p : PrimeSpectrum A) (hp : p ∈ support A M) :
    ringKrullDim (A ⧸ p.asIdeal) ≤ supportDim A M := by
  rw [ringKrullDim_quotient, supportDim]
  refine Order.krullDim_le_of_strictMono
    (fun q => ⟨q.1, mem_support_mono (show p ≤ q.1 from q.2) hp⟩) ?_
  intro a b hab
  exact hab

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- For primes `p ⊊ q` of `A`, `dim A/q + 1 ≤ dim A/p`. -/
lemma ringKrullDim_quotient_add_one_le {p q : Ideal A} [p.IsPrime] (hpq : p ≤ q) {x : A}
    (hxq : x ∈ q) (hxp : x ∉ p) :
    ringKrullDim (A ⧸ q) + 1 ≤ ringKrullDim (A ⧸ p) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hpq)
    (Ideal.Quotient.factor_surjective hpq) (r := Ideal.Quotient.mk p x) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxp)
  · simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq

/-- An element `z ≠ 0` of a finite module over a Noetherian local ring can be rewritten as
`z = r ^ k • w` with `w ∉ r M`, for any `r` in the maximal ideal (Krull's intersection theorem). -/
lemma exists_pow_smul_eq_not_mem_smul_top (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] {r : A} (hr : r ∈ maximalIdeal A) {z : M} (hz : z ≠ 0) :
    ∃ (k : ℕ) (w : M), r ^ k • w = z ∧ ∀ w' : M, r • w' ≠ w := by
  have hex : ∃ k, ¬ ∃ w : M, r ^ k • w = z := by
    by_contra! hall
    apply hz
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (I := Ideal.span {r})
      (by simpa [Ideal.span_singleton_eq_top] using hr)
    rw [← Submodule.mem_bot A, ← hbot, Submodule.mem_iInf]
    intro k
    obtain ⟨w, hw⟩ := hall k
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, ← hw]
    exact Submodule.smul_mem_pointwise_smul w _ ⊤ trivial
  classical
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    exact (h ▸ Nat.find_spec hex) ⟨z, by simp⟩
  obtain ⟨w, hw⟩ : ∃ w : M, r ^ (Nat.find hex - 1) • w = z := by
    by_contra h
    exact Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero h0) one_pos) h
  refine ⟨Nat.find hex - 1, w, hw, fun w' hw' => Nat.find_spec hex ⟨w', ?_⟩⟩
  calc r ^ Nat.find hex • w' = r ^ (Nat.find hex - 1) • (r • w') := by
        rw [smul_smul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)]
    _ = z := by rw [hw', hw]

/-- If `M` has a weakly regular sequence of length `n` in the maximal ideal, then every
associated prime `p` of `M` satisfies `n ≤ dim A/p`. -/
lemma length_le_ringKrullDim_quotient_of_mem_associatedPrimes (rs : List A)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal A) :
    ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M], IsWeaklyRegular M rs →
      ∀ p ∈ associatedPrimes A M, (rs.length : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p) := by
  induction rs with
  | nil =>
    intro M _ _ _ _ p hp
    have : p.IsPrime := hp.isPrime
    simpa using ringKrullDim_nonneg_of_nontrivial (R := A ⧸ p)
  | cons r rs ih =>
    intro M _ _ _ hrs p hp
    rw [isWeaklyRegular_cons_iff] at hrs
    have hr : r ∈ maximalIdeal A := hmem r List.mem_cons_self
    obtain ⟨hpp, z, rfl⟩ := (isAssociatedPrime_iff).mp hp
    have hz : z ≠ 0 := by
      rintro rfl
      exact hpp.ne_top (by ext a; simp [Submodule.mem_colon_singleton])
    obtain ⟨k, w, rfl, hw⟩ := exists_pow_smul_eq_not_mem_smul_top M hr hz
    have hw0 : w ≠ 0 := by rintro rfl; simp at hz
    have hcolon : (⊥ : Submodule A M).colon {r ^ k • w} = (⊥ : Submodule A M).colon {w} := by
      ext a
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
      rw [smul_comm]
      exact ⟨fun h => (hrs.1.pow k).right_eq_zero_of_smul h, fun h => by rw [h, smul_zero]⟩
    rw [hcolon] at hpp ⊢
    let w' : QuotSMulTop r M := Submodule.Quotient.mk w
    have hw' : w' ≠ 0 := by
      intro h
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h
      obtain ⟨v, -, hv⟩ := h
      exact hw v hv
    obtain ⟨q, hq, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A w' hw'
    have hpq : (⊥ : Submodule A M).colon {w} ≤ q := by
      refine le_trans ?_ hle
      intro a ha
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at ha ⊢
      simp [w', ← Submodule.Quotient.mk_smul, ha]
    have hrq : r ∈ q := by
      apply hle
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_pointwise_smul w _ ⊤ trivial
    have hrp : r ∉ (⊥ : Submodule A M).colon {w} := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact fun h => hw0 (hrs.1.right_eq_zero_of_smul h)
    have := ih (fun y hy => hmem y (List.mem_cons_of_mem _ hy)) (QuotSMulTop r M) hrs.2 q hq
    calc (((r :: rs).length : ℕ) : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) + 1 := by simp
      _ ≤ ringKrullDim (A ⧸ q) + 1 := by gcongr
      _ ≤ _ := ringKrullDim_quotient_add_one_le hpq hrq hrp

/-- Module form of the Cohen–Macaulay direction: if `M` has a regular sequence in the maximal
ideal whose length is `dim Supp M`, and `x₁, …, xᵣ` in the maximal ideal cut the support
dimension down by exactly `r`, then `x₁, …, xᵣ` is weakly regular on `M`. -/
lemma isWeaklyRegular_of_supportDim_quotient_ofList_add_length (xs : List A)
    (hxm : ∀ x ∈ xs, x ∈ maximalIdeal A) :
    ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (rs : List A),
      (rs.length : WithBot ℕ∞) = supportDim A M → (∀ r ∈ rs, r ∈ maximalIdeal A) →
      IsRegular M rs →
      supportDim A (M ⧸ (Ideal.ofList xs • ⊤ : Submodule A M)) + xs.length = supportDim A M →
      IsWeaklyRegular M xs := by
  induction xs with
  | nil => intros; exact IsWeaklyRegular.nil A _
  | cons x xs ih =>
    intro M _ _ _ rs hlen hmem hrs hdim
    have : Nontrivial M := hrs.nontrivial
    have hx : x ∈ maximalIdeal A := hxm x List.mem_cons_self
    have hxm' : ∀ y ∈ xs, y ∈ maximalIdeal A := fun y hy => hxm y (List.mem_cons_of_mem _ hy)
    have : Nontrivial (QuotSMulTop x M) := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
    obtain ⟨d, hd⟩ := exists_supportDim_eq_natCast (A := A) M
    obtain ⟨e, he⟩ := exists_supportDim_eq_natCast (A := A) (QuotSMulTop x M)
    rw [supportDim_eq_of_equiv (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x xs),
      hd] at hdim
    have : Nontrivial (QuotSMulTop x M ⧸
        (Ideal.ofList xs • ⊤ : Submodule A (QuotSMulTop x M))) := by
      rw [← supportDim_ne_bot_iff_nontrivial A]
      intro h
      rw [h, WithBot.bot_add] at hdim
      exact WithBot.bot_ne_coe hdim
    obtain ⟨f, hf⟩ := exists_supportDim_eq_natCast (A := A) (QuotSMulTop x M ⧸
        (Ideal.ofList xs • ⊤ : Submodule A (QuotSMulTop x M)))
    rw [hf] at hdim
    have hdim' : f + (xs.length + 1) = d := by exact_mod_cast hdim
    have h1 : e ≤ f + xs.length := by
      have := supportDim_le_supportDim_quotient_ofList_add_length xs hxm' (QuotSMulTop x M)
      rw [he, hf] at this
      exact_mod_cast this
    have h2 : d ≤ e + 1 := by
      have := supportDim_le_supportDim_quotSMulTop_succ (M := M) hx
      rw [he, hd] at this
      exact_mod_cast this
    have hlen' : rs.length = d := by rw [hd] at hlen; exact_mod_cast hlen
    have hreg : IsSMulRegular M x := by
      by_contra hreg
      have hmemU : x ∈ ⋃ p ∈ associatedPrimes A M, (p : Set A) := by
        rw [biUnion_associatedPrimes_eq_compl_regular A M]
        exact hreg
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hmemU
      obtain ⟨p, hp, hxp⟩ := hmemU
      have hU := length_le_ringKrullDim_quotient_of_mem_associatedPrimes rs hmem M
        hrs.toIsWeaklyRegular p hp
      have hpp : p.IsPrime := hp.isPrime
      have hsupp : (⟨p, hpp⟩ : PrimeSpectrum A) ∈ support A (QuotSMulTop x M) := by
        rw [support_quotSMulTop]
        refine ⟨?_, by simpa using hxp⟩
        rw [mem_support_iff_of_finite]
        obtain ⟨-, z, rfl⟩ := (isAssociatedPrime_iff).mp hp
        intro a ha
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
        exact Module.mem_annihilator.mp ha z
      have hV := ringKrullDim_quotient_le_supportDim (QuotSMulTop x M) ⟨p, hpp⟩ hsupp
      rw [he, hlen'] at *
      have : (d : WithBot ℕ∞) ≤ e := hU.trans hV
      have : d ≤ e := by exact_mod_cast this
      omega
    obtain ⟨rs', hlen'', hmem', hrs'⟩ := exists_isRegular_quotSMulTop M hx hreg e rs
      (by omega) hmem hrs
    refine (isWeaklyRegular_cons_iff M x xs).mpr ⟨hreg, ih hxm' (QuotSMulTop x M) rs'
      (by rw [hlen'', he]) hmem' hrs' ?_⟩
    rw [hf, he]
    exact_mod_cast (show f + xs.length = e by omega)

section Depth

variable (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

omit [IsNoetherianRing B] in
lemma maximalIdeal_smul_top_ne_top :
    maximalIdeal B • (⊤ : Submodule B B) ≠ ⊤ := by
  rw [smul_eq_mul, Ideal.mul_top]
  exact (maximalIdeal.isMaximal B).ne_top

/-- The depth of a Noetherian local ring is at most its Krull dimension. -/
lemma depth_le_ringKrullDim : (Module.depth B B : WithBot ℕ∞) ≤ ringKrullDim B := by
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := B))
  rw [Module.depth, if_neg (maximalIdeal_smul_top_ne_top B), ← he, WithBot.coe_le_coe]
  refine iSup_le fun ⟨rs, hrs, _⟩ => ?_
  have hne : Ideal.ofList rs ≠ ⊤ := by
    intro h
    apply hrs.top_ne_smul
    rw [h, smul_eq_mul, Ideal.top_mul]
  have : Nontrivial (B ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.mpr hne
  have h := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hrs
  rw [← he] at h
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := B ⧸ Ideal.ofList rs)
  have : ((rs.length : ℕ∞) : WithBot ℕ∞) ≤ e := by
    rw [← h]
    calc ((rs.length : ℕ∞) : WithBot ℕ∞) = 0 + (rs.length : WithBot ℕ∞) := by simp
      _ ≤ _ := by gcongr
  exact_mod_cast this

/-- A Noetherian local ring with a regular sequence in its maximal ideal of length equal to its
Krull dimension is Cohen–Macaulay. -/
lemma isCohenMacaulayLocalRing_of_isRegular (rs : List B)
    (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim B)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal B) (hrs : IsRegular B rs) :
    IsCohenMacaulayLocalRing B where
  depth_eq_ringKrullDim := by
    refine le_antisymm (depth_le_ringKrullDim B) ?_
    rw [← hlen, Module.depth, if_neg (maximalIdeal_smul_top_ne_top B)]
    have : (rs.length : ℕ∞) ≤ ⨆ rs : {rs : List B //
        RingTheory.Sequence.IsRegular B rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal B},
        (rs.1.length : ℕ∞) :=
      le_iSup_of_le (⟨rs, hrs, hmem⟩ : {rs : List B //
        RingTheory.Sequence.IsRegular B rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal B}) le_rfl
    exact_mod_cast this

end Depth

end Hartshorne.CohenMacaulay

open Hartshorne.CohenMacaulay

namespace IsCohenMacaulayLocalRing

variable {A : Type u} [CommRing A] [IsCohenMacaulayLocalRing A]

/-- A Cohen–Macaulay local ring has a regular sequence in its maximal ideal whose length is the
Krull dimension. -/
theorem exists_isRegular_length_eq_ringKrullDim :
    ∃ rs : List A, (rs.length : WithBot ℕ∞) = ringKrullDim A ∧
      (∀ r ∈ rs, r ∈ maximalIdeal A) ∧ IsRegular A rs := by
  have h := IsCohenMacaulayLocalRing.depth_eq_ringKrullDim (R := A)
  rw [Module.depth, if_neg (maximalIdeal_smul_top_ne_top A)] at h
  have : Nonempty {rs : List A //
      RingTheory.Sequence.IsRegular A rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal A} :=
    ⟨⟨[], IsRegular.nil A A, by simp⟩⟩
  have hlt : (⨆ rs : {rs : List A //
      RingTheory.Sequence.IsRegular A rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal A},
      (rs.1.length : ℕ∞)) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [htop] at h
    exact ringKrullDim_ne_top h.symm
  obtain ⟨⟨rs, hrs, hmem⟩, hi⟩ := ENat.exists_eq_iSup_of_lt_top hlt
  refine ⟨rs, ?_, hmem, hrs⟩
  rw [← h, ← hi]
  rfl

/-- **Hartshorne II, Theorem 8.21A(c)**: in a Noetherian Cohen–Macaulay local ring `A`, a
sequence `x₁, …, xᵣ` of elements of the maximal ideal is regular if and only if
`dim A/(x₁, …, xᵣ) = dim A - r`, written additively as `dim A/(x₁, …, xᵣ) + r = dim A`. -/
theorem isRegular_iff_ringKrullDim_quotient_ofList_add_length (xs : List A)
    (hxm : ∀ x ∈ xs, x ∈ maximalIdeal A) :
    IsRegular A xs ↔ ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A := by
  refine ⟨fun h => ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs h, fun h => ?_⟩
  obtain ⟨rs, hlen, hmem, hrs⟩ := exists_isRegular_length_eq_ringKrullDim (A := A)
  have hI : (Ideal.ofList xs • ⊤ : Submodule A A) = Ideal.ofList xs := by
    rw [smul_eq_mul, Ideal.mul_top]
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hxm]
  refine isWeaklyRegular_of_supportDim_quotient_ofList_add_length xs hxm A rs
    (by rw [hlen, supportDim_self_eq_ringKrullDim]) hmem hrs ?_
  rw [supportDim_self_eq_ringKrullDim, supportDim_quotient_eq_ringKrullDim, hI, h]

/-- **Hartshorne II, Theorem 8.21A(c)**, with Hartshorne's notion of regular sequence (each `xᵢ`
is a non-zero-divisor modulo `x₁, …, xᵢ₋₁`): for `x₁, …, xᵣ` in the maximal ideal of a
Cohen–Macaulay local ring `A`, the sequence is regular if and only if
`dim A/(x₁, …, xᵣ) + r = dim A`. -/
theorem isWeaklyRegular_iff_ringKrullDim_quotient_ofList_add_length (xs : List A)
    (hxm : ∀ x ∈ xs, x ∈ maximalIdeal A) :
    IsWeaklyRegular A xs ↔ ringKrullDim (A ⧸ Ideal.ofList xs) + xs.length = ringKrullDim A := by
  rw [← IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hxm]
  exact isRegular_iff_ringKrullDim_quotient_ofList_add_length xs hxm

/-- **Hartshorne II, Theorem 8.21A(c)**, last clause: the quotient of a Cohen–Macaulay local ring
by a regular sequence is Cohen–Macaulay. (The elements of a regular sequence in a local ring
automatically lie in the maximal ideal.) -/
theorem quotient_ofList (xs : List A) (hxs : IsRegular A xs) :
    IsCohenMacaulayLocalRing (A ⧸ Ideal.ofList xs) := by
  have hI : (Ideal.ofList xs • ⊤ : Submodule A A) = Ideal.ofList xs := by
    rw [smul_eq_mul, Ideal.mul_top]
  have hne : Ideal.ofList xs ≠ ⊤ := by
    intro h
    apply hxs.top_ne_smul
    rw [hI, h]
  have hxm : ∀ x ∈ xs, x ∈ maximalIdeal A := fun x hx => by
    by_contra hx'
    exact hne (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hx)
      (IsLocalRing.notMem_maximalIdeal.mp hx'))
  have : Nontrivial (A ⧸ Ideal.ofList xs) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (A ⧸ Ideal.ofList xs) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular xs hxs
  obtain ⟨rs, hlen, hmem, hrs⟩ := exists_isRegular_length_eq_ringKrullDim (A := A)
  obtain ⟨k, hk⟩ := exists_supportDim_eq_natCast (A := A) (A ⧸ Ideal.ofList xs)
  rw [supportDim_quotient_eq_ringKrullDim] at hk
  have hklen : rs.length = k + xs.length := by
    rw [hk, ← hlen] at hdim
    exact_mod_cast hdim.symm
  obtain ⟨ys, hylen, hymem, hys⟩ := exists_isRegular_quotient_ofList xs hxm A hxs k rs hklen
    hmem hrs
  rw [LinearEquiv.isRegular_congr (Submodule.quotEquivOfEq _ _ hI)] at hys
  have hmap : ∀ y ∈ ys.map (algebraMap A (A ⧸ Ideal.ofList xs)),
      y ∈ maximalIdeal (A ⧸ Ideal.ofList xs) := by
    intro y hy
    obtain ⟨y, hy', rfl⟩ := List.mem_map.mp hy
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.ofList xs))
      Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem _ (hymem y hy')
  refine isCohenMacaulayLocalRing_of_isRegular (A ⧸ Ideal.ofList xs)
    (ys.map (algebraMap A (A ⧸ Ideal.ofList xs))) (by simp [hylen, hk]) hmap ?_
  refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ hmap ?_
  exact (isWeaklyRegular_map_algebraMap_iff (A ⧸ Ideal.ofList xs) (A ⧸ Ideal.ofList xs)
    ys).mpr hys.toIsWeaklyRegular

end IsCohenMacaulayLocalRing
