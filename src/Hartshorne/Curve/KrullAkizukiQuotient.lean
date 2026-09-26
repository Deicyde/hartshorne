/-
Copyright (c) 2026 Hartshorne formalization contributors and Dokying Yang.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.KrullAkizukiPrincipal

/-!
# Finite-length ideal quotients in the Krull--Akizuki argument

This file proves the ideal-quotient step of Krull--Akizuki.  If `A` is a
one-dimensional Noetherian domain, `L` is finite over its fraction field,
and `B` is any intermediate ring in `L`, then `B/I` has finite
`A`-length for every nonzero ideal `I` of `B`.  In particular, `B/I`
is a finite `A`-module.

The proof follows Stacks Project, Tags 0H7L and 00PG, and the implementation
strategy of Mathlib PR #41755.  It uses the principal-quotient theorem from
`Hartshorne.Curve.KrullAkizukiPrincipal`; no finiteness or integrality
assumption is imposed on `B`.
-/

namespace Hartshorne

open scoped Pointwise

variable (A : Type*) [CommRing A]

/-- If a nonzero element `b ∈ J` satisfies a nonzero polynomial over `A`,
then `J` contains a nonzero element coming from `A`. -/
private lemma ideal_inter_of_aeval_eq_zero
    (B : Type*) [CommRing B] [IsDomain B] [Algebra A B]
    (J : Ideal B) (b : B) (hb : b ≠ 0) (hbJ : b ∈ J)
    (p : Polynomial A) (hp : p ≠ 0) (heval : Polynomial.aeval b p = 0) :
    ∃ a : A, a ≠ 0 ∧ algebraMap A B a ∈ J := by
  obtain ⟨q, hq_eq⟩ := Polynomial.pow_rootMultiplicity_dvd p 0
  rw [Polynomial.C_0, sub_zero] at hq_eq
  refine ⟨q.coeff 0, fun h ↦ ?_, ?_⟩
  · apply Polynomial.pow_rootMultiplicity_not_dvd hp 0
    rw [Polynomial.C_0, sub_zero, pow_succ]
    have hdvd := mul_dvd_mul_left (Polynomial.X ^ Polynomial.rootMultiplicity 0 p)
      (Polynomial.X_dvd_iff.mpr h)
    rw [← hq_eq] at hdvd
    exact hdvd
  · have hq_eval : Polynomial.aeval b q = 0 := by
      rw [hq_eq, map_mul, map_pow, Polynomial.aeval_X] at heval
      exact (mul_eq_zero.mp heval).resolve_left (pow_ne_zero _ hb)
    obtain ⟨r, hr⟩ : Polynomial.X ∣ q - Polynomial.C (q.coeff 0) := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero, sub_self]
    have h_sub := congrArg (Polynomial.aeval b) hr
    rw [map_sub, hq_eval, zero_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X] at h_sub
    rw [← neg_neg (algebraMap A B (q.coeff 0)), h_sub]
    exact J.neg_mem (J.mul_mem_right _ hbJ)

variable
  (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  (B : Type*) [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra B L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [NoZeroSMulDivisors B L]

open Classical in
/-- The `A`-rank of an arbitrary intermediate ring `B ⊆ L` is at most
`[L : K]`. -/
theorem krullAkizuki_rank_le_finrank :
    Module.rank A B ≤ Module.finrank K L := by
  have h_indep : ∀ (s : Set B), LinearIndependent A (fun x : s => x : s → B) →
      LinearIndependent K (fun x : s => algebraMap B L x : s → L) := by
    intro s hs
    have h_AL_indep : LinearIndependent A (fun x : s => algebraMap B L x) := by
      have h_ker : LinearMap.ker (IsScalarTower.toAlgHom A B L).toLinearMap = ⊥ := by
        apply LinearMap.ker_eq_bot_of_injective
        exact FaithfulSMul.algebraMap_injective B L
      exact hs.map' (IsScalarTower.toAlgHom A B L).toLinearMap h_ker
    rw [linearIndependent_iff'] at h_AL_indep ⊢
    intro t g hg i hi
    obtain ⟨d_sub, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) t g
    let a_fun : s → A := fun j => if hj : j ∈ t then (hd j hj).choose else 0
    have ha : ∀ j ∈ t, algebraMap A K (d_sub : A) * g j = algebraMap A K (a_fun j) := by
      intro j hj
      rw [show a_fun j = (hd j hj).choose from dif_pos hj, (hd j hj).choose_spec,
        Algebra.smul_def]
    have hg_d2 : ∑ i ∈ t, a_fun i • algebraMap B L i = 0 := by
      rw [← smul_zero (algebraMap A K (d_sub : A)), ← hg, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Algebra.smul_def, IsScalarTower.algebraMap_apply A K L, ← ha j hj,
        map_mul, mul_assoc]
    have ha_zero := h_AL_indep t a_fun hg_d2 i hi
    have h_gi : algebraMap A K (d_sub : A) * g i = 0 := by
      rw [ha i hi, ha_zero, map_zero]
    have hd_nz : algebraMap A K (d_sub : A) ≠ 0 := fun h =>
      mem_nonZeroDivisors_iff_ne_zero.mp d_sub.property <|
        (map_eq_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mp h
    exact (mul_eq_zero.mp h_gi).resolve_left hd_nz
  have h_rank_le : ∀ (s : Set B), LinearIndependent A (fun x : s => x : s → B) →
      Cardinal.mk s ≤ Module.finrank K L :=
    fun s hs => LinearIndependent.cardinalMk_le_finrank (h_indep s hs)
  rw [Module.rank]
  exact ciSup_le' fun s => h_rank_le s.val s.property

include K L

/-- Every nonzero ideal of an arbitrary intermediate ring `B ⊆ L` contains
a nonzero element coming from `A`.  This is Stacks Project, Tag 0H7L. -/
theorem krullAkizuki_ideal_inter_nonzero
    (J : Ideal B) (hJ : J ≠ ⊥) :
    ∃ a : A, a ≠ 0 ∧ algebraMap A B a ∈ J := by
  obtain ⟨b, hbJ, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hinj : Function.Injective (algebraMap B L) :=
    FaithfulSMul.algebraMap_injective B L
  let _ : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  obtain ⟨p, hp, heval_L⟩ :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr
      (Algebra.IsAlgebraic.isAlgebraic (algebraMap B L b))
  exact ideal_inter_of_aeval_eq_zero A B J b hb hbJ p hp <| hinj <| by
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply L b p, heval_L]

variable [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- The quotient of an arbitrary intermediate ring `B ⊆ L` by a nonzero
ideal has finite `A`-length. -/
private theorem krullAkizuki_quotientIdeal_length_lt_top
    (I : Ideal B) (hI : I ≠ ⊥) :
    Module.length A (B ⧸ I) < ⊤ := by
  obtain ⟨a, ha_ne, ha_mem⟩ := krullAkizuki_ideal_inter_nonzero A K L B I hI
  let J : Ideal B := Ideal.span {algebraMap A B a}
  have hJ_le_I : J ≤ I := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha_mem)
  let g : (B ⧸ J) →ₗ[A] (B ⧸ I) :=
    (Submodule.mapQ J I LinearMap.id ((Submodule.comap_id I).symm ▸ hJ_le_I)).restrictScalars A
  have h_AB_inj : Function.Injective (algebraMap A B) := by
    have h_AL_inj : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective A K)
    rw [IsScalarTower.algebraMap_eq A B L] at h_AL_inj
    exact Function.Injective.of_comp h_AL_inj
  let _ : NoZeroSMulDivisors A B := by
    constructor
    intro c b hcb
    rw [Algebra.smul_def] at hcb
    rcases mul_eq_zero.mp hcb with hc | hb
    · exact Or.inl (h_AB_inj (by simpa using hc))
    · exact Or.inr hb
  have hrank := krullAkizuki_rank_le_finrank A K L B
  have hrank_finite : Module.rank A B < Cardinal.aleph0 :=
    lt_of_le_of_lt hrank Cardinal.natCast_lt_aleph0
  have hJ_smul : a • (⊤ : Submodule A B) = J.restrictScalars A := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x a ⊤).mp hx
      exact Ideal.mem_span_singleton.mpr ⟨y, by rw [Algebra.smul_def]⟩
    · intro x hx
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_pointwise_smul b a ⊤ Submodule.mem_top
  have hbase : Module.length A (A ⧸ Ideal.span {a}) < ⊤ :=
    (Module.length_ne_top_iff.mpr <|
      isFiniteLength_quotient_span_singleton A
        (mem_nonZeroDivisors_iff_ne_zero.mpr ha_ne)).lt_top
  have hJ_finite : Module.length A (B ⧸ a • ⊤) < ⊤ :=
    calc
      Module.length A (B ⧸ a • ⊤)
          ≤ (Module.rank A B).toNat * Module.length A (A ⧸ Ideal.span {a}) :=
        length_quotient_smul_le A B a ha_ne _
          (Cardinal.cast_toNat_of_lt_aleph0 hrank_finite).symm
      _ ≤ Module.finrank K L * Module.length A (A ⧸ Ideal.span {a}) := by
        gcongr
        exact Cardinal.toNat_natCast (Module.finrank K L) ▸
          Cardinal.toNat_le_toNat hrank Cardinal.natCast_lt_aleph0
      _ < ⊤ := WithTop.mul_lt_top (ENat.natCast_lt_top _) hbase
  rw [hJ_smul] at hJ_finite
  exact lt_of_le_of_lt (Module.length_le_of_surjective g <|
    fun x => (Ideal.Quotient.mk_surjective x).elim fun b hb =>
      ⟨Ideal.Quotient.mk J b, hb⟩) hJ_finite

/-- For every nonzero ideal `I` of an arbitrary intermediate ring
`A ⊆ B ⊆ L`, the quotient `B/I` has finite length as an `A`-module. -/
theorem krullAkizuki_quotientIdeal_isFiniteLength
    (I : Ideal B) (hI : I ≠ ⊥) :
    IsFiniteLength A (B ⧸ I) := by
  rw [← Module.length_ne_top_iff]
  exact (krullAkizuki_quotientIdeal_length_lt_top A K L B I hI).ne

/-- The finite-length quotient `B/I` is, in particular, a finite
`A`-module. -/
theorem krullAkizuki_quotientIdeal_moduleFinite
    (I : Ideal B) (hI : I ≠ ⊥) :
    Module.Finite A (B ⧸ I) := by
  let _ : IsNoetherian A (B ⧸ I) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp <|
      krullAkizuki_quotientIdeal_isFiniteLength A K L B I hI).1
  infer_instance

end Hartshorne
