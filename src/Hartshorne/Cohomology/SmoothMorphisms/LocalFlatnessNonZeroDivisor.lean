/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The non-zero-divisor local criterion for flatness

Hartshorne, *Algebraic Geometry*, III.10, Lemma 10.3A (p. 270), citing Bourbaki,
*Algèbre commutative* III §5, and Altman–Kleiman V §3.

For a local homomorphism `A → B` of Noetherian local rings, a finite `B`-module `M`, and a nonunit
non-zero-divisor `t` of `A`, the module `M` is `A`-flat if and only if `t` is `M`-regular and
`M ⧸ t M` is flat over `A ⧸ (t)`.

The converse direction is proved with the equational criterion for flatness, without `Tor`.
Given a relation `∑ fᵢ xᵢ = 0` in `M`, flatness modulo `t` makes it trivial up to a multiple of
`t`. The error terms give a relation among `f` and elements `c` of the colon ideal `(f) : t`. If
the `c` already lie in `(f)` the correction is explicit; otherwise the ideal grows, and Noetherian
induction on ideals of `A` applies. Since `t` is `M`-regular, the procedure iterates, so the
relation is trivial modulo `tˢ` for every `s`. Krull's intersection theorem, applied to the finite
`B`-module of relations modulo trivial ones and the ideal `t B` of the local ring `B`, finishes the
proof.

The locality of `A` is part of the source's hypotheses but is not needed for the proof: the
nonunit `t` maps into the maximal ideal of `B` because `A → B` is a local homomorphism.
-/

namespace Hartshorne

open Module Pointwise

section

variable {A B M : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

variable (B) in
/-- The trivial relations for a coefficient family `f`, as a `B`-submodule. -/
private def trivRel {l : ℕ} (f : Fin l → A) : Submodule B (Fin l → M) where
  carrier := {x | IsTrivialRelation f x}
  zero_mem' := ⟨0, fun _ => Fin.elim0, Fin.elim0, fun i => by simp, fun j => Fin.elim0 j⟩
  add_mem' := by
    rintro x x' ⟨k, a, y, hx, ha⟩ ⟨k', a', y', hx', ha'⟩
    refine ⟨k + k', fun i => Fin.append (a i) (a' i), Fin.append y y', fun i => ?_, fun j => ?_⟩
    · simp [Fin.sum_univ_add, hx, hx']
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [ha, ha']
  smul_mem' := by
    rintro b x ⟨k, a, y, hx, ha⟩
    refine ⟨k, a, fun j => b • y j, fun i => ?_, ha⟩
    simp [hx, Finset.smul_sum, smul_comm b]

omit [Module B M] [IsScalarTower A B M] in
private lemma sum_smul_eq_zero_of_isTrivialRelation {l : ℕ} {f : Fin l → A} {x : Fin l → M}
    (h : IsTrivialRelation f x) : ∑ i, f i • x i = 0 := by
  obtain ⟨k, a, y, hx, ha⟩ := h
  simp only [hx, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [← Finset.sum_smul, ha]

omit [Module B M] [IsScalarTower A B M] in
/-- Lifting a trivialisation of a relation modulo `t`. -/
private lemma exists_lift_of_flat_quotSMulTop {t : A}
    [Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t M)] {l : ℕ} (f : Fin l → A) (x : Fin l → M)
    (hfx : ∑ i, f i • x i = 0) :
    ∃ (k : ℕ) (a : Fin l → Fin k → A) (y : Fin k → M) (z : Fin l → M) (c : Fin k → A),
      (∀ i, x i = ∑ j, a i j • y j + t • z i) ∧ ∀ j, ∑ i, f i * a i j = t * c j := by
  have hbar : ∑ i, (Ideal.Quotient.mk (Ideal.span {t}) (f i)) •
      (Submodule.Quotient.mk (x i) : QuotSMulTop t M) = 0 := by
    have h : ∀ i, (Ideal.Quotient.mk (Ideal.span {t}) (f i)) •
        (Submodule.Quotient.mk (x i) : QuotSMulTop t M) = Submodule.Quotient.mk (f i • x i) :=
      fun i => rfl
    simp only [h]
    simpa [map_sum] using congrArg (t • (⊤ : Submodule A M)).mkQ hfx
  obtain ⟨k, abar, ybar, hx, ha⟩ := Flat.iff_forall_isTrivialRelation.mp inferInstance hbar
  choose a ha' using fun i j => Ideal.Quotient.mk_surjective (abar i j)
  choose y hy using fun j => Submodule.Quotient.mk_surjective _ (ybar j)
  have hz : ∀ i, ∃ z, x i = ∑ j, a i j • y j + t • z := by
    intro i
    have h0 : (Submodule.Quotient.mk (x i - ∑ j, a i j • y j) : QuotSMulTop t M) = 0 := by
      rw [Submodule.Quotient.mk_sub, sub_eq_zero,
        show (Submodule.Quotient.mk (x i) : QuotSMulTop t M) = _ from hx i,
        ← Submodule.mkQ_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ha', ← hy]
      rfl
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h0
    obtain ⟨z, -, hz⟩ := h0
    exact ⟨z, by rw [hz]; abel⟩
  choose z hz using hz
  have hc : ∀ j, ∃ c, ∑ i, f i * a i j = t * c := by
    intro j
    have h0 : Ideal.Quotient.mk (Ideal.span {t}) (∑ i, f i * a i j) = 0 := by
      simpa [ha'] using ha j
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
    obtain ⟨c, hc⟩ := h0
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  exact ⟨k, a, y, z, c, hz, hc⟩

omit [Module B M] [IsScalarTower A B M] in
/-- One step of the descent: a relation is trivial up to a multiple of `t`, assuming that all
relations among generators of strictly larger ideals are trivial. -/
private lemma exists_trivial_add_smul {t : A} (hM : IsSMulRegular M t)
    [Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t M)] (J : Ideal A)
    (ih : ∀ J' : Ideal A, J < J' → ∀ {l : ℕ} (f : Fin l → A), Ideal.span (Set.range f) = J' →
      ∀ x : Fin l → M, ∑ i, f i • x i = 0 → IsTrivialRelation f x)
    {l : ℕ} (f : Fin l → A) (hfJ : Ideal.span (Set.range f) = J)
    (x : Fin l → M) (hfx : ∑ i, f i • x i = 0) :
    ∃ τ : Fin l → M, IsTrivialRelation f τ ∧ ∃ z : Fin l → M, x = τ + t • z := by
  obtain ⟨k, a, y, z, c, hx, hc⟩ := exists_lift_of_flat_quotSMulTop (t := t) f x hfx
  have h3 : ∑ j, c j • y j + ∑ i, f i • z i = 0 := by
    apply hM
    beta_reduce
    simp only [smul_add, smul_zero, Finset.smul_sum, smul_smul]
    have hz : ∀ i, t • z i = x i - ∑ j, a i j • y j := fun i => by rw [hx i]; abel
    simp_rw [← hc, mul_comm t (f _), mul_smul, hz, smul_sub, Finset.sum_sub_distrib, hfx,
      Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    abel
  by_cases hcJ : ∀ j, c j ∈ J
  · choose d hd using fun j => Ideal.mem_span_range_iff_exists_fun.mp (hfJ ▸ hcJ j)
    refine ⟨fun i => ∑ j, (a i j - t * d j i) • y j,
      ⟨k, fun i j => a i j - t * d j i, y, fun i => rfl, fun j => ?_⟩,
      fun i => z i + ∑ j, d j i • y j, ?_⟩
    · simp only [mul_sub, Finset.sum_sub_distrib, hc, ← hd, Finset.mul_sum]
      rw [sub_eq_zero]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · funext i
      simp only [Pi.add_apply, Pi.smul_apply, sub_smul, Finset.sum_sub_distrib, smul_add,
        Finset.smul_sum, smul_smul, hx i]
      abel
  · push Not at hcJ
    obtain ⟨j₀, hj₀⟩ := hcJ
    set f' : Fin (l + k) → A := Fin.append f c with hf'
    have hJ' : J < Ideal.span (Set.range f') := by
      rw [← hfJ]
      refine lt_of_le_of_ne (Ideal.span_mono ?_) ?_
      · rintro _ ⟨i, rfl⟩
        exact ⟨Fin.castAdd k i, by simp [f']⟩
      · intro h
        apply hj₀
        rw [← hfJ, h]
        exact Ideal.subset_span ⟨Fin.natAdd l j₀, by simp [f']⟩
    obtain ⟨k', α, w, hw, hα⟩ := ih _ hJ' f' rfl (Fin.append z y)
      (by simp [f', Fin.sum_univ_add, ← h3, add_comm])
    have hy : ∀ j, y j = ∑ p, α (Fin.natAdd l j) p • w p := fun j => by
      simpa using hw (Fin.natAdd l j)
    have hz : ∀ i, z i = ∑ p, α (Fin.castAdd k i) p • w p := fun i => by
      simpa using hw (Fin.castAdd k i)
    refine ⟨x, ⟨k', fun i p => ∑ j, a i j * α (Fin.natAdd l j) p + t * α (Fin.castAdd k i) p, w,
      fun i => ?_, fun p => ?_⟩, 0, by simp⟩
    · rw [hx i, hz i]
      simp only [hy, Finset.smul_sum, smul_smul, add_smul, Finset.sum_smul,
        Finset.sum_add_distrib]
      rw [Finset.sum_comm]
    · have h := hα p
      simp only [f', Fin.sum_univ_add, Fin.append_left, Fin.append_right] at h
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul, hc]
      have h' : ∑ x, t * c x * α (Fin.natAdd l x) p + ∑ x, f x * t * α (Fin.castAdd k x) p =
          t * (∑ x, f x * α (Fin.castAdd k x) p + ∑ x, c x * α (Fin.natAdd l x) p) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, add_comm]
        congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
      rw [h', h, mul_zero]

/-- The converse direction of the local criterion: a finite module over a Noetherian local
`A`-algebra on which `t` is regular, and whose reduction modulo `t` is flat over `A ⧸ (t)`, is
flat over `A`. -/
private lemma flat_of_isSMulRegular_of_flat_quotSMulTop [IsNoetherianRing A] [IsLocalRing B]
    [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] [Module.Finite B M] {t : A}
    (ht : ¬IsUnit t) (hM : IsSMulRegular M t)
    [Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t M)] : Flat A M := by
  have hI : Ideal.span {algebraMap A B t} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun h => ht ((isUnit_map_iff (algebraMap A B) t).mp h)
  have main : ∀ J : Ideal A, ∀ {l : ℕ} (f : Fin l → A), Ideal.span (Set.range f) = J →
      ∀ x : Fin l → M, ∑ i, f i • x i = 0 → IsTrivialRelation f x := by
    intro J
    induction J using WellFoundedGT.induction with
    | _ J ih =>
    intro l f hfJ x hfx
    have iter : ∀ s : ℕ, ∀ x : Fin l → M, ∑ i, f i • x i = 0 →
        ∃ τ ∈ trivRel B f, ∃ z : Fin l → M, x = τ + t ^ s • z := by
      intro s
      induction s with
      | zero => exact fun x _ => ⟨0, zero_mem _, x, by simp⟩
      | succ s ihs =>
        intro x hfx
        obtain ⟨τ, hτ, z, rfl⟩ := ihs x hfx
        have hz : ∑ i, f i • z i = 0 := by
          apply hM.pow s
          beta_reduce
          have hτ0 := sum_smul_eq_zero_of_isTrivialRelation (show IsTrivialRelation f τ from hτ)
          simp only [Pi.add_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib, hτ0,
            zero_add] at hfx
          simpa [Finset.smul_sum, smul_comm (t ^ s)] using hfx
        obtain ⟨τ', hτ', z', rfl⟩ := exists_trivial_add_smul hM J ih f hfJ z hz
        refine ⟨τ + t ^ s • τ', add_mem hτ (Submodule.smul_of_tower_mem _ _ hτ'), z', ?_⟩
        rw [smul_add, smul_smul, ← pow_succ, add_assoc]
    let N := trivRel B (M := M) f
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := (Fin l → M) ⧸ N) _ hI
    have hmem : N.mkQ x ∈
        (⨅ i : ℕ, (Ideal.span {algebraMap A B t}) ^ i • ⊤ : Submodule B ((Fin l → M) ⧸ N)) := by
      rw [Submodule.mem_iInf]
      intro s
      obtain ⟨τ, hτ, z, hxz⟩ := iter s x hfx
      have h : N.mkQ x = (algebraMap A B t) ^ s • N.mkQ z := by
        rw [hxz, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hτ, zero_add,
          ← map_pow, algebraMap_smul, LinearMap.map_smul_of_tower]
      rw [h]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) s)
        Submodule.mem_top
    rw [hK, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem
  exact Flat.iff_forall_isTrivialRelation.mpr fun {l f x} hfx => main _ f rfl x hfx

omit [Module B M] [IsScalarTower A B M] in
/-- Reduction modulo `t` preserves flatness. -/
private lemma flat_quotSMulTop_of_flat [Flat A M] (t : A) :
    Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t M) :=
  Flat.of_linearEquiv ((QuotSMulTop.equivQuotTensor t M).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective)

end

/-- **Hartshorne III, Lemma 10.3A** (local criterion for flatness across a non-zero-divisor).
Let `A → B` be a local homomorphism of Noetherian local rings, `M` a finite `B`-module, and `t`
a nonunit and non-zero-divisor of `A`. Then `M` is flat over `A` if and only if multiplication
by `t` is injective on `M` and `M ⧸ t M` is flat over `A ⧸ (t)`. -/
theorem flat_iff_isSMulRegular_and_flat_quotSMulTop {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] {t : A} (ht : ¬IsUnit t)
    (htreg : t ∈ nonZeroDivisors A) :
    Flat A M ↔ IsSMulRegular M t ∧ Flat (A ⧸ Ideal.span {t}) (QuotSMulTop t M) := by
  refine ⟨fun _ => ⟨Flat.isSMulRegular_of_nonZeroDivisors htreg, flat_quotSMulTop_of_flat t⟩,
    fun ⟨hM, _⟩ => flat_of_isSMulRegular_of_flat_quotSMulTop (B := B) ht hM⟩

end Hartshorne
