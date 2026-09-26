/-
Copyright (c) 2026 Hartshorne formalization contributors and Dokying Yang.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Principal quotients in the Krull--Akizuki argument

This file proves the module-theoretic core of Stacks Project, Tag 00PF.
The proof follows the quantitative argument developed by Dokying Yang in
Mathlib PR #41755, adapted here to the project's pinned Mathlib checkout.
-/

namespace Hartshorne

open scoped Pointwise

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- For an endomorphism `φ` of a module of finite length, the length of `ker φ` equals the
length of `coker φ`. -/
theorem length_ker_eq_length_coker
    (φ : M →ₗ[R] M) (hlen : Module.length R M < ⊤) :
    Module.length R (LinearMap.ker φ) = Module.length R (M ⧸ LinearMap.range φ) := by
  have h1 : Module.length R M =
      Module.length R (LinearMap.ker φ) + Module.length R (LinearMap.range φ) := by
    convert Module.length_eq_add_of_exact (LinearMap.ker φ).subtype (LinearMap.rangeRestrict φ)
      Subtype.coe_injective
      (fun x => ⟨Classical.choose x.2, Subtype.ext (Classical.choose_spec x.2)⟩)
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, LinearMap.ker_rangeRestrict]) using 1
  have h2 : Module.length R M =
      Module.length R (LinearMap.range φ) + Module.length R (M ⧸ LinearMap.range φ) := by
    convert Module.length_eq_add_of_exact (LinearMap.range φ).subtype
      (Submodule.mkQ (LinearMap.range φ))
      Subtype.coe_injective (Submodule.mkQ_surjective _)
      (by rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]) using 1
  obtain hr | hr := eq_or_ne (Module.length R (LinearMap.range φ)) ⊤
  · exfalso; rw [hr] at h2; simp only [top_add] at h2; exact hlen.ne h2
  · exact WithTop.add_right_cancel hr (h1.symm.trans (h2.trans (add_comm _ _)))

lemma length_quotient_chain
    (S T : Submodule R M) (hST : S ≤ T) :
    Module.length R (M ⧸ S) =
      Module.length R (M ⧸ T) + Module.length R (T ⧸ S.comap T.subtype) := by
  have h_iso : (T ⧸ S.comap T.subtype) ≃ₗ[R] T.map S.mkQ :=
    (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).symm.trans <|
      (LinearMap.quotKerEquivRange (S.mkQ.comp T.subtype)).trans <|
      LinearEquiv.ofEq _ _ (by rw [LinearMap.range_comp, Submodule.range_subtype])
  rw [Module.length_eq_add_of_exact (T.map S.mkQ).subtype (T.map S.mkQ).mkQ
        (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
        (LinearMap.exact_subtype_mkQ _),
      (Submodule.quotientQuotientEquivQuotient S T hST).length_eq,
      ← h_iso.length_eq,
      add_comm]

variable
  (A : Type*) [CommRing A]
  (M : Type*) [AddCommGroup M] [Module A M]

/-- If every element of a finitely generated submodule `N` can be scaled into `F` by a
non-zero divisor, then a single non-zero divisor scales all of `N` into `F`. -/
theorem Submodule.exists_smul_mem_of_fg
    {F N : Submodule A M} (hNfg : N.FG)
    (hclear : ∀ x ∈ N, ∃ c ∈ nonZeroDivisors A, c • x ∈ F) :
    ∃ c ∈ nonZeroDivisors A, ∀ x ∈ N, c • x ∈ F := by
  obtain ⟨s, hs⟩ := hNfg
  choose d hd_nz hd_mem using fun x : s => hclear x.1 (hs ▸ Submodule.subset_span x.2)
  refine ⟨∏ x : s, d x, prod_mem fun x _ => hd_nz x, fun x hx => ?_⟩
  have hP : ↑s ⊆ (F.comap (LinearMap.lsmul A M (∏ x : s, d x)) : Set M) := fun y hy => by
    obtain ⟨e, he⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ ⟨y, hy⟩)
    change (∏ x : s, d x) • y ∈ F
    rw [he, mul_comm, mul_smul]
    exact F.smul_mem e (hd_mem ⟨y, hy⟩)
  exact Submodule.span_le.mpr hP (hs.symm ▸ hx)

private lemma range_smul_mkQ
    (F N : Submodule A M) (a : A) :
    LinearMap.range (a • LinearMap.id : (N ⧸ F.comap N.subtype) →ₗ[A] (N ⧸ F.comap N.subtype)) =
      Submodule.map (Submodule.mkQ (F.comap N.subtype))
        ((a • N ⊔ F).comap N.subtype) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply, Submodule.mem_map,
    Submodule.mem_comap, Submodule.mem_sup, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨a • y', ⟨a • (y' : M), ⟨y', y'.property, rfl⟩, 0, F.zero_mem, add_zero _⟩, rfl⟩
  · rintro ⟨y, ⟨_, ⟨z, hz, rfl⟩, y₂, hy₂, h_add⟩, rfl⟩
    refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
    change Submodule.Quotient.mk (a • ⟨z, hz⟩) = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    change a • z - N.subtype y ∈ F
    rw [← h_add, sub_add_eq_sub_sub, sub_self, zero_sub]
    exact F.neg_mem hy₂

/-- The length of `Aʳ ⧸ (a) · Aʳ` equals `r * length(A ⧸ (a))`. -/
theorem length_free_quotient_smul
    (a : A) (r : ℕ) :
    Module.length A ((Fin r → A) ⧸ ((Ideal.span {a}) • (⊤ : Submodule A (Fin r → A))))
      = r * Module.length A (A ⧸ Ideal.span {a}) := by
  have h_iso_fin : ((Fin r → A) ⧸ Ideal.span {a} • (⊤ : Submodule A (Fin r → A))) ≃ₗ[A]
      (Fin r → (A ⧸ Ideal.span {a})) := by
    have h_free : Ideal.span {a} • (⊤ : Submodule A (Fin r → A)) =
        Submodule.pi Set.univ (fun _ => Ideal.span {a}) := by
      rw [Submodule.ideal_span_singleton_smul]
      ext x
      simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
        Submodule.mem_pi, Set.mem_univ, forall_true_left]
      refine ⟨fun ⟨y, hy_eq⟩ i => hy_eq ▸ Ideal.mul_mem_right (y i) _
        (Ideal.mem_span_singleton_self a), fun hx => ?_⟩
      choose f hf using fun i => Ideal.mem_span_singleton.mp (hx i)
      exact ⟨f, by ext i; rw [Pi.smul_apply, smul_eq_mul]; exact (hf i).symm⟩
    rw [h_free]
    exact Submodule.quotientPi fun _ => Ideal.span {a}
  rw [LinearEquiv.length_eq h_iso_fin, Module.length_pi,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]

private lemma length_ker_smul_eq [NoZeroSMulDivisors A M]
    (F N : Submodule A M) (a : A) (ha : a ≠ 0) :
    Module.length A (LinearMap.ker
      (a • LinearMap.id : (N ⧸ F.comap N.subtype) →ₗ[A] (N ⧸ F.comap N.subtype))) =
      Module.length A (((a • N ⊓ F).comap N.subtype) ⧸
        ((a • F).comap N.subtype).comap ((a • N ⊓ F).comap N.subtype).subtype) := by
  let F' := F.comap N.subtype
  let aNF := (a • N ⊓ F).comap N.subtype
  let aF_N := (a • F).comap N.subtype
  let K := Submodule.comap (a • LinearMap.id : ↥N →ₗ[A] ↥N) F'
  have h_cod : ∀ x : ↥K, ((a • LinearMap.id : ↥N →ₗ[A] ↥N).comp K.subtype) x ∈ aNF := by
    intro x
    refine ⟨?_, x.property⟩
    exact ⟨x.val, x.val.property, rfl⟩
  let g := LinearMap.codRestrict aNF ((a • LinearMap.id : ↥N →ₗ[A] ↥N).comp K.subtype) h_cod
  let g_q := (Submodule.mkQ (aF_N.comap aNF.subtype)).comp g
  have hF'_ker : F'.comap K.subtype ≤ LinearMap.ker g_q := by
    intro x hx
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (g x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x.val, hx, rfl⟩
  let h := Submodule.liftQ (F'.comap K.subtype) g_q hF'_ker
  have h_bij : Function.Bijective h := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      change (Submodule.Quotient.mk (⟨x, hx⟩ : K) : K ⧸ F'.comap K.subtype) =
        Submodule.Quotient.mk (⟨y, hy⟩ : K)
      rw [Submodule.Quotient.eq]
      change (x.val : M) - (y.val : M) ∈ F
      have h_diff : Submodule.Quotient.mk (g ⟨x, hx⟩) = Submodule.Quotient.mk (g ⟨y, hy⟩) := hxy
      rw [Submodule.Quotient.eq] at h_diff
      change a • (x.val : M) - a • (y.val : M) ∈ a • F at h_diff
      rw [← smul_sub, Submodule.mem_smul_pointwise_iff_exists] at h_diff
      obtain ⟨z, hz, hz_eq⟩ := h_diff
      have h_z : (z : M) = x.val - y.val := by
        refine sub_eq_zero.mp
          ((NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero ?_).resolve_left ha)
        rw [smul_sub, hz_eq, sub_self]
      rw [← h_z]
      exact hz
    · intro y
      obtain ⟨y_pre, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      have hy_ideal : (y_pre.val : M) ∈ a • N := y_pre.property.1
      rw [Submodule.mem_smul_pointwise_iff_exists] at hy_ideal
      obtain ⟨x, hx, hx_eq⟩ := hy_ideal
      have hxK : a • x ∈ F := hx_eq.symm ▸ y_pre.property.2
      refine ⟨Submodule.Quotient.mk ⟨⟨x, hx⟩, hxK⟩, ?_⟩
      change Submodule.Quotient.mk (g ⟨⟨x, hx⟩, hxK⟩) = Submodule.Quotient.mk y_pre
      rw [Submodule.Quotient.eq]
      have h_g : g ⟨⟨x, hx⟩, hxK⟩ = y_pre := by ext; exact hx_eq
      rw [h_g, sub_self]
      exact Submodule.zero_mem _
  have h_length_K_ker : Module.length A (↥K ⧸ F'.comap K.subtype) =
      Module.length A (LinearMap.ker (a • LinearMap.id : (N ⧸ F') →ₗ[A] (N ⧸ F'))) := by
    let f_ker_pre := (Submodule.mkQ F').comp K.subtype
    have h_ker_cod : ∀ x : K, f_ker_pre x ∈
        LinearMap.ker (a • LinearMap.id : (N ⧸ F') →ₗ[A] (N ⧸ F')) := by
      intro x
      change Submodule.Quotient.mk (a • x.val) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact x.property
    let f_ker := LinearMap.codRestrict _ f_ker_pre h_ker_cod
    have h_ker_ker : F'.comap K.subtype ≤ LinearMap.ker f_ker := by
      intro x hx
      rw [LinearMap.mem_ker]
      ext
      change Submodule.Quotient.mk x.val = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hx
    let f_ker_lift := Submodule.liftQ _ f_ker h_ker_ker
    refine LinearEquiv.length_eq (LinearEquiv.ofBijective f_ker_lift ⟨?_, ?_⟩)
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      have h_eq : F'.mkQ x = F'.mkQ y := by
        have h_ker_eq : f_ker ⟨x, hx⟩ = f_ker ⟨y, hy⟩ := hxy
        change (f_ker ⟨x, hx⟩).val = (f_ker ⟨y, hy⟩).val
        rw [h_ker_eq]
      change (Submodule.Quotient.mk (⟨x, hx⟩ : K) : K ⧸ F'.comap K.subtype) =
        Submodule.Quotient.mk (⟨y, hy⟩ : K)
      simp only [Submodule.mkQ_apply] at h_eq
      rw [Submodule.Quotient.eq] at h_eq ⊢
      exact h_eq
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx_eq⟩ := Submodule.Quotient.mk_surjective _ y
      have hxK : a • x ∈ F' := by
        change a • y = 0 at hy
        rw [← hx_eq] at hy
        change Submodule.Quotient.mk (a • x) = 0 at hy
        rw [Submodule.Quotient.mk_eq_zero] at hy
        exact hy
      refine ⟨Submodule.Quotient.mk ⟨x, hxK⟩, ?_⟩
      ext
      exact hx_eq
  rw [← h_length_K_ker]
  exact (LinearEquiv.ofBijective h h_bij).length_eq

/-- A module of rank `r` over a domain contains a free submodule of rank `r` such that
every element can be scaled into it by a non-zero divisor. -/
theorem exists_free_submodule_of_rank [IsDomain A]
    (r : ℕ) (hrank : Module.rank A M = r) :
    ∃ F : Submodule A M,
      Nonempty (F ≃ₗ[A] (Fin r → A)) ∧
      ∀ x : M, ∃ c ∈ nonZeroDivisors A, c • x ∈ F := by
  obtain ⟨v, hv⟩ : ∃ (v : Fin r → M), LinearIndependent A v :=
    exists_linearIndependent_of_le_rank hrank.symm.le
  use Submodule.span A (Set.range v)
  refine ⟨⟨(Module.Basis.span hv).equivFun⟩, fun x => ?_⟩
  have h_dep : ¬LinearIndependent A (Fin.cons x v) := fun h_ind => by
    have h_rank := h_ind.cardinal_lift_le_rank
    rw [hrank, Cardinal.mk_fin (r + 1)] at h_rank
    simp only [Cardinal.lift_natCast] at h_rank
    exact absurd h_rank (not_le.mpr (Nat.cast_lt.mpr (Nat.lt_succ_self r)))
  obtain ⟨g, hg_sum, i, hgi⟩ := Fintype.not_linearIndependent_iff.mp h_dep
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hg_sum
  have hg0 : g 0 ≠ 0 := fun h0 => by
    simp only [h0, zero_smul, zero_add] at hg_sum
    exact hgi (Fin.cases h0
      (Fintype.linearIndependent_iff.mp hv (fun (j : Fin r) => g j.succ) hg_sum) i)
  use g 0, mem_nonZeroDivisors_iff_ne_zero.mpr hg0
  rw [add_eq_zero_iff_eq_neg] at hg_sum
  rw [hg_sum]
  exact Submodule.neg_mem _ (Submodule.sum_mem _
    fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _)))

variable [IsNoetherianRing A]

lemma build_fg_witness
    (F : Submodule A M) (r : ℕ)
    (hF_iso : Nonempty (F ≃ₗ[A] (Fin r → A)))
    (a : A)
    (p : LTSeries (Submodule A (M ⧸ a • (⊤ : Submodule A M)))) :
    ∃ (N : Submodule A M), F ≤ N ∧ N.FG ∧
      ∃ (q : LTSeries (Submodule A N)), q.length = p.length ∧
        ∀ i, (a • N).comap N.subtype ≤ q i := by
  have hF_fg : F.FG := Module.Finite.iff_fg.mp (Module.Finite.of_injective _ hF_iso.some.injective)
  let e := Submodule.comapMkQRelIso (a • (⊤ : Submodule A M))
  let q : LTSeries (Set.Ici (a • (⊤ : Submodule A M))) := LTSeries.map p ⇑e e.strictMono
  obtain ⟨S, hS_fg, hS⟩ : ∃ S : Submodule A M, S.FG ∧ ∀ i : Fin q.length,
      (q.toFun (Fin.castSucc i)).val ≤ (q.toFun (Fin.succ i)).val ∧
        ∃ y ∈ (q.toFun (Fin.succ i)).val, y ∉ (q.toFun (Fin.castSucc i)).val ∧ y ∈ S := by
    choose y hy using fun i : Fin q.length =>
      SetLike.exists_of_lt (show (q.toFun (Fin.castSucc i)).val <
        (q.toFun (Fin.succ i)).val from q.step i)
    refine ⟨Submodule.span A (Set.range y), Submodule.fg_span (Set.finite_range y), fun i => ?_⟩
    exact ⟨(show (q.toFun (Fin.castSucc i)).val <
        (q.toFun (Fin.succ i)).val from q.step i).le,
      y i, (hy i).1, (hy i).2, Submodule.subset_span (Set.mem_range_self i)⟩
  let FS : Submodule A M := F ⊔ S
  refine ⟨FS, le_sup_left, Submodule.FG.sup hF_fg hS_fg, ?_⟩
  let q' : LTSeries (Submodule A FS) :=
    { length := q.length
      toFun := fun i => Submodule.comap (Submodule.subtype FS) (q.toFun i).val
      step := fun i =>
        have h_lt : Submodule.comap FS.subtype (q.toFun (Fin.castSucc i)).val <
            Submodule.comap FS.subtype (q.toFun (Fin.succ i)).val :=
          SetLike.lt_iff_le_and_exists.mpr (by
            obtain ⟨hle, z, hz1, hz2, hz3⟩ := hS i
            exact ⟨Submodule.comap_mono hle, ⟨z, Submodule.mem_sup_right hz3⟩, hz1, hz2⟩)
        h_lt }
  refine ⟨q', rfl, fun i x hx => ?_⟩
  obtain ⟨y, hy, hy_eq⟩ := (Submodule.mem_smul_pointwise_iff_exists x.val a FS).mp hx
  have hx_top : (x.val : M) ∈ a • (⊤ : Submodule A M) :=
    (Submodule.mem_smul_pointwise_iff_exists x.val a (⊤ : Submodule A M)).mpr
      ⟨y, Set.mem_univ y, hy_eq⟩
  exact (q.toFun i).property hx_top

variable [IsDomain A] [Ring.KrullDimLE 1 A]

/-- The quotient of a one-dimensional Noetherian ring by a nonzero principal ideal is
Artinian. -/
theorem quotient_isArtinian_of_nonzero
    (a : A) (ha : a ≠ 0) :
    IsArtinianRing (A ⧸ Ideal.span {a}) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro I hI
  have h_max : (Ideal.comap (Ideal.Quotient.mk (Ideal.span {a})) I).IsMaximal :=
    Ideal.IsPrime.isMaximal_of_ne_bot inferInstance fun h_bot =>
      ha <| Ideal.mem_bot.mp (h_bot ▸ Ideal.mem_comap.mpr
        ((Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.mem_span_singleton_self a)).symm ▸ Submodule.zero_mem I))
  have h_map : Ideal.map (Ideal.Quotient.mk (Ideal.span {a}))
      (Ideal.comap (Ideal.Quotient.mk (Ideal.span {a})) I) = I :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I
  rw [← h_map] at hI ⊢
  exact (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective h_max).elim
    (fun h_top => absurd h_top hI.ne_top) id

/-- If `N` is finitely generated and every element of `N` can be scaled by a non-zero divisor
into `F`, then `N ⧸ F` has finite length. -/
theorem finiteLength_quotient_of_fg
    (F N : Submodule A M)
    (hNfg : N.FG)
    (hclear : ∀ x ∈ N, ∃ c ∈ nonZeroDivisors A, c • x ∈ F) :
    Module.length A (N ⧸ F.comap N.subtype) < ⊤ := by
  obtain ⟨c, hc_nz, hc_clear⟩ := Submodule.exists_smul_mem_of_fg A M hNfg hclear
  have hc_ne : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc_nz
  have hc_ann : ∀ x : N ⧸ F.comap N.subtype, c • x = 0 := by
    intro x; induction x using Quotient.inductionOn with
    | h x =>
      change Submodule.Quotient.mk (c • x) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hc_clear (↑x) x.property
  have htorsI : Module.IsTorsionBySet A (N ⧸ F.comap N.subtype) (Ideal.span {c}) := by
    intro x a
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp a.property
    change (a : A) • x = 0
    rw [hd, mul_comm, mul_smul, hc_ann, smul_zero]
  let _ := htorsI.module
  have _ : IsScalarTower A (A ⧸ Ideal.span {c}) (N ⧸ F.comap N.subtype) := htorsI.isScalarTower
  have _ : Module.Finite A N := Module.Finite.iff_fg.mpr hNfg
  have _ : Module.Finite A (N ⧸ F.comap N.subtype) := Module.Finite.quotient _ _
  have _ : Module.Finite (A ⧸ Ideal.span {c}) (N ⧸ F.comap N.subtype) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have _ : IsNoetherian A (N ⧸ F.comap N.subtype) :=
    isNoetherian_of_isNoetherianRing_of_finite A _
  have hArt : IsArtinianRing (A ⧸ Ideal.span {c}) := quotient_isArtinian_of_nonzero A c hc_ne
  have _ : IsArtinian A (N ⧸ F.comap N.subtype) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := Ideal.span {c}))
  exact lt_top_iff_ne_top.mpr Module.length_ne_top

variable [NoZeroSMulDivisors A M]

/-- The length of the quotient `N ⧸ aN` equals the length of `F ⧸ aF` when `F ≤ N`
with `N` finitely generated, the element `a` non-zero, and
every element of `N` can be scaled into `F`. -/
theorem length_quotient_smul_eq_free
    (F N : Submodule A M) (a : A) (ha : a ≠ 0)
    (hFN : F ≤ N) (hNfg : N.FG)
    (hclear : ∀ x ∈ N, ∃ c ∈ nonZeroDivisors A, c • x ∈ F) :
    Module.length A (N ⧸ (a • N).comap N.subtype)
      = Module.length A (F ⧸ (a • F).comap F.subtype) := by
  have h_snake : Module.length A (N ⧸ (a • N).comap N.subtype) =
      Module.length A (N ⧸ (a • N ⊔ F).comap N.subtype) +
      Module.length A (F ⧸ (F ⊓ a • N).comap F.subtype) := by
    rw [length_quotient_chain _ _ (Submodule.comap_mono le_sup_left)]
    congr 1
    let aN := a • N
    let T := (aN ⊔ F).comap N.subtype
    let S := aN.comap N.subtype
    let g_pre : F →ₗ[A] T :=
      { toFun := fun x => ⟨⟨x.val, hFN x.property⟩, Submodule.mem_sup_right x.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let g := (Submodule.mkQ (S.comap T.subtype)).comp g_pre
    have h_ker : LinearMap.ker g = (F ⊓ aN).comap F.subtype := by
      ext ⟨x, hx⟩
      simp only [g, g_pre, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_inf,
        Submodule.coe_subtype]
      exact ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
    have h_surj : LinearMap.range g = ⊤ := by
      rw [LinearMap.range_eq_top]
      rintro ⟨⟨x, hxN⟩, hxT⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxT
      refine ⟨⟨z, hz⟩, ?_⟩
      have h_eq : (S.comap T.subtype).mkQ ⟨⟨z, hFN hz⟩, Submodule.mem_sup_right hz⟩ =
          (S.comap T.subtype).mkQ ⟨⟨y + z, hxN⟩, hxT⟩ := by
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        change z - (y + z) ∈ aN
        have h_abel : z - (y + z) = -y := by abel
        rw [h_abel]
        exact Submodule.neg_mem _ hy
      exact h_eq
    exact (LinearEquiv.length_eq (LinearEquiv.ofBijective
      (Submodule.liftQ _ g (le_of_eq h_ker.symm))
      ⟨by rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, h_ker, Submodule.mkQ_map_self],
       by rw [← LinearMap.range_eq_top, Submodule.range_liftQ, h_surj]⟩)).symm
  have h_snake_ker : Module.length A (N ⧸ (a • N ⊔ F).comap N.subtype) =
      Module.length A (((a • N ⊓ F).comap N.subtype) ⧸
        ((a • F).comap N.subtype).comap ((a • N ⊓ F).comap N.subtype).subtype) := by
    rw [← LinearEquiv.length_eq
          (Submodule.quotientQuotientEquivQuotient _ _ (Submodule.comap_mono le_sup_right)),
        ← range_smul_mkQ A M F N a,
        ← length_ker_eq_length_coker _ (finiteLength_quotient_of_fg A M F N hNfg hclear),
        length_ker_smul_eq A M F N a ha]
  have h_decomp : Module.length A (F ⧸ (a • F).comap F.subtype) =
      Module.length A (F ⧸ (F ⊓ a • N).comap F.subtype) +
      Module.length A (((F ⊓ a • N).comap F.subtype) ⧸
        ((a • F).comap F.subtype).comap ((F ⊓ a • N).comap F.subtype).subtype) := by
    refine length_quotient_chain _ _ (fun x hx => ?_)
    simp only [Submodule.mem_comap, Submodule.mem_inf] at hx ⊢
    refine ⟨x.property, ?_⟩
    obtain ⟨y, hy, heq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ a F).mp hx
    exact heq ▸ (Submodule.mem_smul_pointwise_iff_exists _ a N).mpr ⟨y, hFN hy, rfl⟩
  have h_match : Module.length A (((a • N ⊓ F).comap N.subtype) ⧸
        ((a • F).comap N.subtype).comap ((a • N ⊓ F).comap N.subtype).subtype) =
      Module.length A (((F ⊓ a • N).comap F.subtype) ⧸
        ((a • F).comap F.subtype).comap ((F ⊓ a • N).comap F.subtype).subtype) := by
    let e : ((a • N ⊓ F).comap N.subtype) ≃ₗ[A] ((F ⊓ a • N).comap F.subtype) :=
      { toFun := fun x => ⟨⟨x.val.val, x.property.2⟩, ⟨x.property.2, x.property.1⟩⟩
        invFun := fun x => ⟨⟨x.val.val, hFN x.property.1⟩, ⟨x.property.2, x.property.1⟩⟩
        left_inv := fun _ => by ext; rfl
        right_inv := fun _ => by ext; rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e ?_)
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · rintro ⟨y, hy, hy_eq⟩
      change y.val.val ∈ a • F at hy
      have h_eq : y.val.val = x.val.val :=
        congr_arg (fun z : ((F ⊓ a • N).comap F.subtype) => z.val.val) hy_eq
      rw [h_eq] at hy
      exact hy
    · intro hx
      change x.val.val ∈ a • F at hx
      have hy_eq : e (e.symm x) = x := e.apply_symm_apply x
      have h_eq : (e.symm x).val.val = x.val.val :=
        congr_arg (fun z : ((F ⊓ a • N).comap F.subtype) => z.val.val) hy_eq
      refine ⟨e.symm x, ?_, hy_eq⟩
      rw [h_eq]
      exact hx
  rw [h_snake, h_snake_ker, h_decomp, h_match, add_comm]

lemma length_fg_quotient_eq_bound
    (F : Submodule A M) (a : A) (ha : a ≠ 0) (r : ℕ)
    (hF : Nonempty (F ≃ₗ[A] (Fin r → A)))
    (N : Submodule A M) (hFN : F ≤ N) (hNfg : N.FG)
    (hclear : ∀ x ∈ N, ∃ c ∈ nonZeroDivisors A, c • x ∈ F) :
    Module.length A (N ⧸ (a • N).comap N.subtype)
      = r * Module.length A (A ⧸ Ideal.span {a}) := by
  have h_F_eq : Module.length A (F ⧸ (a • F).comap F.subtype) =
      Module.length A ((Fin r → A) ⧸ ((Ideal.span {a}) • (⊤ : Submodule A (Fin r → A)))) := by
    obtain ⟨e⟩ := hF
    have h_iso : Submodule.comap F.subtype (a • F) = Ideal.span {a} • ⊤ := by
      ext ⟨x, hx⟩
      simp only [Submodule.ideal_span_singleton_smul, Submodule.mem_comap,
        Submodule.mem_smul_pointwise_iff_exists, Subtype.ext_iff, Submodule.mem_top, true_and]
      exact ⟨fun ⟨y, hy, eq⟩ => ⟨⟨y, hy⟩, eq⟩, fun ⟨⟨y, hy⟩, eq⟩ => ⟨y, hy, eq⟩⟩
    have h_range : LinearMap.range (e : F →ₗ[A] (Fin r → A)) = ⊤ :=
      LinearMap.range_eq_top.mpr e.surjective
    exact LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e (by
      change Submodule.map (e : F →ₗ[A] (Fin r → A)) _ = _
      rw [h_iso, Submodule.map_smul'', Submodule.map_top, h_range]))
  rw [length_quotient_smul_eq_free A M F N a ha hFN hNfg hclear,
      h_F_eq,
      length_free_quotient_smul A a r]

/-- The length of `M ⧸ aM` is at most `r * length(A ⧸ (a))` where `r` is the rank
of `M` and `a` is non-zero. -/
theorem length_quotient_smul_le
    (a : A) (ha : a ≠ 0)
    (r : ℕ) (hrank : Module.rank A M = r) :
    Module.length A (M ⧸ a • (⊤ : Submodule A M))
      ≤ r * Module.length A (A ⧸ Ideal.span {a}) := by
  obtain ⟨F, hF_iso, hF_clear⟩ := exists_free_submodule_of_rank A M r hrank
  rw [Module.length_eq_height, Order.height_le_iff]
  intro p hp
  obtain ⟨N, hFN, hNfg, q, hqlen, hqbase⟩ := build_fg_witness A M F r hF_iso a p
  rw [← length_fg_quotient_eq_bound A M F a ha r hF_iso N hFN hNfg (fun x _ => hF_clear x),
    ← hqlen, Module.length]
  let q_Ici : LTSeries (Set.Ici ((a • N).comap N.subtype)) :=
    { length := q.length,
      toFun := fun i => ⟨q i, hqbase i⟩,
      step := fun i => q.step i }
  let e := (Submodule.comapMkQRelIso ((a • N).comap N.subtype)).symm
  exact (WithBot.le_unbot_iff _).mpr (le_iSup_of_le (LTSeries.map q_Ici ⇑e e.strictMono) le_rfl)

universe u v

/-- If `A` is a one-dimensional Noetherian domain with fraction field `K`,
`M` is any `A`-submodule of `K^r`, and `a ≠ 0`, then `M / aM` has
finite length over `A`.  This is Stacks Project, Tag 00PF. -/
theorem krullAkizuki_principalQuotient_isFiniteLength
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (r : ℕ) (M : Submodule A (Fin r → K))
    (a : A) (ha : a ≠ 0) :
    IsFiniteLength A (M ⧸ a • (⊤ : Submodule A M)) := by
  let _ : NoZeroSMulDivisors A M := by
    constructor
    intro c x hcx
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    apply Subtype.ext
    funext i
    have hi := congr_fun (congrArg (fun y : M => (y : Fin r → K)) hcx) i
    change c • ((x : Fin r → K) i) = 0 at hi
    rw [Algebra.smul_def] at hi
    exact (mul_eq_zero.mp hi).resolve_left fun hcK =>
      hc ((map_eq_zero_iff (algebraMap A K) (IsFractionRing.injective A K)).mp hcK)
  have hrank_ambient : Module.rank A (Fin r → K) = r := by
    rw [← IsFractionRing.rank_right_eq A K (Fin r → K)]
    simp
  have hrank_lt : Module.rank A M < Cardinal.aleph0 :=
    lt_of_le_of_lt (Submodule.rank_le M) <| by
      rw [hrank_ambient]
      exact Cardinal.natCast_lt_aleph0
  have hbound := length_quotient_smul_le A M a ha _
    (Cardinal.cast_toNat_of_lt_aleph0 hrank_lt).symm
  rw [← Module.length_ne_top_iff]
  exact (lt_of_le_of_lt hbound <| WithTop.mul_lt_top (ENat.natCast_lt_top _) <|
    (Module.length_ne_top_iff.mpr <|
      isFiniteLength_quotient_span_singleton A
        (mem_nonZeroDivisors_iff_ne_zero.mpr ha)).lt_top).ne

end Hartshorne
