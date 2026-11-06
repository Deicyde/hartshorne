/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Unramified.Field

/-!
# Differentials of finitely generated field extensions

Hartshorne, *Algebraic Geometry*, II.8, Theorem 8.6A (p. 174), citing Matsumura,
*Commutative Algebra*, Theorem 59.

For a finitely generated field extension `K/k` we prove `trdeg_k K ≤ dim_K Ω_{K/k}`, with equality
exactly when `K/k` is separably generated, and that `Ω_{K/k} = 0` exactly when `K/k` is separable.

Choose `t ⊆ K` such that the differentials `dt` form a basis of `Ω_{K/k}`. Then `Ω_{K/k(t)} = 0`,
so `K` is formally unramified, hence separable algebraic, over `k(t)` (Mathlib's
`Algebra.FormallyUnramified.isSeparable`, using that `K/k(t)` is essentially of finite type).
Hence `t` contains a transcendence basis of `K/k`, which gives the inequality; in case of equality
that basis is all of `t`, so `t` is a separating transcendence basis. Conversely, for a separating
transcendence basis `s`, the field `K` is formally étale over the polynomial ring `k[s]`, so
`Ω_{K/k} ≅ K ⊗_{k[s]} Ω_{k[s]/k}` is free of rank `#s = trdeg_k K`.
-/

open KaehlerDifferential Cardinal

namespace Hartshorne

universe u v
variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- For a separating transcendence basis `s` of `K/k`, the module `Ω_{K/k}` has rank `#s`: it is
the base change of the free module of differentials of the polynomial ring on `s`, because `K` is
formally étale over that polynomial ring. -/
theorem rank_kaehlerDifferential_eq_of_isSeparable {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    [Algebra.IsSeparable (IntermediateField.adjoin k s) K] :
    Module.rank K Ω[K⁄k] = #s := by
  classical
  have hr : Set.range ((↑) : s → K) = s := Subtype.range_coe
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := by
    rw [hr]; infer_instance
  have : Algebra.FormallyEtale (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K :=
    .of_isSeparable _ K
  have : Algebra.FormallyEtale (Algebra.adjoin k (Set.range ((↑) : s → K)))
      (IntermediateField.adjoin k (Set.range ((↑) : s → K))) :=
    .of_isLocalization (nonZeroDivisors _)
  have : Algebra.FormallyEtale (Algebra.adjoin k (Set.range ((↑) : s → K))) K :=
    .comp _ (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K
  let : Algebra (MvPolynomial s k) (Algebra.adjoin k (Set.range ((↑) : s → K))) :=
    hs.1.aevalEquiv.toRingHom.toAlgebra
  have : Algebra.FormallyEtale (MvPolynomial s k) (Algebra.adjoin k (Set.range ((↑) : s → K))) :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId _ _) hs.1.aevalEquiv.bijective)
  let : Algebra (MvPolynomial s k) K := (MvPolynomial.aeval ((↑) : s → K)).toRingHom.toAlgebra
  have : IsScalarTower (MvPolynomial s k) (Algebra.adjoin k (Set.range ((↑) : s → K))) K :=
    IsScalarTower.of_algebraMap_eq fun p => (hs.1.algebraMap_aevalEquiv p).symm
  have : Algebra.FormallyEtale (MvPolynomial s k) K :=
    .comp _ (Algebra.adjoin k (Set.range ((↑) : s → K))) K
  have : IsScalarTower k (MvPolynomial s k) K :=
    IsScalarTower.of_algebraMap_eq fun r => ((MvPolynomial.aeval ((↑) : s → K)).commutes r).symm
  have h1 := (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial s k) K).lift_rank_eq
  have h2 := ((mvPolynomialBasis k s).baseChange K).mk_eq_rank
  rw [h1] at h2
  exact (Cardinal.lift_inj.{v, max u v}.mp h2).symm


/-- If the differentials of elements coming from an intermediate algebra `L` span `Ω_{K/k}`,
then `Ω_{K/L} = 0`. -/
theorem subsingleton_kaehlerDifferential_of_span {L : Type*} [CommRing L] [Algebra k L]
    [Algebra L K] [IsScalarTower k L K] {t : Set K} (htL : t ⊆ Set.range (algebraMap L K))
    (ht : Submodule.span K (D k K '' t) = ⊤) :
    Subsingleton Ω[K⁄L] := by
  have hle : Submodule.span K (D k K '' t) ≤ LinearMap.ker (map k L K K) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := htL hy
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_D]
    exact (D L K).map_algebraMap z
  rw [ht, top_le_iff, LinearMap.ker_eq_top] at hle
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := map_surjective k L K a
  obtain ⟨b, rfl⟩ := map_surjective k L K b
  simp [hle]


/-- **Hartshorne II, Theorem 8.6A** (Matsumura, Theorem 59). Let `K/k` be a finitely generated
field extension. Then `trdeg_k K ≤ dim_K Ω_{K/k}`, with equality if and only if `K/k` is separably
generated, i.e. has a transcendence basis `s` such that `K` is separable algebraic over `k(s)`.
Moreover `Ω_{K/k} = 0` exactly when `K/k` is separable (algebraic); in particular this applies to
finite algebraic extensions. -/
theorem trdeg_le_rank_kaehlerDifferential (hfg : (⊤ : IntermediateField k K).FG) :
    Algebra.trdeg k K ≤ Module.rank K Ω[K⁄k] ∧
      (Algebra.trdeg k K = Module.rank K Ω[K⁄k] ↔
        ∃ s : Set K, IsTranscendenceBasis k ((↑) : s → K) ∧
          Algebra.IsSeparable (IntermediateField.adjoin k s) K) ∧
      (Subsingleton Ω[K⁄k] ↔ Algebra.IsSeparable k K) := by
  have : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp hfg
  -- a subset `t` of `K` whose differentials form a basis of `Ω_{K/k}`
  obtain ⟨t, ht_ind, ht_max⟩ := exists_maximal_linearIndepOn K (D k K)
  have hspan : Submodule.span K (D k K '' t) = ⊤ := by
    rw [eq_top_iff, ← span_range_derivation, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    by_cases hy : y ∈ t
    · exact Submodule.subset_span ⟨y, hy, rfl⟩
    · obtain ⟨a, ha, hmem⟩ := ht_max y hy
      have := Submodule.smul_mem _ a⁻¹ hmem
      rwa [inv_smul_smul₀ ha] at this
  have hrank : Module.rank K Ω[K⁄k] = #t := by
    have := rank_span ht_ind.linearIndependent
    rw [show Set.range (fun x : t => D k K x) = D k K '' t from (Set.image_eq_range _ _).symm,
      hspan, rank_top, Cardinal.mk_image_eq_of_injOn _ _ ht_ind.injOn] at this
    exact this
  have htfin : t.Finite := by
    rw [← Cardinal.lt_aleph0_iff_set_finite, ← hrank]
    exact Module.rank_lt_aleph0 K Ω[K⁄k]
  -- `K` is separable algebraic over `k(t)`
  have hsub : Subsingleton Ω[K⁄IntermediateField.adjoin k t] :=
    subsingleton_kaehlerDifferential_of_span
      (fun y hy => ⟨⟨y, IntermediateField.subset_adjoin k t hy⟩, rfl⟩) hspan
  have : Algebra.FormallyUnramified (IntermediateField.adjoin k t) K := ⟨hsub⟩
  have : Algebra.EssFiniteType (IntermediateField.adjoin k t) K := .of_comp k _ K
  have hsepL : Algebra.IsSeparable (IntermediateField.adjoin k t) K :=
    Algebra.FormallyUnramified.isSeparable _ K
  have : Algebra.IsAlgebraic (Algebra.adjoin k t) K :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp inferInstance
  obtain ⟨u, hut, hu⟩ := exists_isTranscendenceBasis_subset (R := k) t
  have htr : Algebra.trdeg k K = #u := hu.cardinalMk_eq_trdeg.symm
  refine ⟨?_, ⟨fun h => ?_, fun ⟨s, hs, hsep⟩ => ?_⟩, ?_⟩
  · rw [htr, hrank]
    exact Cardinal.mk_le_mk_of_subset hut
  · have hut' : u = t := by
      have hc : #u = #t := htr ▸ hrank ▸ h
      refine Set.eq_of_subset_of_ncard_le hut ?_ htfin
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card, Nat.card, hc]
    subst hut'
    exact ⟨u, hu, hsepL⟩
  · rw [rank_kaehlerDifferential_eq_of_isSeparable hs, hs.cardinalMk_eq_trdeg]
  · refine ⟨fun h => ?_, fun _ => ?_⟩
    · have : Algebra.FormallyUnramified k K := ⟨h⟩
      exact Algebra.FormallyUnramified.isSeparable k K
    · have := Algebra.FormallyUnramified.of_isSeparable k K
      infer_instance

end Hartshorne
