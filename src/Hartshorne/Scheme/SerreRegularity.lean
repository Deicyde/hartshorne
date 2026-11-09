/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RegularLocalGlobalDimension
import Hartshorne.Scheme.Differentials.RegularLocalLift

/-!
# Serre's criterion: finite projective dimension of the residue field forces regularity

Let `B` be a Noetherian local ring whose residue field `k` has finite projective dimension.
Then `B` is regular (Serre; compare Matsumura, *Commutative Ring Theory*, §19).
Combined with the finiteness of global dimension of regular local rings and the behaviour of
projective dimension under localization, this shows that every localization of a regular local
ring at a prime is regular (compare Matsumura, §19).

## Proof outline

By induction on a bound `n` for the projective dimension of `k`.

* If `k` is projective, it is free, so `𝔪 = 0` and `B` is a field.
* If `𝔪` is an associated prime of `B`, choose `s ≠ 0` with `𝔪 s = 0`. A finitely generated
  module of finite projective dimension is then projective: in a minimal presentation
  `0 → K → F → M → 0` the kernel `K ⊆ 𝔪 F` is killed by `s`, but by induction it is free.
* Otherwise prime avoidance gives a non-zero-divisor `x ∈ 𝔪 \ 𝔪²`. The module `𝔪` has projective
  dimension `< n`, hence so does `𝔪 / x𝔪` over `B' = B / (x)`; since `x ∉ 𝔪²`, the residue field
  of `B'` is a direct summand of `𝔪 / x𝔪`. By induction `B'` is regular, and then so is `B`.
-/

universe u

open CategoryTheory Abelian IsLocalRing Pointwise
open scoped TensorProduct

namespace Hartshorne.SerreRegularity

variable {B : Type u} [CommRing B]

/-- A Noetherian local ring with zero maximal ideal is regular. -/
lemma isRegularLocalRing_of_maximalIdeal_eq_bot [IsLocalRing B] [IsNoetherianRing B]
    (h : maximalIdeal B = ⊥) : IsRegularLocalRing B := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [h, Submodule.spanFinrank_bot, Nat.cast_zero]
  exact ringKrullDim_nonneg_of_nontrivial

/-- If the residue field of a local ring is a projective module, the maximal ideal is zero. -/
lemma maximalIdeal_eq_bot_of_projective [IsLocalRing B]
    (h : Module.Projective B (ResidueField B)) : maximalIdeal B = ⊥ := by
  have : Module.Free B (ResidueField B) := Module.free_of_flat_of_isLocalRing
  rw [eq_bot_iff]
  intro a ha
  have hann : a ∈ Module.annihilator B (ResidueField B) := by
    rw [Module.mem_annihilator]
    intro y
    obtain ⟨y, rfl⟩ := residue_surjective y
    rw [Algebra.smul_def, ResidueField.algebraMap_eq, ← map_mul, residue_eq_zero_iff]
    exact (maximalIdeal B).mul_mem_right y ha
  rwa [Module.annihilator_eq_bot.mpr inferInstance] at hann

/-- Over a local ring every finitely generated module has a minimal presentation: a surjection
from a finite free module whose kernel lies in `𝔪 F`. -/
theorem exists_surjective_ker_le_maximalIdeal_smul [IsLocalRing B] (M : Type u)
    [AddCommGroup M] [Module B M] [Module.Finite B M] :
    ∃ (r : ℕ) (π : (Fin r → B) →ₗ[B] M), Function.Surjective π ∧
      LinearMap.ker π ≤ maximalIdeal B • (⊤ : Submodule B (Fin r → B)) := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (Module.Finite.fg_top (R := B) (M := M))
  set r := s.card
  let v : Fin r → M := fun i => (s.equivFin.symm i : M)
  have hrange : Set.range v = s := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hy
      exact ⟨s.equivFin ⟨y, hy⟩, by simp [v]⟩
  let π := Fintype.linearCombination B v
  have hsurj : Function.Surjective π := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hrange, hspan]
  refine ⟨r, π, hsurj, fun a ha => ?_⟩
  have hcoef : ∀ j, a j ∈ maximalIdeal B := by
    intro j
    by_contra hj
    have hu : IsUnit (a j) := (IsLocalRing.notMem_maximalIdeal).mp hj
    have hsum : ∑ i, a i • v i = 0 := by
      rw [← Fintype.linearCombination_apply]
      exact ha
    have hvj : v j ∈ Submodule.span B (v '' {i | i ≠ j}) := by
      rw [Fintype.sum_eq_add_sum_compl j] at hsum
      have : a j • v j = -∑ i ∈ ({j}ᶜ : Finset (Fin r)), a i • v i := eq_neg_of_add_eq_zero_left hsum
      have hmem : a j • v j ∈ Submodule.span B (v '' {i | i ≠ j}) := by
        rw [this]
        refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
        exact Submodule.subset_span ⟨i, by simpa using hi, rfl⟩
      have := Submodule.smul_mem _ (hu.unit⁻¹ : Bˣ).1 hmem
      rwa [smul_smul, hu.val_inv_mul, one_smul] at this
    have htop : Submodule.span B (v '' {i | i ≠ j}) = ⊤ := by
      rw [eq_top_iff, ← hspan, ← hrange, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases hij : i = j
      · exact hij ▸ hvj
      · exact Submodule.subset_span ⟨i, hij, rfl⟩
    have hle := Submodule.spanFinrank_span_le_ncard_of_finite (R := B)
      ((Set.toFinite {i : Fin r | i ≠ j}).image v)
    rw [htop, ← hcard] at hle
    have h2 : (v '' {i | i ≠ j}).ncard ≤ r - 1 := by
      refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
      have : ({i : Fin r | i ≠ j}).ncard = r - 1 := by
        rw [Set.ncard_eq_toFinset_card']
        simp [Finset.filter_ne', Finset.card_erase_of_mem]
      omega
    have : 0 < r := Fin.pos j
    change s.card ≤ _ at hle
    omega
  rw [pi_eq_sum_univ a]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hcoef j) trivial

/-- If the maximal ideal of a Noetherian local ring `B` is an associated prime of `B`, every
finitely generated `B`-module of finite projective dimension is projective. -/
theorem projective_of_mem_associatedPrimes [IsLocalRing B] [IsNoetherianRing B]
    (hass : maximalIdeal B ∈ associatedPrimes B B) (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M],
      HasProjectiveDimensionLE (ModuleCat.of B M) n → Module.Projective B M := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hass
  obtain ⟨-, s, hs⟩ := hass
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h1 : (1 : B) ∈ maximalIdeal B := by
      rw [hs, Submodule.mem_colon_singleton]
      simp
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  induction n with
  | zero =>
    intro M _ _ _ h
    rw [IsProjective.iff_projective M, projective_iff_hasProjectiveDimensionLE_zero]
    exact h
  | succ n ih =>
    intro M _ _ _ h
    obtain ⟨r, π, hπ, hker⟩ := exists_surjective_ker_le_maximalIdeal_smul (B := B) M
    have hS := LinearMap.shortExact_shortComplexKer (f := π) hπ
    have hF : Projective (ModuleCat.of B (Fin r → B)) :=
      (IsProjective.iff_projective (Fin r → B)).mp inferInstance
    have hK : HasProjectiveDimensionLE (ModuleCat.of B (LinearMap.ker π)) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n hF).mp h
    have := ih (LinearMap.ker π) hK
    have : Module.Free B (LinearMap.ker π) := Module.free_of_flat_of_isLocalRing
    have hsK : ∀ k : LinearMap.ker π, s • k = 0 := by
      intro k
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_zero]
      have hk : (k : Fin r → B) ∈ maximalIdeal B • (⊤ : Submodule B (Fin r → B)) := hker k.2
      refine Submodule.smul_induction_on hk (fun a ha f _ => ?_) (fun f g hf hg => ?_)
      · rw [smul_smul]
        have : a * s = 0 := by
          rw [hs, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at ha
          exact ha
        rw [mul_comm, this, zero_smul]
      · rw [smul_add, hf, hg, add_zero]
    have hsub : Subsingleton (LinearMap.ker π) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      have hmem : s ∈ Module.annihilator B (LinearMap.ker π) := Module.mem_annihilator.mpr hsK
      rw [Module.annihilator_eq_bot.mpr inferInstance] at hmem
      exact hs0 hmem
    have hinj : Function.Injective π :=
      LinearMap.ker_eq_bot.mp (Submodule.eq_bot_of_subsingleton)
    exact Module.Projective.of_equiv (LinearEquiv.ofBijective π ⟨hinj, hπ⟩)

/-- If `x` is a non-zero-divisor in the maximal ideal of a Noetherian local ring `B` and
`B ⧸ (x)` is regular, then `B` is regular. -/
@[deprecated Hartshorne.isRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton
  (since := "2026-11-09")]
theorem isRegularLocalRing_of_quotient [IsLocalRing B] [IsNoetherianRing B] {x : B}
    (hx : x ∈ nonZeroDivisors B) [IsLocalRing (B ⧸ Ideal.span {x})]
    (h : IsRegularLocalRing (B ⧸ Ideal.span {x})) : IsRegularLocalRing B := by
  classical
  let π : B →+* B ⧸ Ideal.span {x} := Ideal.Quotient.mk _
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (B ⧸ Ideal.span {x})).comap π = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective π hπ)
  obtain ⟨T', hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal (B ⧸ Ideal.span {x})).fg_of_isNoetherianRing
  let T : Finset B := T'.image (Function.surjInv hπ)
  have hT : T.image π = T' := by
    simp only [T, Finset.image_image, Function.comp_def, Function.surjInv_eq hπ,
      Finset.image_id']
  have hm : maximalIdeal B = Ideal.span (insert x (T : Set B)) := by
    rw [← hcomap, ← hspan, ← hT, Finset.coe_image]
    change Ideal.comap π (Ideal.span (π '' ↑T)) = _
    rw [← Ideal.map_span,
      Ideal.comap_map_of_surjective _ hπ, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      Ideal.span_insert, sup_comm]
  have hle : (maximalIdeal B).spanFinrank ≤ (maximalIdeal (B ⧸ Ideal.span {x})).spanFinrank + 1 := by
    rw [hm]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (T.finite_toSet.insert x)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_coe_finset, ← hcard]
    exact Nat.add_le_add_right (Finset.card_image_le) 1
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx)
  rw [← (isRegularLocalRing_iff _).mp h]
  exact_mod_cast hle

/-- Membership in `(x) M` is divisibility by `x`. -/
lemma mem_span_singleton_smul_top_iff {M : Type*} [AddCommGroup M] [Module B M] (x : B) (m : M) :
    m ∈ Ideal.span {x} • (⊤ : Submodule B M) ↔ ∃ y : M, x • y = m := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- If `M` is projective over `B`, then `M ⧸ I M` is projective over `B ⧸ I`. -/
lemma projective_quotient_smul_top (I : Ideal B) (M : Type u) [AddCommGroup M] [Module B M]
    [Module.Projective B M] : Module.Projective (B ⧸ I) (M ⧸ I • (⊤ : Submodule B M)) := by
  have hsurj : Function.Surjective (algebraMap B (B ⧸ I)) := Ideal.Quotient.mk_surjective
  let e := TensorProduct.quotTensorEquivQuotSMul M I
  let f : (B ⧸ I) ⊗[B] M →ₗ[B ⧸ I] M ⧸ I • (⊤ : Submodule B M) :=
    e.toLinearMap.extendScalarsOfSurjective hsurj
  let g : M ⧸ I • (⊤ : Submodule B M) →ₗ[B ⧸ I] (B ⧸ I) ⊗[B] M :=
    e.symm.toLinearMap.extendScalarsOfSurjective hsurj
  have : Module.Projective (B ⧸ I) ((B ⧸ I) ⊗[B] M) :=
    Module.Projective.tensorProduct (R := B ⧸ I) (R₀ := B)
  exact Module.Projective.of_split g f (LinearMap.ext fun y => e.apply_symm_apply y)

/-- Change of rings for projective dimension: if `x` is a non-zero-divisor on the Noetherian
ring `B` and on the finitely generated module `M`, then the projective dimension of `M ⧸ x M`
over `B ⧸ (x)` is at most that of `M` over `B`. -/
theorem hasProjectiveDimensionLE_quotient [IsNoetherianRing B] {x : B} (hB : IsSMulRegular B x)
    (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M], IsSMulRegular M x →
      HasProjectiveDimensionLE (ModuleCat.of B M) n →
      HasProjectiveDimensionLE (ModuleCat.of (B ⧸ Ideal.span {x})
        (M ⧸ Ideal.span {x} • (⊤ : Submodule B M))) n := by
  have hsurj : Function.Surjective (algebraMap B (B ⧸ Ideal.span {x})) :=
    Ideal.Quotient.mk_surjective
  induction n with
  | zero =>
    intro M _ _ _ _ h
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h ⊢
    exact projective_quotient_smul_top _ M
  | succ n ih =>
    intro M _ _ _ hM h
    set I := Ideal.span {x}
    obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' B M
    have hS := LinearMap.shortExact_shortComplexKer (f := π) hπ
    have hF : Projective (ModuleCat.of B (Fin r → B)) :=
      (IsProjective.iff_projective (Fin r → B)).mp inferInstance
    have hK : HasProjectiveDimensionLE (ModuleCat.of B (LinearMap.ker π)) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n hF).mp h
    have hFreg : IsSMulRegular (Fin r → B) x :=
      IsSMulRegular.of_right_eq_zero_of_smul fun (f : Fin r → B) (hf : x • f = 0) => funext fun m =>
        hB.right_eq_zero_of_smul (by simpa using congrArg (· m) hf)
    have hKreg : IsSMulRegular (LinearMap.ker π) x :=
      IsSMulRegular.of_right_eq_zero_of_smul fun (k : LinearMap.ker π) (hk : x • k = 0) =>
        Subtype.ext (hFreg.right_eq_zero_of_smul (congrArg Subtype.val hk))
    have ihK := ih (LinearMap.ker π) hKreg hK
    set K : Submodule B (Fin r → B) := LinearMap.ker π with hKdef
    let f₀ : (K ⧸ I • (⊤ : Submodule B K)) →ₗ[B]
        ((Fin r → B) ⧸ I • (⊤ : Submodule B (Fin r → B))) :=
      Submodule.mapQ _ _ K.subtype (Submodule.smul_top_le_comap_smul_top I K.subtype)
    let g₀ : ((Fin r → B) ⧸ I • (⊤ : Submodule B (Fin r → B))) →ₗ[B]
        (M ⧸ I • (⊤ : Submodule B M)) :=
      Submodule.mapQ _ _ π (Submodule.smul_top_le_comap_smul_top I π)
    let f' := f₀.extendScalarsOfSurjective hsurj
    let g' := g₀.extendScalarsOfSurjective hsurj
    have hinj : Function.Injective f' := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro k hk
      obtain ⟨k, rfl⟩ := Submodule.mkQ_surjective _ k
      rw [LinearMap.mem_ker] at hk
      change Submodule.Quotient.mk (k : Fin r → B) = 0 at hk
      rw [Submodule.Quotient.mk_eq_zero, mem_span_singleton_smul_top_iff] at hk
      obtain ⟨f, hf⟩ := hk
      have hfK : f ∈ LinearMap.ker π := by
        rw [LinearMap.mem_ker]
        apply hM.right_eq_zero_of_smul
        rw [← map_smul, hf]
        exact k.2
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        mem_span_singleton_smul_top_iff]
      exact ⟨⟨f, hfK⟩, Subtype.ext hf⟩
    have hsurjg : Function.Surjective g' := by
      intro m
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ m
      obtain ⟨f, rfl⟩ := hπ m
      exact ⟨Submodule.Quotient.mk f, rfl⟩
    have hexact : Function.Exact f' g' := by
      intro f
      obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ f
      constructor
      · intro hf
        change Submodule.Quotient.mk (π f) = 0 at hf
        rw [Submodule.Quotient.mk_eq_zero, mem_span_singleton_smul_top_iff] at hf
        obtain ⟨m, hm⟩ := hf
        obtain ⟨f₁, rfl⟩ := hπ m
        have hmem : f - x • f₁ ∈ LinearMap.ker π := by
          rw [LinearMap.mem_ker, map_sub, map_smul, hm, sub_self]
        refine ⟨Submodule.Quotient.mk ⟨f - x • f₁, hmem⟩, ?_⟩
        change Submodule.Quotient.mk (f - x • f₁) = Submodule.Quotient.mk f
        rw [Submodule.Quotient.eq, sub_sub_cancel_left, Submodule.neg_mem_iff,
          mem_span_singleton_smul_top_iff]
        exact ⟨f₁, rfl⟩
      · rintro ⟨k, hk⟩
        rw [← hk]
        obtain ⟨k, rfl⟩ := Submodule.mkQ_surjective _ k
        change Submodule.Quotient.mk (π k) = 0
        rw [LinearMap.mem_ker.mp k.2, Submodule.Quotient.mk_zero]
    let S' : ShortComplex (ModuleCat.{u} (B ⧸ I)) :=
      ModuleCat.shortComplexOfCompEqZero f' g'
        (LinearMap.ext fun y => hexact.apply_apply_eq_zero y)
    have hS' : S'.ShortExact := ModuleCat.shortComplex_shortExact S' hexact hinj hsurjg
    have hF' : HasProjectiveDimensionLE (ModuleCat.of (B ⧸ I)
        ((Fin r → B) ⧸ I • (⊤ : Submodule B (Fin r → B)))) (n + 1) := by
      have : Projective (ModuleCat.of (B ⧸ I) ((Fin r → B) ⧸ I • (⊤ : Submodule B (Fin r → B)))) :=
        (IsProjective.iff_projective _).mp (projective_quotient_smul_top I (Fin r → B))
      exact hasProjectiveDimensionLT_of_ge _ 1 _ (by omega)
    exact hS'.hasProjectiveDimensionLT_X₃ (n + 1) ihK hF'

/-- Let `x ∈ 𝔪 \ 𝔪²` in a local ring `B`. Then the residue field of `B ⧸ (x)` is a direct
summand of `𝔪 ⧸ x 𝔪` as a `B ⧸ (x)`-module. -/
theorem nonempty_retract_residueField_quotient [IsLocalRing B] {x : B}
    (hxm : x ∈ maximalIdeal B) (hx2 : x ∉ maximalIdeal B ^ 2) [IsLocalRing (B ⧸ Ideal.span {x})] :
    Nonempty (Retract (ModuleCat.of (B ⧸ Ideal.span {x}) (ResidueField (B ⧸ Ideal.span {x})))
      (ModuleCat.of (B ⧸ Ideal.span {x})
        (maximalIdeal B ⧸ Ideal.span {x} • (⊤ : Submodule B (maximalIdeal B))))) := by
  set I := Ideal.span {x}
  have hsurj : Function.Surjective (algebraMap B (B ⧸ I)) := Ideal.Quotient.mk_surjective
  have hcomap : (maximalIdeal (B ⧸ I)).comap (algebraMap B (B ⧸ I)) = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hsurj)
  have hIm : I ≤ maximalIdeal B := (Ideal.span_singleton_le_iff_mem _).mpr hxm
  let ξ : maximalIdeal B ⧸ I • (⊤ : Submodule B (maximalIdeal B)) :=
    Submodule.Quotient.mk ⟨x, hxm⟩
  have hξ : ∀ a ∈ maximalIdeal B, a • ξ = 0 := by
    intro a ha
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      mem_span_singleton_smul_top_iff]
    exact ⟨⟨a, ha⟩, Subtype.ext (by simp [mul_comm])⟩
  let i₀ : (B ⧸ I) →ₗ[B ⧸ I] maximalIdeal B ⧸ I • (⊤ : Submodule B (maximalIdeal B)) :=
    LinearMap.toSpanSingleton (B ⧸ I) _ ξ
  have hi₀ : maximalIdeal (B ⧸ I) ≤ LinearMap.ker i₀ := by
    intro b hb
    obtain ⟨a, rfl⟩ := hsurj b
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, algebraMap_smul]
    exact hξ a (by rw [← hcomap]; exact hb)
  let i : ResidueField (B ⧸ I) →ₗ[B ⧸ I]
      maximalIdeal B ⧸ I • (⊤ : Submodule B (maximalIdeal B)) :=
    (maximalIdeal (B ⧸ I)).liftQ i₀ hi₀
  let v : CotangentSpace B := (maximalIdeal B).toCotangent ⟨x, hxm⟩
  have hv : v ≠ 0 := by
    rwa [Ne, Ideal.toCotangent_eq_zero]
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (ResidueField B) hv
  let φ' : Module.Dual (ResidueField B) (CotangentSpace B) := (φ v)⁻¹ • φ
  have hφ' : φ' v = 1 := by
    simp only [φ', LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hφ
  let ψ : ResidueField B →ₗ[B] ResidueField (B ⧸ I) :=
    (maximalIdeal B).liftQ (Algebra.linearMap B (ResidueField (B ⧸ I))) (by
      intro a ha
      rw [LinearMap.mem_ker, Algebra.linearMap_apply,
        IsScalarTower.algebraMap_apply B (B ⧸ I) (ResidueField (B ⧸ I)),
        ResidueField.algebraMap_eq, residue_eq_zero_iff]
      rw [← hcomap] at ha
      exact ha)
  let p₀ : maximalIdeal B →ₗ[B] ResidueField (B ⧸ I) :=
    ψ ∘ₗ (φ'.restrictScalars B) ∘ₗ (maximalIdeal B).toCotangent
  have hp₀ : I • (⊤ : Submodule B (maximalIdeal B)) ≤ LinearMap.ker p₀ := by
    rw [Submodule.smul_le]
    intro r hr y _
    rw [LinearMap.mem_ker]
    have : (maximalIdeal B).toCotangent (r • y) = 0 := by
      rw [Ideal.toCotangent_eq_zero, Submodule.coe_smul, smul_eq_mul, pow_two]
      exact Ideal.mul_mem_mul (hIm hr) y.2
    simp only [p₀, LinearMap.comp_apply, this, map_zero]
  let p : (maximalIdeal B ⧸ I • (⊤ : Submodule B (maximalIdeal B))) →ₗ[B ⧸ I]
      ResidueField (B ⧸ I) :=
    ((I • (⊤ : Submodule B (maximalIdeal B))).liftQ p₀ hp₀).extendScalarsOfSurjective hsurj
  have hpξ : p ξ = 1 := by
    change ψ (φ' v) = 1
    have hψ : ∀ b : B, ψ (residue B b) = algebraMap B (ResidueField (B ⧸ I)) b := fun b => rfl
    rw [hφ', ← map_one (residue B), hψ, map_one]
  refine ⟨{ i := ModuleCat.ofHom i, r := ModuleCat.ofHom p, retract := ?_ }⟩
  ext y
  obtain ⟨b, rfl⟩ := residue_surjective y
  change p (i₀ b) = residue (B ⧸ I) b
  rw [LinearMap.toSpanSingleton_apply, map_smul, hpξ, Algebra.smul_def, mul_one,
    ResidueField.algebraMap_eq]

/-- **Serre's criterion**: a Noetherian local ring whose residue field has finite projective
dimension is regular (compare Matsumura, *Commutative Ring Theory*, §19). -/
theorem isRegularLocalRing_of_hasProjectiveDimensionLE (n : ℕ) :
    ∀ (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B],
      HasProjectiveDimensionLE (ModuleCat.of B (ResidueField B)) n → IsRegularLocalRing B := by
  induction n with
  | zero =>
    intro B _ _ _ h
    rw [← projective_iff_hasProjectiveDimensionLE_zero, ← IsProjective.iff_projective] at h
    exact isRegularLocalRing_of_maximalIdeal_eq_bot (maximalIdeal_eq_bot_of_projective h)
  | succ n ih =>
    intro B _ _ _ h
    by_cases hass : maximalIdeal B ∈ associatedPrimes B B
    · exact isRegularLocalRing_of_maximalIdeal_eq_bot (maximalIdeal_eq_bot_of_projective
        (projective_of_mem_associatedPrimes hass (n + 1) _ h))
    by_cases hbot : maximalIdeal B = ⊥
    · exact isRegularLocalRing_of_maximalIdeal_eq_bot hbot
    -- Prime avoidance: a non-zero-divisor in `𝔪 \ 𝔪²`.
    have hm2 : ¬ maximalIdeal B ≤ maximalIdeal B ^ 2 := by
      intro hle
      refine hbot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B)
        (maximalIdeal B) (maximalIdeal B).fg_of_isNoetherianRing ?_ (maximalIdeal_le_jacobson ⊥))
      rwa [smul_eq_mul, ← pow_two]
    have hass' : ∀ P ∈ associatedPrimes B B, ¬ maximalIdeal B ≤ P := by
      intro P hP hle
      have hPm : P = maximalIdeal B :=
        ((maximalIdeal.isMaximal B).eq_of_le hP.isPrime.ne_top hle).symm
      exact hass (hPm ▸ hP)
    set S : Set (Ideal B) := insert (maximalIdeal B ^ 2) (associatedPrimes B B)
    have hS : S.Finite := (associatedPrimes.finite B B).insert _
    have hnot : ¬ ((maximalIdeal B : Set B) ⊆ ⋃ i ∈ S, ((id i : Ideal B) : Set B)) := by
      rw [Ideal.subset_union_prime_finite hS (maximalIdeal B ^ 2) (maximalIdeal B ^ 2)]
      · rintro ⟨i, hi, hle⟩
        rcases hi with rfl | hi
        · exact hm2 hle
        · exact hass' i hi hle
      · rintro i (rfl | hi) h _
        · exact absurd rfl h
        · exact hi.isPrime
    simp only [Set.not_subset, Set.mem_iUnion, not_exists, SetLike.mem_coe, id] at hnot
    obtain ⟨x, hxm, hx⟩ := hnot
    have hx2 : x ∉ maximalIdeal B ^ 2 := fun h => hx _ (Set.mem_insert _ _) h
    have hxreg : IsSMulRegular B x := by
      by_contra hreg
      have : x ∈ ⋃ p ∈ associatedPrimes B B, (p : Set B) := by
        rw [biUnion_associatedPrimes_eq_compl_regular B B]
        exact hreg
      simp only [Set.mem_iUnion, SetLike.mem_coe] at this
      obtain ⟨P, hP, hxP⟩ := this
      exact hx P (Set.mem_insert_of_mem _ hP) hxP
    set I := Ideal.span {x}
    have hI : I ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact (IsLocalRing.mem_maximalIdeal x).mp hxm
    have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    have : IsLocalRing (B ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    -- The maximal ideal has projective dimension at most `n`.
    have hS := LinearMap.shortExact_shortComplexKer (f := (maximalIdeal B).mkQ)
      (Submodule.mkQ_surjective _)
    have hB : Projective (ModuleCat.of B B) := (IsProjective.iff_projective B).mp inferInstance
    have h' : HasProjectiveDimensionLE (ModuleCat.of B (B ⧸ maximalIdeal B)) (n + 1) := h
    have hker : HasProjectiveDimensionLE
        (ModuleCat.of B (LinearMap.ker (maximalIdeal B).mkQ)) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n hB).mp h'
    have hm : HasProjectiveDimensionLE (ModuleCat.of B (maximalIdeal B)) n :=
      hasProjectiveDimensionLT_of_iso
        (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ (maximalIdeal B))).toModuleIso _
    have hmreg : IsSMulRegular (maximalIdeal B) x :=
      IsSMulRegular.of_right_eq_zero_of_smul fun (y : maximalIdeal B) (hy : x • y = 0) =>
        Subtype.ext (hxreg.right_eq_zero_of_smul (congrArg Subtype.val hy))
    have hq := hasProjectiveDimensionLE_quotient hxreg n (maximalIdeal B) hmreg hm
    obtain ⟨ret⟩ := nonempty_retract_residueField_quotient hxm hx2
    have hk' := ret.hasProjectiveDimensionLT (n + 1)
    have hreg' := ih (B ⧸ I) hk'
    have : IsRegularLocalRing (B ⧸ Ideal.span {x}) := hreg'
    refine Hartshorne.isRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton
      (f := x) ?_ hxm
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    exact hxreg.right_eq_zero_of_smul (by rwa [smul_eq_mul, mul_comm])

end Hartshorne.SerreRegularity

namespace Hartshorne.RegularLocal

/-- **Hartshorne II, Theorem 8.14A** (p. 177, cited there from Matsumura [2], p. 139).
Localizations of regular local rings are regular: if `A` is a regular local ring and `𝔭` is a
prime ideal of `A`, then `A_𝔭` is a regular local ring. -/
theorem isRegularLocalRing_localization_atPrime (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (p : Ideal A) [p.IsPrime] : IsRegularLocalRing (Localization.AtPrime p) :=
  Hartshorne.SerreRegularity.isRegularLocalRing_of_hasProjectiveDimensionLE _ _
    (hasProjectiveDimensionLE_residueField_localization A p)

/-- A regular local ring is a regular ring: all its localizations at primes are regular. -/
theorem isRegularRing_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsRegularRing A :=
  (isRegularRing_iff).mpr fun p _ => isRegularLocalRing_localization_atPrime A p

end Hartshorne.RegularLocal
