/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RegularLocalGlobalDimension

/-!
# Serre's criterion: finite projective dimension of the residue field forces regularity

Let `B` be a Noetherian local ring whose residue field `k` has finite projective dimension.
Then `B` is regular (Matsumura, *Commutative Ring Theory*, Theorem 19.2, second half; Stacks,
tag 00OD). Combined with the finiteness of global dimension of regular local rings and the
behaviour of projective dimension under localization, this shows that every localization of a
regular local ring at a prime is regular (Matsumura, Theorem 19.3; Stacks, tag 00OE).

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

end Hartshorne.SerreRegularity
