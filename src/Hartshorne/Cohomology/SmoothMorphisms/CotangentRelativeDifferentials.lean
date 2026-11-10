/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SmoothMorphisms.ZariskiTangentMap
import Hartshorne.Scheme.Differentials.LocalCotangentViaDifferentials

/-!
# Cotangent spaces and the fibre of relative differentials

Hartshorne, *Algebraic Geometry*, III, proof of Proposition 10.4 (p. 270), at the level of local
rings.

Let `k` be a field and `A → B` a local homomorphism of local `k`-algebras such that `k` maps
isomorphically onto the residue field `κ_B` of `B`. Then the sequence of `κ_B`-vector spaces

`κ_B ⊗_{κ_A} 𝔪_A/𝔪_A² → 𝔪_B/𝔪_B² → κ_B ⊗_B Ω_{B/A} → 0`

is exact, where the second map sends the class of `b` to `1 ⊗ db`. This is the fibre at the
closed point of the exact sequence `f^* Ω_Y → Ω_X → Ω_{X/Y} → 0` after the identifications
`Ω_X ⊗ k(x) ≅ 𝔪_x/𝔪_x²` of Hartshorne II.8.7.

## Main results

* `Hartshorne.CotangentKaehler.cotangentToFiber`: the map `𝔪_B/𝔪_B² → κ_B ⊗_B Ω_{B/R}`.
* `Hartshorne.CotangentKaehler.ker_cotangentToFiber`: exactness in the middle.
* `Hartshorne.CotangentKaehler.cotangentToFiber_surjective`: exactness on the right.
* `Hartshorne.CotangentKaehler.finrank_fiber_add_finrank_range`: the resulting dimension count.
* `Hartshorne.CotangentKaehler.injective_localCotangentBaseChange_iff`: the scalar-extended
  cotangent map is injective if and only if
  `dim κ_B ⊗ Ω_{B/A} + dim 𝔪_A/𝔪_A² = dim 𝔪_B/𝔪_B²`.
-/

namespace Hartshorne

noncomputable section

open IsLocalRing Module KaehlerDifferential
open scoped TensorProduct

universe u v w

namespace CotangentKaehler

theorem ker_algebraMap_residueField (B : Type v) [CommRing B] [IsLocalRing B] :
    RingHom.ker (algebraMap B (ResidueField B)) = maximalIdeal B := by
  rw [ResidueField.algebraMap_eq, ker_residue]

theorem algebraMap_residueField_surjective (B : Type v) [CommRing B] [IsLocalRing B] :
    Function.Surjective (algebraMap B (ResidueField B)) := by
  rw [ResidueField.algebraMap_eq]
  exact residue_surjective

section Fiber

variable (R : Type u) (B : Type v) [CommRing R] [CommRing B] [IsLocalRing B] [Algebra R B]

/-- The map `𝔪_B/𝔪_B² → κ_B ⊗_B Ω_{B/R}` sending the class of `b` to `1 ⊗ db`. -/
def cotangentToFiber : CotangentSpace B →ₗ[ResidueField B] ResidueField B ⊗[B] Ω[B⁄R] :=
  LinearMap.extendScalarsOfSurjective (algebraMap_residueField_surjective B)
    (kerCotangentToTensor R B (ResidueField B) ∘ₗ
      (Ideal.Cotangent.equivOfEq _ _ (ker_algebraMap_residueField B).symm).toLinearMap)

@[simp]
theorem cotangentToFiber_toCotangent (b : maximalIdeal B) :
    cotangentToFiber R B ((maximalIdeal B).toCotangent b) = 1 ⊗ₜ D R B (b : B) :=
  rfl

/-- `cotangentToFiber` is injective when a coefficient field `R` maps isomorphically onto the
residue field (Hartshorne II.8.7). -/
theorem cotangentToFiber_injective {k : Type u} [Field k] [Algebra k B]
    (hk : Function.Bijective (algebraMap k (ResidueField B))) :
    Function.Injective (cotangentToFiber k B) := by
  intro x y h
  apply (localCotangentToDifferentials_bijective k B hk).injective
  change TensorProduct.comm _ _ _ (cotangentToFiber k B x) =
    TensorProduct.comm _ _ _ (cotangentToFiber k B y)
  rw [h]

end Fiber

section Exact

variable (k : Type u) (A : Type v) (B : Type w) [Field k] [CommRing A] [IsLocalRing A]
  [CommRing B] [IsLocalRing B] [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  [IsLocalHom (algebraMap A B)]

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
theorem algebraMap_residueField_surjective_of_field
    (hk : Function.Surjective (algebraMap k (ResidueField B))) :
    Function.Surjective (algebraMap A (ResidueField B)) := by
  intro z
  obtain ⟨s, rfl⟩ := hk z
  refine ⟨algebraMap k A s, ?_⟩
  change residue B (algebraMap A B (algebraMap k A s)) = residue B (algebraMap k B s)
  rw [← IsScalarTower.algebraMap_apply]

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- Exactness on the right: `𝔪_B/𝔪_B² → κ_B ⊗_B Ω_{B/A}` is surjective when `k → κ_B` is. -/
theorem cotangentToFiber_surjective
    (hk : Function.Surjective (algebraMap k (ResidueField B))) :
    Function.Surjective (cotangentToFiber A B) := by
  have := KaehlerDifferential.subsingleton_of_surjective A (ResidueField B)
    (algebraMap_residueField_surjective_of_field k A B hk)
  have hrange := KaehlerDifferential.range_kerCotangentToTensor A B (ResidueField B)
    (algebraMap_residueField_surjective B)
  intro z
  have hz : z ∈ LinearMap.range (kerCotangentToTensor A B (ResidueField B)) := by
    rw [hrange, Submodule.restrictScalars_mem, LinearMap.mem_ker]
    exact Subsingleton.elim _ _
  obtain ⟨w, rfl⟩ := hz
  let e := Ideal.Cotangent.equivOfEq _ _ (ker_algebraMap_residueField B).symm
  refine ⟨e.symm w, ?_⟩
  change kerCotangentToTensor A B (ResidueField B) (e (e.symm w)) = _
  rw [LinearEquiv.apply_symm_apply]

omit [Field k] [Algebra k A] [Algebra k B] [IsScalarTower k A B] in
/-- The composite `𝔪_A/𝔪_A² → 𝔪_B/𝔪_B² → κ_B ⊗_B Ω_{B/A}` vanishes. -/
theorem cotangentToFiber_localCotangentMap (ω : CotangentSpace A) :
    cotangentToFiber A B (localCotangentMap A B ω) = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ ω
  rw [localCotangentMap_toCotangent, cotangentToFiber_toCotangent]
  simp

/-- Exactness in the middle, the hard inclusion: an element of `𝔪_B/𝔪_B²` with `1 ⊗ db = 0` in
`κ_B ⊗_B Ω_{B/A}` comes from `κ_B ⊗_{κ_A} 𝔪_A/𝔪_A²`. -/
theorem mem_range_of_cotangentToFiber_eq_zero
    (hk : Function.Bijective (algebraMap k (ResidueField B))) (ξ : CotangentSpace B)
    (hξ : cotangentToFiber A B ξ = 0) :
    ξ ∈ LinearMap.range (localCotangentBaseChange A B) := by
  set W := LinearMap.range (localCotangentBaseChange A B)
  have hcomp : ∀ ξ, cotangentToFiber A B ξ =
      (KaehlerDifferential.map k A B B).lTensor (ResidueField B) (cotangentToFiber k B ξ) := by
    intro ξ
    obtain ⟨b, rfl⟩ := Ideal.toCotangent_surjective _ ξ
    simp [cotangentToFiber_toCotangent]
  have hex := lTensor_exact (ResidueField B) (KaehlerDifferential.exact_mapBaseChange_map k A B)
    (KaehlerDifferential.map_surjective k A B)
  rw [hcomp] at hξ
  obtain ⟨t, ht⟩ := (hex _).mp hξ
  have gen : ∀ (c : ResidueField B) (a : A), ∃ η ∈ W,
      cotangentToFiber k B η = c ⊗ₜ D k B (algebraMap A B a) := by
    intro c a
    obtain ⟨s, hs⟩ := hk.2 (residue B (algebraMap A B a))
    have ha' : a - algebraMap k A s ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map (algebraMap A B)
      rw [map_sub, ← IsScalarTower.algebraMap_apply] at hu'
      have h0 : residue B (algebraMap A B a - algebraMap k B s) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact hs.symm
      exact (mem_maximalIdeal _).mp ((residue_eq_zero_iff _).mp h0) hu'
    refine ⟨c • localCotangentMap A B ((maximalIdeal A).toCotangent ⟨_, ha'⟩), ?_, ?_⟩
    · exact W.smul_mem c ⟨1 ⊗ₜ _, by rw [localCotangentBaseChange_tmul, one_smul]⟩
    · rw [map_smul, localCotangentMap_toCotangent, cotangentToFiber_toCotangent]
      simp only [map_sub, ← IsScalarTower.algebraMap_apply, Derivation.map_algebraMap, sub_zero]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hΩ : ∀ (ω : Ω[A⁄k]) (c : ResidueField B), ∃ η ∈ W,
      cotangentToFiber k B η = c ⊗ₜ KaehlerDifferential.map k k A B ω := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range (D k A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro c
      rw [KaehlerDifferential.map_D]
      exact gen c a
    | zero => exact fun c ↦ ⟨0, W.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      intro c
      obtain ⟨η₁, h₁, e₁⟩ := hx c
      obtain ⟨η₂, h₂, e₂⟩ := hy c
      exact ⟨η₁ + η₂, W.add_mem h₁ h₂, by rw [map_add, map_add, TensorProduct.tmul_add, e₁, e₂]⟩
    | smul a x _ hx =>
      intro c
      obtain ⟨η, hη, e⟩ := hx (algebraMap A B a • c)
      refine ⟨η, hη, ?_⟩
      rw [e, map_smul, ← algebraMap_smul B a, TensorProduct.smul_tmul]
  have key : ∀ t, ∃ η ∈ W, cotangentToFiber k B η =
      (KaehlerDifferential.mapBaseChange k A B).lTensor (ResidueField B) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, W.zero_mem, by simp⟩
    | add x y hx hy =>
      obtain ⟨η₁, h₁, e₁⟩ := hx
      obtain ⟨η₂, h₂, e₂⟩ := hy
      exact ⟨η₁ + η₂, W.add_mem h₁ h₂, by rw [map_add, map_add, e₁, e₂]⟩
    | tmul c u =>
      induction u using TensorProduct.induction_on with
      | zero => exact ⟨0, W.zero_mem, by simp⟩
      | add x y hx hy =>
        obtain ⟨η₁, h₁, e₁⟩ := hx
        obtain ⟨η₂, h₂, e₂⟩ := hy
        exact ⟨η₁ + η₂, W.add_mem h₁ h₂, by
          rw [map_add, TensorProduct.tmul_add, map_add, e₁, e₂]⟩
      | tmul β ω =>
        rw [LinearMap.lTensor_tmul, KaehlerDifferential.mapBaseChange_tmul,
          ← TensorProduct.smul_tmul]
        exact hΩ ω (β • c)
  obtain ⟨η, hη, hηt⟩ := key t
  rwa [cotangentToFiber_injective B hk (hηt.trans ht)] at hη

/-- **Exactness in the middle** of `κ_B ⊗_{κ_A} 𝔪_A/𝔪_A² → 𝔪_B/𝔪_B² → κ_B ⊗_B Ω_{B/A}`, for local
`k`-algebras with `k ≅ κ_B`. -/
theorem ker_cotangentToFiber (hk : Function.Bijective (algebraMap k (ResidueField B))) :
    LinearMap.ker (cotangentToFiber A B) = LinearMap.range (localCotangentBaseChange A B) := by
  ext ξ
  refine ⟨mem_range_of_cotangentToFiber_eq_zero k A B hk ξ, ?_⟩
  rintro ⟨t, rfl⟩
  rw [LinearMap.mem_ker]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul c ω =>
    rw [localCotangentBaseChange_tmul, map_smul, cotangentToFiber_localCotangentMap, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- **Dimension count.** For a local homomorphism `A → B` of local `k`-algebras with `k ≅ κ_B` and
`B` Noetherian, `dim κ_B ⊗_B Ω_{B/A} + rank (κ_B ⊗ 𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²) = dim 𝔪_B/𝔪_B²`. -/
theorem finrank_fiber_add_finrank_range [IsNoetherianRing B]
    (hk : Function.Bijective (algebraMap k (ResidueField B))) :
    finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄A]) +
        finrank (ResidueField B) (LinearMap.range (localCotangentBaseChange A B)) =
      finrank (ResidueField B) (CotangentSpace B) := by
  rw [← ker_cotangentToFiber k A B hk,
    ← LinearMap.finrank_range_add_finrank_ker (cotangentToFiber A B),
    LinearMap.range_eq_top.mpr (cotangentToFiber_surjective k A B hk.2), finrank_top]

/-- **Hartshorne III, proof of Proposition 10.4** (local form). For a local homomorphism `A → B`
of Noetherian local `k`-algebras with `k ≅ κ_B`, the scalar-extended cotangent map
`κ_B ⊗_{κ_A} 𝔪_A/𝔪_A² → 𝔪_B/𝔪_B²` is injective if and only if
`dim κ_B ⊗_B Ω_{B/A} + dim 𝔪_A/𝔪_A² = dim 𝔪_B/𝔪_B²`. -/
theorem injective_localCotangentBaseChange_iff [IsNoetherianRing A] [IsNoetherianRing B]
    (hk : Function.Bijective (algebraMap k (ResidueField B))) :
    Function.Injective (localCotangentBaseChange A B) ↔
      finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄A]) +
          finrank (ResidueField A) (CotangentSpace A) =
        finrank (ResidueField B) (CotangentSpace B) := by
  have hbc : finrank (ResidueField B) (ResidueField B ⊗[ResidueField A] CotangentSpace A) =
      finrank (ResidueField A) (CotangentSpace A) := Module.finrank_baseChange
  rw [← finrank_fiber_add_finrank_range k A B hk, Nat.add_left_cancel_iff, ← hbc]
  constructor
  · exact fun h ↦ (LinearMap.finrank_range_of_inj h).symm
  · intro h
    rw [← LinearMap.ker_eq_bot]
    have := LinearMap.finrank_range_add_finrank_ker (localCotangentBaseChange A B)
    exact Submodule.finrank_eq_zero.mp (by omega)

end Exact

end CotangentKaehler

end

end Hartshorne
