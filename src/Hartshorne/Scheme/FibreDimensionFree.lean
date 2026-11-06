/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Equal special and generic fibre dimension forces freeness over a local domain

Let `R` be a local domain with residue field `k` and fraction field `K`, and let `M` be a finitely
generated `R`-module. If `dim_k (k ⊗ M) = dim_K (K ⊗ M)`, then `M` is free of that rank.

This is the local algebraic core of Hartshorne II, Exercise 5.8(c) for integral schemes: a
coherent sheaf on an integral scheme whose fibre dimension is constant is locally free. Proof:
lifting a `k`-basis of `k ⊗ M` gives, by Nakayama's lemma, a surjection `φ : R ^ n → M` with
`n = dim_k (k ⊗ M)`. After base change to `K` it becomes a surjection between `K`-vector spaces of
the same finite dimension, hence injective; since `R ^ n → K ^ n` is injective, `φ` is injective.
-/

open TensorProduct IsLocalRing Module

namespace Hartshorne

universe u

/-- Over a local domain `R`, a finitely generated module `M` whose special fibre `k ⊗ M` and
generic fibre `K ⊗ M` have the same dimension is free, with a basis indexed by `Fin n` where
`n = dim_k (k ⊗ M)`. -/
theorem free_of_finrank_residueField_eq_finrank_fractionRing
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : finrank (ResidueField R) (ResidueField R ⊗[R] M) =
      finrank (FractionRing R) (FractionRing R ⊗[R] M)) :
    Nonempty (Basis (Fin (finrank (ResidueField R) (ResidueField R ⊗[R] M))) R M) := by
  set k := ResidueField R
  set K := FractionRing R
  set n := finrank k (k ⊗[R] M)
  let b : Basis (Fin n) k (k ⊗[R] M) := Module.finBasis k (k ⊗[R] M)
  have hsurj : ∀ y : k ⊗[R] M, ∃ m : M, (1 : k) ⊗ₜ[R] m = y := by
    intro y
    have htop := (map_tensorProduct_mk_eq_top (R := R) (M := M) (N := ⊤)).2 rfl
    have : y ∈ (⊤ : Submodule R M).map (TensorProduct.mk R k M 1) := htop ▸ Submodule.mem_top
    obtain ⟨m, -, hm⟩ := this
    exact ⟨m, hm⟩
  choose f hf using fun i => hsurj (b i)
  have hspan : Submodule.span R (Set.range f) = ⊤ :=
    span_eq_top_of_tmul_eq_basis f b hf
  let φ : (Fin n →₀ R) →ₗ[R] M := Finsupp.linearCombination R f
  have hφs : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hspan]
  have hψs : Function.Surjective (φ.baseChange K) := LinearMap.lTensor_surjective K hφs
  have hfin : finrank K (K ⊗[R] (Fin n →₀ R)) = finrank K (K ⊗[R] M) := by
    rw [Module.finrank_baseChange, Module.finrank_finsupp_self, Fintype.card_fin]
    exact h
  have hψi : Function.Injective (φ.baseChange K) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hψs
  have hι : Function.Injective ((Algebra.linearMap R K).rTensor (Fin n →₀ R)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective R K)
  have hφi : Function.Injective φ := by
    intro x y hxy
    have h1 : (1 : K) ⊗ₜ[R] x = (1 : K) ⊗ₜ[R] y := by
      apply hψi
      simp [LinearMap.baseChange_tmul, hxy]
    have h2 : (Algebra.linearMap R K).rTensor (Fin n →₀ R) ((1 : R) ⊗ₜ x) =
        (Algebra.linearMap R K).rTensor (Fin n →₀ R) ((1 : R) ⊗ₜ y) := by
      simpa using h1
    have h3 := hι h2
    simpa using congrArg (TensorProduct.lid R (Fin n →₀ R)) h3
  exact ⟨Basis.ofRepr (LinearEquiv.ofBijective φ ⟨hφi, hφs⟩).symm⟩

end Hartshorne
