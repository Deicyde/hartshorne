/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Constant fibre dimension forces freeness over a reduced local ring

Let `R` be a local ring with residue field `k` and `M` a finitely generated `R`-module with
`n = dim_k (k ⊗ M)`. If `(K i)` is a family of fields over `R` that jointly detect zero in `R`
and `dim_{K i} (K i ⊗ M) = n` for every `i`, then `M` is free of rank `n`. Two special cases:
over a local domain, the generic fibre alone suffices; over a reduced local ring, the fibres
`κ(𝔭) ⊗ M` at all primes `𝔭` suffice, since an element lying in every prime is nilpotent.

This is the local algebraic core of Hartshorne II, Exercise 5.8(c), and the family theorem also
gives Hartshorne II, Lemma 8.9 (used by the regular local differential criterion). Ex. 5.8(c):
a coherent sheaf on a
reduced Noetherian scheme whose fibre dimension is constant is locally free. Proof: lifting a
`k`-basis of `k ⊗ M` gives, by Nakayama's lemma, a surjection `φ : R ^ n → M`. After base change
to each `K i` it becomes a surjection between `K i`-vector spaces of the same finite dimension,
hence injective; so every coordinate of an element of `ker φ` vanishes in every `K i`, hence is
zero.
-/

open TensorProduct IsLocalRing Module

namespace Hartshorne

universe u

/-- Over a local ring `R`, let `M` be a finitely generated module and `n = dim_k (k ⊗ M)`. Suppose
`(K i)` is a family of fields that are `R`-algebras, jointly detecting zero in `R` (an element of
`R` vanishing in every `K i` is zero), with `dim_{K i} (K i ⊗ M) = n` for every `i`. Then `M` is
free with a basis indexed by `Fin n`. -/
theorem free_of_finrank_tensor_family_eq_finrank_residueField
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {ι : Type*} (K : ι → Type*) [∀ i, Field (K i)] [∀ i, Algebra R (K i)]
    (hK : ∀ r : R, (∀ i, algebraMap R (K i) r = 0) → r = 0)
    (h : ∀ i, finrank (K i) (K i ⊗[R] M) = finrank (ResidueField R) (ResidueField R ⊗[R] M)) :
    Nonempty (Basis (Fin (finrank (ResidueField R) (ResidueField R ⊗[R] M))) R M) := by
  set k := ResidueField R
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
  have hφi : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    ext j
    refine hK _ fun i => ?_
    have hψs : Function.Surjective (φ.baseChange (K i)) := LinearMap.lTensor_surjective _ hφs
    have hfin : finrank (K i) (K i ⊗[R] (Fin n →₀ R)) = finrank (K i) (K i ⊗[R] M) := by
      rw [Module.finrank_baseChange, Module.finrank_finsupp_self, Fintype.card_fin]
      exact (h i).symm
    have hψi : Function.Injective (φ.baseChange (K i)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hψs
    have h1 : (1 : K i) ⊗ₜ[R] x = 0 := by
      apply hψi
      simp [LinearMap.baseChange_tmul, hx]
    have h2 := congrArg (fun t => finsuppScalarRight R (K i) (K i) (Fin n) t j) h1
    simpa [Algebra.smul_def] using h2
  exact ⟨Basis.ofRepr (LinearEquiv.ofBijective φ ⟨hφi, hφs⟩).symm⟩

/-- Over a local domain `R`, a finitely generated module `M` whose special fibre `k ⊗ M` and
generic fibre `K ⊗ M` have the same dimension is free, with a basis indexed by `Fin n` where
`n = dim_k (k ⊗ M)`. -/
theorem free_of_finrank_residueField_eq_finrank_fractionRing
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : finrank (ResidueField R) (ResidueField R ⊗[R] M) =
      finrank (FractionRing R) (FractionRing R ⊗[R] M)) :
    Nonempty (Basis (Fin (finrank (ResidueField R) (ResidueField R ⊗[R] M))) R M) :=
  free_of_finrank_tensor_family_eq_finrank_residueField M (fun _ : Unit => FractionRing R)
    (fun r hr => IsFractionRing.injective R (FractionRing R) (by simpa using hr ()))
    (fun _ => h.symm)

/-- Over a reduced local ring `R`, a finitely generated module `M` whose fibre
`κ(𝔭) ⊗ M` has the same dimension `n = dim_k (k ⊗ M)` at every prime `𝔭` is free, with a basis
indexed by `Fin n`. -/
theorem free_of_forall_finrank_fiber_eq_of_isReduced
    {R : Type u} [CommRing R] [IsReduced R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : ∀ P : PrimeSpectrum R, finrank P.asIdeal.ResidueField (P.asIdeal.ResidueField ⊗[R] M) =
      finrank (ResidueField R) (ResidueField R ⊗[R] M)) :
    Nonempty (Basis (Fin (finrank (ResidueField R) (ResidueField R ⊗[R] M))) R M) := by
  refine free_of_finrank_tensor_family_eq_finrank_residueField M
    (fun P : PrimeSpectrum R => P.asIdeal.ResidueField) (fun r hr => ?_) h
  have hmem : ∀ J : Ideal R, J.IsPrime → r ∈ J := fun J hJ =>
    Ideal.algebraMap_residueField_eq_zero.mp (hr ⟨J, hJ⟩)
  exact (nilpotent_iff_mem_prime.mpr hmem).eq_zero

end Hartshorne
