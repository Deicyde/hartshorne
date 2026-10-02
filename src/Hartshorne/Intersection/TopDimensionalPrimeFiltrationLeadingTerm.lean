/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.GradedMultiplicity
import Hartshorne.Intersection.HilbertPolynomialPrimeQuotient
import Hartshorne.Intersection.ProjectiveHilbertPolynomial
import Hartshorne.Intersection.ProjectiveProperClosedDimensionDrop
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The leading Hilbert coefficient and top-dimensional minimal primes

This is the prime-filtration calculation in the proof of Hartshorne,
*Algebraic Geometry*, Theorem I.7.7 (p. 53).  A shift does not change a
prime quotient's leading coefficient, lower-dimensional filtration factors
do not contribute, and the occurrences of each remaining minimal prime are
its localized module length.
-/

namespace Hartshorne

open DirectSum Filter Finset MvPolynomial Polynomial Set TopologicalSpace
open scoped Polynomial

noncomputable section

universe u v

local instance {A : Type*} [CommSemiring A] :
    DecidableEq (PrimeSpectrum A) := Classical.decEq _

private theorem IsNumericalPolynomial.finset_sum
    {ι : Type*} {s : Finset ι} {P : ι → ℚ[X]}
    (hP : ∀ i ∈ s, IsNumericalPolynomial (P i)) :
    IsNumericalPolynomial (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [IsNumericalPolynomial]
      exact Filter.Eventually.of_forall fun _ => ⟨0, by simp⟩
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, IsNumericalPolynomial]
      filter_upwards [hP a (Finset.mem_insert_self _ _),
        ih fun i hi => hP i (Finset.mem_insert_of_mem hi)] with n hnP hnQ
      obtain ⟨x, hx⟩ := hnP
      obtain ⟨y, hy⟩ := hnQ
      exact ⟨x + y, by simp [hx, hy]⟩

private theorem IsNumericalPolynomial.taylor_int {P : ℚ[X]}
    (hP : IsNumericalPolynomial P) (l : ℤ) :
    IsNumericalPolynomial (P.taylor (l : ℚ)) := by
  rw [IsNumericalPolynomial]
  exact Filter.Eventually.of_forall fun n => by
    obtain ⟨a, ha⟩ := hP.integerValued (n + l)
    refine ⟨a, ?_⟩
    rw [Polynomial.taylor_eval]
    push_cast at ha ⊢
    exact ha

private theorem IsHilbertPolynomial.twist
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    {P : ℚ[X]} (hP : IsHilbertPolynomial (σ := σ) ℳ P) (l : ℤ) :
    IsHilbertPolynomial (σ := σ) (gradedModuleTwist ℳ l)
      (P.taylor (l : ℚ)) := by
  refine ⟨hP.1.taylor_int l, ?_⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP.2
  refine Filter.eventually_atTop.mpr ⟨N - l, fun d hd => ?_⟩
  rw [Polynomial.taylor_eval, hilbertFunction_twist]
  simpa only [Int.cast_add] using hN (d + l) (by omega)

private noncomputable def GradedLinearEquiv.pieceLinearEquiv
    {k R : Type*} [Field k] [Semiring R] [Algebra k R]
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module k M] [Module k N] [Module R M] [Module R N]
    [IsScalarTower k R M] [IsScalarTower k R N]
    {ℳ : ℤ → Submodule k M} {ℴ : ℤ → Submodule k N}
    (e : GradedLinearEquiv R ℳ ℴ) (d : ℤ) : ℳ d ≃ₗ[k] ℴ d where
  toFun x := ⟨e x, e.map_mem x.property⟩
  invFun y := ⟨e.symm y, e.symm.map_mem y.property⟩
  left_inv x := by
    ext
    exact e.toLinearEquiv.symm_apply_apply (x : M)
  right_inv y := by
    ext
    exact e.toLinearEquiv.apply_symm_apply (y : N)
  map_add' x y := by ext; exact e.toLinearEquiv.map_add x y
  map_smul' r x := by
    ext
    exact e.toLinearEquiv.toLinearMap.map_smul_of_tower r x

private noncomputable def GradedLinearEquiv.pieceLinearEquivOfCompatibleSMul
    {k R : Type*} [Field k] [Semiring R] [Algebra k R]
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module k M] [Module k N] [Module R M] [Module R N]
    {ℳ : ℤ → Submodule k M} {ℴ : ℤ → Submodule k N}
    (e : GradedLinearEquiv R ℳ ℴ)
    (hM : ∀ (r : k) (x : M), algebraMap k R r • x = r • x)
    (hN : ∀ (r : k) (x : N), algebraMap k R r • x = r • x)
    (d : ℤ) : ℳ d ≃ₗ[k] ℴ d where
  toFun x := ⟨e x, e.map_mem x.property⟩
  invFun y := ⟨e.symm y, e.symm.map_mem y.property⟩
  left_inv x := by
    ext
    exact e.toLinearEquiv.symm_apply_apply (x : M)
  right_inv y := by
    ext
    exact e.toLinearEquiv.apply_symm_apply (y : N)
  map_add' x y := by ext; exact e.toLinearEquiv.map_add x y
  map_smul' r x := by
    ext
    change e.toLinearEquiv (r • (x : M)) = r • e.toLinearEquiv (x : M)
    rw [← hM r, e.toLinearEquiv.map_smul, hN r]

private theorem mvPolynomialQuotient_algebraMap_smul
    {k : Type u} [Field k] {σ : Type v}
    (I : Ideal (MvPolynomial σ k)) (r : k)
    (x : MvPolynomial σ k ⧸ I) :
    algebraMap k (MvPolynomial σ k) r • x = r • x := by
  rcases x with ⟨x⟩
  change Submodule.Quotient.mk ((algebraMap k (MvPolynomial σ k) r) • x) =
    Submodule.Quotient.mk (r • x)
  rw [IsScalarTower.algebraMap_smul]

private theorem hilbertFunction_eq_of_gradedLinearEquiv
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} {N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module k M] [Module k N]
    [Module (MvPolynomial σ k) M] [Module (MvPolynomial σ k) N]
    [IsScalarTower k (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) N]
    (ℳ : ℤ → Submodule k M) (ℴ : ℤ → Submodule k N)
    [DirectSum.Decomposition ℳ] [DirectSum.Decomposition ℴ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℴ]
    [Module.Finite (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) N]
    (e : GradedLinearEquiv (MvPolynomial σ k) ℳ ℴ) (d : ℤ) :
    hilbertFunction (σ := σ) ℳ d = hilbertFunction (σ := σ) ℴ d := by
  let _ : Module.Finite k (ℳ d) := finite_gradedPiece (σ := σ) ℳ d
  let _ : Module.Finite k (ℴ d) := finite_gradedPiece (σ := σ) ℴ d
  exact LinearEquiv.finrank_eq (e.pieceLinearEquiv (k := k) d)

private noncomputable def gradedSubmoduleOfEquiv
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (𝓐 : ℤ → Submodule R A) [GradedAlgebra 𝓐]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝓐 ℳ]
    (N₁ N₂ : HomogeneousSubmodule 𝓐 ℳ) (h : N₁ ≤ N₂) :
    GradedLinearEquiv A
      (gradedSubmodulePiece 𝓐 ℳ N₁)
      (gradedSubmodulePiece 𝓐 (gradedSubmodulePiece 𝓐 ℳ N₂)
        (gradedSubmoduleOf 𝓐 ℳ N₁ N₂ h)) where
  toLinearEquiv :=
    { toFun := fun x => ⟨⟨x.1, h x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1.1, x.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun x y => by ext; rfl
      map_smul' := fun a x => by ext; rfl }
  map_piece d := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨⟨x.1.1, x.2⟩, hx, ?_⟩
      rfl

private theorem hilbertFunction_filtrationStep
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    (N₁ N₂ : HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ)
    (data : GradedPrimeFiltrationFactorData
      (integerHomogeneousSubmodule k σ) ℳ N₁ N₂) (d : ℤ) :
    hilbertFunction (σ := σ)
        (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₂) d =
      hilbertFunction (σ := σ)
          (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₁) d +
        hilbertFunction (σ := σ)
          (gradedModuleTwist
            (gradedQuotientPiece
              (integerHomogeneousSubmodule k σ)
              (integerHomogeneousSubmodule k σ)
              (homogeneousIdealSubmodule
                (integerHomogeneousSubmodule k σ)
                data.prime.1 data.homogeneous)) data.twist) d := by
  let _ : Module.Finite (MvPolynomial σ k) N₂ :=
    homogeneousSubmoduleFinite ℳ N₂
  have h := hilbertFunction_subquotient (σ := σ)
    (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₂)
    (gradedSubmoduleOf (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le) d
  letI : DirectSum.Decomposition
      (gradedFactorPiece (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le) :=
    gradedQuotientPieceDecomposition
      (integerHomogeneousSubmodule k σ)
      (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₂)
      (gradedSubmoduleOf (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le)
  letI : SetLike.GradedSMul (integerHomogeneousSubmodule k σ)
      (gradedFactorPiece (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le) :=
    gradedQuotientPieceGradedSMul
      (integerHomogeneousSubmodule k σ)
      (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₂)
      (gradedSubmoduleOf (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le)
  have hleft := hilbertFunction_eq_of_gradedLinearEquiv
    (k := k) (σ := σ) (M := N₁)
    (N := gradedSubmoduleOf
      (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le)
    (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₁)
    (gradedSubmodulePiece (integerHomogeneousSubmodule k σ)
      (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₂)
      (gradedSubmoduleOf (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le))
    (gradedSubmoduleOfEquiv
      (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le) d
  have hright :
      hilbertFunction (σ := σ)
          (gradedModuleTwist
            (gradedQuotientPiece
              (integerHomogeneousSubmodule k σ)
              (integerHomogeneousSubmodule k σ)
              (homogeneousIdealSubmodule
                (integerHomogeneousSubmodule k σ)
                data.prime.1 data.homogeneous)) data.twist) d =
        hilbertFunction (σ := σ)
          (gradedFactorPiece
            (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le) d := by
    unfold hilbertFunction
    exact LinearEquiv.finrank_eq <|
      data.equiv.pieceLinearEquivOfCompatibleSMul
        (fun r x => mvPolynomialQuotient_algebraMap_smul data.prime.1 r x)
        (fun r x => IsScalarTower.algebraMap_smul
          (R := k) (A := MvPolynomial σ k) r x) d
  calc
    hilbertFunction (σ := σ)
        (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₂) d =
        hilbertFunction (σ := σ)
            (gradedSubmodulePiece (integerHomogeneousSubmodule k σ)
              (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₂)
              (gradedSubmoduleOf
                (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le)) d +
          hilbertFunction (σ := σ)
            (gradedQuotientPiece (integerHomogeneousSubmodule k σ)
              (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N₂)
              (gradedSubmoduleOf
                (integerHomogeneousSubmodule k σ) ℳ N₁ N₂ data.le)) d := h
    _ = _ := by
      rw [← hleft]
      congr 1
      exact hright.symm

private noncomputable def gradedTopEquiv
    {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    (𝓐 : ℤ → Submodule R A) [GradedAlgebra 𝓐]
    (ℳ : ℤ → Submodule R M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul 𝓐 ℳ] :
    GradedLinearEquiv A ℳ
      (gradedSubmodulePiece 𝓐 ℳ
        (⊤ : HomogeneousSubmodule 𝓐 ℳ)) where
  toLinearEquiv :=
    { toFun := fun x => ⟨x, trivial⟩
      invFun := fun x => x.1
      left_inv := fun _ => rfl
      right_inv := fun x => by ext; rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_piece d := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩

private noncomputable def filtrationFactorHilbertFunction
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    (s : RelSeries
      {q : HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ ×
          HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k σ) ℳ q.1 q.2})
    (j : ℕ) (d : ℤ) : ℕ :=
  if hj : j < s.length then
    let data := gradedPrimeFiltrationFactorDataAt
      (integerHomogeneousSubmodule k σ) ℳ s ⟨j, hj⟩
    hilbertFunction (σ := σ)
      (gradedModuleTwist
        (gradedQuotientPiece
          (integerHomogeneousSubmodule k σ)
          (integerHomogeneousSubmodule k σ)
          (homogeneousIdealSubmodule
            (integerHomogeneousSubmodule k σ)
            data.prime.1 data.homogeneous)) data.twist) d
  else 0

private theorem hilbertFunction_eq_sum_filtrationFactors
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    (s : RelSeries
      {q : HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ ×
          HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k σ) ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤) (d : ℤ) :
    hilbertFunction (σ := σ) ℳ d =
      ∑ j ∈ Finset.range s.length,
        filtrationFactorHilbertFunction ℳ s j d := by
  have hpartial : ∀ m (hm : m ≤ s.length),
      hilbertFunction (σ := σ)
          (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ
            (s ⟨m, Nat.lt_succ_of_le hm⟩)) d =
        ∑ j ∈ Finset.range m,
          filtrationFactorHilbertFunction ℳ s j d := by
    intro m hm
    induction m with
    | zero =>
        rw [show s ⟨0, Nat.zero_lt_succ _⟩ = s.head from rfl, hshead]
        unfold hilbertFunction
        letI : Subsingleton
            (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ
              (⊥ : HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ) d) :=
          ⟨fun x y => by
            apply Subtype.ext
            apply Subtype.ext
            have hxmem := x.1.property
            have hymem := y.1.property
            change (x.1.1 : M) ∈ (⊥ : Submodule (MvPolynomial σ k) M) at hxmem
            change (y.1.1 : M) ∈ (⊥ : Submodule (MvPolynomial σ k) M) at hymem
            have hx : (x.1.1 : M) = 0 := hxmem
            have hy : (y.1.1 : M) = 0 := hymem
            rw [hx, hy]⟩
        exact Module.finrank_zero_of_subsingleton
    | succ m ih =>
        have hmlt : m < s.length := Nat.lt_of_succ_le hm
        let i : Fin s.length := ⟨m, hmlt⟩
        let data := gradedPrimeFiltrationFactorDataAt
          (integerHomogeneousSubmodule k σ) ℳ s i
        have hstep := hilbertFunction_filtrationStep ℳ
          (s (Fin.castSucc i)) (s i.succ) data d
        have him := ih (Nat.le_of_lt hmlt)
        change hilbertFunction (σ := σ)
          (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ
            (s i.succ)) d = _
        rw [hstep, Finset.sum_range_succ]
        have him' : hilbertFunction (σ := σ)
            (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ
              (s (Fin.castSucc i))) d =
            ∑ j ∈ Finset.range m,
              filtrationFactorHilbertFunction ℳ s j d := by
          simpa [i] using him
        rw [him']
        simp [filtrationFactorHilbertFunction, i, data, hmlt]
  have hlast := hpartial s.length le_rfl
  have htop := hilbertFunction_eq_of_gradedLinearEquiv
    (k := k) (σ := σ) ℳ
    (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ
      (⊤ : HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ))
    (gradedTopEquiv (integerHomogeneousSubmodule k σ) ℳ) d
  rw [show s ⟨s.length, Nat.lt_succ_self _⟩ = s.last from rfl,
    hslast, ← htop] at hlast
  exact hlast

private theorem isProjAlgebraicSet_projZeroSet_of_isHomogeneous
    {k : Type u} [Field k] {σ : Type*}
    (I : Ideal (MvPolynomial σ k)) (hI : IsHomogeneousIdeal I) :
    IsProjAlgebraicSet (projZeroSet (I : Set (MvPolynomial σ k))) := by
  obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists
    (𝒜 := homogeneousSubmodule σ k) (I := I)).mp hI
  let U : Set (MvPolynomial σ k) := Subtype.val '' T
  refine ⟨U, ?_, ?_⟩
  · rintro f ⟨g, -, rfl⟩
    exact isHomogeneousElem_iff.mp g.2
  · calc
      projZeroSet (I : Set (MvPolynomial σ k)) =
          projZeroSet (Ideal.span U : Set (MvPolynomial σ k)) := by
        rw [hT]
      _ = projZeroSet U := projZeroSet_span _

private theorem isClosed_projZeroSet_of_isHomogeneousIdeal
    {k : Type u} [Field k] {σ : Type*}
    (I : Ideal (MvPolynomial σ k)) (hI : IsHomogeneousIdeal I) :
    IsClosed (projZeroSet (I : Set (MvPolynomial σ k))) :=
  isClosed_iff_isProjAlgebraicSet.mpr
    (isProjAlgebraicSet_projZeroSet_of_isHomogeneous I hI)

private theorem isProjVariety_projZeroSet_of_isHomogeneous_isPrime
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hI : IsHomogeneousIdeal I)
    (hprime : I.IsPrime)
    (hne : (projZeroSet (I : Set (MvPolynomial σ k))).Nonempty) :
    IsProjVariety (projZeroSet (I : Set (MvPolynomial σ k))) := by
  let hAlg := isProjAlgebraicSet_projZeroSet_of_isHomogeneous I hI
  refine ⟨(isIrreducible_iff_isPrime_homogeneousVanishingIdeal hAlg).mpr ?_,
    isClosed_iff_isProjAlgebraicSet.mpr hAlg⟩
  rw [homogeneousVanishingIdeal_projZeroSet hI hne, hprime.radical]
  exact hprime

private theorem projDim_empty
    {k : Type u} [Field k] {σ : Type*} :
    projDim (∅ : Set (ProjectiveSpace k σ)) = ⊥ := by
  unfold projDim topologicalKrullDim
  letI : IsEmpty
      (IrreducibleCloseds (↥(∅ : Set (ProjectiveSpace k σ)))) :=
    ⟨fun Z => Z.2.1.nonempty.elim fun x => x.2⟩
  exact Order.krullDim_eq_bot

private theorem gradedHilbertPolynomial_quotGrading_eq_of_eq
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (I J : HomogeneousIdeal
      (integerHomogeneousSubmodule k (Fin (n + 1))))
    [DirectSum.Decomposition
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I)]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k (Fin (n + 1)))
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I)]
    [DirectSum.Decomposition
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) J)]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k (Fin (n + 1)))
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) J)]
    (h : I = J) :
    gradedHilbertPolynomial (k := k) (n := n)
        (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) I) =
      gradedHilbertPolynomial (k := k) (n := n)
        (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1))) J) := by
  subst J
  rfl

/-- The canonical Hilbert polynomial of one shifted prime-quotient factor in
a graded prime filtration. -/
noncomputable def gradedPrimeFiltrationFactorHilbertPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2})
    (i : Fin s.length) : ℚ[X] :=
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let data := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
  let ℱ := gradedQuotientPiece 𝓐 𝓐
    (homogeneousIdealSubmodule 𝓐 data.prime.1 data.homogeneous)
  gradedHilbertPolynomial (k := k) (n := n)
    (gradedModuleTwist ℱ data.twist)

/-- Along a graded prime filtration, the canonical Hilbert polynomial of the
module is the sum of the canonical Hilbert polynomials of the shifted prime
quotients. -/
theorem gradedHilbertPolynomial_eq_sum_filtrationFactors
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤) :
    gradedHilbertPolynomial (k := k) (n := n) ℳ =
      ∑ i : Fin s.length,
        gradedPrimeFiltrationFactorHilbertPolynomial ℳ s i := by
  let P (i : Fin s.length) : ℚ[X] :=
    gradedPrimeFiltrationFactorHilbertPolynomial ℳ s i
  have hP (i : Fin s.length) :
      let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
      let data := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
      let ℱ := gradedQuotientPiece 𝓐 𝓐
        (homogeneousIdealSubmodule 𝓐 data.prime.1 data.homogeneous)
      IsHilbertPolynomial (σ := Fin (n + 1))
        (gradedModuleTwist ℱ data.twist) (P i) := by
    dsimp only
    exact gradedHilbertPolynomial_isHilbertPolynomial
      (k := k) (n := n) _
  have hsum : IsHilbertPolynomial (σ := Fin (n + 1)) ℳ
      (∑ i : Fin s.length, P i) := by
    refine ⟨IsNumericalPolynomial.finset_sum
      (s := Finset.univ) (fun i _ => (hP i).1), ?_⟩
    have hall : ∀ᶠ d : ℤ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin s.length)),
          (P i).eval (d : ℚ) =
            (let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
             let data := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
             let ℱ := gradedQuotientPiece 𝓐 𝓐
               (homogeneousIdealSubmodule 𝓐 data.prime.1 data.homogeneous)
             (hilbertFunction (σ := Fin (n + 1))
               (gradedModuleTwist ℱ data.twist) d : ℚ)) :=
      (Finset.eventually_all Finset.univ).2 fun i _ => (hP i).2
    filter_upwards [hall] with d hd
    rw [Polynomial.eval_finsetSum,
      hilbertFunction_eq_sum_filtrationFactors ℳ s hshead hslast d]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hd i (Finset.mem_univ i)]
    simp [filtrationFactorHilbertFunction, i.2]
  exact isHilbertPolynomial_unique ℳ
    (gradedHilbertPolynomial_isHilbertPolynomial
      (k := k) (n := n) ℳ) hsum

/-- The distinct primes in a chosen finite graded prime filtration. -/
noncomputable def gradedPrimeFiltrationPrimes
    {k : Type u} [Field k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2}) :
    Finset (PrimeSpectrum (MvPolynomial (Fin (n + 1)) k)) := by
  classical
  exact Finset.univ.image
    (gradedPrimeFiltrationFactorPrime
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s)

/-- The finite set of minimal annihilator primes whose projective zero sets
have the module's specified top dimension. -/
noncomputable def topDimensionalMinimalAnnihilatorPrimes
    {k : Type u} [Field k] {n r : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2}) :
    Finset (PrimeSpectrum (MvPolynomial (Fin (n + 1)) k)) := by
  classical
  exact (gradedPrimeFiltrationPrimes ℳ s).filter fun P =>
    (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M).IsMinimalPrime P.1 ∧
      projDim (projZeroSet
        (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
          (r : WithBot ℕ∞)

theorem mem_topDimensionalMinimalAnnihilatorPrimes_iff
    {k : Type u} [Field k] {n r : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (P : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k)) :
    P ∈ topDimensionalMinimalAnnihilatorPrimes (r := r) ℳ s ↔
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M).IsMinimalPrime P.1 ∧
        projDim (projZeroSet
          (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
            (r : WithBot ℕ∞) := by
  classical
  unfold topDimensionalMinimalAnnihilatorPrimes
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    have hfactor : IsGradedPrimeFiltrationFactorOf
        (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s P :=
      (gradedPrimeFiltration_minimal_factor_iff
        (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ
        s hshead hslast P).2 h.1 |>.prop
    obtain ⟨i, hi⟩ :=
      (isGradedPrimeFiltrationFactorOf_iff_exists_factorPrime_eq
        (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s P).1 hfactor
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩

/-- Every prime factor's projective zero set lies in the projective support of
the filtered module. -/
theorem gradedPrimeFiltrationFactor_projDim_le
    {k : Type u} [Field k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (i : Fin s.length) :
    projDim (projZeroSet
        ((gradedPrimeFiltrationFactorPrime
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s i).1 :
            Set (MvPolynomial (Fin (n + 1)) k))) ≤
      projDim (projZeroSet
        (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
          Set (MvPolynomial (Fin (n + 1)) k))) := by
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let q := gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i
  have hAnnq : Module.annihilator (MvPolynomial (Fin (n + 1)) k) M ≤ q.1 :=
    (gradedPrimeFiltration_annihilator_le_iff
      𝓐 ℳ s hshead hslast q).2
      ⟨q, ⟨i, gradedPrimeFiltrationFactorPrime_spec 𝓐 ℳ s i⟩, le_rfl⟩
  exact (Topology.IsEmbedding.inclusion
    (projZeroSet_anti_mono hAnnq)).isInducing.topologicalKrullDim_le

/-- A filtration factor with the full projective dimension is a minimal prime
over the module annihilator. -/
theorem gradedPrimeFiltrationFactor_isMinimalPrime_of_projDim_eq
    {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (hsupportDim : projDim (projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
        Set (MvPolynomial (Fin (n + 1)) k))) = (r : WithBot ℕ∞))
    (i : Fin s.length)
    (hiDim : projDim (projZeroSet
      ((gradedPrimeFiltrationFactorPrime
        (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s i).1 :
          Set (MvPolynomial (Fin (n + 1)) k))) = (r : WithBot ℕ∞)) :
    (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M).IsMinimalPrime
      (gradedPrimeFiltrationFactorPrime
        (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s i).1 := by
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let q := gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i
  let data := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
  have hqFactor : IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s q :=
    ⟨i, gradedPrimeFiltrationFactorPrime_spec 𝓐 ℳ s i⟩
  have hAnnq : Module.annihilator (MvPolynomial (Fin (n + 1)) k) M ≤ q.1 :=
    (gradedPrimeFiltration_annihilator_le_iff
      𝓐 ℳ s hshead hslast q).2 ⟨q, hqFactor, le_rfl⟩
  obtain ⟨p, hpMin, hpq⟩ := Ideal.exists_minimalPrimes_le hAnnq
  let P : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k) := ⟨p, hpMin.isPrime⟩
  have hpq' : P ≤ q := hpq
  by_cases hPq : P = q
  · change (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M).IsMinimalPrime q.1
    rw [← hPq]
    simpa [P] using hpMin
  have hPFactor : IsGradedPrimeFiltrationFactorOf 𝓐 ℳ s P :=
    ((gradedPrimeFiltration_minimal_factor_iff
      𝓐 ℳ s hshead hslast P).2 (by simpa [P] using hpMin)).prop
  obtain ⟨j, hj⟩ :=
    (isGradedPrimeFiltrationFactorOf_iff_exists_factorPrime_eq
      𝓐 ℳ s P).1 hPFactor
  let pdata := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s j
  have hPHom : P.1.IsHomogeneous 𝓐 := by
    have h := pdata.homogeneous
    change (gradedPrimeFiltrationFactorPrime 𝓐 ℳ s j).1.IsHomogeneous 𝓐 at h
    rwa [hj] at h
  have hqHom : q.1.IsHomogeneous 𝓐 := by
    simpa [q, data, gradedPrimeFiltrationFactorPrime] using data.homogeneous
  have hPHomNat : IsHomogeneousIdeal P.1 :=
    (ideal_isHomogeneous_integer_iff k (Fin (n + 1)) P.1).1 hPHom
  have hqHomNat : IsHomogeneousIdeal q.1 :=
    (ideal_isHomogeneous_integer_iff k (Fin (n + 1)) q.1).1 hqHom
  let ZP : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet (P.1 : Set (MvPolynomial (Fin (n + 1)) k))
  let Zq : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet (q.1 : Set (MvPolynomial (Fin (n + 1)) k))
  have hZqne : Zq.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hZq
    have hbot : projDim Zq = ⊥ := by rw [hZq, projDim_empty]
    have : (⊥ : WithBot ℕ∞) = (r : WithBot ℕ∞) :=
      hbot.symm.trans (by simpa [Zq, q, 𝓐] using hiDim)
    simp at this
  have hZqZP : Zq ⊆ ZP := projZeroSet_anti_mono hpq'
  have hZPne : ZP.Nonempty := hZqne.mono hZqZP
  have hZne : Zq ≠ ZP := by
    intro hEq
    have hJq : homogeneousVanishingIdeal Zq = q.1 := by
      change homogeneousVanishingIdeal
        (projZeroSet (q.1 : Set (MvPolynomial (Fin (n + 1)) k))) = q.1
      rw [homogeneousVanishingIdeal_projZeroSet hqHomNat hZqne, q.2.radical]
    have hJP : homogeneousVanishingIdeal ZP = P.1 := by
      change homogeneousVanishingIdeal
        (projZeroSet (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) = P.1
      rw [homogeneousVanishingIdeal_projZeroSet hPHomNat hZPne, P.2.radical]
    apply hPq
    apply PrimeSpectrum.ext
    exact hJP.symm.trans ((congrArg homogeneousVanishingIdeal hEq).symm.trans hJq)
  have hss : Zq ⊂ ZP := Set.ssubset_iff_subset_ne.mpr ⟨hZqZP, hZne⟩
  have hZPvar : IsProjVariety ZP :=
    isProjVariety_projZeroSet_of_isHomogeneous_isPrime
      P.1 hPHomNat P.2 hZPne
  have hZqclosed : IsClosed Zq :=
    isClosed_projZeroSet_of_isHomogeneousIdeal q.1 hqHomNat
  have hlt : projDim Zq < projDim ZP :=
    projDim_lt_of_closed_ssubset_isProjVariety hZPvar hZqclosed hss
  have hPAnn : Module.annihilator (MvPolynomial (Fin (n + 1)) k) M ≤ P.1 :=
    hpMin.le
  have hPle : projDim ZP ≤ projDim (projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
        Set (MvPolynomial (Fin (n + 1)) k))) :=
    (Topology.IsEmbedding.inclusion
      (projZeroSet_anti_mono hPAnn)).isInducing.topologicalKrullDim_le
  have hirr : (r : WithBot ℕ∞) < (r : WithBot ℕ∞) := by
    calc
      (r : WithBot ℕ∞) = projDim Zq := by
        simpa [Zq, q, 𝓐] using hiDim.symm
      _ < projDim ZP := hlt
      _ ≤ projDim (projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
            Set (MvPolynomial (Fin (n + 1)) k))) := hPle
      _ = (r : WithBot ℕ∞) := hsupportDim
  exact (lt_irrefl _ hirr).elim

/-- The degree-`r` coefficient of a shifted homogeneous prime quotient with
projective dimension `r` is its projective degree divided by `r!`. -/
theorem twistedPrimeQuotient_coeff_eq_inv_factorial_mul_projectiveDegree
    {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ}
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
    (hp : p.1.IsHomogeneous
      (integerHomogeneousSubmodule k (Fin (n + 1))))
    (l : ℤ)
    (hdim : projDim (projZeroSet
      (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
        (r : WithBot ℕ∞)) :
    let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
    let ℱ := gradedQuotientPiece 𝓐 𝓐
      (homogeneousIdealSubmodule 𝓐 p.1 hp)
    (gradedHilbertPolynomial (k := k) (n := n)
      (gradedModuleTwist ℱ l)).coeff r =
      (r.factorial : ℚ)⁻¹ *
        projectiveDegree (projZeroSet
          (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) := by
  dsimp only
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let ℱ := gradedQuotientPiece 𝓐 𝓐
    (homogeneousIdealSubmodule 𝓐 p.1 hp)
  let P₀ : ℚ[X] := gradedHilbertPolynomial (k := k) (n := n) ℱ
  let Pₗ : ℚ[X] := gradedHilbertPolynomial (k := k) (n := n)
    (gradedModuleTwist ℱ l)
  let Z : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet (p.1 : Set (MvPolynomial (Fin (n + 1)) k))
  have hZne : Z.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hZ
    have hbot : projDim Z = ⊥ := by rw [hZ, projDim_empty]
    have : (⊥ : WithBot ℕ∞) = (r : WithBot ℕ∞) :=
      hbot.symm.trans (by simpa [Z] using hdim)
    simp at this
  have hpHomNat : IsHomogeneousIdeal p.1 :=
    (ideal_isHomogeneous_integer_iff k (Fin (n + 1)) p.1).1 hp
  have hJ : homogeneousVanishingIdeal Z = p.1 := by
    change homogeneousVanishingIdeal
      (projZeroSet (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) = p.1
    rw [homogeneousVanishingIdeal_projZeroSet hpHomNat hZne, p.2.radical]
  have hP₀Hilbert : IsHilbertPolynomial (σ := Fin (n + 1)) ℱ P₀ :=
    gradedHilbertPolynomial_isHilbertPolynomial (k := k) (n := n) ℱ
  have hPₗHilbert : IsHilbertPolynomial (σ := Fin (n + 1))
      (gradedModuleTwist ℱ l) Pₗ :=
    gradedHilbertPolynomial_isHilbertPolynomial
      (k := k) (n := n) (gradedModuleTwist ℱ l)
  have hPₗeq : Pₗ = P₀.taylor (l : ℚ) :=
    isHilbertPolynomial_unique (gradedModuleTwist ℱ l)
      hPₗHilbert (hP₀Hilbert.twist ℱ l)
  have hann : Module.annihilator (MvPolynomial (Fin (n + 1)) k)
      (MvPolynomial (Fin (n + 1)) k ⧸
        (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule) = p.1 := by
    change Module.annihilator (MvPolynomial (Fin (n + 1)) k)
      (MvPolynomial (Fin (n + 1)) k ⧸ p.1) = p.1
    exact Ideal.annihilator_quotient
  have hP₀degree : hilbertPolynomialDegree P₀ = projDim Z := by
    simpa only [P₀, Z, hann] using
      (gradedHilbertPolynomial_degree (k := k) (n := n) ℱ)
  have hPₗdegree : hilbertPolynomialDegree Pₗ = projDim Z := by
    simpa only [Pₗ, Z, hann] using
      (gradedHilbertPolynomial_degree
        (k := k) (n := n) (gradedModuleTwist ℱ l))
  have hP₀ne : P₀ ≠ 0 := by
    intro hzero
    have : (⊥ : WithBot ℕ∞) = (r : WithBot ℕ∞) := by
      simpa [hilbertPolynomialDegree, hzero] using hP₀degree.trans hdim
    simp at this
  have hPₗne : Pₗ ≠ 0 := by
    intro hzero
    have : (⊥ : WithBot ℕ∞) = (r : WithBot ℕ∞) := by
      simpa [hilbertPolynomialDegree, hzero] using hPₗdegree.trans hdim
    simp at this
  have hP₀nat : P₀.natDegree = r := by
    have hcast : (P₀.natDegree : WithBot ℕ∞) = (r : WithBot ℕ∞) := by
      simpa [hilbertPolynomialDegree, hP₀ne] using hP₀degree.trans hdim
    exact_mod_cast hcast
  have hPₗnat : Pₗ.natDegree = r := by
    have hcast : (Pₗ.natDegree : WithBot ℕ∞) = (r : WithBot ℕ∞) := by
      simpa [hilbertPolynomialDegree, hPₗne] using hPₗdegree.trans hdim
    exact_mod_cast hcast
  have hPₗlc : Pₗ.leadingCoeff = P₀.leadingCoeff := by
    rw [hPₗeq, Polynomial.leadingCoeff_taylor]
  have hPₗcoeff : Pₗ.coeff r = Pₗ.leadingCoeff := by
    rw [← hPₗnat, Polynomial.coeff_natDegree]
  have hJ' : homogeneousVanishingIdeal
      (projZeroSet (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) = p.1 := by
    simpa [Z] using hJ
  have hproj : projectiveHilbertPolynomial Z = P₀ := by
    have hHI : integerProjVanishingIdeal Z =
        homogeneousIdealSubmodule 𝓐 p.1 hp :=
      HomogeneousIdeal.ext hJ'
    letI : DirectSum.Decomposition
        (quotGrading 𝓐 (integerProjVanishingIdeal Z)) :=
      integerProjCoordGradingDecomposition Z
    letI : SetLike.GradedSMul 𝓐
        (quotGrading 𝓐 (integerProjVanishingIdeal Z)) :=
      integerProjCoordGradingGradedSMul Z
    letI : DirectSum.Decomposition
        (quotGrading 𝓐 (homogeneousIdealSubmodule 𝓐 p.1 hp)) :=
      gradedQuotientPieceDecomposition 𝓐 𝓐
        (homogeneousIdealSubmodule 𝓐 p.1 hp)
    letI : SetLike.GradedSMul 𝓐
        (quotGrading 𝓐 (homogeneousIdealSubmodule 𝓐 p.1 hp)) :=
      gradedQuotientPieceGradedSMul 𝓐 𝓐
        (homogeneousIdealSubmodule 𝓐 p.1 hp)
    change gradedHilbertPolynomial (k := k) (n := n)
        (quotGrading 𝓐 (integerProjVanishingIdeal Z)) =
      gradedHilbertPolynomial (k := k) (n := n)
        (quotGrading 𝓐 (homogeneousIdealSubmodule 𝓐 p.1 hp))
    exact gradedHilbertPolynomial_quotGrading_eq_of_eq
      (integerProjVanishingIdeal Z)
      (homogeneousIdealSubmodule 𝓐 p.1 hp) hHI
  rw [show (gradedHilbertPolynomial (k := k) (n := n)
      (gradedModuleTwist ℱ l)).coeff r = Pₗ.coeff r from rfl,
    hPₗcoeff, hPₗlc,
    projectiveDegree, hproj, hP₀nat]
  field_simp

/-- A shifted prime quotient whose projective dimension is strictly below
`r` has zero `r`th coefficient. -/
theorem twistedPrimeQuotient_coeff_eq_zero_of_projDim_lt
    {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ}
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
    (hp : p.1.IsHomogeneous
      (integerHomogeneousSubmodule k (Fin (n + 1))))
    (l : ℤ)
    (hdim : projDim (projZeroSet
      (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) <
        (r : WithBot ℕ∞)) :
    let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
    let ℱ := gradedQuotientPiece 𝓐 𝓐
      (homogeneousIdealSubmodule 𝓐 p.1 hp)
    (gradedHilbertPolynomial (k := k) (n := n)
      (gradedModuleTwist ℱ l)).coeff r = 0 := by
  dsimp only
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let ℱ := gradedQuotientPiece 𝓐 𝓐
    (homogeneousIdealSubmodule 𝓐 p.1 hp)
  let P : ℚ[X] := gradedHilbertPolynomial (k := k) (n := n)
    (gradedModuleTwist ℱ l)
  let Z : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet (p.1 : Set (MvPolynomial (Fin (n + 1)) k))
  have hann : Module.annihilator (MvPolynomial (Fin (n + 1)) k)
      (MvPolynomial (Fin (n + 1)) k ⧸
        (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule) = p.1 := by
    change Module.annihilator (MvPolynomial (Fin (n + 1)) k)
      (MvPolynomial (Fin (n + 1)) k ⧸ p.1) = p.1
    exact Ideal.annihilator_quotient
  have hPdegree : hilbertPolynomialDegree P = projDim Z := by
    simpa only [P, Z, hann] using
      (gradedHilbertPolynomial_degree
        (k := k) (n := n) (gradedModuleTwist ℱ l))
  by_cases hPzero : P = 0
  · change P.coeff r = 0
    rw [hPzero, Polynomial.coeff_zero]
  · have heq : (P.natDegree : WithBot ℕ∞) = projDim Z := by
      simpa [hilbertPolynomialDegree, hPzero] using hPdegree
    have hcast : (P.natDegree : WithBot ℕ∞) < (r : WithBot ℕ∞) :=
      heq.trans_lt (by simpa [Z] using hdim)
    have hnat : P.natDegree < r := by exact_mod_cast hcast
    exact Polynomial.coeff_eq_zero_of_natDegree_lt hnat

private theorem gradedPrimeFiltrationFactor_coeff_eq_ite
    {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (hsupportDim : projDim (projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
        Set (MvPolynomial (Fin (n + 1)) k))) = (r : WithBot ℕ∞))
    (i : Fin s.length) :
    (gradedPrimeFiltrationFactorHilbertPolynomial ℳ s i).coeff r =
      if gradedPrimeFiltrationFactorPrime
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s i ∈
            topDimensionalMinimalAnnihilatorPrimes (r := r) ℳ s then
        (r.factorial : ℚ)⁻¹ *
          projectiveDegree (projZeroSet
            ((gradedPrimeFiltrationFactorPrime
              (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s i).1 :
                Set (MvPolynomial (Fin (n + 1)) k)))
      else 0 := by
  classical
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let data := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
  let q := gradedPrimeFiltrationFactorPrime 𝓐 ℳ s i
  let T := topDimensionalMinimalAnnihilatorPrimes (r := r) ℳ s
  have htop_iff : q ∈ T ↔
      projDim (projZeroSet
        (q.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
          (r : WithBot ℕ∞) := by
    rw [mem_topDimensionalMinimalAnnihilatorPrimes_iff
      ℳ s hshead hslast]
    constructor
    · exact And.right
    · intro hdim
      exact ⟨gradedPrimeFiltrationFactor_isMinimalPrime_of_projDim_eq
        ℳ s hshead hslast hsupportDim i (by simpa [q, 𝓐] using hdim), hdim⟩
  by_cases htop : q ∈ T
  · rw [if_pos (by simpa [q, T, 𝓐] using htop)]
    have hdim := htop_iff.mp htop
    simpa [gradedPrimeFiltrationFactorHilbertPolynomial,
      q, data, 𝓐, gradedPrimeFiltrationFactorPrime] using
      (twistedPrimeQuotient_coeff_eq_inv_factorial_mul_projectiveDegree
        data.prime data.homogeneous data.twist hdim)
  · rw [if_neg (by simpa [q, T, 𝓐] using htop)]
    have hne : projDim (projZeroSet
        (q.1 : Set (MvPolynomial (Fin (n + 1)) k))) ≠
          (r : WithBot ℕ∞) := fun hdim => htop (htop_iff.mpr hdim)
    have hle : projDim (projZeroSet
        (q.1 : Set (MvPolynomial (Fin (n + 1)) k))) ≤
          (r : WithBot ℕ∞) := by
      exact (gradedPrimeFiltrationFactor_projDim_le
        ℳ s hshead hslast i).trans_eq hsupportDim
    have hlt : projDim (projZeroSet
        (q.1 : Set (MvPolynomial (Fin (n + 1)) k))) <
          (r : WithBot ℕ∞) := lt_of_le_of_ne hle hne
    simpa [gradedPrimeFiltrationFactorHilbertPolynomial,
      q, data, 𝓐, gradedPrimeFiltrationFactorPrime] using
      (twistedPrimeQuotient_coeff_eq_zero_of_projDim_lt
        data.prime data.homogeneous data.twist hlt)

/-- **Top-dimensional prime-filtration formula.** If the projective support
of a finite integer-graded module has dimension `r`, its `z^r` Hilbert
coefficient is `1 / r!` times the sum, over the minimal annihilator primes
whose projective zero sets have dimension `r`, of localized multiplicity
times projective degree. -/
theorem gradedHilbertPolynomial_coeff_eq_sum_minimalPrimes
    {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (hsupportDim : projDim (projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
        Set (MvPolynomial (Fin (n + 1)) k))) = (r : WithBot ℕ∞)) :
    (gradedHilbertPolynomial (k := k) (n := n) ℳ).coeff r =
      (r.factorial : ℚ)⁻¹ *
        ∑ P ∈ topDimensionalMinimalAnnihilatorPrimes (r := r) ℳ s,
          (ENat.toNat
              (gradedMultiplicity (MvPolynomial (Fin (n + 1)) k) M P) : ℚ) *
            projectiveDegree (projZeroSet
              (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) := by
  classical
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let g : Fin s.length → PrimeSpectrum (MvPolynomial (Fin (n + 1)) k) :=
    gradedPrimeFiltrationFactorPrime 𝓐 ℳ s
  let T := topDimensionalMinimalAnnihilatorPrimes (r := r) ℳ s
  let c : ℚ := (r.factorial : ℚ)⁻¹
  let w (P : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k)) : ℚ :=
    if P ∈ T then
      c * projectiveDegree (projZeroSet
        (P.1 : Set (MvPolynomial (Fin (n + 1)) k)))
    else 0
  have hpoint (i : Fin s.length) :
      (gradedPrimeFiltrationFactorHilbertPolynomial ℳ s i).coeff r = w (g i) := by
    simpa [w, g, T, c, 𝓐] using
      (gradedPrimeFiltrationFactor_coeff_eq_ite
        ℳ s hshead hslast hsupportDim i)
  have hgroup := Finset.sum_comp
    (s := (Finset.univ : Finset (Fin s.length))) w g
  have hgroup' :
      (∑ i : Fin s.length, w (g i)) =
        ∑ P ∈ gradedPrimeFiltrationPrimes ℳ s,
          ((Finset.filter (fun i : Fin s.length => g i = P)
            Finset.univ).card : ℕ) • w P := by
    simpa [gradedPrimeFiltrationPrimes, g, 𝓐] using hgroup
  have hsubset : T ⊆ gradedPrimeFiltrationPrimes ℳ s := by
    exact Finset.filter_subset _ _
  have hrestrict :
      (∑ P ∈ gradedPrimeFiltrationPrimes ℳ s,
          ((Finset.filter (fun i : Fin s.length => g i = P)
            Finset.univ).card : ℕ) • w P) =
        ∑ P ∈ T,
          ((Finset.filter (fun i : Fin s.length => g i = P)
            Finset.univ).card : ℕ) • w P := by
    symm
    apply Finset.sum_subset hsubset
    intro P _ hPT
    simp [w, hPT]
  rw [gradedHilbertPolynomial_eq_sum_filtrationFactors
    ℳ s hshead hslast, Polynomial.finsetSum_coeff]
  calc
    (∑ i : Fin s.length,
        (gradedPrimeFiltrationFactorHilbertPolynomial ℳ s i).coeff r) =
        ∑ i : Fin s.length, w (g i) :=
      Finset.sum_congr rfl fun i _ => hpoint i
    _ = ∑ P ∈ gradedPrimeFiltrationPrimes ℳ s,
        ((Finset.filter (fun i : Fin s.length => g i = P)
          Finset.univ).card : ℕ) • w P := hgroup'
    _ = ∑ P ∈ T,
        ((Finset.filter (fun i : Fin s.length => g i = P)
          Finset.univ).card : ℕ) • w P := hrestrict
    _ = c * ∑ P ∈ T,
        (ENat.toNat
            (gradedMultiplicity (MvPolynomial (Fin (n + 1)) k) M P) : ℚ) *
          projectiveDegree (projZeroSet
            (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hPT
      have hPmin :=
        ((mem_topDimensionalMinimalAnnihilatorPrimes_iff
          ℳ s hshead hslast P).1 (by simpa [T] using hPT)).1
      have hcountNat :
          ENat.toNat
              (gradedMultiplicity (MvPolynomial (Fin (n + 1)) k) M P) =
            (Finset.filter (fun i : Fin s.length => g i = P)
              Finset.univ).card := by
        simpa [g, 𝓐] using congrArg ENat.toNat
          (gradedPrimeFiltration_multiplicity_eq_count
            𝓐 ℳ s hshead hslast P hPmin)
      simp only [w, if_pos hPT, nsmul_eq_mul]
      rw [hcountNat]
      ring
    _ = (r.factorial : ℚ)⁻¹ *
        ∑ P ∈ topDimensionalMinimalAnnihilatorPrimes (r := r) ℳ s,
          (ENat.toNat
              (gradedMultiplicity (MvPolynomial (Fin (n + 1)) k) M P) : ℚ) *
            projectiveDegree (projZeroSet
              (P.1 : Set (MvPolynomial (Fin (n + 1)) k))) := by
      rfl

end

end Hartshorne
