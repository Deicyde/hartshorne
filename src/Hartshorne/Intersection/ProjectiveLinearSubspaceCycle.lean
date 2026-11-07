/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Ideal
import Hartshorne.Intersection.ChowGroups
import Hartshorne.Intersection.ProjectiveSpaceHilbertPolynomial
import Hartshorne.Intersection.RationalEquivalenceCodimOne
import Hartshorne.Projective.Correspondence
import Hartshorne.Rational.ContractedCurves
import Hartshorne.Scheme.ProjectiveIntersectionDegree
import Hartshorne.Scheme.ProjectiveSpaceClassGroup

/-!
# Linear subspaces of projective space as cycles

Toward Hartshorne, *Algebraic Geometry*, Appendix A, Exercise 6.3 (p. 437).

Let `ℙⁿ_k = Proj k[x₀, …, xₙ]`. This file sets up projective space as a variety in the sense of
the cycle and rational-equivalence API of Appendix A.1, and records its coordinate linear
subspaces as cycles:

* the structure morphism `ℙⁿ_k ⟶ Spec k` is of finite type and separated;
* `ℙⁿ_k` has dimension `n`;
* for `m ≤ n`, the coordinate linear subspace `Lₘ = V(x_{m+1}, …, xₙ)` is a point of `ℙⁿ_k`
  whose closure has codimension `n - m`, so `[Lₘ]` is a codimension-`(n - m)` cycle;
* for `k` algebraically closed, `Lₘ` has degree `1`: its Hilbert polynomial is
  `z ↦ choose (z + m) m`.

It then proves the two extreme cases of Exercise 6.3, for `k` algebraically closed. An integral
subvariety `Y` of codimension `0` is `ℙⁿ_k` itself, of degree `1`, so `[Y] = 1 · [Lₙ]`. An
integral subvariety of codimension `1` (a hypersurface of degree `d`) is rationally equivalent to
`d · [L_{n-1}]`, by Hartshorne II.6.4 together with the agreement of rational and linear
equivalence in codimension one. Finally it reduces the general case to two inputs: degree
vanishes on rational equivalence, and `[Y]` is rationally equivalent to some multiple of `[Lₘ]`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial Order TopologicalSpace

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

section PrimeSpan

/-- The ideal spanned by the variables `X i`, `i ∈ s`, is the kernel of the substitution killing
those variables. -/
theorem ker_aeval_ite_eq_span_X_image {σ R : Type*} [CommRing R] (s : Set σ)
    [DecidablePred (· ∈ s)] :
    RingHom.ker (aeval (R := R) fun i ↦ if i ∈ s then (0 : MvPolynomial σ R) else X i).toRingHom =
      Ideal.span (X '' s : Set (MvPolynomial σ R)) := by
  let φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := aeval fun i ↦ if i ∈ s then 0 else X i
  have hsub : ∀ f, f - φ f ∈ Ideal.span (X '' s : Set (MvPolynomial σ R)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [φ]
    | add p q hp hq =>
      rw [map_add, add_sub_add_comm]
      exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, show p * X i - φ p * φ (X i) = (p - φ p) * X i + φ p * (X i - φ (X i)) by
        ring]
      refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
      by_cases hi : i ∈ s
      · simpa [φ, hi] using
          (Ideal.subset_span ⟨i, hi, rfl⟩ : X i ∈ Ideal.span (X '' s : Set (MvPolynomial σ R)))
      · simp [φ, hi]
  apply le_antisymm
  · intro f hf
    have h := hsub f
    rwa [show φ f = 0 from hf, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    change φ (X i) = 0
    simp [φ, hi]

/-- An ideal of a polynomial ring over a domain spanned by a set of variables is prime. -/
theorem isPrime_span_X_image {σ R : Type*} [CommRing R] [IsDomain R] (s : Set σ) :
    (Ideal.span (X '' s : Set (MvPolynomial σ R))).IsPrime := by
  classical
  rw [← ker_aeval_ite_eq_span_X_image]
  exact RingHom.ker_isPrime _

/-- A variable `X j` lies in the ideal spanned by the variables `X i`, `i ∈ s`, only if
`j ∈ s`. -/
theorem X_mem_span_X_image_iff {σ R : Type*} [CommRing R] [Nontrivial R] (s : Set σ) (j : σ) :
    (X j : MvPolynomial σ R) ∈ Ideal.span (X '' s : Set (MvPolynomial σ R)) ↔ j ∈ s := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ Ideal.subset_span ⟨j, h, rfl⟩⟩
  rw [mem_ideal_span_X_image] at h
  obtain ⟨i, hi, hne⟩ := h (Finsupp.single j 1) (by simp [support_X])
  by_cases hij : i = j
  · exact hij ▸ hi
  · simp [Ne.symm hij] at hne

end PrimeSpan

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) k

local notation "𝕊" => MvPolynomial (Fin (n + 1)) k

section StructureMorphism

/-- The degree-zero part of `k[x₀, …, xₙ]` is `k`: the algebra map `k → S₀` is bijective. -/
theorem bijective_algebraMap_homogeneousSubmodule_zero :
    Function.Bijective (algebraMap k (𝒜 0)) := by
  refine ⟨fun a b h ↦ C_injective (Fin (n + 1)) k (congrArg Subtype.val h), fun x ↦ ?_⟩
  have hx : (x : 𝕊).IsHomogeneous 0 := (mem_homogeneousSubmodule 0 _).mp x.2
  refine ⟨coeff 0 (x : 𝕊), Subtype.ext ?_⟩
  change C (coeff 0 (x : 𝕊)) = (x : 𝕊)
  exact (totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hx.totalDegree_le)).symm

/-- The structure morphism `ℙⁿ_k ⟶ Spec k`: the morphism `Proj S ⟶ Spec S₀` followed by the
identification `S₀ = k`. -/
def projectiveSpaceStructureMorphism : Proj 𝒜 ⟶ Spec (.of k) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒜 0)))

instance : IsIso (CommRingCat.ofHom (algebraMap k (𝒜 0))) :=
  (RingEquiv.ofBijective _ bijective_algebraMap_homogeneousSubmodule_zero).toCommRingCatIso.isIso_hom

/-- `ℙⁿ_k` is of finite type over `k`. -/
theorem finiteType_projectiveSpaceStructureMorphism :
    FiniteType (projectiveSpaceStructureMorphism (k := k) (n := n)) := by
  let σ := Fin (n + 1)
  let _ : IsScalarTower k (𝒜 0) (MvPolynomial σ k) :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := 𝒜 0) (A := MvPolynomial σ k) fun _ ↦ rfl
  let _ : Algebra.FiniteType (𝒜 0) (MvPolynomial σ k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType (R := k) (S := 𝒜 0) (A := MvPolynomial σ k)
  unfold projectiveSpaceStructureMorphism
  exact ⟨inferInstance, inferInstance⟩

instance : IsSeparated (projectiveSpaceStructureMorphism (k := k) (n := n)) := by
  unfold projectiveSpaceStructureMorphism
  infer_instance

end StructureMorphism

section LinearSubspaces

/-- The homogeneous ideal `(x_{m+1}, …, xₙ)` of `k[x₀, …, xₙ]`, spanned by the variables `xᵢ` with
`i > m`. -/
def linearSubspaceIdeal (n m : ℕ) : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) :=
  ⟨Ideal.span (X '' {i : Fin (n + 1) | m < (i : ℕ)}), Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, -, rfl⟩
    exact ⟨1, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X k i)⟩)⟩

theorem linearSubspaceIdeal_toIdeal (n m : ℕ) :
    (linearSubspaceIdeal (k := k) n m).toIdeal =
      Ideal.span (X '' {i : Fin (n + 1) | m < (i : ℕ)}) :=
  rfl

theorem X_mem_linearSubspaceIdeal_iff (m : ℕ) (i : Fin (n + 1)) :
    (X i : 𝕊) ∈ (linearSubspaceIdeal (k := k) n m).toIdeal ↔ m < (i : ℕ) :=
  X_mem_span_X_image_iff _ i

/-- The homogeneous prime `(x_{m+1}, …, xₙ)` as a point of the projective spectrum of
`k[x₀, …, xₙ]`. -/
def linearSubspaceSpectrumPoint (m : ℕ) : ProjectiveSpectrum 𝒜 :=
  ⟨linearSubspaceIdeal n m, isPrime_span_X_image _, fun h ↦ by
    have h0 := (X_mem_linearSubspaceIdeal_iff (k := k) m 0).mp
      (h (X_mem_irrelevant_projectiveSpace 0))
    simp at h0⟩

/-- **The coordinate linear subspace `Lₘ = V(x_{m+1}, …, xₙ)` of `ℙⁿ_k`**, as the point of
`ℙⁿ_k = Proj k[x₀, …, xₙ]` given by the homogeneous prime `(x_{m+1}, …, xₙ)`. For `m ≥ n` it is
the generic point. -/
def linearSubspacePoint (m : ℕ) : Proj 𝒜 :=
  linearSubspaceSpectrumPoint (k := k) (n := n) m

theorem linearSubspacePoint_asHomogeneousIdeal (m : ℕ) :
    (linearSubspacePoint (k := k) (n := n) m).asHomogeneousIdeal = linearSubspaceIdeal n m :=
  rfl

/-- For `m < n`, `L_{m+1} ⊊ Lₘ` as homogeneous primes: `L_{m+1}` specializes to `Lₘ`. -/
theorem linearSubspaceIdeal_succ_lt {m : ℕ} (hm : m < n) :
    linearSubspaceIdeal (k := k) n (m + 1) < linearSubspaceIdeal n m := by
  refine lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ ?_
  · have hsub : (X '' {i : Fin (n + 1) | m + 1 < (i : ℕ)} : Set 𝕊) ⊆
        X '' {i : Fin (n + 1) | m < (i : ℕ)} := by
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨i, ?_, rfl⟩
      change m + 1 < (i : ℕ) at hi
      change m < (i : ℕ)
      omega
    exact (Ideal.span_mono hsub : _ ≤ _) hf
  · have h1 : (X ⟨m + 1, by omega⟩ : 𝕊) ∈ (linearSubspaceIdeal (k := k) n m).toIdeal :=
      (X_mem_linearSubspaceIdeal_iff m _).mpr (Nat.lt_succ_self m)
    rw [← h, X_mem_linearSubspaceIdeal_iff] at h1
    exact lt_irrefl _ h1

theorem linearSubspaceSpectrumPoint_succ_lt {m : ℕ} (hm : m < n) :
    linearSubspaceSpectrumPoint (k := k) (n := n) (m + 1) < linearSubspaceSpectrumPoint m :=
  linearSubspaceIdeal_succ_lt hm

/-- The homogeneous prime of a point of `ℙⁿ_k`, as a point of `Spec k[x₀, …, xₙ]`. -/
def projectiveSpectrumToPrimeSpectrum (x : ProjectiveSpectrum 𝒜) : PrimeSpectrum 𝕊 :=
  ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

theorem strictMono_projectiveSpectrumToPrimeSpectrum :
    StrictMono (projectiveSpectrumToPrimeSpectrum (k := k) (n := n)) :=
  fun _ _ h ↦ h

/-- The irrelevant ideal `(x₀, …, xₙ)`, as a point of `Spec k[x₀, …, xₙ]`. -/
def irrelevantPrimeSpectrum : PrimeSpectrum 𝕊 :=
  ⟨(HomogeneousIdeal.irrelevant 𝒜).toIdeal, by
    rw [HomogeneousIdeal.toIdeal_irrelevant]
    exact RingHom.ker_isPrime _⟩

/-- Every homogeneous prime of `ℙⁿ_k` is properly contained in the irrelevant ideal. -/
theorem projectiveSpectrumToPrimeSpectrum_lt_irrelevant (x : ProjectiveSpectrum 𝒜) :
    projectiveSpectrumToPrimeSpectrum x < irrelevantPrimeSpectrum (k := k) (n := n) := by
  refine lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ x.not_irrelevant_le ?_
  · change f ∈ HomogeneousIdeal.irrelevant 𝒜
    rw [HomogeneousIdeal.mem_irrelevant_iff]
    rw [GradedRing.proj_apply]
    have h0 : (DirectSum.decompose 𝒜 f 0 : 𝕊) ∈ x.asHomogeneousIdeal.toIdeal :=
      (x.asHomogeneousIdeal.isHomogeneous.mem_iff 𝒜).mp hf 0
    obtain ⟨c, hc⟩ := bijective_algebraMap_homogeneousSubmodule_zero.2
      (DirectSum.decompose 𝒜 f 0)
    have hc' : C c = (DirectSum.decompose 𝒜 f 0 : 𝕊) := congrArg Subtype.val hc
    by_contra hne
    rw [← hc'] at h0 hne
    have hc0 : c ≠ 0 := by rintro rfl; simp at hne
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((isUnit_iff_ne_zero.mpr hc0).map C))
  · intro f hf
    change f ∈ (projectiveSpectrumToPrimeSpectrum x).asIdeal
    rw [h]
    exact hf

/-- The polynomial ring `k[x₀, …, xₙ]` has Krull dimension `n + 1`. -/
theorem krullDim_primeSpectrum_mvPolynomial :
    krullDim (PrimeSpectrum 𝕊) = (n + 1 : ℕ) := by
  change ringKrullDim 𝕊 = _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
    Fintype.card_fin, zero_add]

/-- The height plus `1` plus the coheight of a point of `ℙⁿ_k` (computed among homogeneous primes
of `k[x₀, …, xₙ]`) is at most `n + 1`. -/
theorem height_add_coheight_projectiveSpectrumToPrimeSpectrum_le (x : ProjectiveSpectrum 𝒜) :
    height (projectiveSpectrumToPrimeSpectrum x) +
        coheight (projectiveSpectrumToPrimeSpectrum x) ≤ (n + 1 : ℕ) := by
  have h := krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum 𝕊)
  rw [krullDim_primeSpectrum_mvPolynomial] at h
  have h' : (height (projectiveSpectrumToPrimeSpectrum x) +
      coheight (projectiveSpectrumToPrimeSpectrum x) : ℕ∞) ≤
      ⨆ a : PrimeSpectrum 𝕊, height a + coheight a :=
    le_iSup (fun a : PrimeSpectrum 𝕊 ↦ height a + coheight a) _
  have h'' : ((⨆ a : PrimeSpectrum 𝕊, height a + coheight a : ℕ∞) : WithBot ℕ∞) = ((n + 1 : ℕ) : ℕ∞) :=
    h.symm
  exact h'.trans (WithBot.coe_le_coe.mp h''.le)

/-- A point of `ℙⁿ_k` has coheight at least `1` in `Spec k[x₀, …, xₙ]`. -/
theorem one_le_coheight_projectiveSpectrumToPrimeSpectrum (x : ProjectiveSpectrum 𝒜) :
    1 ≤ coheight (projectiveSpectrumToPrimeSpectrum x) := by
  have := coheight_add_one_le (projectiveSpectrumToPrimeSpectrum_lt_irrelevant x)
  exact le_trans (by simp) this

/-- The height of a point of `ℙⁿ_k` (among homogeneous primes) is at most `n`. -/
theorem height_projectiveSpectrum_le (x : ProjectiveSpectrum 𝒜) : height x ≤ n := by
  have h1 := height_le_height_apply_of_strictMono _
    (strictMono_projectiveSpectrumToPrimeSpectrum (k := k) (n := n)) x
  have h2 := height_add_coheight_projectiveSpectrumToPrimeSpectrum_le x
  have h3 := one_le_coheight_projectiveSpectrumToPrimeSpectrum x
  have h4 : height (projectiveSpectrumToPrimeSpectrum x) + 1 ≤ (n + 1 : ℕ) :=
    (add_le_add le_rfl h3).trans h2
  have h5 : height (projectiveSpectrumToPrimeSpectrum x) ≤ n := by
    rw [Nat.cast_add, Nat.cast_one] at h4
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h4
  exact h1.trans h5

/-- The coheight of `Lₘ` in `Spec k[x₀, …, xₙ]` is at least `m + 1` (for `m ≤ n`). -/
theorem coheight_linearSubspaceSpectrumPoint_ge {m : ℕ} (hm : m ≤ n) :
    ((m + 1 : ℕ) : ℕ∞) ≤
      coheight (projectiveSpectrumToPrimeSpectrum (linearSubspaceSpectrumPoint (k := k) (n := n) m)) := by
  induction m with
  | zero => simpa using one_le_coheight_projectiveSpectrumToPrimeSpectrum _
  | succ m ih =>
    have h := coheight_add_one_le (strictMono_projectiveSpectrumToPrimeSpectrum
      (linearSubspaceSpectrumPoint_succ_lt (k := k) (n := n) (m := m) (by omega)))
    refine le_trans ?_ h
    have := ih (by omega)
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add this le_rfl

/-- The height of `Lₘ` among homogeneous primes is at least `n - m`. -/
theorem height_linearSubspaceSpectrumPoint_ge (m : ℕ) :
    ((n - m : ℕ) : ℕ∞) ≤ height (linearSubspaceSpectrumPoint (k := k) (n := n) m) := by
  induction h : n - m generalizing m with
  | zero => simp
  | succ j ih =>
    have hm : m < n := by omega
    have h1 := height_add_one_le (linearSubspaceSpectrumPoint_succ_lt (k := k) (n := n) hm)
    refine le_trans ?_ h1
    have := ih (m + 1) (by omega)
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add this le_rfl

/-- **The height of `Lₘ` is `n - m`** (for `m ≤ n`): the linear subspace `Lₘ` has codimension
`n - m` in `ℙⁿ_k`. -/
theorem height_linearSubspaceSpectrumPoint {m : ℕ} (hm : m ≤ n) :
    height (linearSubspaceSpectrumPoint (k := k) (n := n) m) = (n - m : ℕ) := by
  refine le_antisymm ?_ (height_linearSubspaceSpectrumPoint_ge m)
  have h1 := height_le_height_apply_of_strictMono _
    (strictMono_projectiveSpectrumToPrimeSpectrum (k := k) (n := n))
    (linearSubspaceSpectrumPoint (k := k) (n := n) m)
  have h2 := height_add_coheight_projectiveSpectrumToPrimeSpectrum_le
    (linearSubspaceSpectrumPoint (k := k) (n := n) m)
  have h3 := coheight_linearSubspaceSpectrumPoint_ge (k := k) hm
  refine h1.trans ?_
  have h4 : height (projectiveSpectrumToPrimeSpectrum (linearSubspaceSpectrumPoint (k := k) (n := n) m)) +
      ((m + 1 : ℕ) : ℕ∞) ≤ ((n - m : ℕ) : ℕ∞) + ((m + 1 : ℕ) : ℕ∞) := by
    refine (add_le_add le_rfl h3).trans (h2.trans ?_)
    rw [← Nat.cast_add]
    exact_mod_cast (by omega : n + 1 ≤ n - m + (m + 1))
  exact (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp h4

/-- The homogeneous primes of `ℙⁿ_k` form a poset of Krull dimension `n`. -/
theorem krullDim_projectiveSpectrum : krullDim (ProjectiveSpectrum 𝒜) = n := by
  refine le_antisymm ?_ ?_
  · rw [krullDim_eq_iSup_height]
    exact iSup_le fun x ↦ WithBot.coe_le_coe.mpr (height_projectiveSpectrum_le x)
  · have h := height_le_krullDim (linearSubspaceSpectrumPoint (k := k) (n := n) 0)
    rw [height_linearSubspaceSpectrumPoint (Nat.zero_le n), Nat.sub_zero] at h
    exact h

end LinearSubspaces

section SchemeDimension

/-- The points of the scheme `ℙⁿ_k` with the specialization order (`x ≤ y` when `y ⤳ x`) are the
homogeneous primes of `k[x₀, …, xₙ]` with the reverse inclusion order. -/
def projectiveSpaceOrderIso : Proj 𝒜 ≃o (ProjectiveSpectrum 𝒜)ᵒᵈ where
  toFun x := OrderDual.toDual (show ProjectiveSpectrum 𝒜 from x)
  invFun x := show Proj 𝒜 from OrderDual.ofDual x
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {x y} := by
    change (show ProjectiveSpectrum 𝒜 from y) ≤ (show ProjectiveSpectrum 𝒜 from x) ↔ y ⤳ x
    rw [ProjectiveSpectrum.le_iff_mem_closure, specializes_iff_mem_closure]
    exact Iff.rfl

/-- **`ℙⁿ_k` has dimension `n`.** -/
theorem topologicalKrullDim_projectiveSpace : topologicalKrullDim (Proj 𝒜) = n := by
  rw [topologicalKrullDim, krullDim_eq_of_orderIso irreducibleSetEquivPoints,
    krullDim_eq_of_orderIso projectiveSpaceOrderIso, krullDim_orderDual,
    krullDim_projectiveSpectrum]

/-- The codimension in `ℙⁿ_k` of the closure of a point is the height of its homogeneous prime
among the homogeneous primes of `k[x₀, …, xₙ]`. -/
theorem codim_closure_projectiveSpace_point (x : Proj 𝒜) :
    codim (closure ({x} : Set (Proj 𝒜))) = height (show ProjectiveSpectrum 𝒜 from x) := by
  rw [codim_closure_singleton_eq_coheight, ← coheight_orderIso projectiveSpaceOrderIso x]
  rfl

/-- **The linear subspace `Lₘ` has codimension `n - m` in `ℙⁿ_k`** (for `m ≤ n`). -/
theorem codim_closure_linearSubspacePoint {m : ℕ} (hm : m ≤ n) :
    codim (closure ({linearSubspacePoint (k := k) (n := n) m} : Set (Proj 𝒜))) = (n - m : ℕ) := by
  rw [codim_closure_projectiveSpace_point]
  exact height_linearSubspaceSpectrumPoint hm

end SchemeDimension

section LinearSubspaceDegree

/-- The substitution `k[x₀, …, xₙ] → k[x₀, …, xₘ]` keeping `xᵢ` for `i ≤ m` and killing `xᵢ` for
`i > m`. -/
def linearSubspaceRestrict (n m : ℕ) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (m + 1)) k :=
  aeval fun i ↦ if h : (i : ℕ) ≤ m then X ⟨i, by omega⟩ else 0

theorem linearSubspaceRestrict_rename {m : ℕ} (hm : m ≤ n) (t : MvPolynomial (Fin (m + 1)) k) :
    linearSubspaceRestrict n m (rename (Fin.castLE (by omega)) t) = t := by
  have h : (linearSubspaceRestrict (k := k) n m).comp (rename (Fin.castLE (by omega))) =
      AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro j
    have hj : ¬ m < (j : ℕ) := by
      have := j.isLt
      omega
    simp [linearSubspaceRestrict, hj]
  exact DFunLike.congr_fun h t

theorem linearSubspaceRestrict_surjective {m : ℕ} (hm : m ≤ n) :
    Function.Surjective (linearSubspaceRestrict (k := k) n m) :=
  fun t ↦ ⟨_, linearSubspaceRestrict_rename hm t⟩

theorem ker_linearSubspaceRestrict {m : ℕ} (hm : m ≤ n) :
    RingHom.ker (linearSubspaceRestrict (k := k) n m).toRingHom =
      (linearSubspaceIdeal (k := k) n m).toIdeal := by
  let ι : MvPolynomial (Fin (m + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    rename (Fin.castLE (by omega))
  have hι : Function.Injective ι := rename_injective _ (Fin.castLE_injective _)
  have hcomp : ι.comp (linearSubspaceRestrict n m) =
      aeval fun i ↦ if i ∈ {i : Fin (n + 1) | m < (i : ℕ)} then (0 : 𝕊) else X i := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases hi : (i : ℕ) ≤ m
    · have hi' : ¬ m < (i : ℕ) := by omega
      simp only [AlgHom.comp_apply, linearSubspaceRestrict, aeval_X, dif_pos hi, ι, rename_X]
      rw [if_neg (show i ∉ {i : Fin (n + 1) | m < (i : ℕ)} from hi')]
      congr 1
    · have hi' : m < (i : ℕ) := by omega
      simp [linearSubspaceRestrict, hi, hi', ι]
  rw [linearSubspaceIdeal_toIdeal, ← ker_aeval_ite_eq_span_X_image, ← hcomp]
  ext f
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply]
  exact ⟨fun h ↦ by rw [h, map_zero], fun h ↦ hι (by rw [h, map_zero])⟩

/-- The linear subspace `Lₘ` is a nonempty algebraic set: it contains `[1 : 0 : ⋯ : 0]`. -/
theorem projZeroSet_linearSubspaceIdeal_nonempty (m : ℕ) :
    (projZeroSet ((linearSubspaceIdeal (k := k) n m).toIdeal : Set 𝕊)).Nonempty := by
  classical
  have hv : (Pi.single 0 1 : Fin (n + 1) → k) ≠ 0 := by
    intro h
    simpa using congrFun h 0
  refine ⟨Projectivization.mk k _ hv, fun f hf ↦ ?_⟩
  have hle : (linearSubspaceIdeal (k := k) n m).toIdeal ≤
      RingHom.ker (eval (Projectivization.mk k _ hv).rep) := by
    rw [linearSubspaceIdeal_toIdeal, Ideal.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd hi (by simp)
    have h := (homogeneousVanish_X_iff (k := k) (i := i) hv).mpr (by simp [hi0])
    exact h
  exact hle hf

/-- The homogeneous vanishing ideal of `Lₘ` is `(x_{m+1}, …, xₙ)`. -/
theorem homogeneousVanishingIdeal_linearSubspace [IsAlgClosed k] (m : ℕ) :
    homogeneousVanishingIdeal (projZeroSet ((linearSubspaceIdeal (k := k) n m).toIdeal : Set 𝕊)) =
      (linearSubspaceIdeal (k := k) n m).toIdeal := by
  rw [homogeneousVanishingIdeal_projZeroSet (linearSubspaceIdeal n m).isHomogeneous
    (projZeroSet_linearSubspaceIdeal_nonempty m)]
  exact (isPrime_span_X_image _).radical

/-- The Hilbert function of `Lₘ ≅ ℙᵐ` in degree `l ≥ 0` is `choose (l + m) m`. -/
theorem hilbertFunction_linearSubspace [IsAlgClosed k] {m : ℕ} (hm : m ≤ n) (l : ℕ) :
    hilbertFunction (k := k) (σ := Fin (n + 1))
        (integerProjCoordGrading
          (projZeroSet ((linearSubspaceIdeal (k := k) n m).toIdeal : Set 𝕊))) (l : ℤ) =
      (l + m).choose m := by
  rw [hilbertFunction, integerProjCoordGrading_ofNat]
  set Y := projZeroSet ((linearSubspaceIdeal (k := k) n m).toIdeal : Set 𝕊)
  have hI : homogeneousVanishingIdeal Y = RingHom.ker (linearSubspaceRestrict (k := k) n m).toRingHom := by
    rw [homogeneousVanishingIdeal_linearSubspace, ker_linearSubspaceRestrict hm]
  let e : homogeneousCoordinateRing Y ≃ₐ[k] MvPolynomial (Fin (m + 1)) k :=
    (Ideal.quotientEquivAlgOfEq k hI).trans
      (Ideal.quotientKerAlgEquivOfSurjective (linearSubspaceRestrict_surjective hm))
  have he : ∀ p : 𝕊, e (Ideal.Quotient.mk _ p) = linearSubspaceRestrict n m p := fun p ↦ rfl
  have hmap : (projCoordGrading Y l).map e.toLinearEquiv.toLinearMap =
      MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k l := by
    ext t
    constructor
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      change e (Ideal.Quotient.mk _ p) ∈ _
      rw [he, mem_homogeneousSubmodule]
      have hp' : p.IsHomogeneous l := (mem_homogeneousSubmodule l p).mp hp
      have h := hp'.eval₂ (algebraMap k (MvPolynomial (Fin (m + 1)) k))
        (fun i : Fin (n + 1) ↦ if h : (i : ℕ) ≤ m then (X ⟨i, by omega⟩ : MvPolynomial (Fin (m + 1)) k) else 0)
        (fun r ↦ isHomogeneous_C _ r) (fun i ↦ by
          by_cases h : (i : ℕ) ≤ m
          · simp only [dif_pos h]
            exact isHomogeneous_X k _
          · simp only [dif_neg h]
            exact isHomogeneous_zero _ _ _)
      rw [one_mul] at h
      exact h
    · intro ht
      refine ⟨Ideal.Quotient.mk _ (rename (Fin.castLE (by omega)) t), ⟨_, ?_, rfl⟩, ?_⟩
      · exact (mem_homogeneousSubmodule l _).mpr
          (((mem_homogeneousSubmodule l t).mp ht).rename_isHomogeneous)
      · change e (Ideal.Quotient.mk _ _) = t
        rw [he, linearSubspaceRestrict_rename hm]
  calc Module.finrank k (projCoordGrading Y l) =
        Module.finrank k ((projCoordGrading Y l).map e.toLinearEquiv.toLinearMap) :=
      (e.toLinearEquiv.finrank_map_eq _).symm
    _ = Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) k l) := by rw [hmap]
    _ = (l + m).choose m := finrank_homogeneousSubmodule m l

/-- **The linear subspace `Lₘ` has degree `1`** (for `m ≤ n`, `k` algebraically closed): its
Hilbert polynomial is `z ↦ choose (z + m) m`, with leading coefficient `1 / m!`. -/
theorem projectiveSpectrumPointDegree_linearSubspacePoint [IsAlgClosed k] {m : ℕ} (hm : m ≤ n) :
    projectiveSpectrumPointDegree (linearSubspacePoint (k := k) (n := n) m) = 1 := by
  set Y := projZeroSet ((linearSubspaceIdeal (k := k) n m).toIdeal : Set 𝕊)
  have hpoly : IsHilbertPolynomial (σ := Fin (n + 1)) (integerProjCoordGrading Y)
      ((numericalBinomial m).taylor (m : ℚ)) :=
    translatedNumericalBinomial_isHilbertPolynomial _ m (hilbertFunction_linearSubspace hm)
  have hP : projectiveHilbertPolynomial Y = (numericalBinomial m).taylor (m : ℚ) :=
    isHilbertPolynomial_unique (integerProjCoordGrading Y)
      (projectiveHilbertPolynomial_isHilbertPolynomial Y) hpoly
  have hdeg : projectiveDegree Y = 1 := by
    rw [projectiveDegree, hP, Polynomial.natDegree_taylor, numericalBinomial_natDegree,
      Polynomial.leadingCoeff_taylor, numericalBinomial_leadingCoeff]
    exact mul_inv_cancel₀ (by positivity)
  have h := projectiveSpectrumPointDegree_cast (linearSubspacePoint (k := k) (n := n) m)
  change _ = projectiveDegree Y at h
  rw [hdeg] at h
  exact_mod_cast h

end LinearSubspaceDegree

section Cycles

open scoped Classical in
/-- The cycle `1 · [V]` of the integral closed subset `V = closure {x}` of a scheme, when `V` has
codimension `r`. -/
def pointCodimensionCycle {X : Scheme.{u}} (x : X) {r : ℕ}
    (hx : codim (closure ({x} : Set X)) = r) : codimensionCycles X r :=
  ⟨Function.locallyFinsuppWithin.single x 1, by
    have hsupp : ∀ y, (Function.locallyFinsuppWithin.single x (1 : ℤ) : AlgebraicCycle X ℤ) y ≠ 0 →
        y = x := by
      intro y hy
      by_contra h
      exact hy (by simp [Function.locallyFinsuppWithin.single_apply, h])
    refine ⟨(Set.finite_singleton x).subset fun y hy ↦ hsupp y hy, fun y hy ↦ ?_⟩
    rw [hsupp y hy]
    exact hx⟩

open scoped Classical in
theorem pointCodimensionCycle_apply {X : Scheme.{u}} (x : X) {r : ℕ}
    (hx : codim (closure ({x} : Set X)) = r) (y : X) :
    (pointCodimensionCycle x hx : AlgebraicCycle X ℤ) y = if y = x then 1 else 0 := by
  change Function.locallyFinsuppWithin.single x (1 : ℤ) y = _
  rw [Function.locallyFinsuppWithin.single_apply]

/-- The point of `ℙⁿ_k` of codimension zero is the generic point `Lₙ`. -/
theorem eq_linearSubspacePoint_of_codim_eq_zero {y : Proj 𝒜}
    (hy : codim (closure ({y} : Set (Proj 𝒜))) = 0) :
    y = linearSubspacePoint (k := k) (n := n) n := by
  rw [codim_closure_projectiveSpace_point, height_eq_zero] at hy
  have hle : linearSubspaceSpectrumPoint (k := k) (n := n) n ≤ (show ProjectiveSpectrum 𝒜 from y) := by
    intro f hf
    change f ∈ Ideal.span (X '' {i : Fin (n + 1) | n < (i : ℕ)}) at hf
    have hempty : {i : Fin (n + 1) | n < (i : ℕ)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun i hi ↦ by
        change n < (i : ℕ) at hi
        omega
    rw [hempty, Set.image_empty, Ideal.span_empty, Ideal.mem_bot] at hf
    rw [hf]
    exact zero_mem _
  exact (hy.eq_of_le hle).symm

/-- **Hartshorne A, Exercise 6.3, the case of codimension zero.** For `k` algebraically closed, an
integral subvariety `Y = closure {y}` of `ℙⁿ_k` of codimension zero (dimension `n`) is rationally
equivalent to `deg Y · [Lₙ]`; indeed `Y = Lₙ = ℙⁿ_k` and `deg Y = 1`. -/
theorem rationallyEquivalent_degree_smul_linearSubspace_of_codim_eq_zero [IsAlgClosed k]
    {y : Proj 𝒜} (hy : codim (closure ({y} : Set (Proj 𝒜))) = (0 : ℕ)) :
    RationallyEquivalent projectiveSpaceStructureMorphism
      finiteType_projectiveSpaceStructureMorphism topologicalKrullDim_projectiveSpace
      (pointCodimensionCycle y hy)
      (projectiveSpectrumPointDegree y •
        pointCodimensionCycle (linearSubspacePoint (k := k) (n := n) n)
          ((codim_closure_linearSubspacePoint le_rfl).trans (by rw [Nat.sub_self]))) := by
  obtain rfl := eq_linearSubspacePoint_of_codim_eq_zero (k := k) (n := n) (by exact_mod_cast hy)
  rw [projectiveSpectrumPointDegree_linearSubspacePoint le_rfl, one_smul, RationallyEquivalent,
    sub_self]
  exact zero_mem _

/-- For `n ≥ 1`, the hyperplane `V(xₙ)` of `ℙⁿ_k` is the linear subspace `L_{n-1}`. -/
theorem projectiveHyperplanePrimeDivisor_X_last (hn : 0 < n) :
    (projectiveHyperplanePrimeDivisor hn (isHomogeneous_X k (Fin.last n))
      (X_ne_zero (Fin.last n))).1 = linearSubspacePoint (k := k) (n := n) (n - 1) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.toIdeal_injective
  rw [projectiveHyperplanePrimeDivisor, projectiveHypersurfacePrimeDivisor_asHomogeneousIdeal,
    linearSubspacePoint_asHomogeneousIdeal, linearSubspaceIdeal_toIdeal]
  have hset : {i : Fin (n + 1) | n - 1 < (i : ℕ)} = {Fin.last n} := by
    ext i
    simp only [Set.mem_singleton_iff, Fin.ext_iff, Fin.val_last]
    change n - 1 < (i : ℕ) ↔ _
    have := i.2
    omega
  rw [hset, Set.image_singleton]

/-- **Hartshorne A, Exercise 6.3, the case of codimension one.** For `k` algebraically closed and
`n ≥ 1`, an integral hypersurface `Y = closure {y}` of `ℙⁿ_k`, of degree `d`, is rationally
equivalent to `d · [L_{n-1}]`, where `L_{n-1} = V(xₙ)` is a hyperplane. This combines
Hartshorne II.6.4 (`Y ∼ d · H`) with the agreement of rational and linear equivalence in
codimension one on the normal variety `ℙⁿ_k`. -/
theorem rationallyEquivalent_degree_smul_linearSubspace_of_codim_eq_one [IsAlgClosed k]
    (hn : 0 < n) {y : Proj 𝒜} (hy : codim (closure ({y} : Set (Proj 𝒜))) = (1 : ℕ)) :
    RationallyEquivalent projectiveSpaceStructureMorphism
      finiteType_projectiveSpaceStructureMorphism topologicalKrullDim_projectiveSpace
      (pointCodimensionCycle y hy)
      (projectiveSpectrumPointDegree y •
        pointCodimensionCycle (linearSubspacePoint (k := k) (n := n) (n - 1))
          ((codim_closure_linearSubspacePoint (Nat.sub_le n 1)).trans
            (by rw [Nat.sub_sub_self hn]))) := by
  have : IsNormal (Proj 𝒜) := isNormal_of_isRegular projectiveSpace_isRegular
  have hcoh : coheight y = 1 := by
    rw [← codim_closure_singleton_eq_coheight]
    exact_mod_cast hy
  let P : (Proj 𝒜).PrimeDivisor := ⟨y, hcoh⟩
  let H := projectiveHyperplanePrimeDivisor hn (isHomogeneous_X k (Fin.last n))
    (X_ne_zero (Fin.last n))
  have hH : H.1 = linearSubspacePoint (k := k) (n := n) (n - 1) :=
    projectiveHyperplanePrimeDivisor_X_last hn
  have hcycle : ∀ (Q : (Proj 𝒜).PrimeDivisor) (h : codim (closure ({Q.1} : Set (Proj 𝒜))) =
      (1 : ℕ)), pointCodimensionCycle Q.1 h = weilDivisorToCodimOneCycles
        (satisfiesConditionStar_of_isNormal_of_finiteType projectiveSpaceStructureMorphism
          finiteType_projectiveSpaceStructureMorphism) Q.toWeilDivisor := by
    intro Q h
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    rw [pointCodimensionCycle_apply, coe_weilDivisorToCodimOneCycles]
    by_cases hx : x = Q.1
    · rw [if_pos hx, hx, Q.toWeilDivisor_apply_self]
    · rw [if_neg hx, Q.toWeilDivisor_apply_of_ne hx]
  have hY := hcycle P hy
  have hL : pointCodimensionCycle (linearSubspacePoint (k := k) (n := n) (n - 1))
      ((codim_closure_linearSubspacePoint (Nat.sub_le n 1)).trans
        (by rw [Nat.sub_sub_self hn])) =
      weilDivisorToCodimOneCycles
        (satisfiesConditionStar_of_isNormal_of_finiteType projectiveSpaceStructureMorphism
          finiteType_projectiveSpaceStructureMorphism) H.toWeilDivisor := by
    have h := hcycle H (by rw [hH, codim_closure_linearSubspacePoint (Nat.sub_le n 1),
      Nat.sub_sub_self hn])
    convert h using 2
    rw [hH]
  have hdeg : projectiveSpectrumPointDegree y = projectiveSpaceWeilDivisorDegree P.toWeilDivisor := by
    rw [projectiveSpaceWeilDivisorDegree_toWeilDivisor]
    exact projectiveSpectrumPointDegree_primeDivisor hn P
  rw [hY, hL, ← map_zsmul, rationallyEquivalent_weilDivisorToCodimOneCycles_iff, hdeg]
  exact projectiveSpace_linearEquivalent_degree_smul_hyperplane hn _ _ P.toWeilDivisor

/-- The degree of a codimension-`r` cycle `∑ nᵢ [Yᵢ]` on `ℙⁿ_k`: `∑ nᵢ deg Yᵢ`, where `deg Yᵢ` is
the projective degree of `Yᵢ`. -/
def cycleProjectiveDegree [IsAlgClosed k] (r : ℕ) : codimensionCycles (Proj 𝒜) r →+ ℤ where
  toFun c := ∑ᶠ x : Proj 𝒜, (c : AlgebraicCycle (Proj 𝒜) ℤ) x * projectiveSpectrumPointDegree x
  map_zero' := by simp
  map_add' c d := by
    have hfin : ∀ e : codimensionCycles (Proj 𝒜) r, (Function.support fun x : Proj 𝒜 ↦
        (e : AlgebraicCycle (Proj 𝒜) ℤ) x * projectiveSpectrumPointDegree x).Finite :=
      fun e ↦ e.2.1.subset fun x hx ↦ left_ne_zero_of_mul hx
    simp only [AddSubgroup.coe_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_mul]
    exact finsum_add_distrib (hfin c) (hfin d)

/-- The degree of the cycle `1 · [closure {x}]` is the projective degree of `closure {x}`. -/
theorem cycleProjectiveDegree_pointCodimensionCycle [IsAlgClosed k] {x : Proj 𝒜} {r : ℕ}
    (hx : codim (closure ({x} : Set (Proj 𝒜))) = r) :
    cycleProjectiveDegree r (pointCodimensionCycle x hx) = projectiveSpectrumPointDegree x := by
  change ∑ᶠ y : Proj 𝒜, (pointCodimensionCycle x hx : AlgebraicCycle (Proj 𝒜) ℤ) y *
    projectiveSpectrumPointDegree y = _
  rw [finsum_eq_single _ x]
  · rw [pointCodimensionCycle_apply, if_pos rfl, one_mul]
  · intro y hy
    rw [pointCodimensionCycle_apply, if_neg hy, zero_mul]

/-- **Reduction of Hartshorne A, Exercise 6.3, to its two missing inputs.** Let `k` be
algebraically closed and `Y = closure {y}` an integral subvariety of `ℙⁿ_k` of dimension `m`.
Suppose that degree vanishes on the rational-equivalence subgroup in codimension `n - m`, and that
`[Y]` is rationally equivalent to some integer multiple of `[Lₘ]`. Then `[Y]` is rationally
equivalent to `deg Y · [Lₘ]`, because `deg Lₘ = 1`. -/
theorem rationallyEquivalent_degree_smul_linearSubspace_of_exists [IsAlgClosed k] {m : ℕ}
    (hm : m ≤ n) {y : Proj 𝒜} (hy : codim (closure ({y} : Set (Proj 𝒜))) = (n - m : ℕ))
    (hdeg : ∀ c ∈ rationalEquivalenceSubgroup projectiveSpaceStructureMorphism
      finiteType_projectiveSpaceStructureMorphism topologicalKrullDim_projectiveSpace (n - m),
      cycleProjectiveDegree (k := k) (n := n) (n - m) c = 0)
    (hgen : ∃ a : ℤ, RationallyEquivalent projectiveSpaceStructureMorphism
      finiteType_projectiveSpaceStructureMorphism topologicalKrullDim_projectiveSpace
      (pointCodimensionCycle y hy)
      (a • pointCodimensionCycle (linearSubspacePoint (k := k) (n := n) m)
        (codim_closure_linearSubspacePoint hm))) :
    RationallyEquivalent projectiveSpaceStructureMorphism
      finiteType_projectiveSpaceStructureMorphism topologicalKrullDim_projectiveSpace
      (pointCodimensionCycle y hy)
      (projectiveSpectrumPointDegree y •
        pointCodimensionCycle (linearSubspacePoint (k := k) (n := n) m)
          (codim_closure_linearSubspacePoint hm)) := by
  obtain ⟨a, ha⟩ := hgen
  have h := hdeg _ ha
  rw [map_sub, map_zsmul, cycleProjectiveDegree_pointCodimensionCycle,
    cycleProjectiveDegree_pointCodimensionCycle,
    projectiveSpectrumPointDegree_linearSubspacePoint hm, smul_eq_mul, mul_one,
    sub_eq_zero] at h
  rwa [h]

end Cycles
