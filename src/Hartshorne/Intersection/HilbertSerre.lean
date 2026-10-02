/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.PrimeFiltrationSupport
import Hartshorne.Intersection.HilbertFunction
import Hartshorne.Intersection.NumericalAntidifference
import Hartshorne.Intersection.AffineConeDimension
import Hartshorne.Intersection.ProjectiveDimensionTheorem
import Hartshorne.Intersection.ProjectiveIntersectionNonempty
import Hartshorne.Intersection.ProjectiveCodimensionOne
import Hartshorne.Projective.Correspondence
import Hartshorne.Projective.PointIdeal
import Hartshorne.Projective.ProjSpaceDimension
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Hilbert--Serre

Hartshorne, *Algebraic Geometry*, Theorem I.7.5 (pp. 51--52).
-/

namespace Hartshorne

open DirectSum Filter Finset MvPolynomial Polynomial Set TopologicalSpace
open scoped Polynomial

noncomputable section

universe u v w

/-- The degree convention for Hilbert polynomials: the zero polynomial has
degree `-1`, represented by `⊥`. -/
def hilbertPolynomialDegree (P : ℚ[X]) : WithBot ℕ∞ :=
  if P = 0 then ⊥ else (P.natDegree : WithBot ℕ∞)

/-- A polynomial which eventually represents the Hilbert function of a
graded module. -/
def IsHilbertPolynomial {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M] (P : ℚ[X]) : Prop :=
  IsNumericalPolynomial P ∧
    ∀ᶠ d : ℤ in atTop,
      P.eval (d : ℚ) = (hilbertFunction (σ := σ) ℳ d : ℚ)

/-- Existence, dimension, and the positivity statement needed to prevent
cancellation in a prime-filtration sum. -/
private def HasHilbertData {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M] : Prop :=
  ∃ P : ℚ[X], IsHilbertPolynomial (σ := σ) ℳ P ∧
    hilbertPolynomialDegree P =
      projDim (projZeroSet
        (Module.annihilator (MvPolynomial σ k) M : Set (MvPolynomial σ k))) ∧
    ((projZeroSet
      (Module.annihilator (MvPolynomial σ k) M : Set (MvPolynomial σ k))).Nonempty →
        0 < P.leadingCoeff)

private theorem isNumericalPolynomial_zero :
    IsNumericalPolynomial (0 : ℚ[X]) := by
  rw [IsNumericalPolynomial]
  exact Filter.Eventually.of_forall fun _ => ⟨0, by simp⟩

private theorem IsNumericalPolynomial.add {P Q : ℚ[X]}
    (hP : IsNumericalPolynomial P) (hQ : IsNumericalPolynomial Q) :
    IsNumericalPolynomial (P + Q) := by
  rw [IsNumericalPolynomial]
  filter_upwards [hP, hQ] with n hnP hnQ
  obtain ⟨a, ha⟩ := hnP
  obtain ⟨b, hb⟩ := hnQ
  exact ⟨a + b, by simp [ha, hb]⟩

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

private theorem IsNumericalPolynomial.finset_sum
    {ι : Type*} {s : Finset ι} {P : ι → ℚ[X]}
    (hP : ∀ i ∈ s, IsNumericalPolynomial (P i)) :
    IsNumericalPolynomial (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isNumericalPolynomial_zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hP a (Finset.mem_insert_self _ _)).add <|
        ih fun i hi => hP i (Finset.mem_insert_of_mem hi)

private theorem hilbertPolynomialDegree_eq_bot_iff (P : ℚ[X]) :
    hilbertPolynomialDegree P = ⊥ ↔ P = 0 := by
  simp [hilbertPolynomialDegree]

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

private theorem HasHilbertData.twist
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    (h : HasHilbertData (σ := σ) ℳ) (l : ℤ) :
    HasHilbertData (σ := σ) (gradedModuleTwist ℳ l) := by
  obtain ⟨P, hP, hdeg, hlc⟩ := h
  refine ⟨P.taylor (l : ℚ), hP.twist ℳ l, ?_, ?_⟩
  · unfold hilbertPolynomialDegree
    simp only [Polynomial.taylor_eq_zero, Polynomial.natDegree_taylor]
    exact hdeg
  · intro hne
    rw [Polynomial.leadingCoeff_taylor]
    exact hlc hne

private theorem finset_sum_polynomial_degree
    {ι : Type*} (s : Finset ι) (P : ι → ℚ[X]) (r : ℕ)
    (hdeg : ∀ i ∈ s, (P i).natDegree ≤ r)
    (hnonneg : ∀ i ∈ s, 0 ≤ (P i).coeff r)
    (hpos : ∃ i ∈ s, 0 < (P i).coeff r) :
    (∑ i ∈ s, P i).natDegree = r ∧
      0 < (∑ i ∈ s, P i).leadingCoeff := by
  classical
  have hcoeff : 0 < (∑ i ∈ s, P i).coeff r := by
    rw [Polynomial.finsetSum_coeff]
    exact Finset.sum_pos' hnonneg hpos
  have hle : (∑ i ∈ s, P i).natDegree ≤ r :=
    Polynomial.natDegree_sum_le_of_forall_le s P hdeg
  have hge : r ≤ (∑ i ∈ s, P i).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff.ne'
  have heq := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  rw [Polynomial.leadingCoeff, heq]
  exact hcoeff

private theorem projDim_empty
    {k : Type u} [Field k] {σ : Type*} :
    projDim (∅ : Set (ProjectiveSpace k σ)) = ⊥ := by
  unfold projDim topologicalKrullDim
  letI : IsEmpty
      (IrreducibleCloseds (↥(∅ : Set (ProjectiveSpace k σ)))) :=
    ⟨fun Z => Z.2.1.nonempty.elim fun x => x.2⟩
  exact Order.krullDim_eq_bot

private theorem projDim_ne_bot_of_nonempty
    {k : Type u} [Field k] {σ : Type*}
    {Y : Set (ProjectiveSpace k σ)} (hY : Y.Nonempty) : projDim Y ≠ ⊥ := by
  unfold projDim topologicalKrullDim
  rw [Order.krullDim_ne_bot_iff]
  obtain ⟨y, hy⟩ := hY
  let y' : Y := ⟨y, hy⟩
  exact ⟨⟨irreducibleComponent y', isIrreducible_irreducibleComponent,
    isClosed_irreducibleComponent⟩⟩

private theorem polynomial_eq_of_eventually_eval_eq {P Q : ℚ[X]}
    (h : ∀ᶠ d : ℤ in atTop, P.eval (d : ℚ) = Q.eval (d : ℚ)) : P = Q := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  apply Polynomial.eq_of_infinite_eval_eq
  let T : Set ℚ := (fun n : ℕ => (n : ℚ)) '' Set.Ioi N.natAbs
  have hT : T.Infinite :=
    (Set.Ioi_infinite N.natAbs).image
      (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℚ))).injOn
  refine hT.mono ?_
  rintro x ⟨n, hn, rfl⟩
  apply hN (n : ℤ)
  have hNabs : N ≤ (N.natAbs : ℤ) := Int.le_natAbs
  exact hNabs.trans (by exact_mod_cast hn.le)

/-- A graded linear equivalence restricts to a linear equivalence on every
homogeneous piece. -/
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

private theorem quotientXMem
    {k : Type u} [Field k] {σ : Type*}
    (p : Ideal (MvPolynomial σ k))
    (hp : p.IsHomogeneous (integerHomogeneousSubmodule k σ)) (i : σ) :
    (Submodule.Quotient.mk (MvPolynomial.X i) : MvPolynomial σ k ⧸ p) ∈
      gradedQuotientPiece
        (integerHomogeneousSubmodule k σ)
        (integerHomogeneousSubmodule k σ)
        (homogeneousIdealSubmodule (integerHomogeneousSubmodule k σ) p hp) 1 :=
  ⟨MvPolynomial.X i, isHomogeneous_X k i, rfl⟩

/-- The homogeneous cyclic submodule generated by the class of `X i` in a
homogeneous quotient of the polynomial ring. -/
private noncomputable def quotientXSubmodule
    {k : Type u} [Field k] {σ : Type*}
    (p : Ideal (MvPolynomial σ k))
    (hp : p.IsHomogeneous (integerHomogeneousSubmodule k σ)) (i : σ) :=
  gradedCyclicSubmodule
    (integerHomogeneousSubmodule k σ)
    (gradedQuotientPiece
      (integerHomogeneousSubmodule k σ)
      (integerHomogeneousSubmodule k σ)
      (homogeneousIdealSubmodule (integerHomogeneousSubmodule k σ) p hp))
    (quotientXMem p hp i)

private theorem torsionOf_quotientX_eq
    {k : Type u} [Field k] {σ : Type*}
    (p : PrimeSpectrum (MvPolynomial σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ p.1) :
    Ideal.torsionOf (MvPolynomial σ k) (MvPolynomial σ k ⧸ p.1)
      (Submodule.Quotient.mk (MvPolynomial.X i)) = p.1 := by
  ext f
  rw [Ideal.mem_torsionOf_iff]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  change f * MvPolynomial.X i ∈ p.1 ↔ f ∈ p.1
  constructor
  · intro hf
    exact (p.2.mem_or_mem hf).resolve_right hi
  · exact fun hf => p.1.mul_mem_right _ hf

private theorem quotientXSubmodule_toSubmodule
    {k : Type u} [Field k] {σ : Type*}
    (p : Ideal (MvPolynomial σ k))
    (hp : p.IsHomogeneous (integerHomogeneousSubmodule k σ)) (i : σ) :
    (quotientXSubmodule p hp i).toSubmodule =
      Submodule.map
        (homogeneousIdealSubmodule
          (integerHomogeneousSubmodule k σ) p hp).toSubmodule.mkQ
        (Ideal.span ({MvPolynomial.X i} : Set (MvPolynomial σ k))) := by
  simp [quotientXSubmodule, gradedCyclicSubmodule, Submodule.map_span]
  rfl

private theorem annihilator_quotientXSubmodule_eq
    {k : Type u} [Field k] {σ : Type*}
    (p : Ideal (MvPolynomial σ k))
    (hp : p.IsHomogeneous (integerHomogeneousSubmodule k σ)) (i : σ) :
    Module.annihilator (MvPolynomial σ k)
        ((MvPolynomial σ k ⧸
            (homogeneousIdealSubmodule
              (integerHomogeneousSubmodule k σ) p hp).toSubmodule) ⧸
          (quotientXSubmodule p hp i).toSubmodule) =
      p ⊔ Ideal.span ({MvPolynomial.X i} : Set (MvPolynomial σ k)) := by
  rw [quotientXSubmodule_toSubmodule]
  let e := Submodule.quotientQuotientEquivQuotientSup
    (homogeneousIdealSubmodule (integerHomogeneousSubmodule k σ) p hp).toSubmodule
    (Ideal.span ({MvPolynomial.X i} : Set (MvPolynomial σ k)) :
      Submodule (MvPolynomial σ k) (MvPolynomial σ k))
  rw [e.annihilator_eq]
  exact Ideal.annihilator_quotient

/-- The coordinate hyperplane exact sequence on a homogeneous prime quotient,
expressed as an equality of Hilbert functions. -/
private theorem hilbertFunction_primeQuotient_eq_pred_add
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    (p : PrimeSpectrum (MvPolynomial σ k))
    (hp : p.1.IsHomogeneous (integerHomogeneousSubmodule k σ))
    (i : σ) (hi : MvPolynomial.X i ∉ p.1) (d : ℤ) :
    let ℱ := gradedQuotientPiece
      (integerHomogeneousSubmodule k σ)
      (integerHomogeneousSubmodule k σ)
      (homogeneousIdealSubmodule (integerHomogeneousSubmodule k σ) p.1 hp)
    let N := quotientXSubmodule p.1 hp i
    hilbertFunction (σ := σ) ℱ d =
      hilbertFunction (σ := σ) ℱ (d - 1) +
        hilbertFunction (σ := σ)
          (gradedQuotientPiece (integerHomogeneousSubmodule k σ) ℱ N) d := by
  dsimp only
  let 𝓐 := integerHomogeneousSubmodule k σ
  let ℱ := gradedQuotientPiece 𝓐 𝓐
    (homogeneousIdealSubmodule 𝓐 p.1 hp)
  let hx := quotientXMem p.1 hp i
  let N := quotientXSubmodule p.1 hp i
  have htor := torsionOf_quotientX_eq p i hi
  have hT : gradedTorsionSubmodule 𝓐 ℱ hx =
      homogeneousIdealSubmodule 𝓐 p.1 hp := by
    ext f
    exact SetLike.ext_iff.mp htor f
  let e := gradedCyclicModuleEquiv 𝓐 ℱ hx
  rw [hT] at e
  change GradedLinearEquiv (MvPolynomial σ k)
    (gradedModuleTwist ℱ (-1))
    (gradedSubmodulePiece 𝓐 ℱ N) at e
  have hN : hilbertFunction (σ := σ) (gradedModuleTwist ℱ (-1)) d =
      hilbertFunction (σ := σ) (gradedSubmodulePiece 𝓐 ℱ N) d := by
    unfold hilbertFunction
    exact LinearEquiv.finrank_eq <|
      e.pieceLinearEquivOfCompatibleSMul
        (fun r x => mvPolynomialQuotient_algebraMap_smul
          (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule r x)
        (fun r x => IsScalarTower.algebraMap_smul
          (R := k) (A := MvPolynomial σ k) r x) d
  have hsub := hilbertFunction_subquotient (σ := σ) ℱ N d
  rw [← hN, hilbertFunction_twist] at hsub
  simpa [ℱ, N, 𝓐, sub_eq_add_neg] using hsub

/-- A homogeneous prime quotient with empty projective support has eventually
zero Hilbert function. -/
private theorem primeQuotient_hasHilbertData_of_empty
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
    (hp : p.1.IsHomogeneous
      (integerHomogeneousSubmodule k (Fin (n + 1))))
    (hempty : projZeroSet
      (p.1 : Set (MvPolynomial (Fin (n + 1)) k)) = ∅) :
    HasHilbertData (σ := Fin (n + 1))
      (gradedQuotientPiece
        (integerHomogeneousSubmodule k (Fin (n + 1)))
        (integerHomogeneousSubmodule k (Fin (n + 1)))
        (homogeneousIdealSubmodule
          (integerHomogeneousSubmodule k (Fin (n + 1))) p.1 hp)) := by
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let ℱ := gradedQuotientPiece 𝓐 𝓐
    (homogeneousIdealSubmodule 𝓐 p.1 hp)
  have hpHomNat : IsHomogeneousIdeal p.1 :=
    (ideal_isHomogeneous_integer_iff
      (k := k) (σ := Fin (n + 1)) p.1).mp hp
  have hirrel : irrelevantIdeal k (Fin (n + 1)) ≤ p.1 := by
    rw [← p.2.radical]
    exact (projZeroSet_eq_empty_iff hpHomNat).mp hempty
  have hzero : IsHilbertPolynomial (σ := Fin (n + 1)) ℱ 0 := by
    refine ⟨isNumericalPolynomial_zero,
      Filter.eventually_atTop.mpr ⟨1, fun d hd => ?_⟩⟩
    have hd0 : 0 ≤ d := by omega
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hd0
    have hm : 0 < m := by exact_mod_cast hd
    letI : Subsingleton (ℱ (m : ℤ)) := ⟨fun x y => by
      apply Subtype.ext
      have hqzero : ∀ z : ℱ (m : ℤ),
          (z : MvPolynomial (Fin (n + 1)) k ⧸
            (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule) = 0 := by
        intro z
        obtain ⟨f, hf, hfz⟩ := z.property
        rw [← hfz]
        apply (Submodule.Quotient.mk_eq_zero
          (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule).mpr
        apply hirrel
        have heval : eval (0 : Fin (n + 1) → k) f = 0 := by
          rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
          exact hf.coeff_eq_zero (by simpa using hm.ne)
        have hmem := sub_C_eval_zero_mem_irrelevantIdeal f
        rwa [heval, map_zero, sub_zero] at hmem
      exact (hqzero x).trans (hqzero y).symm⟩
    simp only [Polynomial.eval_zero]
    exact_mod_cast Module.finrank_zero_of_subsingleton.symm
  refine ⟨0, hzero, ?_, ?_⟩
  · rw [Ideal.annihilator_quotient]
    change hilbertPolynomialDegree 0 =
      projDim (projZeroSet (p.1 : Set (MvPolynomial (Fin (n + 1)) k)))
    rw [hempty]
    change ⊥ = topologicalKrullDim
      (↥(∅ : Set (ProjectiveSpace k (Fin (n + 1)))))
    unfold topologicalKrullDim
    letI : IsEmpty
        (IrreducibleCloseds (↥(∅ : Set (ProjectiveSpace k (Fin (n + 1)))))) :=
      ⟨fun Z => Z.2.1.nonempty.elim fun x => x.2⟩
    exact Order.krullDim_eq_bot.symm
  · rw [Ideal.annihilator_quotient]
    change (projZeroSet
      (p.1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty → _
    simpa [hempty]

private theorem hilbertFunction_eq_of_gradedLinearEquiv
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
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

/-- The same homogeneous submodule, first viewed in `M` and then in a larger
homogeneous submodule, has the same graded module structure. -/
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

theorem isHilbertPolynomial_unique
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    {P Q : ℚ[X]} (hP : IsHilbertPolynomial (σ := σ) ℳ P)
    (hQ : IsHilbertPolynomial (σ := σ) ℳ Q) : P = Q := by
  apply polynomial_eq_of_eventually_eval_eq
  filter_upwards [hP.2, hQ.2] with d hdP hdQ
  exact hdP.trans hdQ.symm

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

private theorem projZeroSet_sup
    {k : Type u} [Field k] {σ : Type*}
    (I J : Ideal (MvPolynomial σ k)) :
    projZeroSet ((I ⊔ J : Ideal (MvPolynomial σ k)) : Set (MvPolynomial σ k)) =
      projZeroSet (I : Set (MvPolynomial σ k)) ∩
        projZeroSet (J : Set (MvPolynomial σ k)) := by
  calc
    projZeroSet ((I ⊔ J : Ideal (MvPolynomial σ k)) : Set (MvPolynomial σ k)) =
        projZeroSet
          (Ideal.span ((I : Set (MvPolynomial σ k)) ∪
            (J : Set (MvPolynomial σ k))) : Set (MvPolynomial σ k)) := by
      rw [Ideal.span_union, Ideal.span_eq, Ideal.span_eq]
    _ = projZeroSet
        ((I : Set (MvPolynomial σ k)) ∪ (J : Set (MvPolynomial σ k))) :=
      projZeroSet_span _
    _ = _ := by
      ext P
      simp only [Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩
      · rintro ⟨hI, hJ⟩ f (hf | hf)
        · exact hI f hf
        · exact hJ f hf

private theorem isClosed_projZeroSet_of_isHomogeneousIdeal
    {k : Type u} [Field k] {σ : Type*}
    (I : Ideal (MvPolynomial σ k)) (hI : IsHomogeneousIdeal I) :
    IsClosed (projZeroSet (I : Set (MvPolynomial σ k))) :=
  isClosed_iff_isProjAlgebraicSet.mpr
    (isProjAlgebraicSet_projZeroSet_of_isHomogeneous I hI)

private theorem ideal_le_pointIdeal_of_mem_projZeroSet
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type*} [Finite σ]
    {I : Ideal (MvPolynomial σ k)} (hI : IsHomogeneousIdeal I)
    {P : ProjectiveSpace k σ}
    (hP : P ∈ projZeroSet (I : Set (MvPolynomial σ k))) :
    I ≤ homogeneousVanishingIdeal ({P} : Set (ProjectiveSpace k σ)) := by
  have hnonempty : (projZeroSet (I : Set (MvPolynomial σ k))).Nonempty := ⟨P, hP⟩
  calc
    I ≤ I.radical := Ideal.le_radical
    _ = homogeneousVanishingIdeal
        (projZeroSet (I : Set (MvPolynomial σ k))) :=
      (homogeneousVanishingIdeal_projZeroSet hI hnonempty).symm
    _ ≤ homogeneousVanishingIdeal ({P} : Set (ProjectiveSpace k σ)) :=
      homogeneousVanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hP)

private theorem projZeroSet_annihilator_eq_iUnion_factorPrimes
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type*} [Finite σ]
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    (s : RelSeries
      {q : HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ ×
          HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k σ) ℳ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤) :
    projZeroSet
        (Module.annihilator (MvPolynomial σ k) M : Set (MvPolynomial σ k)) =
      ⋃ i : Fin s.length,
        projZeroSet
          (gradedPrimeFiltrationFactorPrime
            (integerHomogeneousSubmodule k σ) ℳ s i).1 := by
  classical
  have hAnnHom : IsHomogeneousIdeal
      (Module.annihilator (MvPolynomial σ k) M) :=
    (ideal_isHomogeneous_integer_iff
      (k := k) (σ := σ) (Module.annihilator (MvPolynomial σ k) M)).mp
      (annihilator_isHomogeneous (integerHomogeneousSubmodule k σ) ℳ)
  ext P
  simp only [Set.mem_iUnion]
  let J : Ideal (MvPolynomial σ k) :=
    homogeneousVanishingIdeal ({P} : Set (ProjectiveSpace k σ))
  let JP : PrimeSpectrum (MvPolynomial σ k) :=
    ⟨J, isPrime_homogeneousVanishingIdeal_singleton P⟩
  constructor
  · intro hP
    have hAnnJ : Module.annihilator (MvPolynomial σ k) M ≤ J :=
      ideal_le_pointIdeal_of_mem_projZeroSet hAnnHom hP
    obtain ⟨q, hqfactor, hqJ⟩ :=
      (gradedPrimeFiltration_annihilator_le_iff
        (integerHomogeneousSubmodule k σ) ℳ s hshead hslast JP).mp hAnnJ
    obtain ⟨i, hi⟩ :=
      (isGradedPrimeFiltrationFactorOf_iff_exists_factorPrime_eq
        (integerHomogeneousSubmodule k σ) ℳ s q).mp hqfactor
    refine ⟨i, ?_⟩
    rw [hi]
    intro f hf
    exact eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal (hqJ hf) rfl
  · rintro ⟨i, hPi⟩
    let q := gradedPrimeFiltrationFactorPrime
      (integerHomogeneousSubmodule k σ) ℳ s i
    let data := gradedPrimeFiltrationFactorDataAt
      (integerHomogeneousSubmodule k σ) ℳ s i
    have hqhom : IsHomogeneousIdeal q.1 :=
      (ideal_isHomogeneous_integer_iff (k := k) (σ := σ) q.1).mp
        data.homogeneous
    have hqJ : q.1 ≤ J :=
      ideal_le_pointIdeal_of_mem_projZeroSet hqhom hPi
    have hAnnJ : Module.annihilator (MvPolynomial σ k) M ≤ J :=
      (gradedPrimeFiltration_annihilator_le_iff
        (integerHomogeneousSubmodule k σ) ℳ s hshead hslast JP).mpr
          ⟨q,
            ⟨i, gradedPrimeFiltrationFactorPrime_spec
              (integerHomogeneousSubmodule k σ) ℳ s i⟩,
            hqJ⟩
    intro f hf
    exact eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal (hAnnJ hf) rfl

/-- The dimension of a nonempty finite union of closed subsets is attained
by one member. -/
private theorem exists_topologicalKrullDim_eq_of_finite_closed_iUnion
    {X : Type*} [TopologicalSpace X] (S : Finset (Set X))
    (hS : S.Nonempty) (hclosed : ∀ t ∈ S, IsClosed t) :
    ∃ t ∈ S,
      topologicalKrullDim (⋃ t ∈ S, t) = topologicalKrullDim t := by
  classical
  obtain ⟨t, htS, htmax⟩ :=
    Finset.exists_max_image S (fun t : Set X => topologicalKrullDim t) hS
  refine ⟨t, htS, le_antisymm ?_ ?_⟩
  · have hUclosed : IsClosed (⋃ u ∈ S, u) :=
      S.finite_toSet.isClosed_biUnion fun u hu => hclosed u hu
    rw [topologicalKrullDim_subtype_eq hUclosed, Order.krullDim]
    refine iSup_le fun p => ?_
    obtain ⟨u, huS, hlast⟩ :=
      IsIrreducible.exists_mem_subset_of_subset_biUnion
        p.last.1.isIrreducible S hclosed p.last.2
    let q : LTSeries
        {Z : IrreducibleCloseds X // (Z : Set X) ⊆ u} :=
      LTSeries.mk p.length
        (fun i => ⟨(p i).1,
          (show ((p i).1 : Set X) ⊆ (p.last).1 from
            p.monotone (Fin.le_last i)).trans hlast⟩)
        (fun _ _ hij => p.strictMono hij)
    have hp_u : (p.length : WithBot ℕ∞) ≤ topologicalKrullDim u := by
      rw [topologicalKrullDim_subtype_eq (hclosed u huS), Order.krullDim]
      exact le_iSup_of_le q (le_of_eq rfl)
    exact hp_u.trans (htmax u huS)
  · have hsub : t ⊆ ⋃ u ∈ S, u := by
      intro x hx
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨t, htS, hx⟩
    exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le

private theorem topologicalKrullDim_eq_height_of_irreducible_closed
    {X : Type*} [TopologicalSpace X] {Y : Set X}
    (hirr : IsIrreducible Y) (hclosed : IsClosed Y) :
    topologicalKrullDim Y =
      (Order.height
        (⟨Y, hirr, hclosed⟩ : IrreducibleCloseds X) : WithBot ℕ∞) := by
  rw [topologicalKrullDim_subtype_eq hclosed]
  change Order.krullDim
      (Set.Iic (⟨Y, hirr, hclosed⟩ : IrreducibleCloseds X)) = _
  rw [← Order.height_eq_krullDim_Iic]

/-- A proper closed subset of an irreducible projective algebraic set has
strictly smaller dimension. -/
private theorem projDim_lt_of_closed_ssubset_isProjVariety
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type} [Finite σ] [Nonempty σ]
    {Y Z : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y)
    (hZ : IsClosed Z) (hZY : Z ⊂ Y) : projDim Z < projDim Y := by
  classical
  let VY : IrreducibleCloseds (ProjectiveSpace k σ) := ⟨Y, hY.1, hY.2⟩
  have hdimY : projDim Y = (Order.height VY : WithBot ℕ∞) := by
    rw [projDim_def,
      topologicalKrullDim_eq_height_of_irreducible_closed hY.1 hY.2]
  obtain ⟨i⟩ := ‹Nonempty σ›
  have hYle : projDim Y ≤
      projDim (Set.univ : Set (ProjectiveSpace k σ)) :=
    (Topology.IsEmbedding.inclusion (Set.subset_univ Y)).isInducing.topologicalKrullDim_le
  have hheight_ne_top : Order.height VY ≠ ⊤ := by
    have hdimfin : projDim Y < ⊤ := hYle.trans_lt <| by
      rw [projDim_univ (k := k) i]
      exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)
    rw [hdimY] at hdimfin
    intro htop
    rw [htop] at hdimfin
    exact (lt_irrefl _ hdimfin)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hheight_ne_top
  have hn' : Order.height VY = n := hn.symm
  change topologicalKrullDim Z < projDim Y
  rw [topologicalKrullDim_subtype_eq hZ, hdimY, hn']
  change Order.krullDim
    {T : IrreducibleCloseds (ProjectiveSpace k σ) // (T : Set _) ⊆ Z} <
      (n : WithBot ℕ∞)
  rw [Order.krullDim_lt_coe_iff]
  intro p
  let q : LTSeries (IrreducibleCloseds (ProjectiveSpace k σ)) :=
    p.map (fun T => T.1) (fun _ _ h => h)
  have hqY : q.last < VY := by
    change ((q.last : IrreducibleCloseds (ProjectiveSpace k σ)) : Set _) ⊂ Y
    exact Set.ssubset_of_subset_of_ssubset p.last.2 hZY
  have hlen := Order.length_le_height_last (p := q.snoc VY hqY)
  have hlenV : ((q.snoc VY hqY).length : ℕ∞) ≤ Order.height VY := by
    simpa using hlen
  rw [hn'] at hlenV
  have hlen' : p.length + 1 ≤ n := by
    simp [q] at hlenV
    exact_mod_cast hlenV
  omega

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

private theorem coordinateHyperplane_data
    {k : Type u} [Field k] [IsAlgClosed k]
    {n : ℕ} (hn : 0 < n) (i : Fin (n + 1)) :
    let H : Set (ProjectiveSpace k (Fin (n + 1))) :=
      projZeroSet ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))
    IsProjVariety H ∧
      projDim H = ((n - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  let H : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))
  let j : Fin (n + 1) := if i = 0 then ⟨1, by omega⟩ else 0
  have hji : j ≠ i := by
    dsimp only [j]
    split_ifs with hi
    · subst i
      intro h
      have := Fin.ext_iff.mp h
      simp at this
    · exact Ne.symm hi
  let v : Fin (n + 1) → k := Pi.single j 1
  have hvj : v j = 1 := by simp [v]
  have hvne : v ≠ 0 := by
    intro hv
    have := congrFun hv j
    rw [hvj] at this
    exact one_ne_zero this
  let P : ProjectiveSpace k (Fin (n + 1)) := Projectivization.mk k v hvne
  have hPH : P ∈ H := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst f
    exact (homogeneousVanish_X_iff hvne).mpr (by simp [v, hji])
  let I : Ideal (MvPolynomial (Fin (n + 1)) k) :=
    Ideal.span ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))
  have hIhom : IsHomogeneousIdeal I :=
    Ideal.homogeneous_span _ _ fun f hf => by
      rw [Set.mem_singleton_iff] at hf
      subst f
      exact isHomogeneousElem_iff.mpr ⟨1, isHomogeneous_X k i⟩
  have hXprime : Prime (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) k) :=
    MvPolynomial.X_prime
  have hIprime : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hXprime
  have hZI : projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k)) = H := by
    exact projZeroSet_span _
  have hIne : (projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
    rw [hZI]
    exact ⟨P, hPH⟩
  have hH : IsProjVariety H := by
    rw [← hZI]
    exact isProjVariety_projZeroSet_of_isHomogeneous_isPrime I hIhom hIprime hIne
  refine ⟨hH, ?_⟩
  exact (projective_codimension_one_iff_hypersurface hH hn).mpr
    ⟨MvPolynomial.X i, 1, by omega, isHomogeneous_X k i,
      (UniqueFactorizationMonoid.irreducible_iff_prime).mpr MvPolynomial.X_prime, rfl⟩

/-- The dimension of a projective variety is represented by a natural
number. -/
private theorem exists_projDim_eq_nat_of_isProjVariety
    {k : Type u} [Field k] [IsAlgClosed k]
    {σ : Type} [Finite σ] [Nonempty σ]
    {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) :
    ∃ r : ℕ, projDim Y = (r : WithBot ℕ∞) := by
  classical
  obtain ⟨P, hPY⟩ := hY.1.nonempty
  obtain ⟨i, hi⟩ := exists_mem_standardChart P
  have hne : (Y ∩ standardChart i).Nonempty := ⟨P, hPY, hi⟩
  have hA : IsAffineVariety (chartMap i '' (Y ∩ standardChart i)) :=
    isAffineVariety_chartMap_image i hY hne
  letI : IsDomain (coordinateRing (chartMap i '' (Y ∩ standardChart i))) :=
    isDomain_coordinateRing hA
  obtain ⟨r, hr⟩ := exists_ringKrullDim_eq_natCast k
    (coordinateRing (chartMap i '' (Y ∩ standardChart i)))
  refine ⟨r, ?_⟩
  rw [projDim_eq_dim_chart hY i hne,
    dim_eq_ringKrullDim_coordinateRing hA.isAlgebraicSet, hr]

/-- Cutting a positive-dimensional projective variety properly by a coordinate
hyperplane lowers its dimension by exactly one. -/
private theorem projDim_inter_coordinateHyperplane
    {k : Type u} [Field k] [IsAlgClosed k]
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    {Y : Set (ProjectiveSpace k (Fin (n + 1)))} (hY : IsProjVariety Y)
    (hYdim : projDim Y = (r : WithBot ℕ∞)) (i : Fin (n + 1))
    (hproper : ¬Y ⊆
      projZeroSet ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))) :
    projDim (Y ∩
      projZeroSet ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))) =
        ((r - 1 : ℕ) : WithBot ℕ∞) := by
  classical
  let H : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))
  obtain ⟨hH, hHdim⟩ := coordinateHyperplane_data (k := k) hn i
  have hne : (Y ∩ H).Nonempty :=
    projective_inter_nonempty_of_dim hY hH hYdim hHdim (by omega)
  have hclosed : IsClosed (Y ∩ H) := hY.2.inter hH.2
  have hss : Y ∩ H ⊂ Y := Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_left, by
    intro heq
    apply hproper
    intro P hPY
    have hPinter : P ∈ Y ∩ H := by simpa [heq] using hPY
    exact hPinter.2⟩
  have hupper : projDim (Y ∩ H) < (r : WithBot ℕ∞) := by
    rw [← hYdim]
    exact projDim_lt_of_closed_ssubset_isProjVariety hY hclosed hss
  obtain ⟨P, hP⟩ := hne
  let p : ↥(Y ∩ H) := ⟨P, hP⟩
  let W : irreducibleComponents ↥(Y ∩ H) :=
    ⟨irreducibleComponent p, irreducibleComponent_mem_irreducibleComponents p⟩
  have hWvar : IsProjVariety (projectiveComponentCarrier W.1) :=
    isProjVariety_projectiveComponentCarrier hclosed W
  obtain ⟨m, hWdim⟩ := exists_projDim_eq_nat_of_isProjVariety hWvar
  have hbound := projective_dimension_theorem hY hH W
  rw [hYdim, hHdim, hWdim, Nat.card_fin] at hbound
  have hboundNat : r + (n - 1) ≤ m + n := by
    exact_mod_cast hbound
  have hlowNat : r - 1 ≤ m := by omega
  have hlowW : ((r - 1 : ℕ) : WithBot ℕ∞) ≤
      projDim (projectiveComponentCarrier W.1) := by
    rw [hWdim]
    exact_mod_cast hlowNat
  have hWsub : projectiveComponentCarrier W.1 ⊆ Y ∩ H := by
    rintro _ ⟨w, hw, rfl⟩
    exact w.2
  have hWle : projDim (projectiveComponentCarrier W.1) ≤ projDim (Y ∩ H) :=
    (Topology.IsEmbedding.inclusion hWsub).isInducing.topologicalKrullDim_le
  apply le_antisymm
  · by_cases hbot : projDim (Y ∩ H) = ⊥
    · rw [hbot]
      exact bot_le
    · obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
      have halt : a < (r : ℕ∞) := by
        apply WithBot.coe_lt_coe.mp
        rw [ha]
        exact hupper
      have hrEq : (r : ℕ∞) = (r - 1 : ℕ∞) + 1 := by
        norm_cast
        omega
      have hale : a ≤ (r - 1 : ℕ∞) := by
        rw [hrEq] at halt
        exact (ENat.lt_add_one_iff (ENat.natCast_ne_top _)).mp halt
      rw [← ha]
      exact WithBot.coe_le_coe.mpr hale
  · exact hlowW.trans hWle

/-- Assemble Hilbert data for a finite graded module from Hilbert data for the
prime quotients in one chosen graded prime filtration. -/
private theorem hasHilbertData_of_filtrationFactors
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
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (hfactor : ∀ i : Fin s.length,
      let data := gradedPrimeFiltrationFactorDataAt
        (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ s i
      HasHilbertData (σ := Fin (n + 1))
        (gradedQuotientPiece
          (integerHomogeneousSubmodule k (Fin (n + 1)))
          (integerHomogeneousSubmodule k (Fin (n + 1)))
          (homogeneousIdealSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            data.prime.1 data.homogeneous))) :
    HasHilbertData (σ := Fin (n + 1)) ℳ := by
  classical
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let data (i : Fin s.length) :=
    gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
  let q (i : Fin s.length) : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k) :=
    (data i).prime
  let ℱ (i : Fin s.length) :=
    gradedQuotientPiece 𝓐 𝓐
      (homogeneousIdealSubmodule 𝓐 (q i).1 (data i).homogeneous)
  have hfactor' (i : Fin s.length) :
      HasHilbertData (σ := Fin (n + 1)) (ℱ i) := by
    simpa [𝓐, data, q, ℱ] using hfactor i
  let hd (i : Fin s.length) : HasHilbertData (σ := Fin (n + 1))
      (gradedModuleTwist (ℱ i) (data i).twist) :=
    (hfactor' i).twist (ℱ i) (data i).twist
  let P (i : Fin s.length) : ℚ[X] := Classical.choose (hd i)
  have hP (i : Fin s.length) :
      IsHilbertPolynomial (σ := Fin (n + 1))
          (gradedModuleTwist (ℱ i) (data i).twist) (P i) ∧
        hilbertPolynomialDegree (P i) =
          projDim (projZeroSet
            (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
              (MvPolynomial (Fin (n + 1)) k ⧸
                (homogeneousIdealSubmodule
                  𝓐 (q i).1 (data i).homogeneous).toSubmodule) :
              Set (MvPolynomial (Fin (n + 1)) k))) ∧
        ((projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
            (MvPolynomial (Fin (n + 1)) k ⧸
              (homogeneousIdealSubmodule
                𝓐 (q i).1 (data i).homogeneous).toSubmodule) :
            Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
          0 < (P i).leadingCoeff) :=
    Classical.choose_spec (hd i)
  let Z (i : Fin s.length) : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet ((q i).1 : Set (MvPolynomial (Fin (n + 1)) k))
  have hPdeg (i : Fin s.length) :
      hilbertPolynomialDegree (P i) = projDim (Z i) := by
    have h := (hP i).2.1
    rw [Ideal.annihilator_quotient] at h
    change hilbertPolynomialDegree (P i) =
      projDim (projZeroSet
        ((q i).1 : Set (MvPolynomial (Fin (n + 1)) k))) at h
    exact h
  have hPlc (i : Fin s.length) (hne : (Z i).Nonempty) :
      0 < (P i).leadingCoeff := by
    apply (hP i).2.2
    rw [Ideal.annihilator_quotient]
    change (projZeroSet
      ((q i).1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty
    exact hne
  have hsumHilbert : IsHilbertPolynomial (σ := Fin (n + 1)) ℳ
      (∑ i : Fin s.length, P i) := by
    refine ⟨IsNumericalPolynomial.finset_sum
      (s := Finset.univ) (fun i _ => (hP i).1.1), ?_⟩
    have hall : ∀ᶠ d : ℤ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin s.length)),
          (P i).eval (d : ℚ) =
            (hilbertFunction (σ := Fin (n + 1))
              (gradedModuleTwist (ℱ i) (data i).twist) d : ℚ) :=
      (Finset.eventually_all Finset.univ).2 fun i _ => (hP i).1.2
    filter_upwards [hall] with d hdall
    rw [Polynomial.eval_finsetSum,
      hilbertFunction_eq_sum_filtrationFactors ℳ s hshead hslast d]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hdall i (Finset.mem_univ i)]
    simp [filtrationFactorHilbertFunction, data, q, ℱ, 𝓐, i.2]
  have hsupport :
      projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
            Set (MvPolynomial (Fin (n + 1)) k)) =
        ⋃ i : Fin s.length, Z i := by
    simpa [Z, q, data, 𝓐, gradedPrimeFiltrationFactorPrime] using
      (projZeroSet_annihilator_eq_iUnion_factorPrimes
        (k := k) ℳ s hshead hslast)
  let Y : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
        Set (MvPolynomial (Fin (n + 1)) k))
  by_cases hYne : Y.Nonempty
  · have hFin : Nonempty (Fin s.length) := by
      obtain ⟨x, hx⟩ := hYne
      have hx' : x ∈ projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
            Set (MvPolynomial (Fin (n + 1)) k)) := by
        simpa [Y] using hx
      rw [hsupport] at hx'
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
      exact ⟨i⟩
    let S : Finset (Set (ProjectiveSpace k (Fin (n + 1)))) :=
      Finset.univ.image Z
    have hSne : S.Nonempty := by
      let i := Classical.choice hFin
      exact ⟨Z i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hSclosed : ∀ T ∈ S, IsClosed T := by
      intro T hT
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hT
      have hhom : IsHomogeneousIdeal (q i).1 :=
        (ideal_isHomogeneous_integer_iff
          (k := k) (σ := Fin (n + 1)) (q i).1).mp (data i).homogeneous
      exact isClosed_projZeroSet_of_isHomogeneousIdeal (q i).1 hhom
    obtain ⟨T, hTS, hTdim⟩ :=
      exists_topologicalKrullDim_eq_of_finite_closed_iUnion S hSne hSclosed
    obtain ⟨i₀, -, rfl⟩ := Finset.mem_image.mp hTS
    have hUnion : (⋃ T ∈ S, T) = ⋃ i : Fin s.length, Z i := by
      ext x
      simp [S]
    have hmax : projDim Y = projDim (Z i₀) := by
      change topologicalKrullDim
        (projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
            Set (MvPolynomial (Fin (n + 1)) k))) =
        topologicalKrullDim (Z i₀)
      rw [hsupport, ← hUnion]
      exact hTdim
    have hZi₀ne : (Z i₀).Nonempty := by
      by_contra hne
      have hz : Z i₀ = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have := projDim_ne_bot_of_nonempty hYne
      rw [hmax, hz, projDim_empty] at this
      exact this rfl
    have hZi₀var : IsProjVariety (Z i₀) := by
      have hhom : IsHomogeneousIdeal (q i₀).1 :=
        (ideal_isHomogeneous_integer_iff
          (k := k) (σ := Fin (n + 1)) (q i₀).1).mp (data i₀).homogeneous
      exact isProjVariety_projZeroSet_of_isHomogeneous_isPrime
        (q i₀).1 hhom (q i₀).2 hZi₀ne
    obtain ⟨r, hr⟩ := exists_projDim_eq_nat_of_isProjVariety hZi₀var
    have hYdim : projDim Y = (r : WithBot ℕ∞) := hmax.trans hr
    have hZsub (i : Fin s.length) : Z i ⊆ Y := by
      change Z i ⊆ projZeroSet
        (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
          Set (MvPolynomial (Fin (n + 1)) k))
      rw [hsupport]
      exact Set.subset_iUnion Z i
    have hdimle (i : Fin s.length) : projDim (Z i) ≤ (r : WithBot ℕ∞) := by
      rw [← hYdim]
      exact (Topology.IsEmbedding.inclusion (hZsub i)).isInducing.topologicalKrullDim_le
    have hdeg : ∀ i ∈ (Finset.univ : Finset (Fin s.length)),
        (P i).natDegree ≤ r := by
      intro i _
      by_cases hne : (Z i).Nonempty
      · have hhom : IsHomogeneousIdeal (q i).1 :=
          (ideal_isHomogeneous_integer_iff
            (k := k) (σ := Fin (n + 1)) (q i).1).mp (data i).homogeneous
        have hvar := isProjVariety_projZeroSet_of_isHomogeneous_isPrime
          (q i).1 hhom (q i).2 hne
        obtain ⟨m, hm⟩ := exists_projDim_eq_nat_of_isProjVariety hvar
        have hPne : P i ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mp (hPlc i hne).ne'
        have hnat : (P i).natDegree = m := by
          have h := hPdeg i
          rw [hm] at h
          simp [hilbertPolynomialDegree, hPne] at h
          exact_mod_cast h
        rw [hnat]
        have := hdimle i
        rw [hm] at this
        exact_mod_cast this
      · have hz : Z i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have hbot : hilbertPolynomialDegree (P i) = ⊥ := by
          rw [hPdeg i, hz, projDim_empty]
        rw [(hilbertPolynomialDegree_eq_bot_iff (P i)).mp hbot]
        exact Nat.zero_le _
    have hcoeff : ∀ i ∈ (Finset.univ : Finset (Fin s.length)),
        0 ≤ (P i).coeff r := by
      intro i _
      by_cases hne : (Z i).Nonempty
      · have hhom : IsHomogeneousIdeal (q i).1 :=
          (ideal_isHomogeneous_integer_iff
            (k := k) (σ := Fin (n + 1)) (q i).1).mp (data i).homogeneous
        have hvar := isProjVariety_projZeroSet_of_isHomogeneous_isPrime
          (q i).1 hhom (q i).2 hne
        obtain ⟨m, hm⟩ := exists_projDim_eq_nat_of_isProjVariety hvar
        have hPne : P i ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mp (hPlc i hne).ne'
        have hnat : (P i).natDegree = m := by
          have h := hPdeg i
          rw [hm] at h
          simp [hilbertPolynomialDegree, hPne] at h
          exact_mod_cast h
        have hmle : m ≤ r := by
          have := hdimle i
          rw [hm] at this
          exact_mod_cast this
        rcases eq_or_lt_of_le hmle with rfl | hmr
        · rw [← hnat, Polynomial.coeff_natDegree]
          exact (hPlc i hne).le
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hnat.trans_lt hmr)]
      · have hz : Z i = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        have hbot : hilbertPolynomialDegree (P i) = ⊥ := by
          rw [hPdeg i, hz, projDim_empty]
        rw [(hilbertPolynomialDegree_eq_bot_iff (P i)).mp hbot]
        simp
    have hpos : ∃ i ∈ (Finset.univ : Finset (Fin s.length)),
        0 < (P i).coeff r := by
      refine ⟨i₀, Finset.mem_univ _, ?_⟩
      have hPne : P i₀ ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mp (hPlc i₀ hZi₀ne).ne'
      have hnat : (P i₀).natDegree = r := by
        have h := hPdeg i₀
        rw [hr] at h
        simp [hilbertPolynomialDegree, hPne] at h
        exact_mod_cast h
      rw [← hnat, Polynomial.coeff_natDegree]
      exact hPlc i₀ hZi₀ne
    obtain ⟨hsumdeg, hsumlc⟩ :=
      finset_sum_polynomial_degree Finset.univ P r hdeg hcoeff hpos
    have hsumne : (∑ i : Fin s.length, P i) ≠ 0 := by
      intro hzero
      rw [hzero] at hsumlc
      simp at hsumlc
    refine ⟨∑ i : Fin s.length, P i, hsumHilbert, ?_, ?_⟩
    · rw [hilbertPolynomialDegree, if_neg hsumne, hsumdeg]
      simpa [Y] using hYdim.symm
    · intro _
      exact hsumlc
  · have hYempty : Y = ∅ := Set.not_nonempty_iff_eq_empty.mp hYne
    have hPiZero (i : Fin s.length) : P i = 0 := by
      have hZiEmpty : Z i = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hYne
        refine ⟨x, ?_⟩
        change x ∈ projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
            Set (MvPolynomial (Fin (n + 1)) k))
        rw [hsupport]
        exact Set.mem_iUnion.mpr ⟨i, hx⟩
      apply (hilbertPolynomialDegree_eq_bot_iff (P i)).mp
      rw [hPdeg i, hZiEmpty, projDim_empty]
    refine ⟨0, ?_, ?_, ?_⟩
    · simpa [hPiZero] using hsumHilbert
    · change hilbertPolynomialDegree 0 = projDim Y
      rw [hYempty, projDim_empty]
      simp [hilbertPolynomialDegree]
    · change Y.Nonempty → _
      simpa [hYempty]

private theorem eq_empty_of_projDim_lt_zero
    {k : Type u} [Field k] {σ : Type*}
    {Z : Set (ProjectiveSpace k σ)}
    (hZ : projDim Z < (0 : WithBot ℕ∞)) : Z = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hnonneg : (0 : WithBot ℕ∞) ≤ projDim Z := by
    unfold projDim topologicalKrullDim
    apply Order.krullDim_nonneg_iff.mpr
    let z' : Z := ⟨z, hz⟩
    exact ⟨⟨irreducibleComponent z', isIrreducible_irreducibleComponent,
      isClosed_irreducibleComponent⟩⟩
  exact (not_lt_of_ge hnonneg) hZ

private theorem hilbertFunction_primeQuotient_pos
    {k : Type u} [Field k] {σ : Type*} [Finite σ]
    (p : PrimeSpectrum (MvPolynomial σ k))
    (hp : p.1.IsHomogeneous (integerHomogeneousSubmodule k σ))
    (i : σ) (hi : MvPolynomial.X i ∉ p.1) (m : ℕ) :
    0 < hilbertFunction (σ := σ)
      (gradedQuotientPiece
        (integerHomogeneousSubmodule k σ)
        (integerHomogeneousSubmodule k σ)
        (homogeneousIdealSubmodule
          (integerHomogeneousSubmodule k σ) p.1 hp)) (m : ℤ) := by
  let 𝓐 := integerHomogeneousSubmodule k σ
  let ℱ := gradedQuotientPiece 𝓐 𝓐
    (homogeneousIdealSubmodule 𝓐 p.1 hp)
  let z : ℱ (m : ℤ) :=
    ⟨Submodule.Quotient.mk (MvPolynomial.X i ^ m),
      ⟨MvPolynomial.X i ^ m, by
        change (MvPolynomial.X i ^ m).IsHomogeneous m
        exact MvPolynomial.isHomogeneous_X_pow i m, rfl⟩⟩
  have hz : z ≠ 0 := by
    intro hz0
    apply hi
    apply p.2.mem_of_pow_mem m
    apply (Submodule.Quotient.mk_eq_zero p.1).mp
    exact congrArg Subtype.val hz0
  letI : Nontrivial (ℱ (m : ℤ)) := ⟨⟨z, 0, hz⟩⟩
  let _ : Module.Finite k (ℱ (m : ℤ)) :=
    finite_gradedPiece (k := k) (σ := σ) ℱ (m : ℤ)
  exact Module.finrank_pos

private theorem filtrationFactor_hasHilbertData_of_dim_lt
    {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ}
    {C : Type v} [AddCommGroup C] [Module k C]
    [Module (MvPolynomial (Fin (n + 1)) k) C]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) C]
    (ℂ : ℤ → Submodule k C) [DirectSum.Decomposition ℂ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℂ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) C]
    (s : RelSeries
      {q : HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℂ ×
          HomogeneousSubmodule
            (integerHomogeneousSubmodule k (Fin (n + 1))) ℂ |
        IsGradedPrimeFiltrationStep
          (integerHomogeneousSubmodule k (Fin (n + 1))) ℂ q.1 q.2})
    (hshead : s.head = ⊥) (hslast : s.last = ⊤)
    (hCdim : projDim (projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) C :
        Set (MvPolynomial (Fin (n + 1)) k))) =
      if r = 0 then ⊥ else ((r - 1 : ℕ) : WithBot ℕ∞))
    (ih : ∀ m < r,
      ∀ (q : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
        (hq : q.1.IsHomogeneous
          (integerHomogeneousSubmodule k (Fin (n + 1)))),
        (projZeroSet
          (q.1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
        projDim (projZeroSet
          (q.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
            (m : WithBot ℕ∞) →
        HasHilbertData (σ := Fin (n + 1))
          (gradedQuotientPiece
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (homogeneousIdealSubmodule
              (integerHomogeneousSubmodule k (Fin (n + 1))) q.1 hq)))
    (j : Fin s.length) :
    let data := gradedPrimeFiltrationFactorDataAt
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℂ s j
    HasHilbertData (σ := Fin (n + 1))
      (gradedQuotientPiece
        (integerHomogeneousSubmodule k (Fin (n + 1)))
        (integerHomogeneousSubmodule k (Fin (n + 1)))
        (homogeneousIdealSubmodule
          (integerHomogeneousSubmodule k (Fin (n + 1)))
          data.prime.1 data.homogeneous)) := by
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let data := gradedPrimeFiltrationFactorDataAt 𝓐 ℂ s j
  let q := data.prime
  let Zq : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet (q.1 : Set (MvPolynomial (Fin (n + 1)) k))
  by_cases hZq : Zq.Nonempty
  · have hqHomNat : IsHomogeneousIdeal q.1 :=
      (ideal_isHomogeneous_integer_iff
        (k := k) (σ := Fin (n + 1)) q.1).mp data.homogeneous
    have hqvar := isProjVariety_projZeroSet_of_isHomogeneous_isPrime
      q.1 hqHomNat q.2 hZq
    obtain ⟨m, hm⟩ := exists_projDim_eq_nat_of_isProjVariety hqvar
    have hZqsub : Zq ⊆ projZeroSet
        (Module.annihilator (MvPolynomial (Fin (n + 1)) k) C :
          Set (MvPolynomial (Fin (n + 1)) k)) := by
      rw [projZeroSet_annihilator_eq_iUnion_factorPrimes
        (k := k) ℂ s hshead hslast]
      simpa [Zq, q, data, 𝓐, gradedPrimeFiltrationFactorPrime] using
        (Set.subset_iUnion (fun a => projZeroSet
          ((gradedPrimeFiltrationFactorPrime 𝓐 ℂ s a).1 :
            Set (MvPolynomial (Fin (n + 1)) k))) j)
    have hle : (m : WithBot ℕ∞) ≤
        if r = 0 then ⊥ else ((r - 1 : ℕ) : WithBot ℕ∞) := by
      rw [← hm, ← hCdim]
      exact (Topology.IsEmbedding.inclusion hZqsub).isInducing.topologicalKrullDim_le
    have hmr : m < r := by
      by_cases hr0 : r = 0
      · simp [hr0] at hle
      · simp only [if_neg hr0] at hle
        have : m ≤ r - 1 := by exact_mod_cast hle
        omega
    exact ih m hmr q data.homogeneous hZq hm
  · have hempty : Zq = ∅ := Set.not_nonempty_iff_eq_empty.mp hZq
    exact primeQuotient_hasHilbertData_of_empty q data.homogeneous hempty

/-- Apply lower-dimensional prime Hilbert data to a prime filtration of a
coordinate-hyperplane cokernel.  Kept separate so the strong-induction
declaration stays within the normal elaboration budget. -/
private theorem hyperplaneCokernel_hasHilbertData
    {k : Type u} [Field k] [IsAlgClosed k] {n r : ℕ}
    (ih : ∀ m < r,
      ∀ (q : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
        (hq : q.1.IsHomogeneous
          (integerHomogeneousSubmodule k (Fin (n + 1)))),
        (projZeroSet
          (q.1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
        projDim (projZeroSet
          (q.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
            (m : WithBot ℕ∞) →
        HasHilbertData (σ := Fin (n + 1))
          (gradedQuotientPiece
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (homogeneousIdealSubmodule
              (integerHomogeneousSubmodule k (Fin (n + 1))) q.1 hq)))
    (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
    (hp : p.1.IsHomogeneous
      (integerHomogeneousSubmodule k (Fin (n + 1))))
    (i : Fin (n + 1))
    (hCdim :
      let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
      let ℱ := gradedQuotientPiece 𝓐 𝓐
        (homogeneousIdealSubmodule 𝓐 p.1 hp)
      let N := quotientXSubmodule p.1 hp i
      projDim (projZeroSet
        (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
          ((MvPolynomial (Fin (n + 1)) k ⧸
            (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule) ⧸
              N.toSubmodule) : Set (MvPolynomial (Fin (n + 1)) k))) =
        if r = 0 then ⊥ else ((r - 1 : ℕ) : WithBot ℕ∞)) :
    let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
    let ℱ := gradedQuotientPiece 𝓐 𝓐
      (homogeneousIdealSubmodule 𝓐 p.1 hp)
    let N := quotientXSubmodule p.1 hp i
    HasHilbertData (σ := Fin (n + 1)) (gradedQuotientPiece 𝓐 ℱ N) := by
  dsimp only
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  let ℱ := gradedQuotientPiece 𝓐 𝓐
    (homogeneousIdealSubmodule 𝓐 p.1 hp)
  let N := quotientXSubmodule p.1 hp i
  let ℂ := gradedQuotientPiece 𝓐 ℱ N
  obtain ⟨sC, hsChead, hsClast⟩ := exists_gradedPrimeFiltration 𝓐 ℂ
  apply hasHilbertData_of_filtrationFactors ℂ sC hsChead hsClast
  intro j
  exact filtrationFactor_hasHilbertData_of_dim_lt
    ℂ sC hsChead hsClast hCdim ih j

/-- Hilbert--Serre, with positivity, for homogeneous prime quotients.  The
induction is only on the natural dimension of the nonempty prime support; the
hyperplane cokernel is handled by a prime filtration. -/
private theorem primeQuotient_hasHilbertData
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ} :
    ∀ r : ℕ,
      ∀ (p : PrimeSpectrum (MvPolynomial (Fin (n + 1)) k))
        (hp : p.1.IsHomogeneous
          (integerHomogeneousSubmodule k (Fin (n + 1)))),
        (projZeroSet
          (p.1 : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
        projDim (projZeroSet
          (p.1 : Set (MvPolynomial (Fin (n + 1)) k))) =
            (r : WithBot ℕ∞) →
        HasHilbertData (σ := Fin (n + 1))
          (gradedQuotientPiece
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (integerHomogeneousSubmodule k (Fin (n + 1)))
            (homogeneousIdealSubmodule
              (integerHomogeneousSubmodule k (Fin (n + 1))) p.1 hp)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro p hp hYne hYdim
      let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
      let ℱ := gradedQuotientPiece 𝓐 𝓐
        (homogeneousIdealSubmodule 𝓐 p.1 hp)
      let Y : Set (ProjectiveSpace k (Fin (n + 1))) :=
        projZeroSet (p.1 : Set (MvPolynomial (Fin (n + 1)) k))
      have hpHomNat : IsHomogeneousIdeal p.1 :=
        (ideal_isHomogeneous_integer_iff
          (k := k) (σ := Fin (n + 1)) p.1).mp hp
      have hYvar : IsProjVariety Y :=
        isProjVariety_projZeroSet_of_isHomogeneous_isPrime
          p.1 hpHomNat p.2 hYne
      obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), MvPolynomial.X i ∉ p.1 := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        have hirrel : irrelevantIdeal k (Fin (n + 1)) ≤ p.1 := by
          rw [irrelevantIdeal, Ideal.span_le]
          rintro _ ⟨j, rfl⟩
          exact hall j
        have hempty : Y = ∅ := by
          change projZeroSet
            (p.1 : Set (MvPolynomial (Fin (n + 1)) k)) = ∅
          apply (projZeroSet_eq_empty_iff hpHomNat).mpr
          rwa [p.2.radical]
        exact (Set.not_nonempty_iff_eq_empty.mpr hempty) hYne
      let H : Set (ProjectiveSpace k (Fin (n + 1))) :=
        projZeroSet
          ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))
      have hproper : ¬Y ⊆ H := by
        intro hYH
        apply hi
        have hmem : MvPolynomial.X i ∈ homogeneousVanishingIdeal Y := by
          apply Ideal.subset_span
          refine ⟨⟨1, isHomogeneous_X k i⟩, ?_⟩
          intro P hPY
          exact hYH hPY (MvPolynomial.X i) (Set.mem_singleton _)
        change MvPolynomial.X i ∈ p.1
        rw [← p.2.radical,
          ← homogeneousVanishingIdeal_projZeroSet hpHomNat hYne]
        exact hmem
      let N := quotientXSubmodule p.1 hp i
      let ℂ := gradedQuotientPiece 𝓐 ℱ N
      have hCann : Module.annihilator (MvPolynomial (Fin (n + 1)) k)
          ((MvPolynomial (Fin (n + 1)) k ⧸
            (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule) ⧸ N.toSubmodule) =
          p.1 ⊔ Ideal.span
            ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k)) := by
        simpa [𝓐, ℱ, N] using annihilator_quotientXSubmodule_eq p.1 hp i
      have hCsupport :
          projZeroSet
              (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
                ((MvPolynomial (Fin (n + 1)) k ⧸
                  (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule) ⧸
                    N.toSubmodule) : Set (MvPolynomial (Fin (n + 1)) k)) =
            Y ∩ H := by
        rw [hCann, projZeroSet_sup, projZeroSet_span]
      have hCdim : projDim
          (projZeroSet
            (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
              ((MvPolynomial (Fin (n + 1)) k ⧸
                (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule) ⧸
                  N.toSubmodule) : Set (MvPolynomial (Fin (n + 1)) k))) =
          if r = 0 then ⊥ else ((r - 1 : ℕ) : WithBot ℕ∞) := by
        rw [hCsupport]
        by_cases hr0 : r = 0
        · subst r
          simp only [if_pos]
          have hHclosed : IsClosed H := by
            have hspanHom : IsHomogeneousIdeal
                (Ideal.span
                  ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))) :=
              Ideal.homogeneous_span _ _ fun f hf => by
                rw [Set.mem_singleton_iff] at hf
                subst f
                exact isHomogeneousElem_iff.mpr ⟨1, isHomogeneous_X k i⟩
            change IsClosed (projZeroSet
              ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k)))
            rw [← projZeroSet_span]
            exact isClosed_projZeroSet_of_isHomogeneousIdeal
              (Ideal.span
                ({MvPolynomial.X i} : Set (MvPolynomial (Fin (n + 1)) k))) hspanHom
          have hss : Y ∩ H ⊂ Y := Set.ssubset_iff_subset_ne.mpr
            ⟨Set.inter_subset_left, by
              intro heq
              apply hproper
              intro P hP
              exact (show P ∈ Y ∩ H by simpa [heq] using hP).2⟩
          have hlt := projDim_lt_of_closed_ssubset_isProjVariety hYvar
            (hYvar.2.inter hHclosed) hss
          rw [hYdim] at hlt
          rw [eq_empty_of_projDim_lt_zero hlt, projDim_empty]
        · simp only [if_neg hr0]
          have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          have hn : 0 < n := by
            have hle : projDim Y ≤
                projDim (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) :=
              (Topology.IsEmbedding.inclusion (Set.subset_univ Y)).isInducing.topologicalKrullDim_le
            rw [hYdim, projDim_univ_fin] at hle
            have hrn : r ≤ n := by exact_mod_cast hle
            omega
          exact projDim_inter_coordinateHyperplane hn hrpos hYvar hYdim i hproper
      have hCdata : HasHilbertData (σ := Fin (n + 1)) ℂ :=
        hyperplaneCokernel_hasHilbertData ih p hp i hCdim
      obtain ⟨Q, hQ, hQdeg, hQlc⟩ := hCdata
      have hrec (d : ℤ) :
          hilbertFunction (σ := Fin (n + 1)) ℱ d =
            hilbertFunction (σ := Fin (n + 1)) ℱ (d - 1) +
              hilbertFunction (σ := Fin (n + 1)) ℂ d := by
        simpa [𝓐, ℱ, N, ℂ] using
          hilbertFunction_primeQuotient_eq_pred_add p hp i hi d
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · simp only [if_pos] at hCdim
        have hQbot : hilbertPolynomialDegree Q = ⊥ := hQdeg.trans hCdim
        have hQzero : Q = 0 :=
          (hilbertPolynomialDegree_eq_bot_iff Q).mp hQbot
        have hCzero : ∀ᶠ d : ℤ in atTop,
            hilbertFunction (σ := Fin (n + 1)) ℂ d = 0 := by
          filter_upwards [hQ.2] with d hd
          rw [hQzero, Polynomial.eval_zero] at hd
          exact_mod_cast hd.symm
        obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hCzero
        let m := N₀.natAbs
        let a := hilbertFunction (σ := Fin (n + 1)) ℱ (m : ℤ)
        have hconst : ∀ d : ℤ, (m : ℤ) ≤ d →
            hilbertFunction (σ := Fin (n + 1)) ℱ d = a := by
          intro d hd
          refine Int.leInduction (motive := fun d _ =>
            hilbertFunction (σ := Fin (n + 1)) ℱ d = a) rfl ?_ d hd
          intro b hb ihb
          have hz := hN₀ (b + 1) (Int.le_natAbs.trans (by omega))
          have hr := hrec (b + 1)
          have harg : b + 1 - 1 = b := by omega
          rw [harg] at hr
          have hs : hilbertFunction (σ := Fin (n + 1)) ℱ (b + 1) =
              hilbertFunction (σ := Fin (n + 1)) ℱ b := by
            omega
          exact hs.trans ihb
        have ha : 0 < a := by
          exact hilbertFunction_primeQuotient_pos p hp i hi m
        let P : ℚ[X] := Polynomial.C (a : ℚ)
        have hPnum : IsNumericalPolynomial P := by
          rw [IsNumericalPolynomial]
          exact Filter.Eventually.of_forall fun _ => ⟨(a : ℤ), by simp [P]⟩
        have hPHilbert : IsHilbertPolynomial (σ := Fin (n + 1)) ℱ P := by
          refine ⟨hPnum, Filter.eventually_atTop.mpr ⟨(m : ℤ), fun d hd => ?_⟩⟩
          simp [P, hconst d hd]
        refine ⟨P, hPHilbert, ?_, ?_⟩
        · rw [Ideal.annihilator_quotient]
          change hilbertPolynomialDegree P = projDim Y
          rw [hYdim]
          have hane : a ≠ 0 := Nat.ne_of_gt ha
          simp [P, hilbertPolynomialDegree, hane]
        · intro _
          have haq : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha
          dsimp only [P]
          rw [Polynomial.leadingCoeff_C]
          exact haq
      · have hr0 : r ≠ 0 := hrpos.ne'
        simp only [if_neg hr0] at hCdim
        have hCne : (projZeroSet
            (Module.annihilator (MvPolynomial (Fin (n + 1)) k)
              ((MvPolynomial (Fin (n + 1)) k ⧸
                (homogeneousIdealSubmodule 𝓐 p.1 hp).toSubmodule) ⧸
                  N.toSubmodule) : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
          by_contra hne
          have hz := Set.not_nonempty_iff_eq_empty.mp hne
          rw [hz, projDim_empty] at hCdim
          exact WithBot.coe_ne_bot hCdim.symm
        have hQlcpos : 0 < Q.leadingCoeff := hQlc hCne
        have hQne : Q ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mp hQlcpos.ne'
        have hQnat : Q.natDegree = r - 1 := by
          have h := hQdeg.trans hCdim
          simp [hilbertPolynomialDegree, hQne] at h
          exact_mod_cast h
        have hQtaylorNum : IsNumericalPolynomial (Q.taylor 1) :=
          hQ.1.taylor_int 1
        have hdiff : ∀ᶠ d : ℤ in atTop,
            ((((hilbertFunction (σ := Fin (n + 1)) ℱ (d + 1) : ℤ) -
                (hilbertFunction (σ := Fin (n + 1)) ℱ d : ℤ) : ℤ) : ℚ) =
              (Q.taylor 1).eval (d : ℚ)) := by
          obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hQ.2
          refine Filter.eventually_atTop.mpr ⟨N₀ - 1, fun d hd => ?_⟩
          have hQd := hN₀ (d + 1) (by omega)
          have hrd := hrec (d + 1)
          have hrd' : hilbertFunction (σ := Fin (n + 1)) ℱ (d + 1) =
              hilbertFunction (σ := Fin (n + 1)) ℱ d +
                hilbertFunction (σ := Fin (n + 1)) ℂ (d + 1) := by
            simpa using hrd
          rw [Polynomial.taylor_eval]
          push_cast at hQd ⊢
          rw [hQd]
          exact_mod_cast (show
            (hilbertFunction (σ := Fin (n + 1)) ℱ (d + 1) : ℤ) -
                (hilbertFunction (σ := Fin (n + 1)) ℱ d : ℤ) =
              (hilbertFunction (σ := Fin (n + 1)) ℂ (d + 1) : ℤ) by omega)
        obtain ⟨P, hPnum, hPevent, -, hPdegree⟩ :=
          exists_isNumericalPolynomial_eventuallyEq_of_diff
            (fun d => (hilbertFunction (σ := Fin (n + 1)) ℱ d : ℤ))
            (Q.taylor 1) hQtaylorNum hdiff
        have hQtaylorNe : Q.taylor 1 ≠ 0 :=
          (Polynomial.taylor_eq_zero 1 Q).not.mpr hQne
        obtain ⟨hPnat, hPlc⟩ := hPdegree hQtaylorNe
        have hPnat' : P.natDegree = r := by
          rw [Polynomial.natDegree_taylor, hQnat] at hPnat
          omega
        have hPne : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt <| by
          rw [hPnat']
          exact hrpos
        have hPHilbert : IsHilbertPolynomial (σ := Fin (n + 1)) ℱ P := by
          refine ⟨hPnum, ?_⟩
          filter_upwards [hPevent] with d hd
          simpa using hd
        refine ⟨P, hPHilbert, ?_, ?_⟩
        · rw [Ideal.annihilator_quotient]
          change hilbertPolynomialDegree P = projDim Y
          rw [hYdim]
          simp [hilbertPolynomialDegree, hPne, hPnat']
        · intro _
          rw [hPlc, Polynomial.leadingCoeff_taylor]
          positivity

private theorem hasHilbertData
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M] :
    HasHilbertData (σ := Fin (n + 1)) ℳ := by
  let 𝓐 := integerHomogeneousSubmodule k (Fin (n + 1))
  obtain ⟨s, hshead, hslast⟩ := exists_gradedPrimeFiltration 𝓐 ℳ
  apply hasHilbertData_of_filtrationFactors ℳ s hshead hslast
  intro i
  let data := gradedPrimeFiltrationFactorDataAt 𝓐 ℳ s i
  let q := data.prime
  let Zq : Set (ProjectiveSpace k (Fin (n + 1))) :=
    projZeroSet (q.1 : Set (MvPolynomial (Fin (n + 1)) k))
  by_cases hZq : Zq.Nonempty
  · have hqHomNat : IsHomogeneousIdeal q.1 :=
      (ideal_isHomogeneous_integer_iff
        (k := k) (σ := Fin (n + 1)) q.1).mp data.homogeneous
    have hqvar := isProjVariety_projZeroSet_of_isHomogeneous_isPrime
      q.1 hqHomNat q.2 hZq
    obtain ⟨r, hr⟩ := exists_projDim_eq_nat_of_isProjVariety hqvar
    exact primeQuotient_hasHilbertData r q data.homogeneous hZq hr
  · have hempty : Zq = ∅ := Set.not_nonempty_iff_eq_empty.mp hZq
    exact primeQuotient_hasHilbertData_of_empty q data.homogeneous hempty

/-- **Hilbert--Serre (Hartshorne I.7.5).** A finite graded module over
`k[x₀,…,xₙ]` has a unique eventual numerical Hilbert polynomial.  Its
degree is the dimension of the projective zero set of the annihilator (with
the zero polynomial and empty support both assigned degree `−1`).  For
nonempty support its leading coefficient is positive. -/
theorem hilbertSerre
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M] :
    ∃! P : ℚ[X],
      IsHilbertPolynomial (σ := Fin (n + 1)) ℳ P ∧
      hilbertPolynomialDegree P =
        projDim (projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
            Set (MvPolynomial (Fin (n + 1)) k))) ∧
      ((projZeroSet
        (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
          Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
        0 < P.leadingCoeff) := by
  obtain ⟨P, hP, hdeg, hlc⟩ :=
    hasHilbertData (k := k) (n := n) (M := M) ℳ
  refine ⟨P, ⟨hP, hdeg, hlc⟩, ?_⟩
  intro Q hQ
  exact isHilbertPolynomial_unique ℳ hQ.1 hP

/-- The canonical Hilbert polynomial supplied by `hilbertSerre`. -/
noncomputable def gradedHilbertPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M] : ℚ[X] :=
  Classical.choose (hilbertSerre (k := k) (n := n) (M := M) ℳ).exists

theorem gradedHilbertPolynomial_spec
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M] :
    IsHilbertPolynomial (σ := Fin (n + 1)) ℳ
        (gradedHilbertPolynomial (k := k) (n := n) (M := M) ℳ) ∧
      hilbertPolynomialDegree
          (gradedHilbertPolynomial (k := k) (n := n) (M := M) ℳ) =
        projDim (projZeroSet
          (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
            Set (MvPolynomial (Fin (n + 1)) k))) ∧
      ((projZeroSet
        (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
          Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
        0 < (gradedHilbertPolynomial
          (k := k) (n := n) (M := M) ℳ).leadingCoeff) :=
  Classical.choose_spec
    (hilbertSerre (k := k) (n := n) (M := M) ℳ).exists

theorem gradedHilbertPolynomial_isHilbertPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M] :
    IsHilbertPolynomial (σ := Fin (n + 1)) ℳ
      (gradedHilbertPolynomial (k := k) (n := n) (M := M) ℳ) :=
  (gradedHilbertPolynomial_spec (k := k) (n := n) (M := M) ℳ).1

theorem gradedHilbertPolynomial_isNumericalPolynomial
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M] :
    IsNumericalPolynomial
      (gradedHilbertPolynomial (k := k) (n := n) (M := M) ℳ) :=
  (gradedHilbertPolynomial_isHilbertPolynomial
    (k := k) (n := n) (M := M) ℳ).1

theorem gradedHilbertPolynomial_eventually_eval_eq_hilbertFunction
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M] :
    ∀ᶠ d : ℤ in atTop,
      (gradedHilbertPolynomial
        (k := k) (n := n) (M := M) ℳ).eval (d : ℚ) =
        (hilbertFunction (σ := Fin (n + 1)) ℳ d : ℚ) :=
  (gradedHilbertPolynomial_isHilbertPolynomial
    (k := k) (n := n) (M := M) ℳ).2

theorem gradedHilbertPolynomial_degree
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M] :
    hilbertPolynomialDegree
        (gradedHilbertPolynomial (k := k) (n := n) (M := M) ℳ) =
      projDim (projZeroSet
        (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
          Set (MvPolynomial (Fin (n + 1)) k))) :=
  (gradedHilbertPolynomial_spec (k := k) (n := n) (M := M) ℳ).2.1

theorem gradedHilbertPolynomial_eq_zero_of_support_eq_empty
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M]
    (h : projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
        Set (MvPolynomial (Fin (n + 1)) k)) = ∅) :
    gradedHilbertPolynomial (k := k) (n := n) (M := M) ℳ = 0 := by
  apply (hilbertPolynomialDegree_eq_bot_iff _).mp
  rw [gradedHilbertPolynomial_degree
    (k := k) (n := n) (M := M) ℳ, h, projDim_empty]

theorem gradedHilbertPolynomial_leadingCoeff_pos
    {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {M : Type v} [AddCommGroup M] [Module k M]
    [Module (MvPolynomial (Fin (n + 1)) k) M]
    [IsScalarTower k (MvPolynomial (Fin (n + 1)) k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul
      (integerHomogeneousSubmodule k (Fin (n + 1))) ℳ]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) M]
    (h : (projZeroSet
      (Module.annihilator (MvPolynomial (Fin (n + 1)) k) M :
        Set (MvPolynomial (Fin (n + 1)) k))).Nonempty) :
    0 < (gradedHilbertPolynomial
      (k := k) (n := n) (M := M) ℳ).leadingCoeff :=
  (gradedHilbertPolynomial_spec (k := k) (n := n) (M := M) ℳ).2.2 h

end

end Hartshorne
