/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.GradedModuleTwist
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Finite-dimensional homogeneous pieces

For a finite integer-graded module over a polynomial ring in finitely many
variables, every homogeneous piece is finite-dimensional over the ground
field.  This is the finiteness implicit in Hartshorne's definition of the
Hilbert function before Theorem I.7.5.
-/

namespace Hartshorne

open DirectSum MvPolynomial

noncomputable section

universe u v

variable {k : Type u} [Field k] {σ : Type*} [Finite σ]
  {M : Type v} [AddCommGroup M]
  [Module k M] [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]

omit [Finite σ] [IsScalarTower k (MvPolynomial σ k) M] in
/-- The degree-`d` component of a scalar multiple of a homogeneous vector of
degree `e` uses only the degree-`d-e` component of the scalar. -/
private theorem coe_decompose_smul_of_mem
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    (a : MvPolynomial σ k) {e d : ℤ} {m : M} (hm : m ∈ ℳ e) :
    ((DirectSum.decompose ℳ (a • m) d : ℳ d) : M) =
      (DirectSum.decompose (integerHomogeneousSubmodule k σ) a (d - e) :
        MvPolynomial σ k) • m := by
  classical
  conv_lhs =>
    rw [← DirectSum.sum_support_decompose (integerHomogeneousSubmodule k σ) a,
      Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
      AddSubmonoidClass.coe_finsetSum]
  by_cases hde : d - e ∈
      (DirectSum.decompose (integerHomogeneousSubmodule k σ) a).support
  · rw [Finset.sum_eq_single (d - e)]
    · have hmem := SetLike.GradedSMul.smul_mem
        (DirectSum.decompose (integerHomogeneousSubmodule k σ) a (d - e)).property hm
      change _ ∈ ℳ ((d - e) + e) at hmem
      have hdegree : (d - e) + e = d := by omega
      rw [hdegree] at hmem
      exact DirectSum.decompose_of_mem_same ℳ hmem
    · intro i hi hid
      have hmem := SetLike.GradedSMul.smul_mem
        (DirectSum.decompose (integerHomogeneousSubmodule k σ) a i).property hm
      have hne : i +ᵥ e ≠ d := by
        change i + e ≠ d
        omega
      exact DirectSum.decompose_of_mem_ne ℳ hmem hne
    · exact fun hnot => (hnot hde).elim
  · rw [DFinsupp.notMem_support_iff.mp hde]
    simp only [ZeroMemClass.coe_zero, zero_smul]
    apply Finset.sum_eq_zero
    intro i hi
    have hmem := SetLike.GradedSMul.smul_mem
      (DirectSum.decompose (integerHomogeneousSubmodule k σ) a i).property hm
    have hne : i +ᵥ e ≠ d := by
      change i + e ≠ d
      intro hieq
      apply hde
      have : i = d - e := by omega
      rwa [← this]
    exact DirectSum.decompose_of_mem_ne ℳ hmem hne

/-- Every integer-graded piece of the polynomial ring is finitely generated
over the ground field. -/
private theorem integerHomogeneousSubmodule_fg (d : ℤ) :
    (integerHomogeneousSubmodule k σ d).FG := by
  cases d with
  | ofNat n =>
      exact MvPolynomial.homogeneousSubmodule_fg σ k n
  | negSucc n =>
      exact Submodule.fg_bot

/-- Every homogeneous piece of a finite integer-graded module over a
finite-variable polynomial ring is finite-dimensional over the ground field. -/
theorem finite_gradedPiece
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    (d : ℤ) : Module.Finite k (ℳ d) := by
  classical
  let S := MvPolynomial σ k
  obtain ⟨N, g, hg⟩ :=
    Module.Finite.exists_fin (R := S) (M := M)

  /- Replace the finite module generators by all their nonzero homogeneous
  components.  The dependent index type is finite because every direct-sum
  decomposition has finite support. -/
  let I := Σ i : Fin N, ↥(DirectSum.decompose ℳ (g i)).support
  let degree : I → ℤ := fun j ↦ j.2.1
  let gen : I → M := fun j ↦
    (DirectSum.decompose ℳ (g j.1) j.2.1 : ℳ j.2.1)
  let _ : Fintype I := inferInstance

  have hgen_mem (j : I) : gen j ∈ ℳ (degree j) := by
    exact (DirectSum.decompose ℳ (g j.1) j.2.1).property

  have hg_mem (i : Fin N) : g i ∈ Submodule.span S (Set.range gen) := by
    rw [← DirectSum.sum_support_decompose ℳ (g i)]
    apply Submodule.sum_mem
    intro e he
    apply Submodule.subset_span
    exact ⟨⟨i, ⟨e, he⟩⟩, rfl⟩

  have hspan : Submodule.span S (Set.range gen) = ⊤ := by
    apply top_unique
    rw [← hg]
    exact Submodule.span_le.2 fun _ h ↦ by
      obtain ⟨i, rfl⟩ := h
      exact hg_mem i

  /- For each homogeneous generator, map the complementary polynomial piece
  into `M_d` by scalar multiplication, then sum these finitely many images. -/
  let smulMap (j : I) : S →ₗ[k] M :=
    (LinearMap.id (R := k) (M := S)).smulRight (gen j)
  let imagePiece (j : I) : Submodule k M :=
    (integerHomogeneousSubmodule k σ (d - degree j)).map (smulMap j)
  let target : Submodule k M := ⨆ j : I, imagePiece j

  have htarget_fg : target.FG := by
    exact Submodule.fg_iSup imagePiece fun j ↦
      (integerHomogeneousSubmodule_fg (k := k) (σ := σ) (d - degree j)).map (smulMap j)

  have htarget_le : target ≤ ℳ d := by
    refine iSup_le fun j ↦ ?_
    rintro _ ⟨a, ha, rfl⟩
    change a • gen j ∈ ℳ d
    have hsmul := SetLike.GradedSMul.smul_mem ha (hgen_mem j)
    have hdegree : (d - degree j) + degree j = d := by omega
    change a • gen j ∈ ℳ ((d - degree j) + degree j) at hsmul
    rwa [hdegree] at hsmul

  have hlinear_range :
      LinearMap.range (Finsupp.linearCombination S gen) = ⊤ := by
    rw [Finsupp.range_linearCombination, hspan]
  have hsurj : Function.Surjective (Finsupp.linearCombination S gen) :=
    LinearMap.range_eq_top.mp hlinear_range

  have hpiece_le : ℳ d ≤ target := by
    intro x hx
    obtain ⟨c, hc⟩ := hsurj x
    have hdecompose :
        ((DirectSum.decompose ℳ x d : ℳ d) : M) = x := by
      rw [DirectSum.decompose_of_mem_same]
      exact hx
    have hdecompose_mem :
        ((DirectSum.decompose ℳ x d : ℳ d) : M) ∈ target := by
      rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum,
        DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
        AddSubmonoidClass.coe_finsetSum]
      apply Submodule.sum_mem
      intro j hj
      rw [coe_decompose_smul_of_mem (k := k) (σ := σ) ℳ (c j) (hgen_mem j)]
      apply le_iSup (fun j : I ↦ imagePiece j) j
      exact ⟨DirectSum.decompose (integerHomogeneousSubmodule k σ)
        (c j) (d - degree j),
        (DirectSum.decompose (integerHomogeneousSubmodule k σ)
          (c j) (d - degree j)).property, rfl⟩
    rwa [hdecompose] at hdecompose_mem

  have htarget : target = ℳ d := le_antisymm htarget_le hpiece_le
  exact Module.Finite.of_fg (htarget ▸ htarget_fg)

end

end Hartshorne
