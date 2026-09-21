/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Nonsingular.DefiningIdealCotangent
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Independence of the Jacobian rank from defining equations

Hartshorne, *Algebraic Geometry*, I.5 (pp. 31–32).

The intrinsic Jacobian row space of an affine variety at a point is the span
of the gradients of every polynomial in its vanishing ideal.  This file proves
that any family generating that ideal already spans the same row space.  It
follows that the rank of Hartshorne's Jacobian matrix is independent of the
chosen finite generating family.
-/

namespace Hartshorne

open MvPolynomial

universe u v w w'

variable {k : Type u} [Field k] {σ : Type v} {Y : Set (σ → k)}

/-- The Jacobian matrix of a family of polynomials at an ambient point. -/
noncomputable def jacobianMatrix {ι : Type w} (P : σ → k)
    (f : ι → MvPolynomial σ k) : Matrix ι σ k :=
  fun i j => aeval P (pderiv j (f i))

/-- The row space of the Jacobian matrix of a family of polynomials. -/
noncomputable def jacobianRowSpace {ι : Type w} (P : σ → k)
    (f : ι → MvPolynomial σ k) : Submodule k (σ → k) :=
  Submodule.span k (Set.range (jacobianMatrix P f).row)

/-- The intrinsic Jacobian rank, defined using all equations vanishing on the
variety rather than a chosen generating family. -/
noncomputable def jacobianRank [Finite σ] (Y : Set (σ → k)) (P : Y) : ℕ :=
  Module.finrank k (definingIdealGradientSpace P)

/-- A family generating the vanishing ideal has gradient rows spanning the
intrinsic Jacobian row space. -/
theorem definingIdealGradientSpace_eq_jacobianRowSpace_of_span_eq
    [Finite σ] {ι : Type w} (P : Y) (f : ι → MvPolynomial σ k)
    (hf : Ideal.span (Set.range f) = vanishingIdeal k Y) :
    definingIdealGradientSpace P = jacobianRowSpace (P : σ → k) f := by
  classical
  rw [definingIdealGradientSpace, jacobianRowSpace]
  have hfj (j : ι) : f j ∈ vanishingIdeal k Y := by
    rw [← hf]
    exact Ideal.mem_span_range_self
  have hzero (j : ι) : aeval (P : σ → k) (f j) = 0 :=
    hfj j P.1 P.2
  apply le_antisymm
  · rintro x ⟨g, rfl⟩
    have hg : g.1 ∈ Ideal.span (Set.range f) := by
      rw [hf]
      exact g.2
    obtain ⟨c, hc⟩ :=
      Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hg
    have heq :
        definingIdealGradient P g =
          c.sum fun j a =>
            (aeval (P : σ → k) a) • (jacobianMatrix (P : σ → k) f).row j := by
      ext i
      rw [definingIdealGradient_apply, ← hc]
      simp only [Finsupp.sum, map_sum, pderiv_mul, map_add, map_mul,
        hzero, mul_zero, zero_add, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      rfl
    rw [heq]
    apply Submodule.sum_mem
    intro j hj
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · apply Submodule.span_le.2
    rintro x ⟨j, rfl⟩
    refine ⟨⟨f j, hfj j⟩, ?_⟩
    ext i
    exact definingIdealGradient_apply P ⟨f j, hfj j⟩ i

/-- The rank of a Jacobian matrix built from any finite generating family is
the intrinsic Jacobian rank. -/
theorem jacobianMatrix_rank_eq_jacobianRank [Fintype σ] {ι : Type w} [Finite ι]
    (P : Y) (f : ι → MvPolynomial σ k)
    (hf : Ideal.span (Set.range f) = vanishingIdeal k Y) :
    (jacobianMatrix (P : σ → k) f).rank = jacobianRank Y P := by
  rw [Matrix.rank_eq_finrank_span_row, jacobianRank,
    definingIdealGradientSpace_eq_jacobianRowSpace_of_span_eq P f hf,
    jacobianRowSpace]

/-- Any two finite generating families for the vanishing ideal give Jacobian
matrices of the same rank. -/
theorem jacobianMatrix_rank_eq_of_span_eq [Fintype σ]
    {ι : Type w} [Finite ι] {ι' : Type w'} [Finite ι']
    (P : Y) (f : ι → MvPolynomial σ k) (g : ι' → MvPolynomial σ k)
    (hf : Ideal.span (Set.range f) = vanishingIdeal k Y)
    (hg : Ideal.span (Set.range g) = vanishingIdeal k Y) :
    (jacobianMatrix (P : σ → k) f).rank =
      (jacobianMatrix (P : σ → k) g).rank :=
  (jacobianMatrix_rank_eq_jacobianRank P f hf).trans
    (jacobianMatrix_rank_eq_jacobianRank P g hg).symm

/-- In finitely many variables, the vanishing ideal admits a finite family of
generators whose Jacobian matrix computes the intrinsic Jacobian rank. -/
theorem exists_fin_jacobianMatrix_rank_eq_jacobianRank [Fintype σ]
    (Y : Set (σ → k)) (P : Y) :
    ∃ (n : ℕ) (f : Fin n → MvPolynomial σ k),
      Ideal.span (Set.range f) = vanishingIdeal k Y ∧
        (jacobianMatrix (P : σ → k) f).rank = jacobianRank Y P := by
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian (vanishingIdeal k Y))
  exact ⟨n, f, hf, jacobianMatrix_rank_eq_jacobianRank P f hf⟩

end Hartshorne
