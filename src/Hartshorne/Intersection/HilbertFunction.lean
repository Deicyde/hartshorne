/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.FiniteGradedPieces
import Hartshorne.Intersection.GradedSubquotient
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Hilbert functions of finite graded modules

For a finite integer-graded module over a polynomial ring in finitely many
variables, its Hilbert function in degree `d` is the dimension of its
degree-`d` piece over the ground field.  We also record translation under a
twist and additivity for degreewise short exact sequences.
-/

namespace Hartshorne

open DirectSum MvPolynomial

noncomputable section

universe u v

variable {k : Type u} [Field k] {σ : Type*}

/-- The Hilbert function of a finite integer-graded module over a
finite-variable polynomial ring. -/
noncomputable def hilbertFunction
    [Finite σ] {M : Type v} [AddCommMonoid M]
    [Module k M] [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M] (d : ℤ) : ℕ :=
  Module.finrank k (ℳ d)

/-- Twisting a graded module translates the argument of its Hilbert
function. -/
@[simp]
theorem hilbertFunction_twist
    [Finite σ] {M : Type v} [AddCommMonoid M]
    [Module k M] [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M] (l d : ℤ) :
    hilbertFunction (σ := σ) (gradedModuleTwist ℳ l) d =
      hilbertFunction (σ := σ) ℳ (d + l) := by
  rfl

/-- Finite-dimensional rank-nullity in the form needed for a short exact
sequence: the dimension of the middle term is the sum of the dimensions of
the outer terms. -/
theorem finrank_middle_eq_add_of_exact
    {V₁ V₂ V₃ : Type v}
    [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
    [Module k V₁] [Module k V₂] [Module k V₃]
    [Module.Finite k V₁] [Module.Finite k V₂] [Module.Finite k V₃]
    (f : V₁ →ₗ[k] V₂) (g : V₂ →ₗ[k] V₃)
    (hf : Function.Injective f)
    (hexact : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) :
    Module.finrank k V₂ = Module.finrank k V₁ + Module.finrank k V₃ := by
  have hrange_g : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr hg
  have h := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange_g, finrank_top, ← hexact,
    LinearMap.finrank_range_of_inj hf] at h
  omega

/-- A degreewise short exact sequence of finite graded modules makes their
Hilbert functions additive in that degree. -/
theorem hilbertFunction_add_of_degreewise_exact
    [Finite σ] {M₁ M₂ M₃ : Type v}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module k M₁] [Module k M₂] [Module k M₃]
    [Module (MvPolynomial σ k) M₁]
    [Module (MvPolynomial σ k) M₂]
    [Module (MvPolynomial σ k) M₃]
    [IsScalarTower k (MvPolynomial σ k) M₁]
    [IsScalarTower k (MvPolynomial σ k) M₂]
    [IsScalarTower k (MvPolynomial σ k) M₃]
    (ℳ₁ : ℤ → Submodule k M₁) (ℳ₂ : ℤ → Submodule k M₂)
    (ℳ₃ : ℤ → Submodule k M₃)
    [DirectSum.Decomposition ℳ₁] [DirectSum.Decomposition ℳ₂]
    [DirectSum.Decomposition ℳ₃]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ₁]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ₂]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ₃]
    [Module.Finite (MvPolynomial σ k) M₁]
    [Module.Finite (MvPolynomial σ k) M₂]
    [Module.Finite (MvPolynomial σ k) M₃]
    (d : ℤ) (f : ℳ₁ d →ₗ[k] ℳ₂ d) (g : ℳ₂ d →ₗ[k] ℳ₃ d)
    (hf : Function.Injective f)
    (hexact : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) :
    hilbertFunction (σ := σ) ℳ₂ d =
      hilbertFunction (σ := σ) ℳ₁ d +
        hilbertFunction (σ := σ) ℳ₃ d := by
  let _ : Module.Finite k (ℳ₁ d) :=
    finite_gradedPiece (k := k) (σ := σ) ℳ₁ d
  let _ : Module.Finite k (ℳ₂ d) :=
    finite_gradedPiece (k := k) (σ := σ) ℳ₂ d
  let _ : Module.Finite k (ℳ₃ d) :=
    finite_gradedPiece (k := k) (σ := σ) ℳ₃ d
  exact finrank_middle_eq_add_of_exact f g hf hexact hg

/-- A homogeneous submodule of a finite module over a finite-variable
polynomial ring is finite.  This supplies the finiteness hypothesis needed to
take its Hilbert function. -/
noncomputable instance homogeneousSubmoduleFinite
    [Finite σ] {M : Type v} [AddCommGroup M]
    [Module k M] [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    (N : HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ) :
    Module.Finite (MvPolynomial σ k) N := by
  exact Module.Finite.of_fg (IsNoetherian.noetherian N.toSubmodule)

/-- The Hilbert function is additive on a homogeneous submodule and its
graded quotient, degree by degree. -/
theorem hilbertFunction_subquotient
    [Finite σ] {M : Type v} [AddCommGroup M]
    [Module k M] [Module (MvPolynomial σ k) M]
    [IsScalarTower k (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    [SetLike.GradedSMul (integerHomogeneousSubmodule k σ) ℳ]
    [Module.Finite (MvPolynomial σ k) M]
    (N : HomogeneousSubmodule (integerHomogeneousSubmodule k σ) ℳ)
    (d : ℤ) :
    hilbertFunction (σ := σ) ℳ d =
      hilbertFunction (k := k) (σ := σ) (M := N)
          (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N) d +
        hilbertFunction (k := k) (σ := σ) (M := M ⧸ N.toSubmodule)
          (gradedQuotientPiece (integerHomogeneousSubmodule k σ) ℳ N) d := by
  obtain ⟨hinj, hexact, hsurj⟩ :=
    gradedSubquotient_exact (integerHomogeneousSubmodule k σ) ℳ N d
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  exact hilbertFunction_add_of_degreewise_exact (σ := σ)
    (gradedSubmodulePiece (integerHomogeneousSubmodule k σ) ℳ N) ℳ
    (gradedQuotientPiece (integerHomogeneousSubmodule k σ) ℳ N) d
    (gradedSubmodulePieceInclusion
      (integerHomogeneousSubmodule k σ) ℳ N d)
    (gradedQuotientPieceMap
      (integerHomogeneousSubmodule k σ) ℳ N d)
    hinj hexact hsurj

end

end Hartshorne
