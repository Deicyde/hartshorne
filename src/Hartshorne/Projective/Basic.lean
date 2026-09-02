/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Projective space and homogeneous vanishing

Hartshorne, *Algebraic Geometry*, I.2, pp. 8-9.

Projective `n`-space is the set of lines through the origin in `kⁿ⁺¹`, which is
Mathlib's `Projectivization k (σ → k)`. A homogeneous polynomial is not a
function on it, but *whether it vanishes* is well defined, because
`f (a • x) = aᵈ · f x` for `f` homogeneous of degree `d`.

That scaling identity is the only thing standing between Mathlib's graded
polynomial API and Hartshorne's `Z(T)`, and Mathlib does not have it, so it is
proved here.

## Main results

* `MvPolynomial.IsHomogeneous.eval_smul` : the scaling identity.
* `Hartshorne.HomogeneousVanish` : vanishing at a point of projective space,
  shown independent of the representative.
-/

namespace MvPolynomial

variable {k : Type*} [CommRing k] {σ : Type*}

/-- A homogeneous polynomial of degree `n` scales by `aⁿ`.

This is the reason vanishing of a homogeneous polynomial is well defined on
projective space, and it is the only input Hartshorne's `Z(T)` needs beyond the
graded API Mathlib already has. -/
theorem IsHomogeneous.eval_smul {f : MvPolynomial σ k} {n : ℕ}
    (hf : f.IsHomogeneous n) (a : k) (x : σ → k) :
    eval (a • x) f = a ^ n * eval x f := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    rw [← Finsupp.degree_apply, Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.1 hd)
  have hprod : ∏ i ∈ d.support, (a • x) i ^ d i
      = a ^ n * ∏ i ∈ d.support, x i ^ d i := by
    rw [← hdeg, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by
      rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [hprod]
  ring

end MvPolynomial

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- Projective space over `k`, as the lines through the origin in `σ → k`. For
`σ = Fin (n+1)` this is Hartshorne's `ℙⁿ`.

This is Mathlib's `Projectivization`; the abbreviation exists so statements read
in Hartshorne's notation. -/
abbrev ProjectiveSpace (k σ : Type*) [Field k] : Type _ :=
  Projectivization k (σ → k)

/-- A homogeneous polynomial vanishes at a point of projective space when it
vanishes at one, equivalently every, representative. -/
def HomogeneousVanish (f : MvPolynomial σ k) (P : ProjectiveSpace k σ) : Prop :=
  eval P.rep f = 0

/-- Vanishing does not depend on the representative: any two differ by a unit
scalar, and a homogeneous polynomial scales by a power of it.

This is Hartshorne's observation that `f` is not a function on `ℙⁿ` but its
zero set is nonetheless well defined. -/
theorem homogeneousVanish_iff_of_isHomogeneous {f : MvPolynomial σ k} {n : ℕ}
    (hf : f.IsHomogeneous n) {v : σ → k} (hv : v ≠ 0) :
    HomogeneousVanish f (Projectivization.mk k v hv) ↔ eval v f = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  have hscale : eval (Projectivization.mk k v hv).rep f = (a : k) ^ n * eval v f := by
    rw [← ha]
    exact hf.eval_smul (a : k) v
  rw [HomogeneousVanish, hscale, mul_eq_zero]
  simp [Units.ne_zero]

/-- The standard charts. Whether the `i`-th homogeneous coordinate vanishes is
well defined, because `Xᵢ` is homogeneous of degree one; `Uᵢ` is the locus where
it does not. -/
theorem homogeneousVanish_X_iff {i : σ} {v : σ → k} (hv : v ≠ 0) :
    HomogeneousVanish (X i) (Projectivization.mk k v hv) ↔ v i = 0 := by
  rw [homogeneousVanish_iff_of_isHomogeneous (isHomogeneous_X k i) hv]
  simp

/-- The `i`-th standard affine chart of projective space, the complement of the
hyperplane `Xᵢ = 0`. -/
def standardChart (i : σ) : Set (ProjectiveSpace k σ) :=
  {P | ¬ HomogeneousVanish (X i) P}

/-- Every point of projective space lies in some standard chart: a nonzero
representative has a nonzero coordinate. This is what makes the `Uᵢ` an open
cover in Proposition 2.2. -/
theorem exists_mem_standardChart (P : ProjectiveSpace k σ) :
    ∃ i, P ∈ standardChart i := by
  by_contra h
  push Not at h
  refine P.rep_nonzero (funext fun i => ?_)
  simpa [standardChart, HomogeneousVanish] using h i

end Hartshorne
