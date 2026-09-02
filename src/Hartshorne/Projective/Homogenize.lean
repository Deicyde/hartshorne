/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Dehomogenize

/-!
# Homogenisation

Hartshorne, *Algebraic Geometry*, I.2, the map `β` in the proof of
Proposition 2.2 (p. 10).

`β g = xᵢ^{deg g} · g(x_j / xᵢ)` pads every monomial of `g` up to the total
degree with a power of `xᵢ`. Unlike `α` it is not a ring homomorphism: the
padding exponent depends on the degree, so it does not respect sums of
polynomials of different degrees. Mathlib has homogenisation only for
univariate polynomials, so it is built here.

Only two facts are needed, and both are computations over the support:
`β g` is homogeneous of degree `totalDegree g`, and it evaluates to
`(vᵢ)^{deg g}` times `g` evaluated at the ratios.

## Main definitions

* `Hartshorne.homogenize`

## Main results

* `Hartshorne.homogenize_isHomogeneous`
* `Hartshorne.eval_homogenize`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- `Xᵢ ^ n` is homogeneous of degree `n`. -/
theorem isHomogeneous_X_pow (i : σ) (n : ℕ) :
    (X i ^ n : MvPolynomial σ k).IsHomogeneous n := by
  rw [X_pow_eq_monomial]
  exact isHomogeneous_monomial _ (by simp)

/-- A product of powers of variables is homogeneous of the total exponent. -/
theorem isHomogeneous_prod_X_pow {τ : Type*} (s : Finset τ) (f : τ → σ) (e : τ → ℕ) :
    (∏ j ∈ s, X (f j) ^ e j : MvPolynomial σ k).IsHomogeneous (∑ j ∈ s, e j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHomogeneous_one σ k
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (isHomogeneous_X_pow (f a) (e a)).mul ih

variable [DecidableEq σ]

/-- Hartshorne's `β`: pad each monomial of `g` with a power of `xᵢ` bringing it
up to the total degree. -/
noncomputable def homogenize (i : σ) (g : MvPolynomial {j : σ // j ≠ i} k) :
    MvPolynomial σ k :=
  ∑ d ∈ g.support, C (coeff d g) * X i ^ (g.totalDegree - d.degree) *
    ∏ j ∈ d.support, X (j : σ) ^ d j

/-- `β g` is homogeneous of degree `totalDegree g`. Each summand has degree
`(N - d.degree) + d.degree`, which is `N` because `d` lies in the support. -/
theorem homogenize_isHomogeneous (i : σ) (g : MvPolynomial {j : σ // j ≠ i} k) :
    (homogenize i g).IsHomogeneous g.totalDegree := by
  rw [← mem_homogeneousSubmodule]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_homogeneousSubmodule]
  have hdeg : d.degree ≤ g.totalDegree := le_totalDegree hd
  have hsum : ∑ j ∈ d.support, d j = d.degree := (Finsupp.degree_apply d).symm
  have := ((isHomogeneous_C (σ := σ) (coeff d g)).mul
    (isHomogeneous_X_pow (k := k) i (g.totalDegree - d.degree))).mul
      (hsum ▸ isHomogeneous_prod_X_pow (k := k) d.support (fun j => (j : σ)) (fun j => d j))
  simpa [Nat.sub_add_cancel hdeg] using this

/-- The identity that makes `β` do its job: evaluating the homogenisation is
`(vᵢ)^{deg g}` times evaluating `g` at the ratios. Needs `vᵢ ≠ 0`, which holds
exactly on the chart. -/
theorem eval_homogenize (i : σ) (g : MvPolynomial {j : σ // j ≠ i} k)
    {v : σ → k} (hv : v i ≠ 0) :
    eval v (homogenize i g)
      = v i ^ g.totalDegree * eval (fun j : {j : σ // j ≠ i} => v j / v i) g := by
  classical
  rw [homogenize, map_sum, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree ≤ g.totalDegree := le_totalDegree hd
  have hsum : ∑ j ∈ d.support, d j = d.degree := (Finsupp.degree_apply d).symm
  rw [map_mul, map_mul, map_prod, eval_C, map_pow, eval_X]
  simp only [map_pow, eval_X]
  -- Split `(vᵢ)^N` as `(vᵢ)^(N - deg d) * (vᵢ)^(deg d)` and cancel.
  have hsplit : ∏ j ∈ d.support, (v (j : σ) / v i) ^ d j
      = (∏ j ∈ d.support, v (j : σ) ^ d j) / v i ^ d.degree := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [div_pow]
  have hpow : v i ^ g.totalDegree = v i ^ (g.totalDegree - d.degree) * v i ^ d.degree := by
    rw [← pow_add, Nat.sub_add_cancel hdeg]
  rw [hsplit, hpow]
  field_simp

/-- On the chart, a point's image under `φᵢ` lies in `Z(T)` exactly when the
point lies in the zero set of the homogenisations. This is the half of
Proposition 2.2 that needs `β`. -/
theorem chartMap_mem_zeroSet_iff (i : σ) (T : Set (MvPolynomial {j : σ // j ≠ i} k))
    {P : ProjectiveSpace k σ} (hP : P ∈ standardChart i) :
    chartMap i P ∈ zeroSet T ↔ P ∈ projZeroSet (homogenize i '' T) := by
  have hi : P.rep i ≠ 0 := rep_ne_zero_of_mem_standardChart hP
  constructor
  · rintro h _ ⟨g, hg, rfl⟩
    show eval P.rep (homogenize i g) = 0
    rw [eval_homogenize i g hi]
    have hdef : (fun j : {j : σ // j ≠ i} => P.rep j / P.rep i) = chartMap i P := rfl
    rw [hdef, h g hg, mul_zero]
  · intro h g hg
    have hz : eval P.rep (homogenize i g) = 0 := h _ ⟨g, hg, rfl⟩
    rw [eval_homogenize i g hi] at hz
    rcases mul_eq_zero.1 hz with hc | hc
    · exact absurd (pow_eq_zero_iff'.1 hc).1 hi
    · exact hc

/-- The homogenisations of a family are homogeneous, so they cut out a closed
set. -/
theorem isHomogeneousSet_homogenize_image (i : σ)
    (T : Set (MvPolynomial {j : σ // j ≠ i} k)) :
    IsHomogeneousSet (homogenize i '' T) := by
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g.totalDegree, homogenize_isHomogeneous i g⟩

/-- **Hartshorne 2.2**: the standard chart `φᵢ : Uᵢ → 𝔸ⁿ` is a homeomorphism.

This is the key result of I.2: it is what makes projective space locally affine,
and every later local question about a projective variety is answered through
it. -/
theorem continuous_chartMap_restrict (i : σ) :
    Continuous fun P : (standardChart i : Set (ProjectiveSpace k σ)) => chartMap i P.1 := by
  rw [continuous_iff_isClosed]
  intro Y hY
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hY
  have heq : (fun P : (standardChart i : Set (ProjectiveSpace k σ)) => chartMap i P.1)
      ⁻¹' zeroSet T = Subtype.val ⁻¹' projZeroSet (homogenize i '' T) := by
    ext P
    exact chartMap_mem_zeroSet_iff i T P.2
  rw [heq]
  exact (isClosed_iff_isProjAlgebraicSet.2
    ⟨_, isHomogeneousSet_homogenize_image i T, rfl⟩).preimage continuous_subtype_val

noncomputable def chartHomeomorph (i : σ) :
    (standardChart i : Set (ProjectiveSpace k σ)) ≃ₜ ({j : σ // j ≠ i} → k) where
  toEquiv := chartEquiv i
  continuous_toFun := continuous_chartMap_restrict i
  continuous_invFun := (continuous_chartInv i).subtype_mk _

end Hartshorne
