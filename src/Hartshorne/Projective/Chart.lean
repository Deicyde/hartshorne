/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Zariski
import Hartshorne.Affine.Zariski

/-!
# The standard affine charts, as maps

Hartshorne, *Algebraic Geometry*, I.2, Proposition 2.2 (pp. 10-11).

The chart `φᵢ : Uᵢ → 𝔸ⁿ` divides through by the `i`-th homogeneous coordinate.
Hartshorne writes the target as `𝔸ⁿ` with the `i`-th entry omitted; here it is
the function type on `{j : σ // j ≠ i}`, which says the same thing without
choosing a reindexing.

This file establishes the bijection. That `φᵢ` is a homeomorphism, which is the
content of Proposition 2.2, is separate and needs the dehomogenisation and
homogenisation maps.

## Main definitions

* `Hartshorne.chartMap`, `Hartshorne.chartInv`

## Main results

* `Hartshorne.chartMap_chartInv`, `Hartshorne.chartInv_chartMap` : the two are
  mutually inverse on `Uᵢ`.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- A point lies in the `i`-th chart exactly when its `i`-th homogeneous
coordinate is nonzero. -/
theorem mem_standardChart_iff {i : σ} {P : ProjectiveSpace k σ} :
    P ∈ standardChart i ↔ P.rep i ≠ 0 := by
  simp [standardChart, HomogeneousVanish]

theorem rep_ne_zero_of_mem_standardChart {i : σ} {P : ProjectiveSpace k σ}
    (hP : P ∈ standardChart i) : P.rep i ≠ 0 :=
  mem_standardChart_iff.1 hP

/-- Hartshorne's `φᵢ`: divide the homogeneous coordinates by the `i`-th one.
The ratios are unchanged by rescaling the representative, so this is well
defined. -/
noncomputable def chartMap (i : σ) (P : ProjectiveSpace k σ) : {j : σ // j ≠ i} → k :=
  fun j => P.rep j / P.rep i

/-- The computation rule for `φᵢ` on an explicit representative. -/
theorem chartMap_mk (i : σ) {v : σ → k} (hv : v ≠ 0) (j : {j : σ // j ≠ i}) :
    chartMap i (Projectivization.mk k v hv) j = v j / v i := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  rw [chartMap, ← ha]
  simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ (Units.ne_zero a)]

variable [DecidableEq σ]

/-- The representative built from an affine point by putting `1` in slot `i`. -/
def chartInvVec (i : σ) (y : {j : σ // j ≠ i} → k) : σ → k :=
  fun j => if h : j = i then 1 else y ⟨j, h⟩

@[simp]
theorem chartInvVec_self (i : σ) (y : {j : σ // j ≠ i} → k) : chartInvVec i y i = 1 := by
  simp [chartInvVec]

theorem chartInvVec_of_ne {i : σ} (y : {j : σ // j ≠ i} → k) {j : σ} (hj : j ≠ i) :
    chartInvVec i y j = y ⟨j, hj⟩ := by
  simp [chartInvVec, hj]

theorem chartInvVec_ne_zero (i : σ) (y : {j : σ // j ≠ i} → k) : chartInvVec i y ≠ 0 := by
  intro h
  have : chartInvVec i y i = 0 := by rw [h]; rfl
  rw [chartInvVec_self] at this
  exact one_ne_zero this

/-- The inverse of the `i`-th chart: read an affine point as the projective
point whose `i`-th coordinate is `1`. -/
def chartInv (i : σ) (y : {j : σ // j ≠ i} → k) : ProjectiveSpace k σ :=
  Projectivization.mk k (chartInvVec i y) (chartInvVec_ne_zero i y)

theorem chartInv_mem_standardChart (i : σ) (y : {j : σ // j ≠ i} → k) :
    chartInv i y ∈ standardChart i := by
  rw [mem_standardChart_iff]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k (chartInvVec i y)
    (chartInvVec_ne_zero i y)
  rw [chartInv, ← ha]
  simp [Units.smul_def, Units.ne_zero a]

@[simp]
theorem chartMap_chartInv (i : σ) (y : {j : σ // j ≠ i} → k) :
    chartMap i (chartInv i y) = y := by
  funext j
  rw [chartInv, chartMap_mk i (chartInvVec_ne_zero i y) j, chartInvVec_self,
    chartInvVec_of_ne y j.2, div_one]

theorem chartInv_chartMap {i : σ} {P : ProjectiveSpace k σ} (hP : P ∈ standardChart i) :
    chartInv i (chartMap i P) = P := by
  have hi : P.rep i ≠ 0 := rep_ne_zero_of_mem_standardChart hP
  rw [chartInv, ← Projectivization.mk_rep P]
  -- The scaling factor is `(P.rep i)⁻¹`: that is what normalises slot `i` to `1`.
  refine (Projectivization.mk_eq_mk_iff k _ _ _ P.rep_nonzero).2
    ⟨(Units.mk0 (P.rep i) hi)⁻¹, ?_⟩
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Units.smul_def, inv_mul_cancel₀ hi]
  · rw [Units.smul_def, Pi.smul_apply, smul_eq_mul, chartInvVec_of_ne _ hj, chartMap]
    simp [inv_mul_eq_div]

/-- The `i`-th chart as a bijection `Uᵢ ≃ 𝔸ⁿ`.

Proposition 2.2 upgrades this to a homeomorphism; the underlying bijection is
already enough to see that `ℙⁿ` is set-theoretically covered by `n + 1` copies
of affine space. -/
noncomputable def chartEquiv (i : σ) :
    (standardChart i : Set (ProjectiveSpace k σ)) ≃ ({j : σ // j ≠ i} → k) where
  toFun P := chartMap i P.1
  invFun y := ⟨chartInv i y, chartInv_mem_standardChart i y⟩
  left_inv P := Subtype.ext (chartInv_chartMap P.2)
  right_inv y := chartMap_chartInv i y

@[simp]
theorem chartEquiv_apply (i : σ) (P : (standardChart i : Set (ProjectiveSpace k σ))) :
    chartEquiv i P = chartMap i P.1 := rfl

@[simp]
theorem chartEquiv_symm_apply (i : σ) (y : {j : σ // j ≠ i} → k) :
    ((chartEquiv i).symm y : ProjectiveSpace k σ) = chartInv i y := rfl

end Hartshorne
