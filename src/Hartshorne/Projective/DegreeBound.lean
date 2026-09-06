/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.CoordAwayChart
import Hartshorne.Projective.PointIdeal
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The degree bound in Theorem 3.4(a)

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(a).

If `t` lies in the fraction field of `S(Y)` and `xᵢ^{Nᵢ} · t ∈ S(Y)` for every
chart `Uᵢ` meeting `Y`, then `t · S(Y)_N ⊆ S(Y)_N` for any `N` at least the sum
of the `Nᵢ`.

This is Hartshorne's "let `N ≥ Σ Nᵢ`", and it is the only combinatorial step in
part (a) and the only place the cover being finite is used.

## The pigeonhole

`S(Y)_N` is spanned by classes of degree-`N` monomials, so it is enough to treat
`x^α` with `Σ α = N`. Either some variable `xᵢ` occurring in `x^α` belongs to a
chart missing `Y`, in which case `xᵢ` vanishes on `Y`, the class of `x^α` is
zero and there is nothing to prove; or `α` is supported on the charts that meet
`Y`, and then `Σ αᵢ = N ≥ Σ Nᵢ` over those forces `αᵢ ≥ Nᵢ` for some `i`. For
that `i`, `x^α · t = (x^α / xᵢ^{Nᵢ}) · (xᵢ^{Nᵢ} t)`, a product of something of
degree `N − Nᵢ` with something of degree `Nᵢ`.

## Main results

* `Hartshorne.mk_X_eq_zero_of_inter_eq_empty`
* `Hartshorne.mul_mem_map_projCoordGrading`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- A variable belonging to a chart that misses `Y` vanishes on `Y`, so its
class in `S(Y)` is zero. This is what makes the monomials outside the relevant
charts disappear. -/
theorem mk_X_eq_zero_of_inter_eq_empty {Y : Set (ProjectiveSpace k σ)} (i : σ)
    (h : ¬ (Y ∩ standardChart i).Nonempty) :
    (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.subset_span ⟨⟨1, isHomogeneous_X k i⟩, fun P hP => ?_⟩
  show eval P.rep (X i) = 0
  rw [eval_X]
  by_contra hne
  exact h ⟨P, hP, mem_standardChart_iff.2 hne⟩

/-- **The pigeonhole.** An exponent of total degree `N` supported on `good`,
with `N` at least the sum of the bounds over `good`, must reach one of them. -/
theorem exists_le_of_degree_le {good : Finset σ} (hne : good.Nonempty) (Ndeg : σ → ℕ)
    {d : σ →₀ ℕ} (hsupp : d.support ⊆ good) {N : ℕ} (hdeg : d.degree = N)
    (hN : ∑ i ∈ good, Ndeg i ≤ N) : ∃ i ∈ good, Ndeg i ≤ d i := by
  by_contra hcon
  push Not at hcon
  have hsum : ∑ i ∈ good, d i < ∑ i ∈ good, Ndeg i :=
    Finset.sum_lt_sum_of_nonempty hne hcon
  have hEq : ∑ i ∈ good, d i = N := by
    rw [← hdeg, Finsupp.degree]
    exact (Finset.sum_subset hsupp fun x _ hx => Finsupp.notMem_support_iff.1 hx).symm
  omega

/-- Splitting off a power of one variable from a monomial. -/
theorem monomial_eq_mul_X_pow [DecidableEq σ] {d : σ →₀ ℕ} {i : σ} {n : ℕ} (h : n ≤ d i)
    (c : k) : (monomial d c : MvPolynomial σ k)
      = monomial (d - Finsupp.single i n) c * X i ^ n := by
  rw [X_pow_eq_monomial, monomial_mul, mul_one, tsub_add_cancel_of_le]
  exact fun j => by
    rcases eq_or_ne j i with rfl | hj
    · simpa using h
    · simp [hj]

/-- And the degree drops by exactly the power removed. -/
theorem degree_sub_single [DecidableEq σ] {d : σ →₀ ℕ} {i : σ} {n : ℕ} (h : n ≤ d i) :
    (d - Finsupp.single i n).degree + n = d.degree := by
  have hle : Finsupp.single i n ≤ d := fun j => by
    rcases eq_or_ne j i with rfl | hj
    · simpa using h
    · simp [hj]
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, Finsupp.degree_single]

variable [Finite σ] [DecidableEq σ] {Y : Set (ProjectiveSpace k σ)}
  [IsDomain (homogeneousCoordinateRing Y)]

/-- The copy of `S(Y)_N` inside the fraction field. -/
noncomputable abbrev gradedImage (Y : Set (ProjectiveSpace k σ))
    [IsDomain (homogeneousCoordinateRing Y)] (N : ℕ) :
    Submodule k (Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y))) :=
  (projCoordGrading Y N).map
    (IsScalarTower.toAlgHom k (homogeneousCoordinateRing Y)
      (Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y)))).toLinearMap

omit [Finite σ] in
/-- **The degree bound.** If `xᵢ^{Nᵢ} · t` lies in `S(Y)` for every chart meeting
`Y`, then `t` multiplies `S(Y)_N` into itself once `N` is at least the sum of
the `Nᵢ`.

Monomial by monomial: a variable from a chart missing `Y` kills its monomial,
and otherwise the pigeonhole supplies an `i` with `αᵢ ≥ Nᵢ`, so the monomial
absorbs the denominator. -/
theorem mul_mem_gradedImage
    (good : Finset σ) (hgood : ∀ i, i ∈ good ↔ (Y ∩ standardChart i).Nonempty)
    (hne : good.Nonempty) (Ndeg : σ → ℕ) (g : σ → MvPolynomial σ k)
    (hg : ∀ i ∈ good, g i ∈ homogeneousSubmodule σ k (Ndeg i))
    (t : Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y)))
    (ht : ∀ i ∈ good,
      t * algebraMap _ _ (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i ^ Ndeg i))
        = algebraMap _ _ (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (g i)))
    {N : ℕ} (hN : ∑ i ∈ good, Ndeg i ≤ N)
    {s : homogeneousCoordinateRing Y} (hs : s ∈ projCoordGrading Y N) :
    t * algebraMap _ _ s ∈ gradedImage Y N := by
  obtain ⟨p, hp, rfl⟩ := hs
  have hph : p.IsHomogeneous N := (mem_homogeneousSubmodule _ _).1 hp
  show t * algebraMap _ _ (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) p) ∈ _
  rw [MvPolynomial.as_sum p, map_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = N := by
    rw [Finsupp.degree_eq_weight_one]
    exact hph (MvPolynomial.mem_support_iff.1 hd)
  by_cases hsupp : ↑d.support ⊆ (good : Set σ)
  · -- Pigeonhole: some variable carries at least its threshold.
    obtain ⟨i, hi, hle⟩ := exists_le_of_degree_le hne Ndeg (by exact_mod_cast hsupp) hdeg hN
    refine ⟨Ideal.Quotient.mk (homogeneousVanishingIdeal Y)
      (g i * monomial (d - Finsupp.single i (Ndeg i)) (MvPolynomial.coeff d p)), ?_, ?_⟩
    · refine ⟨g i * monomial (d - Finsupp.single i (Ndeg i)) (MvPolynomial.coeff d p), ?_, rfl⟩
      refine (mem_homogeneousSubmodule _ _).2 ?_
      have hd' : (Ndeg i) + (d - Finsupp.single i (Ndeg i)).degree = N := by
        rw [add_comm, degree_sub_single hle, hdeg]
      exact hd' ▸ ((mem_homogeneousSubmodule _ _).1 (hg i hi)).mul
        (isHomogeneous_monomial _ rfl)
    · show algebraMap (homogeneousCoordinateRing Y)
        (Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y)))
        (Ideal.Quotient.mk (homogeneousVanishingIdeal Y)
          (g i * monomial (d - Finsupp.single i (Ndeg i)) (MvPolynomial.coeff d p))) = _
      rw [monomial_eq_mul_X_pow hle, map_mul, map_mul, map_mul, map_mul, ← ht i hi]
      ring
  · -- A variable from a chart missing `Y` kills the monomial.
    obtain ⟨j, hjd, hjg⟩ := Set.not_subset.1 hsupp
    have hj0 : d j ≠ 0 := Finsupp.mem_support_iff.1 hjd
    have hXj : Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X j) = 0 :=
      mk_X_eq_zero_of_inter_eq_empty j fun h => hjg ((hgood j).2 h)
    have hzero : Ideal.Quotient.mk (homogeneousVanishingIdeal Y)
        (monomial d (MvPolynomial.coeff d p)) = 0 := by
      rw [monomial_eq_mul_X_pow (le_refl (d j)), map_mul, map_pow, hXj, zero_pow hj0, mul_zero]
    rw [hzero, map_zero, mul_zero]
    exact Submodule.zero_mem _

end Hartshorne
