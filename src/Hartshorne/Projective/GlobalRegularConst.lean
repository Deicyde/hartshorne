/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.ChartRepresentation
import Hartshorne.Projective.DegreeBound
import Hartshorne.Projective.StableSubspace
import Hartshorne.Projective.CanonicalRational

/-!
# Theorem 3.4(a)

Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(a) (pp. 18-19).

For `Y` a projective variety, `𝒪(Y) = k`.

The pieces are all in place; this file joins them. A global regular `f` is a
ratio of forms `gᵢ/xᵢ^{Nᵢ}` on each chart meeting `Y`; those ratios agree, so
they define one element `t` of the fraction field of `S(Y)`; the degree bound
makes `t` stabilise `S(Y)_N` for `N ≥ Σ Nᵢ`; that piece is nonzero and
finite-dimensional, so `t` is integral over `k` and hence constant; and a
constant on one chart is constant on `Y`.

## Where irreducibility is used

Twice, and both times to compare charts. The ratios on `Uᵢ` and `U_{i₀}` agree
where both are defined, which is an open subset of `Y`, and to conclude that
`gᵢ₀ xᵢ^{Nᵢ} − gᵢ x_{i₀}^{N_{i₀}}` lies in `J(Y)` one needs that a homogeneous
form vanishing on a nonempty open subset of `Y` vanishes on `Y`. The same fact,
at the end, promotes `f = c` from one chart to all of `Y`.

## Main results

* `Hartshorne.exists_const_eq_globalRegular`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (ProjectiveSpace k σ)}

/-- **A form vanishing on a nonempty open piece of `Y` vanishes on `Y`.**

Irreducibility, in the form that a nonempty open subset is dense: the locus
where the form vanishes is closed and contains that subset. -/
theorem eval_eq_zero_of_eval_eq_zero_on_open (hYirr : IsIrreducible Y)
    {n : ℕ} {u : MvPolynomial σ k} (hu : u.IsHomogeneous n)
    {O : Set (ProjectiveSpace k σ)} (hO : IsOpen O) (hYO : (Y ∩ O).Nonempty)
    (hvan : ∀ P ∈ Y ∩ O, eval P.rep u = 0) :
    ∀ P ∈ Y, eval P.rep u = 0 := by
  intro P hP
  by_contra hne
  obtain ⟨Q, hQY, hQO, hQC⟩ :=
    hYirr.2 O {R | eval R.rep u ≠ 0} hO (isOpen_projNonvanishing hu) hYO ⟨P, hP, hne⟩
  exact hQC (hvan Q ⟨hQY, hQO⟩)

/-- Two charts both meeting `Y` meet each other on `Y`. -/
theorem inter_inter_nonempty (hYirr : IsIrreducible Y) (i j : σ)
    (hi : (Y ∩ standardChart i).Nonempty) (hj : (Y ∩ standardChart j).Nonempty) :
    (Y ∩ (standardChart i ∩ standardChart j)).Nonempty :=
  hYirr.2 _ _ (isOpen_standardChart i) (isOpen_standardChart j) hi hj

/-- **The chart ratios agree.**

If `F` is `g/xᵢ^m` on `Y ∩ Uᵢ` and `h/xⱼ^n` on `Y ∩ Uⱼ`, then
`g·xⱼ^n = h·xᵢ^m` in `S(Y)`. The two sides are homogeneous of the same degree
and agree where both charts meet `Y`, which by irreducibility is enough. -/
theorem mk_cross_eq (hYirr : IsIrreducible Y) {F : ProjectiveSpace k σ → k}
    {i j : σ} {m n : ℕ} {g h : MvPolynomial σ k}
    (hg : g.IsHomogeneous m) (hh : h.IsHomogeneous n)
    (hi : (Y ∩ standardChart i).Nonempty) (hj : (Y ∩ standardChart j).Nonempty)
    (hgr : ∀ P ∈ Y, P ∈ standardChart i → F P * P.rep i ^ m = eval P.rep g)
    (hhr : ∀ P ∈ Y, P ∈ standardChart j → F P * P.rep j ^ n = eval P.rep h) :
    Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (g * X j ^ n)
      = Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (h * X i ^ m) := by
  have hXj : (X j ^ n : MvPolynomial σ k).IsHomogeneous n := by
    simpa using (isHomogeneous_X k j).pow n
  have hXi : (X i ^ m : MvPolynomial σ k).IsHomogeneous m := by
    simpa using (isHomogeneous_X k i).pow m
  have hu : (g * X j ^ n - h * X i ^ m).IsHomogeneous (m + n) := by
    refine (hg.mul hXj).sub ?_
    rw [Nat.add_comm m n]
    exact hh.mul hXi
  refine Ideal.Quotient.eq.2 (Ideal.subset_span ⟨⟨m + n, hu⟩, ?_⟩)
  · refine eval_eq_zero_of_eval_eq_zero_on_open hYirr hu
      ((isOpen_standardChart i).inter (isOpen_standardChart j))
      (inter_inter_nonempty hYirr i j hi hj) ?_
    rintro P ⟨hPY, hPi, hPj⟩
    rw [map_sub, sub_eq_zero, map_mul, map_mul, map_pow, map_pow, eval_X, eval_X,
      ← hgr P hPY hPi, ← hhr P hPY hPj]
    ring

/-- A power of a chart variable is nonzero in `S(Y)` when the chart meets `Y`. -/
theorem mk_X_pow_ne_zero {i : σ} (hi : (Y ∩ standardChart i).Nonempty) (N : ℕ) :
    Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i ^ N) ≠ 0 := by
  intro hzero
  obtain ⟨P, hPY, hPc⟩ := hi
  have hmem : (X i ^ N : MvPolynomial σ k) ∈ homogeneousVanishingIdeal Y :=
    Ideal.Quotient.eq_zero_iff_mem.1 hzero
  have hvan := homogeneousVanish_of_mem_homogeneousVanishingIdeal hmem hPY
  rw [show HomogeneousVanish (X i ^ N : MvPolynomial σ k) P
    ↔ eval P.rep (X i ^ N) = 0 from Iff.rfl, map_pow, eval_X] at hvan
  exact pow_ne_zero N (rep_ne_zero_of_mem_standardChart hPc) hvan

section Main

variable [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ]

/-- **Theorem 3.4(a)**: `𝒪(Y) = k` for a projective variety.

A global regular `f` is `gᵢ/xᵢ^{Nᵢ}` on each chart meeting `Y`; those ratios
agree, so they are one element `t` of the fraction field of `S(Y)`; the degree
bound makes `t` stabilise `S(Y)_N` for `N ≥ Σ Nᵢ`; that piece is nonzero and
finite-dimensional, so `t` is a constant; and a constant on one chart is a
constant on `Y`. -/
theorem exists_const_eq_globalRegular (hY : IsProjVariety Y)
    (f : (Variety.ofQuasiProjective hY.isQuasiProjVariety).globalRegular) :
    ∃ c : k, ∀ (P : ProjectiveSpace k σ) (hPY : P ∈ Y), f.1 ⟨⟨P, hPY⟩, trivial⟩ = c := by
  classical
  have hdom : IsDomain (homogeneousCoordinateRing Y) := isDomain_homogeneousCoordinateRing hY
  -- The charts that meet `Y`, and the ratio on each.
  set good : Finset σ := (Set.toFinite {i : σ | (Y ∩ standardChart i).Nonempty}).toFinset with hgooddef
  have hgood : ∀ i, i ∈ good ↔ (Y ∩ standardChart i).Nonempty := by
    intro i; rw [hgooddef, Set.Finite.mem_toFinset]; rfl
  obtain ⟨P₀, hP₀⟩ := hY.1.1
  obtain ⟨i₀, hi₀⟩ : ∃ i, P₀ ∈ standardChart i := by
    have : P₀ ∈ ⋃ i : σ, standardChart i := by rw [iUnion_standardChart]; trivial
    simpa using this
  have hi₀good : i₀ ∈ good := (hgood i₀).2 ⟨P₀, hP₀, hi₀⟩
  have hgoodne : good.Nonempty := ⟨i₀, hi₀good⟩
  set F : ProjectiveSpace k σ → k :=
    fun P => if hP : P ∈ Y then f.1 ⟨⟨P, hP⟩, trivial⟩ else 0 with hFdef
  have hrep : ∀ i : σ, ∃ (N : ℕ) (g : MvPolynomial σ k), g.IsHomogeneous N ∧
      ((Y ∩ standardChart i).Nonempty →
        ∀ P ∈ Y, P ∈ standardChart i → F P * P.rep i ^ N = eval P.rep g) := by
    intro i
    by_cases hi : (Y ∩ standardChart i).Nonempty
    · obtain ⟨N, g, hg, hgr⟩ := exists_homogeneous_repr_of_globalRegular hY i hi f
      refine ⟨N, g, hg, fun _ P hPY hPc => ?_⟩
      rw [hFdef]
      simpa [dif_pos hPY] using hgr P hPY hPc
    · exact ⟨0, 1, isHomogeneous_one _ _, fun h => absurd h hi⟩
  choose Ndeg gpoly hgh hgr using hrep
  -- The single element of the fraction field that all the ratios define.
  have hden : (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i₀ ^ Ndeg i₀))
      ∈ (⊥ : Ideal (homogeneousCoordinateRing Y)).primeCompl :=
    fun hmem => mk_X_pow_ne_zero ((hgood i₀).1 hi₀good) _ (Ideal.mem_bot.1 hmem)
  set t : Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y)) :=
    Localization.mk (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (gpoly i₀))
      ⟨_, hden⟩ with htdef
  have ht : ∀ i ∈ good, t * algebraMap _ _
      (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i ^ Ndeg i))
      = algebraMap _ _ (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (gpoly i)) := by
    intro i hi
    have hcross := mk_cross_eq hY.1 (F := F) (hgh i₀) (hgh i)
      ((hgood i₀).1 hi₀good) ((hgood i).1 hi)
      (hgr i₀ ((hgood i₀).1 hi₀good)) (hgr i ((hgood i).1 hi))
    rw [htdef, ← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, mul_one]
    rw [← map_mul, ← map_mul, hcross, mul_comm]
  -- The degree bound.
  set N : ℕ := ∑ i ∈ good, Ndeg i with hNdef
  have hstab : ∀ v ∈ gradedImage Y N, t * v ∈ gradedImage Y N := by
    rintro v ⟨s, hs, rfl⟩
    exact mul_mem_gradedImage good hgood hgoodne Ndeg gpoly
      (fun i _ => (mem_homogeneousSubmodule _ _).2 (hgh i)) t ht le_rfl hs
  -- The graded piece is finite-dimensional and nonzero.
  have hfd : Module.Finite k ↥(gradedImage Y N) :=
    Module.Finite.of_fg ((fg_projCoordGrading Y N).map _)
  have hinj : Function.Injective
      (algebraMap (homogeneousCoordinateRing Y)
        (Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y)))) :=
    IsLocalization.injective
      (S := Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y)))
      (M := (⊥ : Ideal (homogeneousCoordinateRing Y)).primeCompl)
      (le_of_eq Ideal.primeCompl_bot)
  have hVne : gradedImage Y N ≠ ⊥ := by
    intro hbot
    have hmem : algebraMap (homogeneousCoordinateRing Y) _
        (Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i₀ ^ N)) ∈ gradedImage Y N :=
      ⟨_, ⟨X i₀ ^ N, by simpa using (isHomogeneous_X k i₀).pow N, rfl⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact mk_X_pow_ne_zero ((hgood i₀).1 hi₀good) N (hinj (by simpa using hmem))
  -- Integrality over `k`, hence constancy.
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_mul_mem
    (K := Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y)))
    (gradedImage Y N) hVne hstab
  refine ⟨c, ?_⟩
  -- Read the constant back on the chart, then spread it over `Y`.
  have hCA : algebraMap k (Localization.AtPrime (⊥ : Ideal (homogeneousCoordinateRing Y))) c
      = algebraMap (homogeneousCoordinateRing Y) _
        (algebraMap k (homogeneousCoordinateRing Y) c) :=
    (IsScalarTower.algebraMap_apply k (homogeneousCoordinateRing Y) _ c)
  have hchart : ∀ P ∈ Y, P ∈ standardChart i₀ → F P = c := by
    intro P hPY hPc
    have hAeq : algebraMap k (homogeneousCoordinateRing Y) c
        * Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (X i₀ ^ Ndeg i₀)
        = Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (gpoly i₀) := by
      refine hinj ?_
      rw [map_mul, ← hCA, hc]
      exact ht i₀ hi₀good
    have hpoly : (C c * X i₀ ^ Ndeg i₀ - gpoly i₀ : MvPolynomial σ k)
        ∈ homogeneousVanishingIdeal Y := by
      refine Ideal.Quotient.eq.1 ?_
      rw [map_mul, ← hAeq]
      rfl
    have hvan := homogeneousVanish_of_mem_homogeneousVanishingIdeal hpoly hPY
    rw [show HomogeneousVanish (C c * X i₀ ^ Ndeg i₀ - gpoly i₀ : MvPolynomial σ k) P
      ↔ eval P.rep (C c * X i₀ ^ Ndeg i₀ - gpoly i₀) = 0 from Iff.rfl,
      map_sub, sub_eq_zero, map_mul, map_pow, eval_X, eval_C] at hvan
    have hfP := hgr i₀ ((hgood i₀).1 hi₀good) P hPY hPc
    have hne0 : (P.rep i₀ : k) ^ Ndeg i₀ ≠ 0 :=
      pow_ne_zero _ (rep_ne_zero_of_mem_standardChart hPc)
    exact mul_right_cancel₀ hne0 (hfP.trans hvan.symm)
  -- The identity principle spreads it from the chart to all of `Y`.
  have hconst : f.1 = fun _ => c := by
    refine Variety.eq_of_eqOn (X := Variety.ofQuasiProjective hY.isQuasiProjVariety)
      f.2 (Subalgebra.algebraMap_mem _ c)
      (V := {x : (⊤ : Opens (Variety.ofQuasiProjective hY.isQuasiProjVariety).carrier) |
        x.1.1 ∈ standardChart i₀})
      ((isOpen_standardChart i₀).preimage (by fun_prop)) ⟨⟨⟨P₀, hP₀⟩, trivial⟩, hi₀⟩ ?_
    intro x hx
    have hval := hchart x.1.1 x.1.2 hx
    rw [hFdef] at hval
    simp only [dif_pos x.1.2] at hval
    exact hval
  intro P hPY
  exact congrFun hconst ⟨⟨P, hPY⟩, trivial⟩

end Main

end Hartshorne
