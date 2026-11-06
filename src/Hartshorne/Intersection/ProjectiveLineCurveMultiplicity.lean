/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.LocalPlaneCurveMultiplicity
import Hartshorne.Projective.Dehomogenize

/-!
# A line meets a projective plane curve of degree `d` in `d` points

Hartshorne, *Algebraic Geometry*, Exercise I.5.4(c) (p. 36).

For homogeneous `G, F` in three variables and `P ∈ ℙ²`, the local intersection multiplicity
`(G · F)_P` is computed in a standard affine chart containing `P` from the dehomogenizations.
For a projective plane curve `Y = Z(F)` of degree `d` and a line `L = Z(ℓ)` not contained in
`Y`, the multiplicities over `L ∩ Y` add up to `d`.

## Method

Choose `Q ∈ L \ Y` and a second vector `A` with `L = ℙ(span(A, Q))`.  Then `L ∩ Y` is the image
of the roots of `h(t) = F(A + tQ)`, which has degree exactly `d` because its leading coefficient
is `F(Q) ≠ 0`.  At `[A + tQ]`, the affine computation of the local multiplicity along a line
(in any chart containing the point) gives the order of vanishing of `F(P̃ + τ W)`, where `P̃` is
the chart representative and `W` the chart direction of `L`.  Since `F` is homogeneous, this
order is unchanged when the base point is rescaled and the direction is replaced by `αP̃ + βQ`
with `β ≠ 0`; so it is the root multiplicity of `t` in `h`.  Over an algebraically closed field
the root multiplicities of `h` add up to `deg h = d`.

## Main definitions and results

* `Hartshorne.projectivePlaneLocalIntersectionMultiplicity`: `(G · F)_P` for `P ∈ ℙ²`.
* `Hartshorne.affineLocalIntersectionMultiplicity_chart_eq_rootMultiplicity`: the local
  multiplicity on a line in any chart is a root multiplicity.
* `Hartshorne.finite_and_finsum_projectivePlaneLocalIntersectionMultiplicity`:
  Exercise 5.4(c).
-/

namespace Hartshorne
open MvPolynomial

noncomputable section
universe u
variable {k : Type u} [Field k] {σ : Type*}

/-- The exponent `(d - j, j)` of a binary form of degree `d`. -/
def binaryExponent (d j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (d - j) + Finsupp.single 1 j

theorem binaryExponent_apply_zero (d j : ℕ) : binaryExponent d j 0 = d - j := by
  simp [binaryExponent]

theorem binaryExponent_apply_one (d j : ℕ) : binaryExponent d j 1 = j := by
  simp [binaryExponent]

theorem binaryForm_eq_sum {G : MvPolynomial (Fin 2) k} {d : ℕ} (hG : G.IsHomogeneous d) :
    G = ∑ j ∈ Finset.range (d + 1),
      monomial (binaryExponent d j) (coeff (binaryExponent d j) G) := by
  classical
  ext x
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hx : x.degree = d
  · have hx' : x 0 + x 1 = d := by rw [← hx, Finsupp.degree_eq_sum, Fin.sum_univ_two]
    have hxe : binaryExponent d (x 1) = x := by
      ext i; fin_cases i
      · simp [binaryExponent_apply_zero]; omega
      · simp [binaryExponent_apply_one]
    rw [Finset.sum_eq_single (x 1)]
    · rw [if_pos hxe, hxe]
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      rw [← h, binaryExponent_apply_one]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega : x 1 < d + 1)) h
  · rw [hG.coeff_eq_zero hx]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    rw [if_neg]
    rintro rfl
    apply hx
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, binaryExponent_apply_zero,
      binaryExponent_apply_one]
    have := Finset.mem_range.1 hj
    omega

/-- A binary form of degree `d` evaluates as `∑ⱼ cⱼ u^(d-j) w^j`. -/
theorem aeval_binaryForm {G : MvPolynomial (Fin 2) k} {d : ℕ} (hG : G.IsHomogeneous d)
    {R : Type*} [CommRing R] [Algebra k R] (u w : R) :
    aeval ![u, w] G = ∑ j ∈ Finset.range (d + 1),
      algebraMap k R (coeff (binaryExponent d j) G) * u ^ (d - j) * w ^ j := by
  conv_lhs => rw [binaryForm_eq_sum hG]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two,
    binaryExponent_apply_zero, binaryExponent_apply_one]
  simp [mul_assoc]


/-- The restriction `t ↦ F(X + tY)` of a polynomial to a parametrized line. -/
def homogeneousLineRestrict (F : MvPolynomial σ k) (Xv Yv : σ → k) : Polynomial k :=
  aeval (fun j => Polynomial.C (Xv j) + Polynomial.C (Yv j) * Polynomial.X) F

/-- The binary form `(s, t) ↦ F(sX + tY)`. -/
def binaryRestrict (F : MvPolynomial σ k) (Xv Yv : σ → k) : MvPolynomial (Fin 2) k :=
  aeval (fun j => C (Xv j) * X 0 + C (Yv j) * X 1) F

theorem aeval_binaryRestrict (F : MvPolynomial σ k) (Xv Yv : σ → k) {R : Type*} [CommRing R]
    [Algebra k R] (u w : R) :
    aeval ![u, w] (binaryRestrict F Xv Yv) =
      aeval (fun j => algebraMap k R (Xv j) * u + algebraMap k R (Yv j) * w) F := by
  rw [binaryRestrict, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext j
  simp

theorem isHomogeneous_binaryRestrict {F : MvPolynomial σ k} {d : ℕ} (hF : F.IsHomogeneous d)
    (Xv Yv : σ → k) : (binaryRestrict F Xv Yv).IsHomogeneous d := by
  have := hF.aeval (S := k) (τ := Fin 2) (fun j => C (Xv j) * X 0 + C (Yv j) * X 1) (n := 1)
    (fun j => ((isHomogeneous_C_mul_X (Xv j) 0).add (isHomogeneous_C_mul_X (Yv j) 1)))
  rw [one_mul] at this
  exact this

/-- The coefficients of the binary form `F(sX + tY)`. -/
abbrev binaryCoeff (F : MvPolynomial σ k) (d : ℕ) (Xv Yv : σ → k) (j : ℕ) : k :=
  coeff (binaryExponent d j) (binaryRestrict F Xv Yv)

theorem homogeneousLineRestrict_eq_sum {F : MvPolynomial σ k} {d : ℕ} (hF : F.IsHomogeneous d)
    (Xv Yv : σ → k) :
    homogeneousLineRestrict F Xv Yv = ∑ j ∈ Finset.range (d + 1),
      Polynomial.C (binaryCoeff F d Xv Yv j) * Polynomial.X ^ j := by
  have h := aeval_binaryForm (isHomogeneous_binaryRestrict hF Xv Yv) (1 : Polynomial k)
    Polynomial.X
  rw [aeval_binaryRestrict] at h
  simp only [Polynomial.algebraMap_eq, mul_one, one_pow] at h
  rw [homogeneousLineRestrict, h]

theorem coeff_homogeneousLineRestrict {F : MvPolynomial σ k} {d : ℕ} (hF : F.IsHomogeneous d)
    (Xv Yv : σ → k) (i : ℕ) :
    (homogeneousLineRestrict F Xv Yv).coeff i =
      if i ≤ d then binaryCoeff F d Xv Yv i else 0 := by
  classical
  rw [homogeneousLineRestrict_eq_sum hF, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

theorem eval_eq_binaryCoeff {F : MvPolynomial σ k} {d : ℕ} (hF : F.IsHomogeneous d)
    (Xv Yv : σ → k) : eval Yv F = binaryCoeff F d Xv Yv d := by
  have h := aeval_binaryForm (isHomogeneous_binaryRestrict hF Xv Yv) (0 : k) 1
  rw [aeval_binaryRestrict] at h
  simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_zero, zero_add, mul_one,
    one_pow] at h
  rw [Finset.sum_eq_single d] at h
  · rw [Nat.sub_self, pow_zero, mul_one] at h
    change eval Yv F = coeff (binaryExponent d d) (binaryRestrict F Xv Yv)
    rw [← h, ← coe_aeval_eq_eval]
    rfl
  · intro j hj hjd
    have : 0 < d - j := by have := Finset.mem_range.1 hj; omega
    rw [zero_pow this.ne', mul_zero]
  · intro h; exact absurd (Finset.self_mem_range_succ d) h


theorem homogeneousLineRestrict_change {F : MvPolynomial σ k} {d : ℕ} (hF : F.IsHomogeneous d)
    (Xv Yv : σ → k) (l α β : k) :
    homogeneousLineRestrict F (l • Xv) (α • Xv + β • Yv) = ∑ j ∈ Finset.range (d + 1),
      Polynomial.C (binaryCoeff F d Xv Yv j * β ^ j) *
        ((Polynomial.C l + Polynomial.C α * Polynomial.X) ^ (d - j) * Polynomial.X ^ j) := by
  have h := aeval_binaryForm (isHomogeneous_binaryRestrict hF Xv Yv)
    (Polynomial.C l + Polynomial.C α * Polynomial.X) (Polynomial.C β * Polynomial.X)
  rw [aeval_binaryRestrict] at h
  rw [homogeneousLineRestrict]
  have hfun : (fun j => Polynomial.C ((l • Xv) j) + Polynomial.C ((α • Xv + β • Yv) j) *
      Polynomial.X) = (fun j => algebraMap k (Polynomial k) (Xv j) *
        (Polynomial.C l + Polynomial.C α * Polynomial.X) +
        algebraMap k (Polynomial k) (Yv j) * (Polynomial.C β * Polynomial.X)) := by
    funext j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add,
      Polynomial.algebraMap_eq]
    ring
  rw [hfun, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.algebraMap_eq, map_mul, map_pow, mul_pow]
  ring

/-- **Changing the parametrization of a line.**  Replacing the base point `X` by `l X`
(`l ≠ 0`) and the direction `Y` by `α X + β Y` (`β ≠ 0`) does not change the order of vanishing
at `t = 0` of `F(X + tY)` for a homogeneous `F`. -/
theorem natTrailingDegree_homogeneousLineRestrict_change {F : MvPolynomial σ k} {d : ℕ}
    (hF : F.IsHomogeneous d) (Xv Yv : σ → k) {l α β : k} (hl : l ≠ 0) (hβ : β ≠ 0)
    (hp : homogeneousLineRestrict F Xv Yv ≠ 0) :
    homogeneousLineRestrict F (l • Xv) (α • Xv + β • Yv) ≠ 0 ∧
      (homogeneousLineRestrict F (l • Xv) (α • Xv + β • Yv)).natTrailingDegree =
        (homogeneousLineRestrict F Xv Yv).natTrailingDegree := by
  classical
  set p := homogeneousLineRestrict F Xv Yv
  set e := p.natTrailingDegree
  set c := binaryCoeff F d Xv Yv
  have hpe : p.coeff e ≠ 0 := by
    rw [Polynomial.coeff_natTrailingDegree_ne_zero]; exact hp
  have hed : e ≤ d := by
    by_contra h
    exact hpe (by rw [coeff_homogeneousLineRestrict hF, if_neg h])
  have hce : c e ≠ 0 := by
    rwa [coeff_homogeneousLineRestrict hF, if_pos hed] at hpe
  have hclt : ∀ j < e, c j = 0 := by
    intro j hj
    have := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
    rwa [coeff_homogeneousLineRestrict hF, if_pos (by omega)] at this
  set q := homogeneousLineRestrict F (l • Xv) (α • Xv + β • Yv)
  have hq : ∀ i, q.coeff i = ∑ j ∈ Finset.range (d + 1), c j * β ^ j *
      (if j ≤ i then ((Polynomial.C l + Polynomial.C α * Polynomial.X) ^ (d - j)).coeff (i - j)
        else 0) := by
    intro i
    simp only [q, homogeneousLineRestrict_change hF, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
    rfl
  have hqe : q.coeff e = c e * β ^ e * l ^ (d - e) := by
    rw [hq, Finset.sum_eq_single e]
    · rw [if_pos le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero]
      simp
    · intro j _ hje
      rcases lt_or_gt_of_ne hje with h | h
      · rw [hclt j h]; simp
      · rw [if_neg (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have hqe0 : q.coeff e ≠ 0 := by
    rw [hqe]; exact mul_ne_zero (mul_ne_zero hce (pow_ne_zero _ hβ)) (pow_ne_zero _ hl)
  have hqne : q ≠ 0 := fun h => hqe0 (by rw [h, Polynomial.coeff_zero])
  refine ⟨hqne, le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hqe0)
    (Polynomial.le_natTrailingDegree hqne fun i hi => ?_)⟩
  rw [hq]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hji : j ≤ i
  · rw [hclt j (by omega)]; simp
  · rw [if_neg hji, mul_zero]


/-- The linear form `a₀ x₀ + a₁ x₁ + a₂ x₂`; for `a ≠ 0` its zero set is a line in `ℙ²`. -/
def projectivePlaneLineForm (a : Fin 3 → k) : MvPolynomial (Fin 3) k :=
  ∑ j, C (a j) * X j

theorem eval_projectivePlaneLineForm (a : Fin 3 → k) (x : Fin 3 → k) :
    eval x (projectivePlaneLineForm a) = ∑ j, a j * x j := by
  simp [projectivePlaneLineForm]

theorem isHomogeneous_projectivePlaneLineForm (a : Fin 3 → k) :
    (projectivePlaneLineForm a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (a j) j

/-- The affine chart point, with coordinates indexed by `Fin 2` via `i.succAbove`. -/
abbrev chartPointFin (i : Fin 3) (p : {j : Fin 3 // j ≠ i} → k) : Fin 2 → k :=
  p ∘ finSuccAboveEquiv i

theorem chartInvVec_succAbove (i : Fin 3) (p : {j : Fin 3 // j ≠ i} → k) (t : Fin 2) :
    chartInvVec i p (i.succAbove t) = chartPointFin i p t := by
  rw [chartInvVec_of_ne p (Fin.succAbove_ne i t)]
  rfl

/-- The direction, in homogeneous coordinates, of the line `a = 0` inside the chart `xᵢ ≠ 0`. -/
def chartLineDirection (a : Fin 3 → k) (i : Fin 3) : Fin 3 → k :=
  i.insertNth 0 ![-a (i.succAbove 1), a (i.succAbove 0)]

theorem chartLineDirection_self (a : Fin 3 → k) (i : Fin 3) : chartLineDirection a i i = 0 := by
  simp [chartLineDirection]

theorem eval_chartLineDirection (a : Fin 3 → k) (i : Fin 3) :
    ∑ j, a j * chartLineDirection a i j = 0 := by
  rw [Fin.sum_univ_succAbove _ i]
  simp [chartLineDirection, Fin.sum_univ_two]
  ring

theorem rename_dehomogenize_projectivePlaneLineForm [IsAlgClosed k] (a : Fin 3 → k) (i : Fin 3) :
    rename (finSuccAboveEquiv i).symm (dehomogenize i (projectivePlaneLineForm a)) =
      planeLineEquation (a (i.succAbove 0)) (a (i.succAbove 1)) (a i) := by
  apply MvPolynomial.funext
  intro y
  rw [eval_rename, eval_dehomogenize, eval_projectivePlaneLineForm, eval_planeLineEquation,
    Fin.sum_univ_succAbove _ i, Fin.sum_univ_two, chartInvVec_self]
  have h : ∀ t : Fin 2, chartInvVec i (y ∘ (finSuccAboveEquiv i).symm) (i.succAbove t) = y t := by
    intro t
    rw [chartInvVec_succAbove]
    simp
  rw [h, h]
  ring


theorem lineRestrict_rename_dehomogenize (a : Fin 3 → k) (i : Fin 3)
    (p : {j : Fin 3 // j ≠ i} → k) (F : MvPolynomial (Fin 3) k) :
    lineRestrict (chartPointFin i p) ![-a (i.succAbove 1), a (i.succAbove 0)]
        (rename (finSuccAboveEquiv i).symm (dehomogenize i F)) =
      homogeneousLineRestrict F (chartInvVec i p) (chartLineDirection a i) := by
  rw [homogeneousLineRestrict, ← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨t, rfl⟩
  · simp [chartLineDirection_self]
  · rw [AlgHom.comp_apply, AlgHom.comp_apply, dehomogenize_X_of_ne (Fin.succAbove_ne i t),
      rename_X, aeval_X, aeval_X, chartInvVec_succAbove]
    have ht : (finSuccAboveEquiv i).symm ⟨i.succAbove t, Fin.succAbove_ne i t⟩ = t := by
      rw [Equiv.symm_apply_eq]; rfl
    rw [ht]
    simp [chartLineDirection]

/-- **The local multiplicity of a line in an affine chart.**  In the chart `xᵢ ≠ 0`, at a chart
point `p` of the line `a = 0`, the local intersection multiplicity of the line with `F = 0` is
the order of vanishing at `t = 0` of `F(p̃ + t w)`, where `p̃` is `p` with `1` in slot `i` and
`w` is the direction of the line in the chart. -/
theorem affineLocalIntersectionMultiplicity_chart [IsAlgClosed k] {a : Fin 3 → k} (ha : a ≠ 0)
    (F : MvPolynomial (Fin 3) k) (i : Fin 3) (p : {j : Fin 3 // j ≠ i} → k)
    (hpL : eval (chartInvVec i p) (projectivePlaneLineForm a) = 0)
    (hr : homogeneousLineRestrict F (chartInvVec i p) (chartLineDirection a i) ≠ 0) :
    affineLocalIntersectionMultiplicity (dehomogenize i (projectivePlaneLineForm a))
        (dehomogenize i F) p =
      (homogeneousLineRestrict F (chartInvVec i p) (chartLineDirection a i)).natTrailingDegree := by
  set e := finSuccAboveEquiv i
  set q := chartPointFin i p
  have he : ∀ f, eval q (renameEquiv k e.symm f) = eval p f := by
    intro f
    rw [renameEquiv_apply, eval_rename]
    have : q ∘ e.symm = p := by funext j; simp [q, e]
    rw [this]
  rw [← affineLocalIntersectionMultiplicity_algEquiv (renameEquiv k e.symm) p q he,
    renameEquiv_apply, renameEquiv_apply, rename_dehomogenize_projectivePlaneLineForm]
  have hP : a (i.succAbove 0) * q 0 + a (i.succAbove 1) * q 1 + a i = 0 := by
    rw [← eval_planeLineEquation, ← rename_dehomogenize_projectivePlaneLineForm,
      ← renameEquiv_apply, he, eval_dehomogenize, hpL]
  have hab : a (i.succAbove 0) ≠ 0 ∨ a (i.succAbove 1) ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    rw [h.1, h.2, zero_mul, zero_mul, zero_add, zero_add] at hP
    apply ha
    funext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨t, rfl⟩
    · exact hP
    · fin_cases t
      · exact h.1
      · exact h.2
  rw [affineLocalIntersectionMultiplicity_planeLineEquation hab hP _
    (by rwa [lineRestrict_rename_dehomogenize]), lineRestrict_rename_dehomogenize]


theorem chartLineDirection_ne_zero {a : Fin 3 → k} (ha : a ≠ 0) (i : Fin 3)
    (p : {j : Fin 3 // j ≠ i} → k)
    (hpL : eval (chartInvVec i p) (projectivePlaneLineForm a) = 0) :
    chartLineDirection a i ≠ 0 := by
  intro h0
  have h1 : a (i.succAbove 0) = 0 := by
    have := congrFun h0 (i.succAbove 1)
    simpa [chartLineDirection] using this
  have h2 : a (i.succAbove 1) = 0 := by
    have := congrFun h0 (i.succAbove 0)
    simpa [chartLineDirection] using this
  rw [eval_projectivePlaneLineForm, Fin.sum_univ_succAbove _ i, Fin.sum_univ_two, h1, h2,
    chartInvVec_self] at hpL
  simp only [mul_one, zero_mul, add_zero] at hpL
  apply ha
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨t, rfl⟩
  · exact hpL
  · fin_cases t
    · exact h1
    · exact h2

theorem eval_homogeneousLineRestrict (F : MvPolynomial σ k) (Xv Yv : σ → k) (t : k) :
    (homogeneousLineRestrict F Xv Yv).eval t = eval (Xv + t • Yv) F := by
  rw [homogeneousLineRestrict, polynomial_eval_aeval]
  have : (fun j => (Polynomial.C (Xv j) + Polynomial.C (Yv j) * Polynomial.X).eval t) =
      Xv + t • Yv := by
    funext j
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [this]

theorem homogeneousLineRestrict_comp (F : MvPolynomial σ k) (Xv Yv : σ → k) (t : k) :
    (homogeneousLineRestrict F Xv Yv).comp (Polynomial.X + Polynomial.C t) =
      homogeneousLineRestrict F (Xv + t • Yv) Yv := by
  rw [homogeneousLineRestrict, homogeneousLineRestrict, Polynomial.comp_eq_aeval,
    ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext j
  simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Polynomial.algebraMap_eq]
  ring


/-- A chart containing a point of `ℙ²`. -/
def projectivePlaneChartIndex (P : ProjectiveSpace k (Fin 3)) : Fin 3 :=
  Classical.choose (exists_mem_standardChart P)

theorem mem_standardChart_projectivePlaneChartIndex (P : ProjectiveSpace k (Fin 3)) :
    P ∈ standardChart (projectivePlaneChartIndex P) :=
  Classical.choose_spec (exists_mem_standardChart P)

/-- **Local intersection multiplicity of projective plane curves.**  For homogeneous `G, F` and
`P ∈ ℙ²`, `(G · F)_P` is the local intersection multiplicity of the dehomogenizations in a
standard affine chart containing `P`. -/
def projectivePlaneLocalIntersectionMultiplicity (G F : MvPolynomial (Fin 3) k)
    (P : ProjectiveSpace k (Fin 3)) : ℕ∞ :=
  affineLocalIntersectionMultiplicity (dehomogenize (projectivePlaneChartIndex P) G)
    (dehomogenize (projectivePlaneChartIndex P) F) (chartMap (projectivePlaneChartIndex P) P)

theorem eval_projectivePlaneLineForm_add_smul (a x y : Fin 3 → k) (c : k) :
    eval (x + c • y) (projectivePlaneLineForm a) =
      eval x (projectivePlaneLineForm a) + c * eval y (projectivePlaneLineForm a) := by
  simp only [eval_projectivePlaneLineForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- On the line `ℓ = 0`, spanned by `A` and `Q`, the local intersection multiplicity with
`F = 0` at `[A + tQ]`, computed in any standard chart containing that point, is the multiplicity
of `t` as a root of `F(A + tQ)`. -/
theorem affineLocalIntersectionMultiplicity_chart_eq_rootMultiplicity [IsAlgClosed k]
    {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d) {a : Fin 3 → k} (ha : a ≠ 0)
    {A Q : Fin 3 → k} (hA : eval A (projectivePlaneLineForm a) = 0)
    (hQ : eval Q (projectivePlaneLineForm a) = 0)
    (hspan : ∀ x, eval x (projectivePlaneLineForm a) = 0 → ∃ s t : k, x = s • A + t • Q)
    (hh : homogeneousLineRestrict F A Q ≠ 0) (t : k) (hX : A + t • Q ≠ 0) (i : Fin 3)
    (hPi : Projectivization.mk k (A + t • Q) hX ∈ standardChart i) :
    affineLocalIntersectionMultiplicity (dehomogenize i (projectivePlaneLineForm a))
        (dehomogenize i F) (chartMap i (Projectivization.mk k (A + t • Q) hX)) =
      (homogeneousLineRestrict F A Q).rootMultiplicity t := by
  set Xv := A + t • Q
  set P := Projectivization.mk k Xv hX
  set p := chartMap i P
  set Pt := chartInvVec i p
  -- `Pt` is a nonzero multiple of `Xv`.
  obtain ⟨l, hl⟩ : ∃ l : k, l • Xv = Pt := by
    have h1 : Projectivization.mk k Pt (chartInvVec_ne_zero i p) = P := chartInv_chartMap hPi
    exact (Projectivization.mk_eq_mk_iff' k Pt Xv _ hX).1 h1
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hl
    exact chartInvVec_ne_zero i p hl.symm
  have hXL : eval Xv (projectivePlaneLineForm a) = 0 := by
    rw [eval_projectivePlaneLineForm_add_smul, hA, hQ, mul_zero, add_zero]
  have hPtL : eval Pt (projectivePlaneLineForm a) = 0 := by
    rw [← hl, (isHomogeneous_projectivePlaneLineForm a).eval_smul, hXL, mul_zero]
  -- The chart direction is a combination `α Xv + β Q` with `β ≠ 0`.
  set W := chartLineDirection a i
  have hW0 : W ≠ 0 := chartLineDirection_ne_zero ha i p hPtL
  obtain ⟨s', t', hW⟩ := hspan W (by
    rw [eval_projectivePlaneLineForm]; exact eval_chartLineDirection a i)
  have hWX : W = s' • Xv + (t' - s' * t) • Q := by
    rw [hW]
    funext j
    simp only [Xv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hβ : t' - s' * t ≠ 0 := by
    intro hβ
    rw [hβ, zero_smul, add_zero] at hWX
    have hWi : W i = 0 := chartLineDirection_self a i
    have hXi : Xv i ≠ 0 := by
      intro h0
      have : Pt i = 0 := by rw [← hl, Pi.smul_apply, h0, smul_zero]
      simp only [Pt, chartInvVec_self] at this
      exact one_ne_zero this
    rw [hWX, Pi.smul_apply, smul_eq_mul] at hWi
    have hs' : s' = 0 := (mul_eq_zero.1 hWi).resolve_right hXi
    apply hW0
    rw [hWX, hs', zero_smul]
  -- Compare orders of vanishing.
  have hcomp := homogeneousLineRestrict_comp F A Q t
  have hne : homogeneousLineRestrict F Xv Q ≠ 0 := by
    rw [← hcomp]
    intro h0
    rcases Polynomial.comp_eq_zero_iff.1 h0 with h0 | ⟨-, h0⟩
    · exact hh h0
    · have := congrArg Polynomial.natDegree h0
      rw [Polynomial.natDegree_X_add_C, Polynomial.natDegree_C] at this
      exact one_ne_zero this
  obtain ⟨hne', hntd⟩ := natTrailingDegree_homogeneousLineRestrict_change hF Xv Q (α := s') hl0 hβ hne
  rw [hl, ← hWX] at hne' hntd
  rw [affineLocalIntersectionMultiplicity_chart ha F i p hPtL hne', hntd,
    Polynomial.rootMultiplicity_eq_natTrailingDegree, hcomp]

theorem projectivePlaneLocalIntersectionMultiplicity_eq_rootMultiplicity [IsAlgClosed k]
    {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d) {a : Fin 3 → k} (ha : a ≠ 0)
    {A Q : Fin 3 → k} (hA : eval A (projectivePlaneLineForm a) = 0)
    (hQ : eval Q (projectivePlaneLineForm a) = 0)
    (hspan : ∀ x, eval x (projectivePlaneLineForm a) = 0 → ∃ s t : k, x = s • A + t • Q)
    (hh : homogeneousLineRestrict F A Q ≠ 0) (t : k) (hX : A + t • Q ≠ 0) :
    projectivePlaneLocalIntersectionMultiplicity (projectivePlaneLineForm a) F
        (Projectivization.mk k (A + t • Q) hX) =
      (homogeneousLineRestrict F A Q).rootMultiplicity t :=
  affineLocalIntersectionMultiplicity_chart_eq_rootMultiplicity hF ha hA hQ hspan hh t hX _
    (mem_standardChart_projectivePlaneChartIndex _)


theorem mem_projZeroSet_singleton_mk_iff {G : MvPolynomial (Fin 3) k} {n : ℕ}
    (hG : G.IsHomogeneous n) (v : Fin 3 → k) (hv : v ≠ 0) :
    Projectivization.mk k v hv ∈ projZeroSet {G} ↔ eval v G = 0 := by
  rw [mem_projZeroSet_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact homogeneousVanish_iff_of_isHomogeneous hG hv

theorem mem_projZeroSet_singleton_iff {G : MvPolynomial (Fin 3) k} {n : ℕ}
    (hG : G.IsHomogeneous n) (P : ProjectiveSpace k (Fin 3)) :
    P ∈ projZeroSet {G} ↔ eval P.rep G = 0 := by
  conv_lhs => rw [← Projectivization.mk_rep P]
  exact mem_projZeroSet_singleton_mk_iff hG _ _

/-- **A basis of a line through a given point.**  If `Q ≠ 0` lies on the plane `ℓ = 0`
(`ℓ ≠ 0`), there is `A` such that `A, Q` is a basis of that plane. -/
theorem exists_projectivePlaneLine_basis {a : Fin 3 → k} (ha : a ≠ 0) {Qv : Fin 3 → k}
    (hQv0 : Qv ≠ 0) (hQvL : eval Qv (projectivePlaneLineForm a) = 0) :
    ∃ A : Fin 3 → k, eval A (projectivePlaneLineForm a) = 0 ∧
      (∀ s t : k, s • A + t • Qv = 0 → s = 0 ∧ t = 0) ∧
      ∀ x, eval x (projectivePlaneLineForm a) = 0 → ∃ s t : k, x = s • A + t • Qv := by
  classical
  set ℓ := projectivePlaneLineForm a
  have hℓ : ℓ.IsHomogeneous 1 := isHomogeneous_projectivePlaneLineForm a
  let lin : (Fin 3 → k) →ₗ[k] k :=
    { toFun := fun x => eval x ℓ
      map_add' := fun x y => by
        have := eval_projectivePlaneLineForm_add_smul a x y 1
        rwa [one_smul, one_mul] at this
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [hℓ.eval_smul, pow_one] }
  have hsurj : Function.Surjective lin := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 ha
    simp only [Pi.zero_apply] at hj
    intro c
    refine ⟨Pi.single j (c / a j), ?_⟩
    change eval _ ℓ = c
    rw [eval_projectivePlaneLineForm, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]; field_simp
    · intro m _ hm; rw [Pi.single_eq_of_ne hm, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have hker : Module.finrank k (LinearMap.ker lin) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker lin
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self,
      Module.finrank_fin_fun] at h
    omega
  have hQker : Qv ∈ LinearMap.ker lin := hQvL
  obtain ⟨A, hAker, hAQ⟩ : ∃ A ∈ LinearMap.ker lin, A ∉ k ∙ Qv := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have := Submodule.finrank_mono (show LinearMap.ker lin ≤ k ∙ Qv from fun x hx => h x hx)
    rw [hker, finrank_span_singleton hQv0] at this
    omega
  have hind : ∀ s t : k, s • A + t • Qv = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    by_cases hs : s = 0
    · subst hs
      rw [zero_smul, zero_add, smul_eq_zero] at hst
      exact ⟨rfl, hst.resolve_right hQv0⟩
    · exfalso
      apply hAQ
      rw [Submodule.mem_span_singleton]
      refine ⟨-t / s, ?_⟩
      have h2 : s • A = (-t) • Qv := by
        rw [neg_smul, eq_neg_iff_add_eq_zero]; exact hst
      calc (-t / s) • Qv = s⁻¹ • (s • A) := by rw [h2, smul_smul, div_eq_inv_mul]
        _ = A := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  refine ⟨A, hAker, hind, fun x hx => ?_⟩
  have hS : Submodule.span k (Set.range ![A, Qv]) = LinearMap.ker lin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le, Matrix.range_cons_cons_empty, Set.insert_subset_iff,
        Set.singleton_subset_iff]
      exact ⟨hAker, hQker⟩
    · rw [finrank_span_eq_card (LinearIndependent.pair_iff.2 hind), hker, Fintype.card_fin]
  have hxS : x ∈ Submodule.span k (Set.range ![A, Qv]) := by rw [hS]; exact hx
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hxS
  obtain ⟨s, t, hst⟩ := hxS
  exact ⟨s, t, hst.symm⟩

theorem natDegree_homogeneousLineRestrict {F : MvPolynomial σ k} {d : ℕ}
    (hF : F.IsHomogeneous d) (Xv Yv : σ → k) (hY : eval Yv F ≠ 0) :
    homogeneousLineRestrict F Xv Yv ≠ 0 ∧ (homogeneousLineRestrict F Xv Yv).natDegree = d := by
  have hcoeffd : (homogeneousLineRestrict F Xv Yv).coeff d = eval Yv F := by
    rw [coeff_homogeneousLineRestrict hF, if_pos le_rfl, eval_eq_binaryCoeff hF Xv Yv]
  refine ⟨fun h0 => hY (by rw [← hcoeffd, h0, Polynomial.coeff_zero]), le_antisymm ?_
    (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeffd]; exact hY))⟩
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro i hi
  rw [coeff_homogeneousLineRestrict hF, if_neg (fun hle => absurd hi (not_lt.2 hle))]

/-- The points of `L ∩ Y` are the points `[A + tQ]` with `t` a root of `F(A + tQ)`. -/
theorem projectivePlaneLine_inter_eq_image {F : MvPolynomial (Fin 3) k} {d : ℕ}
    (hF : F.IsHomogeneous d) {a : Fin 3 → k} {A Qv : Fin 3 → k}
    (hAL : eval A (projectivePlaneLineForm a) = 0) (hQvL : eval Qv (projectivePlaneLineForm a) = 0)
    (hQvF : eval Qv F ≠ 0)
    (hspan : ∀ x, eval x (projectivePlaneLineForm a) = 0 → ∃ s t : k, x = s • A + t • Qv)
    (hX : ∀ t : k, A + t • Qv ≠ 0) :
    projZeroSet {projectivePlaneLineForm a} ∩ projZeroSet {F} =
      (fun t => Projectivization.mk k (A + t • Qv) (hX t)) ''
        {t | (homogeneousLineRestrict F A Qv).eval t = 0} := by
  have hℓ := isHomogeneous_projectivePlaneLineForm a
  ext P
  constructor
  · rintro ⟨hPL, hPY⟩
    rw [mem_projZeroSet_singleton_iff hℓ] at hPL
    rw [mem_projZeroSet_singleton_iff hF] at hPY
    obtain ⟨s, t, hst⟩ := hspan P.rep hPL
    have hs : s ≠ 0 := by
      rintro rfl
      rw [zero_smul, zero_add] at hst
      rw [hst, hF.eval_smul] at hPY
      have ht : t = 0 := (pow_eq_zero_iff'.1 ((mul_eq_zero.1 hPY).resolve_right hQvF)).1
      exact P.rep_nonzero (by rw [hst, ht, zero_smul])
    have hXP : A + (t / s) • Qv = s⁻¹ • P.rep := by
      rw [hst, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hs, one_smul, div_eq_inv_mul]
    refine ⟨t / s, ?_, ?_⟩
    · change Polynomial.eval _ _ = 0
      rw [eval_homogeneousLineRestrict, hXP, hF.eval_smul, hPY, mul_zero]
    · change Projectivization.mk k (A + (t / s) • Qv) (hX _) = P
      conv_rhs => rw [← Projectivization.mk_rep P]
      exact (Projectivization.mk_eq_mk_iff' k _ _ _ _).2 ⟨s⁻¹, hXP.symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(mem_projZeroSet_singleton_mk_iff hℓ _ _).2 ?_,
      (mem_projZeroSet_singleton_mk_iff hF _ _).2 ?_⟩
    · rw [eval_projectivePlaneLineForm_add_smul, hAL, hQvL, mul_zero, add_zero]
    · rw [← eval_homogeneousLineRestrict]; exact ht

theorem injective_mk_add_smul {A Qv : Fin 3 → k}
    (hind : ∀ s t : k, s • A + t • Qv = 0 → s = 0 ∧ t = 0) (hX : ∀ t : k, A + t • Qv ≠ 0) :
    Function.Injective fun t => Projectivization.mk k (A + t • Qv) (hX t) := by
  intro t t' htt'
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' k _ _ (hX t) (hX t')).1 htt'
  have h2 := hind (c - 1) (c * t' - t) (by
    rw [sub_smul, sub_smul, one_smul, ← smul_smul, sub_add_sub_comm, ← smul_add, hc, sub_self])
  have hc1 : c = 1 := sub_eq_zero.1 h2.1
  rw [hc1, one_mul] at h2
  exact (sub_eq_zero.1 h2.2).symm

/-- **Hartshorne I, Exercise 5.4(c).** Let `Y = Z(F)` be a projective plane curve of degree `d`
and `L = Z(ℓ)` a line not contained in `Y`.  Then `L ∩ Y` is finite and
`∑_{P ∈ L ∩ Y} (L · Y)_P = d`. -/
theorem finite_and_finsum_projectivePlaneLocalIntersectionMultiplicity [IsAlgClosed k]
    {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d) (hFirr : Irreducible F)
    {a : Fin 3 → k} (ha : a ≠ 0)
    (hLY : ¬projZeroSet {projectivePlaneLineForm a} ⊆ projZeroSet {F}) :
    (projZeroSet {projectivePlaneLineForm a} ∩ projZeroSet {F}).Finite ∧
      ∑ᶠ P ∈ projZeroSet {projectivePlaneLineForm a} ∩ projZeroSet {F},
        projectivePlaneLocalIntersectionMultiplicity (projectivePlaneLineForm a) F P = d := by
  classical
  obtain ⟨Q, hQL, hQY⟩ := Set.not_subset.1 hLY
  rw [mem_projZeroSet_singleton_iff (isHomogeneous_projectivePlaneLineForm a)] at hQL
  rw [mem_projZeroSet_singleton_iff hF] at hQY
  obtain ⟨A, hAL, hind, hspan⟩ := exists_projectivePlaneLine_basis ha Q.rep_nonzero hQL
  obtain ⟨hh0, hdeg⟩ := natDegree_homogeneousLineRestrict hF A Q.rep hQY
  have hX : ∀ t : k, A + t • Q.rep ≠ 0 := fun t h0 =>
    one_ne_zero (hind 1 t (by rw [one_smul]; exact h0)).1
  have hR : {t | (homogeneousLineRestrict F A Q.rep).eval t = 0} =
      ((homogeneousLineRestrict F A Q.rep).roots.toFinset : Set k) := by
    ext t; simp [Polynomial.mem_roots hh0]
  rw [projectivePlaneLine_inter_eq_image hF hAL hQL hQY hspan hX, hR]
  refine ⟨(Finset.finite_toSet _).image _, ?_⟩
  rw [finsum_mem_image (injective_mk_add_smul hind hX).injOn, finsum_mem_coe_finset,
    Finset.sum_congr rfl fun t _ =>
      projectivePlaneLocalIntersectionMultiplicity_eq_rootMultiplicity hF ha hAL hQL hspan hh0
        t (hX t), ← Nat.cast_sum]
  simp_rw [← Polynomial.count_roots]
  rw [Multiset.toFinset_sum_count_eq, IsAlgClosed.card_roots_eq_natDegree, hdeg]

end
end Hartshorne
