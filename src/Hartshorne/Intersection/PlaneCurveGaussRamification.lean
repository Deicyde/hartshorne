/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.PlaneCurveGermDerivation
import Hartshorne.Rational.BlowingUpMorphisms

/-!
# The Gauss pencil of a plane curve and ramification at flexes

Hartshorne, *Algebraic Geometry*, Exercise IV.2.3(a) (p. 304).

Let `X = Z(F) ⊆ ℙ²` be a nonsingular plane curve over an algebraically closed field of
characteristic zero and `L` a line not tangent to `X`.  Then `P ↦ T_P(X) ∩ L` is a morphism
`φ : X → L`, ramified at `P` exactly when `P ∈ L` or `(T_P(X) · X)_P ≥ 3`; consequently `X` has
only finitely many inflection points.

An inflection point (flex) is a point `P` whose tangent line `T_P(X)` is not a component of `X` and
satisfies `(T_P(X) · X)_P ≥ 3`: the intersection multiplicity of Exercise I.5.4 is defined only for
distinct curves.  A line therefore has no flexes.

## Ramification

For a morphism of varieties `φ : X → Y` and `P ∈ X`, the ramification index `e_P` is the largest
`n` with `φ^#(𝔪_{φ(P)}) ⊆ 𝔪_P^n` (`⊤` if there is none).  When `𝒪_{P,X}` is a discrete valuation
ring and `t` generates `𝔪_{φ(P)}`, this is `v_P(φ^# t)`, Hartshorne's definition (IV.2, p. 299):
see `VarietyHom.ramificationIndex_eq_addVal`.  The morphism is ramified at `P` when `e_P > 1`.

## Method

* `φ` is given by the cross product `∇F × b`, `b` the coordinates of `L`.
* A uniformizer of `L` at `Q = φ(P)` is the quotient of the linear form of `T_P(X)` by a linear
  form not vanishing at `Q`; its pullback is the polar `∑ⱼ eⱼ ∂F/∂xⱼ` of the point `e = b × ∇F(P)`
  over a form not vanishing at `P`.
* A germ vanishing at `P` lies in `𝔪_P²` exactly when its derivative along a tangent vector field
  vanishes at `P`.  The derivative of the polar is the Hessian pairing of the tangent direction
  with `Q`, which by Euler's formula vanishes when `Q = P` and otherwise is the second-order
  coefficient of `F` along `T_P(X)`.
* Finiteness: at points off a fixed line `w = 0`, flexes are zeros of the Hessian pairing
  `K = tᵀ (∂²F) t` of the tangent field `t = ∇F × w`.  If `F` divided `K`, every ratio of partial
  derivatives would have zero derivative along the curve, hence (characteristic zero) be constant;
  Euler's formula would then factor `F` through a linear form.  A curve of degree one is its own
  tangent line at every point, so it has no flexes.

## Main definitions

* `Hartshorne.VarietyHom.ramificationIndex`, `Hartshorne.VarietyHom.IsRamifiedAt`
* `Hartshorne.planeCurveInflectionPoints`

## Main results

* `Hartshorne.planeCurve_gaussPencil_ramification`: Exercise IV.2.3(a).
-/

namespace Hartshorne
open MvPolynomial TopologicalSpace IsLocalRing

noncomputable section
universe u v

namespace VarietyHom

variable {k : Type u} [Field k] {X Y : Variety.{u, v} k}

/-- **The ramification index** `e_P` of a morphism of varieties at `P`: the largest `n` with
`φ^#(𝔪_{φ(P)}) ⊆ 𝔪_P^n`, and `⊤` if there is no largest.  For a morphism of nonsingular curves
it is `v_P(φ^# t)` for a uniformizer `t` at `φ(P)` (`ramificationIndex_eq_addVal`). -/
def ramificationIndex (φ : VarietyHom X Y) (P : X.carrier) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : (maximalIdeal (Variety.LocalRingAt Y (φ P))).map (φ.localRingHom P) ≤
      maximalIdeal (Variety.LocalRingAt X P) ^ n), (n : ℕ∞)

/-- A morphism is **ramified** at `P` when its ramification index there exceeds one. -/
def IsRamifiedAt (φ : VarietyHom X Y) (P : X.carrier) : Prop :=
  1 < φ.ramificationIndex P

theorem one_lt_ramificationIndex_iff (φ : VarietyHom X Y) (P : X.carrier) :
    1 < φ.ramificationIndex P ↔
      (maximalIdeal (Variety.LocalRingAt Y (φ P))).map (φ.localRingHom P) ≤
        maximalIdeal (Variety.LocalRingAt X P) ^ 2 := by
  constructor
  · intro h
    by_contra hle
    refine (not_le.2 h) (iSup₂_le fun n hn => ?_)
    by_contra hn1
    have h2 : 2 ≤ n := by
      have : ¬ (n ≤ 1) := fun h' => hn1 (by exact_mod_cast h')
      omega
    exact hle (hn.trans (Ideal.pow_le_pow_right h2))
  · intro h
    have : ((2 : ℕ) : ℕ∞) ≤ φ.ramificationIndex P :=
      le_iSup₂ (f := fun (n : ℕ) (_ : (maximalIdeal (Variety.LocalRingAt Y (φ P))).map
        (φ.localRingHom P) ≤ maximalIdeal (Variety.LocalRingAt X P) ^ n) => (n : ℕ∞)) 2 h
    exact lt_of_lt_of_le (by norm_num) this

theorem iSup_natCast_le_eq (a : ℕ∞) : ⨆ (n : ℕ) (_ : (n : ℕ∞) ≤ a), (n : ℕ∞) = a := by
  refine le_antisymm (iSup₂_le fun n hn => hn) ?_
  induction a using ENat.recTopCoe with
  | top =>
    rw [top_le_iff, ENat.eq_top_iff_forall_ge]
    exact fun m => le_iSup₂_of_le m le_top le_rfl
  | coe m => exact le_iSup₂_of_le m le_rfl le_rfl

/-- **Hartshorne's ramification index.**  If `𝒪_{P,X}` is a discrete valuation ring and `t`
generates the maximal ideal of `𝒪_{φ(P),Y}`, then `e_P = v_P(φ^# t)`. -/
theorem ramificationIndex_eq_addVal (φ : VarietyHom X Y) (P : X.carrier)
    [IsDiscreteValuationRing (Variety.LocalRingAt X P)]
    {t : Variety.LocalRingAt Y (φ P)}
    (ht : maximalIdeal (Variety.LocalRingAt Y (φ P)) = Ideal.span {t}) :
    φ.ramificationIndex P =
      IsDiscreteValuationRing.addVal (Variety.LocalRingAt X P) (φ.localRingHom P t) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Variety.LocalRingAt X P)
  have key : ∀ n : ℕ, ((maximalIdeal (Variety.LocalRingAt Y (φ P))).map (φ.localRingHom P) ≤
      maximalIdeal (Variety.LocalRingAt X P) ^ n) ↔
      (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal _ (φ.localRingHom P t) := by
    intro n
    rw [ht, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem,
      hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
  rw [ramificationIndex]
  simp_rw [key]
  exact iSup_natCast_le_eq _

end VarietyHom

section Hessian

variable {k : Type u} [Field k]

/-- The Hessian pairing `xᵀ (∂²F(v)) y`. -/
def planeHessian (F : MvPolynomial (Fin 3) k) (v x y : Fin 3 → k) : k :=
  ∑ i, x i * ∑ j, y j * eval v (pderiv i (pderiv j F))

theorem planeHessian_comm (F : MvPolynomial (Fin 3) k) (v x y : Fin 3 → k) :
    planeHessian F v x y = planeHessian F v y x := by
  simp only [planeHessian, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_pderiv_comm]
  ring

theorem planeHessian_smul_left (F : MvPolynomial (Fin 3) k) (v x y : Fin 3 → k) (c : k) :
    planeHessian F v (c • x) y = c * planeHessian F v x y := by
  simp only [planeHessian, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring_nf

theorem planeHessian_add_left (F : MvPolynomial (Fin 3) k) (v x x' y : Fin 3 → k) :
    planeHessian F v (x + x') y = planeHessian F v x y + planeHessian F v x' y := by
  simp only [planeHessian, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- **Euler's formula for the Hessian.** -/
theorem planeHessian_self_left {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    (v y : Fin 3 → k) :
    planeHessian F v v y = (d - 1 : ℕ) * ∑ j, y j * eval v (pderiv j F) := by
  have h : ∀ j, ∑ i, v i * eval v (pderiv i (pderiv j F)) = (d - 1 : ℕ) * eval v (pderiv j F) :=
    fun j => by
      have h := congrArg (eval v) (hF.pderiv (i := j)).sum_X_mul_pderiv
      simpa only [map_sum, map_mul, eval_X, map_nsmul, nsmul_eq_mul, map_natCast] using h
  calc planeHessian F v v y = ∑ j, y j * ∑ i, v i * eval v (pderiv i (pderiv j F)) := by
        simp only [planeHessian, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [h]; ring

theorem eval_vectorFieldDeriv_polar (t : Fin 3 → MvPolynomial (Fin 3) k)
    (F : MvPolynomial (Fin 3) k) (e x : Fin 3 → k) :
    eval x (vectorFieldDeriv t (vectorFieldDeriv (fun j => C (e j)) F)) =
      planeHessian F x (fun i => eval x (t i)) e := by
  simp only [vectorFieldDeriv_apply, map_sum, map_mul, eval_C, planeHessian, pderiv_C_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- The second derivative at `0` of `F` along `v + s c` is the Hessian pairing `cᵀ (∂²F(v)) c`. -/
theorem eval_iterate_derivative_two_homogeneousLineRestrict (F : MvPolynomial (Fin 3) k)
    (v c : Fin 3 → k) :
    (Polynomial.derivative^[2] (homogeneousLineRestrict F v c)).eval 0 =
      planeHessian F v c c := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id,
    derivative_homogeneousLineRestrict, Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, Finset.mul_sum, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, eval_homogeneousLineRestrict, zero_smul, add_zero,
    planeHessian]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem eval_derivative_homogeneousLineRestrict_zero (F : MvPolynomial (Fin 3) k)
    (v c : Fin 3 → k) :
    (Polynomial.derivative (homogeneousLineRestrict F v c)).eval 0 =
      ∑ j, c j * eval v (pderiv j F) := by
  rw [derivative_homogeneousLineRestrict, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_homogeneousLineRestrict, zero_smul, add_zero]

/-- **The inflection points** of the plane curve `F = 0`: the points `P` at which the tangent line
`T_P` is not a component of the curve and has local intersection multiplicity at least three with
it.  (The intersection multiplicity of Exercise I.5.4 is defined for distinct curves; without the
first condition every point of a line would be a flex.) -/
def planeCurveInflectionPoints (F : MvPolynomial (Fin 3) k) : Set (ProjectiveSpace k (Fin 3)) :=
  {P | P ∈ projZeroSet ({F} : Set (MvPolynomial (Fin 3) k)) ∧
    ¬ projectivePlaneLineForm (planeCurveTangentLine F P).rep ∣ F ∧
    3 ≤ projectivePlaneLocalIntersectionMultiplicity
      (projectivePlaneLineForm (planeCurveTangentLine F P).rep) F P}

theorem not_isUnit_of_isHomogeneous {E : MvPolynomial (Fin 3) k} {m : ℕ}
    (hE : E.IsHomogeneous m) (hE0 : E ≠ 0) (hm : 0 < m) : ¬ IsUnit E := by
  intro hu
  have := (isUnit_iff_totalDegree_of_isReduced.1 hu).2
  rw [hE.totalDegree hE0] at this
  omega

theorem not_dvd_of_isHomogeneous_lt {F E : MvPolynomial (Fin 3) k} {d m : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (hE : E.IsHomogeneous m) (hE0 : E ≠ 0) (hm : m < d) :
    ¬ F ∣ E := by
  rintro ⟨H, rfl⟩
  have hH0 : H ≠ 0 := by rintro rfl; exact hE0 (mul_zero F)
  have := hE.totalDegree hE0
  rw [totalDegree_mul_of_isDomain hF0 hH0, hF.totalDegree hF0] at this
  omega

theorem mul_eq_mul_of_cross_eq_zero {x y : Fin 3 → k} (h : crossProduct x y = 0) (i j : Fin 3) :
    x i * y j = x j * y i := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [cross_apply, Matrix.cons_val, Pi.zero_apply] at h0 h1 h2
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | linear_combination h0 | linear_combination -h0 | linear_combination h1
    | linear_combination -h1 | linear_combination h2 | linear_combination -h2

end Hessian

section TangentMultiplicity

variable {k : Type u} [Field k]

/-- If `g` is a multiple of `f` and `f` vanishes at `p`, then `(f · g)_p ≥ n` for every `n`. -/
theorem le_affineLocalIntersectionMultiplicity_of_dvd (n : ℕ) {f g : MvPolynomial (Fin 2) k}
    {p : Fin 2 → k} (hf : eval p f = 0) (hfg : f ∣ g) :
    (n : ℕ∞) ≤ affineLocalIntersectionMultiplicity f g p := by
  have hspan : Ideal.span {algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p) f,
      algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p) g} =
      Ideal.span {algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p) f,
      algebraMap (MvPolynomial (Fin 2) k) (affineLocalRing p) 0} := by
    obtain ⟨h, rfl⟩ := hfg
    rw [map_zero, map_mul]
    apply le_antisymm
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Ideal.subset_span (Set.mem_insert _ _), ?_⟩
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Ideal.subset_span (Set.mem_insert _ _), Ideal.zero_mem _⟩
  have h2 := le_affineLocalIntersectionMultiplicity_of_mem_pow p (a := 1) (b := n) (f := f)
    (g := 0) (by rw [pow_one]; exact mem_affinePointIdeal_iff.2 hf) (Ideal.zero_mem _)
  unfold affineLocalIntersectionMultiplicity at h2 ⊢
  rw [hspan]
  simpa using h2

variable [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}

omit [IsAlgClosed k] in
/-- A line contained in the curve meets it with multiplicity at least three at each of its
points. -/
theorem three_le_projectivePlaneLocalIntersectionMultiplicity_of_dvd {b : Fin 3 → k}
    {P : ProjectiveSpace k (Fin 3)} (hvL : eval P.rep (projectivePlaneLineForm b) = 0)
    (hdvd : projectivePlaneLineForm b ∣ F) :
    3 ≤ projectivePlaneLocalIntersectionMultiplicity (projectivePlaneLineForm b) F P := by
  set c := projectivePlaneChartIndex P
  have hc := mem_standardChart_projectivePlaneChartIndex P
  set e := finSuccAboveEquiv c
  set p := chartMap c P
  set q := chartPointFin c p
  have he : ∀ f, eval q (renameEquiv k e.symm f) = eval p f := by
    intro f
    rw [renameEquiv_apply, eval_rename]
    have : q ∘ e.symm = p := by funext j; simp [q, e]
    rw [this]
  have hpv : chartInvVec c p = (P.rep c)⁻¹ • P.rep :=
    chartInvVec_div c (rep_ne_zero_of_mem_standardChart hc)
  unfold projectivePlaneLocalIntersectionMultiplicity
  rw [← affineLocalIntersectionMultiplicity_algEquiv (renameEquiv k e.symm) p q he]
  refine le_affineLocalIntersectionMultiplicity_of_dvd 3 ?_ (map_dvd _ (map_dvd _ hdvd))
  rw [he, eval_dehomogenize, hpv, (isHomogeneous_projectivePlaneLineForm b).eval_smul, hvL,
    mul_zero]

omit [IsAlgClosed k] in
/-- Two independent vectors on a line of `ℙ²` span it. -/
theorem exists_eq_smul_add_smul_of_lineForm {b : Fin 3 → k} (hb : b ≠ 0) {v c : Fin 3 → k}
    (hv : eval v (projectivePlaneLineForm b) = 0) (hc : eval c (projectivePlaneLineForm b) = 0)
    (hind : ∀ s t : k, s • v + t • c = 0 → s = 0 ∧ t = 0) :
    ∀ x, eval x (projectivePlaneLineForm b) = 0 → ∃ s t : k, x = s • v + t • c := by
  have hc0 : c ≠ 0 := fun h => one_ne_zero (hind 0 1 (by rw [h]; simp)).2
  obtain ⟨A, -, -, hspan⟩ := exists_projectivePlaneLine_basis hb hc0 hc
  obtain ⟨s₀, r₀, hv'⟩ := hspan v hv
  have hs₀ : s₀ ≠ 0 := by
    rintro rfl
    have := (hind 1 (-r₀) (by rw [hv']; simp)).1
    exact one_ne_zero this
  intro x hx
  obtain ⟨s, r, rfl⟩ := hspan x hx
  refine ⟨s / s₀, r - s / s₀ * r₀, ?_⟩
  rw [hv']
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **Tangential contact of order three.**  At a nonsingular point `P` of `F = 0`, for a direction
`c` of the tangent line independent of `P`, the tangent line meets the curve with multiplicity at
least three at `P` exactly when the Hessian pairing `cᵀ (∂²F(P)) c` vanishes. -/
theorem three_le_tangent_multiplicity_iff [CharZero k] (hF : F.IsHomogeneous d)
    {P : ProjectiveSpace k (Fin 3)} (hPY : P ∈ projZeroSet ({F} : Set (MvPolynomial (Fin 3) k)))
    (hgrad : (fun l => eval P.rep (pderiv l F)) ≠ 0) {c : Fin 3 → k}
    (hc : ∑ j, c j * eval P.rep (pderiv j F) = 0)
    (hind : ∀ s t : k, s • P.rep + t • c = 0 → s = 0 ∧ t = 0) :
    3 ≤ projectivePlaneLocalIntersectionMultiplicity
        (projectivePlaneLineForm (planeCurveTangentLine F P).rep) F P ↔
      planeHessian F P.rep c c = 0 := by
  set v := P.rep with hv_def
  set a : Fin 3 → k := fun l => eval v (pderiv l F) with ha
  set b := (planeCurveTangentLine F P).rep with hb_def
  have hb0 : b ≠ 0 := Projectivization.rep_nonzero _
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep k a hgrad
  have hbu : b = u • a := by rw [hb_def, planeCurveTangentLine_of_ne hgrad, ← hu]
  have hbx : ∀ x, eval x (projectivePlaneLineForm b) = u * ∑ j, x j * a j := fun x => by
    rw [eval_projectivePlaneLineForm, hbu, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul]
    ring
  have hFv : eval v F = 0 := (mem_projZeroSet_singleton_iff hF P).1 hPY
  have hvL : eval v (projectivePlaneLineForm b) = 0 := by
    rw [hbx]
    exact mul_eq_zero_of_right _ (sum_mul_eval_pderiv_eq_zero hF hFv)
  have hcL : eval c (projectivePlaneLineForm b) = 0 := by rw [hbx, hc, mul_zero]
  have hspan := exists_eq_smul_add_smul_of_lineForm hb0 hvL hcL hind
  by_cases hp : homogeneousLineRestrict F v c = 0
  · have hH : planeHessian F v c c = 0 := by
      rw [← eval_iterate_derivative_two_homogeneousLineRestrict, hp]
      simp
    refine iff_of_true ?_ hH
    have hFc : eval c F = 0 := by
      by_contra hA
      exact (natDegree_homogeneousLineRestrict hF v c hA).1 hp
    have hvan : ∀ Q ∈ projZeroSet ({projectivePlaneLineForm b} :
        Set (MvPolynomial (Fin 3) k)), eval Q.rep F = 0 := by
      intro Q hQ
      have hQL : eval Q.rep (projectivePlaneLineForm b) = 0 := hQ _ rfl
      obtain ⟨s, t, hst⟩ := hspan Q.rep hQL
      rw [hst]
      rcases eq_or_ne s 0 with rfl | hs
      · rw [zero_smul, zero_add, hF.eval_smul, hFc, mul_zero]
      · have : s • v + t • c = s • (v + (t / s) • c) := by
          rw [smul_add, smul_smul, mul_div_cancel₀ t hs]
        rw [this, hF.eval_smul, ← eval_homogeneousLineRestrict, hp, Polynomial.eval_zero,
          mul_zero]
    have hdvd := projectivePlaneLineForm_dvd_of_vanish hb0 hF
      ⟨P, fun f hf => by rw [Set.mem_singleton_iff.1 hf]; exact hvL⟩ hvan
    exact three_le_projectivePlaneLocalIntersectionMultiplicity_of_dvd hvL hdvd
  · have hX : v + (0 : k) • c ≠ 0 := by rw [zero_smul, add_zero]; exact P.rep_nonzero
    have hmk : Projectivization.mk k (v + (0 : k) • c) hX = P := by
      conv_rhs => rw [← Projectivization.mk_rep P]
      congr 1
      rw [zero_smul, add_zero]
    have hmult := projectivePlaneLocalIntersectionMultiplicity_eq_rootMultiplicity hF hb0 hvL hcL
      hspan hp 0 hX
    rw [hmk] at hmult
    have h2 : ((Nat.factorial 2 : ℕ) : k) ∈ nonZeroDivisors k :=
      mem_nonZeroDivisors_of_ne_zero (by norm_num)
    rw [hmult, show ∀ n : ℕ, (3 : ℕ∞) ≤ n ↔ 2 < n from fun n => by norm_cast,
      Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors hp h2]
    constructor
    · intro h
      have := h 2 le_rfl
      rwa [Polynomial.IsRoot.def, eval_iterate_derivative_two_homogeneousLineRestrict] at this
    · intro h m hm
      interval_cases m
      · simp [Polynomial.IsRoot.def, eval_homogeneousLineRestrict, hFv]
      · simpa [Polynomial.IsRoot.def] using
          (eval_derivative_homogeneousLineRestrict_zero F v c).trans hc
      · rwa [Polynomial.IsRoot.def, eval_iterate_derivative_two_homogeneousLineRestrict]

end TangentMultiplicity

section Gauss

variable {k : Type} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
variable (hF : F.IsHomogeneous d) (hFirr : Irreducible F)

omit [IsAlgClosed k] in
theorem pderiv_projectivePlaneLineForm (b : Fin 3 → k) (l : Fin 3) :
    pderiv l (projectivePlaneLineForm b) = C (b l) := by
  simp only [projectivePlaneLineForm, map_sum, pderiv_C_mul]
  rw [Fintype.sum_eq_single l (fun i hi => by rw [pderiv_X_of_ne hi, mul_zero]), pderiv_X_self,
    mul_one]

omit [IsAlgClosed k] in
theorem cross_ne_zero_of_mk_ne {a b : Fin 3 → k} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Projectivization.mk k a ha ≠ Projectivization.mk k b hb) : crossProduct a b ≠ 0 := by
  rw [crossProduct_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff' ha]
  intro c hc
  exact h ((Projectivization.mk_eq_mk_iff' k a b ha hb).2 ⟨c⁻¹, by
    have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hb hc.symm
    rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩)

omit [IsAlgClosed k] in
theorem eq_smul_of_cross_eq_zero {x y : Fin 3 → k} (h : crossProduct x y = 0) {i : Fin 3}
    (hi : x i ≠ 0) : y = (y i / x i) • x := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [cross_apply, Matrix.cons_val, Pi.zero_apply] at h0 h1 h2
  funext j
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  fin_cases i <;> fin_cases j <;> simp at hi ⊢ <;>
    first
    | linear_combination h0 | linear_combination -h0 | linear_combination h1
    | linear_combination -h1 | linear_combination h2 | linear_combination -h2

/-- The line `L ⊆ ℙ²`, given by a point of the dual plane, as a plane curve. -/
abbrev planeLineVariety (L : ProjectiveSpace k (Fin 3)) : Variety k :=
  planeCurveVariety (isHomogeneous_projectivePlaneLineForm L.rep)
    (irreducible_projectivePlaneLineForm L.rep_nonzero)

/-- The linear combination `∑ⱼ mⱼ Gⱼ`. -/
def planeLinComb (m : Fin 3 → k) (G : Fin 3 → MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  ∑ j, C (m j) * G j

omit [IsAlgClosed k] in
theorem isHomogeneous_planeLinComb (m : Fin 3 → k) {G : Fin 3 → MvPolynomial (Fin 3) k} {n : ℕ}
    (hG : ∀ j, (G j).IsHomogeneous n) : (planeLinComb m G).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ fun j _ => by simpa using (isHomogeneous_C (Fin 3) (m j)).mul (hG j)

omit [IsAlgClosed k] in
theorem eval_planeLinComb (m : Fin 3 → k) (G : Fin 3 → MvPolynomial (Fin 3) k) (x : Fin 3 → k) :
    eval x (planeLinComb m G) = m ⬝ᵥ fun j => eval x (G j) := by
  simp [planeLinComb, dotProduct]

omit [IsAlgClosed k] in
/-- `a ⬝ (∇F × b) = ∇F ⬝ (b × a)`: the pullback of the linear form `a` along the Gauss pencil is
the polar of the point `b × a`. -/
theorem planeLinComb_planeTangentField (F : MvPolynomial (Fin 3) k) (a b : Fin 3 → k) :
    planeLinComb a (planeTangentField F b) =
      vectorFieldDeriv (fun j => C (crossProduct b a j)) F := by
  simp only [planeLinComb, planeTangentField, vectorFieldDeriv_apply, cross_apply,
    Fin.sum_univ_three, Matrix.cons_val, map_sub, map_mul]
  ring

/-- **Pulling back a quotient of linear forms** along a morphism given by homogeneous
polynomials `G` gives the quotient of the corresponding combinations of the `G`s. -/
theorem localRingHom_planeCurveQuotGerm {F' : MvPolynomial (Fin 3) k} {d' : ℕ}
    (hF' : F'.IsHomogeneous d') (hF'irr : Irreducible F')
    (φ : VarietyHom (planeCurveVariety hF hFirr) (planeCurveVariety hF' hF'irr))
    {n : ℕ} {G : Fin 3 → MvPolynomial (Fin 3) k} (hG : ∀ j, (G j).IsHomogeneous n)
    (hne : ∀ x : (planeCurveVariety hF hFirr).carrier,
      (fun j => eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep (G j)) ≠ 0)
    (hφ : ∀ x, (Subtype.val (φ x) : ProjectiveSpace k (Fin 3)) = Projectivization.mk k _ (hne x))
    (m h : Fin 3 → k) {P : (planeCurveVariety hF hFirr).carrier}
    (hQ : φ P ∈ planeCurveNonvanishing hF' hF'irr (isHomogeneous_projectivePlaneLineForm h))
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_planeLinComb h hG)) :
    φ.localRingHom P (planeCurveQuotGerm hF' hF'irr (isHomogeneous_projectivePlaneLineForm m)
      (isHomogeneous_projectivePlaneLineForm h) hQ) =
      planeCurveQuotGerm hF hFirr (isHomogeneous_planeLinComb m hG)
        (isHomogeneous_planeLinComb h hG) hP := by
  rw [planeCurveQuotGerm, VarietyHom.localRingHom_mk, planeCurveQuotGerm]
  refine Quotient.sound fun x _ _ => ?_
  change eval (Subtype.val (φ x) : ProjectiveSpace k (Fin 3)).rep (projectivePlaneLineForm m) /
      eval (Subtype.val (φ x) : ProjectiveSpace k (Fin 3)).rep (projectivePlaneLineForm h) =
    eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep (planeLinComb m G) /
      eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep (planeLinComb h G)
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep k _ (hne x)
  rw [hφ x, ← hu, Units.smul_def, ratio_eq_of_smul (isHomogeneous_projectivePlaneLineForm m)
    (isHomogeneous_projectivePlaneLineForm h) u.ne_zero, eval_planeLinComb, eval_planeLinComb,
    eval_projectivePlaneLineForm_eq_dotProduct, eval_projectivePlaneLineForm_eq_dotProduct]

theorem gradient_ne_zero_of_nonsingular (hns : (planeCurveVariety hF hFirr).Nonsingular)
    (x : (planeCurveVariety hF hFirr).carrier) :
    (fun l => eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep (pderiv l F)) ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero_of_nonsingularAt hF hFirr (hns x)
  exact fun h => hj (congrFun h j)

theorem gaussPencil_ne_zero (hns : (planeCurveVariety hF hFirr).Nonsingular)
    (L : ProjectiveSpace k (Fin 3))
    (hL : ∀ P ∈ projZeroSet ({F} : Set (MvPolynomial (Fin 3) k)), planeCurveTangentLine F P ≠ L)
    (x : (planeCurveVariety hF hFirr).carrier) :
    (fun j => eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep
      (planeTangentField F L.rep j)) ≠ 0 := by
  rw [eval_planeTangentField]
  have hgrad := gradient_ne_zero_of_nonsingular hF hFirr hns x
  refine cross_ne_zero_of_mk_ne hgrad L.rep_nonzero ?_
  rw [Projectivization.mk_rep, ← planeCurveTangentLine_of_ne hgrad]
  exact hL _ x.2

/-- **The Gauss pencil** `P ↦ T_P(X) ∩ L` is a morphism `X → L`, given by `∇F × b`. -/
theorem exists_planeGaussPencil (hns : (planeCurveVariety hF hFirr).Nonsingular)
    (L : ProjectiveSpace k (Fin 3))
    (hL : ∀ P ∈ projZeroSet ({F} : Set (MvPolynomial (Fin 3) k)), planeCurveTangentLine F P ≠ L) :
    ∃ φ : VarietyHom (planeCurveVariety hF hFirr) (planeLineVariety L),
      ∀ x, (Subtype.val (φ x) : ProjectiveSpace k (Fin 3)) =
        Projectivization.mk k _ (gaussPencil_ne_zero hF hFirr hns L hL x) := by
  have hY := isProjVariety_planeCurve hF hFirr
  obtain ⟨φ₀, hφ₀⟩ := exists_varietyHom_of_homogeneous hY.isQuasiProjVariety
    (planeTangentField F L.rep) (isHomogeneous_planeTangentField hF L.rep)
    (fun P hP => gaussPencil_ne_zero hF hFirr hns L hL ⟨P, hP⟩)
  have hmem : ∀ x, (φ₀ x).1 ∈ projZeroSet ({projectivePlaneLineForm L.rep} :
      Set (MvPolynomial (Fin 3) k)) := fun x => by
    rw [show (φ₀ x).1 = _ from hφ₀ x,
      mem_projZeroSet_singleton_mk_iff (isHomogeneous_projectivePlaneLineForm _),
      eval_projectivePlaneLineForm_eq_dotProduct, eval_planeTangentField]
    exact dot_cross_self _ _
  obtain ⟨φ, hφ⟩ := exists_varietyHom_codRestrictProj
    (isProjVariety_univ (k := k) (σ := Fin 3)).isQuasiProjVariety
    (isProjVariety_planeCurve (isHomogeneous_projectivePlaneLineForm L.rep)
      (irreducible_projectivePlaneLineForm L.rep_nonzero)).isQuasiProjVariety φ₀ hmem
  refine ⟨φ, fun x => ?_⟩
  have h1 : φ x = ⟨(φ₀ x).1, hmem x⟩ := congrFun hφ x
  rw [h1]
  exact hφ₀ x

end Gauss

section GaussRamification

variable {k : Type} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
variable (hF : F.IsHomogeneous d) (hFirr : Irreducible F)

/-- **Ramification of the Gauss pencil, infinitesimally.**  With `a = ∇F(P)` and `b` the
coordinates of `L`, the Gauss pencil is ramified at `P` exactly when the Hessian pairing of the
tangent direction `a × w` with `b × a` (the point `T_P(X) ∩ L`) vanishes, for any `w, h₀` not
vanishing at `P`. -/
theorem isRamifiedAt_iff_planeHessian (hns : (planeCurveVariety hF hFirr).Nonsingular)
    (L : ProjectiveSpace k (Fin 3))
    (hL : ∀ P ∈ projZeroSet ({F} : Set (MvPolynomial (Fin 3) k)), planeCurveTangentLine F P ≠ L)
    (φ : VarietyHom (planeCurveVariety hF hFirr) (planeLineVariety L))
    (hφ : ∀ x, (Subtype.val (φ x) : ProjectiveSpace k (Fin 3)) =
      Projectivization.mk k _ (gaussPencil_ne_zero hF hFirr hns L hL x))
    (P : (planeCurveVariety hF hFirr).carrier) (w h₀ : Fin 3 → k)
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (hw : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm w)) :
    φ.IsRamifiedAt P ↔
      planeHessian F (Subtype.val P : ProjectiveSpace k (Fin 3)).rep
        (crossProduct (fun l => eval (Subtype.val P : ProjectiveSpace k (Fin 3)).rep (pderiv l F))
          w)
        (crossProduct L.rep
          (fun l => eval (Subtype.val P : ProjectiveSpace k (Fin 3)).rep (pderiv l F))) = 0 := by
  classical
  set v := (Subtype.val P : ProjectiveSpace k (Fin 3)).rep with hv
  set a : Fin 3 → k := fun l => eval v (pderiv l F) with ha
  set b := L.rep with hb
  have hGv : (fun j => eval v (planeTangentField F b j)) = crossProduct a b :=
    eval_planeTangentField F b v
  have hc0 : crossProduct a b ≠ 0 := by
    rw [← hGv]; exact gaussPencil_ne_zero hF hFirr hns L hL P
  have hΛ := isHomogeneous_projectivePlaneLineForm b
  have hΛirr := irreducible_projectivePlaneLineForm L.rep_nonzero
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep k _
    (gaussPencil_ne_zero hF hFirr hns L hL P)
  have hqc : (Subtype.val (φ P) : ProjectiveSpace k (Fin 3)).rep = (u : k) • crossProduct a b := by
    rw [hφ P, ← hu, Units.smul_def, hGv]
  have hnsQ : (planeLineVariety L).NonsingularAt (φ P) := by
    refine (nonsingularAt_planeCurve_iff hΛ hΛirr (φ P)).2 ?_
    obtain ⟨l, hl⟩ := Function.ne_iff.1 L.rep_nonzero
    exact ⟨l, by rw [pderiv_projectivePlaneLineForm, eval_C]; exact hl⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1
    (Projectivization.rep_nonzero (Subtype.val (φ P) : ProjectiveSpace k (Fin 3)))
  set h : Fin 3 → k := Pi.single i 1 with hh
  have hQh : φ P ∈ planeCurveNonvanishing hΛ hΛirr (isHomogeneous_projectivePlaneLineForm h) := by
    rw [mem_planeCurveNonvanishing, eval_projectivePlaneLineForm_eq_dotProduct,
      single_one_dotProduct]
    exact hi
  have hci : crossProduct a b i ≠ 0 := by
    intro h0
    apply hi
    rw [hqc, Pi.smul_apply, h0, smul_zero, Pi.zero_apply]
  have hsirr := irreducible_planeCurveQuotGerm_linear hΛ hΛirr hnsQ (m := a) (h := h)
    (by rw [eval_projectivePlaneLineForm_eq_dotProduct, hqc, dotProduct_smul, dot_self_cross,
      smul_zero])
    (by simp only [pderiv_projectivePlaneLineForm, eval_C]; exact hc0) hQh
  have := isDiscreteValuationRing_planeCurve hΛ hΛirr hnsQ
  have hmax := hsirr.maximalIdeal_eq
  have hPd : P ∈ planeCurveNonvanishing hF hFirr
      (isHomogeneous_planeLinComb h (isHomogeneous_planeTangentField hF b)) := by
    rw [mem_planeCurveNonvanishing, eval_planeLinComb, ← hv, hGv, single_one_dotProduct]
    exact hci
  have hpull := localRingHom_planeCurveQuotGerm hF hFirr hΛ hΛirr φ
    (isHomogeneous_planeTangentField hF b) (gaussPencil_ne_zero hF hFirr hns L hL) hφ a h hQh hPd
  have hNv : eval v (planeLinComb a (planeTangentField F b)) = 0 := by
    rw [eval_planeLinComb, hGv]; exact dot_self_cross _ _
  rw [VarietyHom.IsRamifiedAt, VarietyHom.one_lt_ramificationIndex_iff, hmax, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_le_iff_mem, hpull,
    mem_sq_iff_planeCurveGermDeriv_eq_zero hF hFirr w h₀ (hns P) hP hw
      (by rw [mem_maximalIdeal_iff_evalAtPoint, evalAtPoint_planeCurveQuotGerm, ← hv, hNv,
        zero_div]),
    evalAtPoint_planeCurveGermDeriv_quotGerm, ← hv,
    planeDerivVal_eq_zero_iff w h₀ hNv ((mem_planeCurveNonvanishing hF hFirr _ _).1 hPd)
      ((mem_planeCurveNonvanishing hF hFirr _ _).1 hP),
    planeLinComb_planeTangentField, eval_vectorFieldDeriv_polar, eval_planeTangentField]

/-- **Exercise IV.2.3(a), the ramification criterion.**  The Gauss pencil is ramified at `P`
exactly when `P ∈ L` or the tangent line meets `X` with multiplicity at least three at `P`. -/
theorem isRamifiedAt_planeGaussPencil_iff [CharZero k]
    (hns : (planeCurveVariety hF hFirr).Nonsingular) (L : ProjectiveSpace k (Fin 3))
    (hL : ∀ P ∈ projZeroSet ({F} : Set (MvPolynomial (Fin 3) k)), planeCurveTangentLine F P ≠ L)
    (φ : VarietyHom (planeCurveVariety hF hFirr) (planeLineVariety L))
    (hφ : ∀ x, (Subtype.val (φ x) : ProjectiveSpace k (Fin 3)) =
      Projectivization.mk k _ (gaussPencil_ne_zero hF hFirr hns L hL x))
    (P : (planeCurveVariety hF hFirr).carrier) :
    φ.IsRamifiedAt P ↔
      (Subtype.val P : ProjectiveSpace k (Fin 3)) ∈
          projZeroSet ({projectivePlaneLineForm L.rep} : Set (MvPolynomial (Fin 3) k)) ∨
        3 ≤ projectivePlaneLocalIntersectionMultiplicity
          (projectivePlaneLineForm
            (planeCurveTangentLine F (Subtype.val P : ProjectiveSpace k (Fin 3))).rep) F
          (Subtype.val P : ProjectiveSpace k (Fin 3)) := by
  classical
  set v := (Subtype.val P : ProjectiveSpace k (Fin 3)).rep with hv
  set a : Fin 3 → k := fun l => eval v (pderiv l F) with ha
  set b := L.rep with hb
  have hgrad : a ≠ 0 := gradient_ne_zero_of_nonsingular hF hFirr hns P
  have heuler : v ⬝ᵥ a = 0 := sum_mul_eval_pderiv_eq_zero hF (eval_rep_eq_zero_of_mem hF hFirr P)
  rw [mem_projZeroSet_singleton_iff (isHomogeneous_projectivePlaneLineForm b),
    eval_projectivePlaneLineForm_eq_dotProduct, ← hv]
  by_cases hPL : b ⬝ᵥ v = 0
  · -- `P ∈ L`: the point `T_P(X) ∩ L` is `P` itself.
    refine iff_of_true ?_ (Or.inl hPL)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (Projectivization.rep_nonzero
      (Subtype.val P : ProjectiveSpace k (Fin 3)))
    have hPi : P ∈ planeCurveNonvanishing hF hFirr
        (isHomogeneous_projectivePlaneLineForm (Pi.single i 1)) := by
      rw [mem_planeCurveNonvanishing, eval_projectivePlaneLineForm_eq_dotProduct,
        single_one_dotProduct]
      exact hi
    rw [isRamifiedAt_iff_planeHessian hF hFirr hns L hL φ hφ P _ _ hPi hPi, ← hv]
    have hcross : crossProduct v (crossProduct b a) = 0 := by
      rw [cross_cross_eq_smul_sub_smul', heuler, hPL, zero_smul, zero_smul, sub_zero]
    rw [eq_smul_of_cross_eq_zero hcross hi, planeHessian_comm, planeHessian_smul_left,
      planeHessian_self_left hF]
    have : ∑ j, crossProduct a (Pi.single i 1) j * a j = 0 := by
      have := dot_self_cross a (Pi.single i 1)
      rw [dotProduct_comm] at this
      exact this
    rw [this, mul_zero, mul_zero]
  · -- `P ∉ L`: the point `c = T_P(X) ∩ L` is a second point of the tangent line.
    rw [or_iff_right hPL]
    have hPb : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm b) := by
      rw [mem_planeCurveNonvanishing, eval_projectivePlaneLineForm_eq_dotProduct]
      exact hPL
    have hc0 : crossProduct a b ≠ 0 := by
      have := gaussPencil_ne_zero hF hFirr hns L hL P
      rwa [eval_planeTangentField] at this
    rw [isRamifiedAt_iff_planeHessian hF hFirr hns L hL φ hφ P _ _ hPb hPb, ← hv,
      show crossProduct L.rep a = (-1 : k) • crossProduct a L.rep by
        rw [← cross_anticomm a L.rep]; simp,
      planeHessian_comm, planeHessian_smul_left, neg_one_mul, neg_eq_zero]
    refine (three_le_tangent_multiplicity_iff hF P.2 hgrad ?_ ?_).symm
    · have := dot_self_cross a b
      rw [dotProduct_comm] at this
      exact this
    · intro s t hst
      have h1 := congrArg (b ⬝ᵥ ·) hst
      simp only [dotProduct_add, dotProduct_smul, dotProduct_zero, smul_eq_mul] at h1
      rw [hb, dot_cross_self, mul_zero, add_zero, ← hb, ← hv] at h1
      have hs : s = 0 := (mul_eq_zero.1 h1).resolve_right hPL
      refine ⟨hs, ?_⟩
      rw [hs, zero_smul, zero_add] at hst
      exact (smul_eq_zero.1 hst).resolve_right hc0

end GaussRamification

section Finite

variable {k : Type} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
variable (hF : F.IsHomogeneous d) (hFirr : Irreducible F)

include hF hFirr in
/-- A homogeneous polynomial not divisible by `F` vanishes at only finitely many points of the
curve `F = 0`. -/
theorem finite_inter_projZeroSet {E : MvPolynomial (Fin 3) k} {m : ℕ} (hE : E.IsHomogeneous m)
    (hdvd : ¬ F ∣ E) :
    (projZeroSet ({F} : Set (MvPolynomial (Fin 3) k)) ∩
      projZeroSet ({E} : Set (MvPolynomial (Fin 3) k))).Finite := by
  have hY := isProjVariety_planeCurve hF hFirr
  set Z : Set (planeCurveVariety hF hFirr).carrier :=
    (planeCurveNonvanishing hF hFirr hE : Set _)ᶜ with hZ
  have hZc : IsClosed Z := (planeCurveNonvanishing hF hFirr hE).isOpen.isClosed_compl
  have hZne : Z ≠ Set.univ := by
    intro hZu
    apply hdvd
    refine dvd_of_eval_eq_zero_on_open hF hFirr hE isOpen_univ
      ⟨_, Set.mem_univ (Classical.choice (planeCurveVariety hF hFirr).nonempty)⟩ fun x _ => ?_
    have hx : x ∈ Z := hZu ▸ Set.mem_univ x
    by_contra hne
    exact hx ((mem_planeCurveNonvanishing hF hFirr hE x).2 hne)
  have hfin : Z.Finite :=
    (((hY.isQuasiProjVariety.isCurve_infinite_and_isClosed_iff
      (isCurve_planeCurveVariety hF hFirr)).2 Z).1 hZc).resolve_left hZne
  refine (hfin.image (fun x : (planeCurveVariety hF hFirr).carrier =>
    (Subtype.val x : ProjectiveSpace k (Fin 3)))).subset ?_
  rintro P ⟨hPY, hPE⟩
  refine ⟨⟨P, hPY⟩, fun h => ?_, rfl⟩
  exact ((mem_planeCurveNonvanishing hF hFirr hE _).1 h)
    ((mem_projZeroSet_singleton_iff hE P).1 hPE)

/-- The Hessian pairing `tᵀ (∂²F) t` of the tangent field `t = ∇F × w`, a homogeneous
polynomial. -/
def planeFlexForm (F : MvPolynomial (Fin 3) k) (w : Fin 3 → k) : MvPolynomial (Fin 3) k :=
  ∑ i, planeTangentField F w i * vectorFieldDeriv (planeTangentField F w) (pderiv i F)

omit [IsAlgClosed k] in
include hF in
theorem isHomogeneous_planeFlexForm (w : Fin 3 → k) :
    (planeFlexForm F w).IsHomogeneous ((d - 1) + ((d - 1) + (d - 1 - 1))) :=
  IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_planeTangentField hF w i).mul
    (isHomogeneous_vectorFieldDeriv (isHomogeneous_planeTangentField hF w) hF.pderiv)

omit [IsAlgClosed k] in
theorem eval_vectorFieldDeriv_pderiv (t : Fin 3 → MvPolynomial (Fin 3) k) (x : Fin 3 → k)
    (i : Fin 3) :
    eval x (vectorFieldDeriv t (pderiv i F)) =
      ∑ j, eval x (t j) * eval x (pderiv i (pderiv j F)) := by
  rw [eval_vectorFieldDeriv]
  exact Finset.sum_congr rfl fun j _ => by rw [pderiv_pderiv_comm]

omit [IsAlgClosed k] in
theorem eval_planeFlexForm (w x : Fin 3 → k) :
    eval x (planeFlexForm F w) =
      planeHessian F x (fun j => eval x (planeTangentField F w j))
        (fun j => eval x (planeTangentField F w j)) := by
  simp only [planeFlexForm, map_sum, map_mul, eval_vectorFieldDeriv_pderiv, planeHessian]

omit [IsAlgClosed k] in
include hF in
/-- **Flexes everywhere freeze the Gauss map.**  At a point of the curve off the line `w = 0`
where the flex form vanishes, every ratio of partial derivatives of `F` has zero derivative along
the tangent field `∇F × w`. -/
theorem planeDerivVal_pderiv_eq_zero (h₀ w : Fin 3 → k) {z : Fin 3 → k} (hz : eval z F = 0)
    (hzw : w ⬝ᵥ z ≠ 0) (hK : eval z (planeFlexForm F w) = 0) (i j : Fin 3) :
    planeDerivVal F d w h₀ (pderiv i F) (pderiv j F) z = 0 := by
  set a : Fin 3 → k := fun l => eval z (pderiv l F) with ha
  set c := crossProduct a w with hc
  set u : Fin 3 → k := fun l => eval z (vectorFieldDeriv (planeTangentField F w) (pderiv l F))
    with hu
  have hc' : (fun l => eval z (planeTangentField F w l)) = c := eval_planeTangentField F w z
  have huj : ∀ l, u l = ∑ j, c j * eval z (pderiv l (pderiv j F)) := fun l => by
    simp only [hu, eval_vectorFieldDeriv_pderiv, ← hc']
  have heuler : z ⬝ᵥ a = 0 := sum_mul_eval_pderiv_eq_zero hF hz
  have hzu : z ⬝ᵥ u = 0 := by
    have h := planeHessian_self_left hF z c
    have hca : ∑ j, c j * eval z (pderiv j F) = 0 := by
      have := dot_self_cross a w
      rw [dotProduct_comm] at this
      exact this
    rw [hca, mul_zero] at h
    rw [← h]
    simp only [dotProduct, huj, planeHessian]
  have hcu : c ⬝ᵥ u = 0 := by
    rw [← hK, planeFlexForm, map_sum]
    simp only [map_mul, dotProduct, hu, ← hc']
  have hzc : crossProduct z c = (w ⬝ᵥ z) • a := by
    rw [hc, cross_cross_eq_smul_sub_smul', dotProduct_comm a z, heuler, zero_smul, sub_zero,
      dotProduct_comm]
  have hua : crossProduct u a = 0 := by
    have h := cross_cross_eq_smul_sub_smul' u z c
    rw [dotProduct_comm u c, hcu, hzu, zero_smul, zero_smul, sub_zero, hzc, map_smul] at h
    exact (smul_eq_zero.1 h).resolve_left hzw
  have hnum : eval z (vectorFieldDeriv (planeTangentField F w) (pderiv i F)) * eval z (pderiv j F) -
      eval z (pderiv i F) * eval z (vectorFieldDeriv (planeTangentField F w) (pderiv j F)) = 0 := by
    have := mul_eq_mul_of_cross_eq_zero hua i j
    simp only [hu, ha] at this
    linear_combination this
  simp only [planeDerivVal, planeDerivNum, map_mul, map_sub, map_pow, hnum, zero_mul, zero_div]

/-- **In characteristic zero, the flex form of a curve of degree at least two is not divisible by
`F`**: otherwise every ratio of partial derivatives of `F` would be constant along the curve, and
Euler's formula would split off a linear factor of `F`. -/
theorem not_dvd_planeFlexForm [CharZero k] (hns : (planeCurveVariety hF hFirr).Nonsingular)
    (hd : 2 ≤ d) {P₀ : (planeCurveVariety hF hFirr).carrier} {j₀ : Fin 3}
    (hj₀ : eval (Subtype.val P₀ : ProjectiveSpace k (Fin 3)).rep (pderiv j₀ F) ≠ 0)
    {w : Fin 3 → k}
    (hw : P₀ ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm w)) :
    ¬ F ∣ planeFlexForm F w := by
  intro hdvd
  have hP₀j : P₀ ∈ planeCurveNonvanishing hF hFirr (hF.pderiv (i := j₀)) :=
    (mem_planeCurveNonvanishing hF hFirr _ _).2 hj₀
  have hconst : ∀ i, ∃ lam : k, pderiv i F = C lam * pderiv j₀ F := by
    intro i
    set g := planeCurveQuotGerm hF hFirr (hF.pderiv (i := i)) (hF.pderiv (i := j₀)) hP₀j with hg
    have hDg : planeCurveGermDeriv hF hFirr w w hw g = 0 := by
      refine Quotient.sound fun x hx _ => ?_
      change planeRegDeriv hF hFirr w w _ ⟨x, hx.1⟩ = 0
      rw [planeRegDeriv_eq hF hFirr w w (isQuotRepAt_of_isQuotRepOn hF hFirr
        ⟨isOpen_univ, hF.pderiv, hF.pderiv,
          fun z _ => ⟨(mem_planeCurveNonvanishing hF hFirr _ _).1 z.2, rfl⟩⟩ trivial)]
      refine planeDerivVal_pderiv_eq_zero hF w w (eval_rep_eq_zero_of_mem hF hFirr x) ?_ ?_ i j₀
      · have := (mem_planeCurveNonvanishing hF hFirr _ _).1 hx.2
        rwa [eval_projectivePlaneLineForm_eq_dotProduct] at this
      · obtain ⟨R, hR⟩ := hdvd
        rw [hR, map_mul, eval_rep_eq_zero_of_mem hF hFirr x, zero_mul]
    set lam := Variety.evalAtPoint g
    have hmem : g - algebraMap k _ lam ∈
        maximalIdeal (Variety.LocalRingAt (planeCurveVariety hF hFirr) P₀) := by
      rw [mem_maximalIdeal_iff_evalAtPoint, map_sub]
      exact sub_eq_zero.2 rfl
    have hD : planeCurveGermDeriv hF hFirr w w hw (g - algebraMap k _ lam) = 0 := by
      rw [map_sub, hDg, Derivation.map_algebraMap, sub_zero]
    have hg' : g = algebraMap k _ lam :=
      sub_eq_zero.1 (eq_zero_of_planeCurveGermDeriv_eq_zero hF hFirr w w (hns P₀) hw hw hmem hD)
    have hrel := Quotient.exact hg'
    refine ⟨lam, ?_⟩
    have hE : (pderiv i F - C lam * pderiv j₀ F).IsHomogeneous (d - 1) :=
      hF.pderiv.sub (by simpa using (isHomogeneous_C (Fin 3) lam).mul hF.pderiv)
    have hdvdE : F ∣ pderiv i F - C lam * pderiv j₀ F := by
      refine dvd_of_eval_eq_zero_on_open hF hFirr hE
        (planeCurveNonvanishing hF hFirr (hF.pderiv (i := j₀))).isOpen ⟨P₀, hP₀j⟩ fun x hx => ?_
      have h1 : eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep (pderiv i F) /
          eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep (pderiv j₀ F) = lam :=
        hrel x hx trivial
      have hx' := (mem_planeCurveNonvanishing hF hFirr _ _).1 hx
      rw [div_eq_iff hx'] at h1
      simp only [map_sub, map_mul, eval_C]
      linear_combination h1
    by_contra hne
    exact not_dvd_of_isHomogeneous_lt hF hFirr.ne_zero hE (sub_ne_zero.2 hne) (by omega) hdvdE
  choose lam hlam using hconst
  have hfac : F = (C ((d : k)⁻¹) * projectivePlaneLineForm lam) * pderiv j₀ F := by
    have heul := hF.sum_X_mul_pderiv
    have hd0 : (d : k) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : (d : MvPolynomial (Fin 3) k) * F = projectivePlaneLineForm lam * pderiv j₀ F := by
      rw [← nsmul_eq_mul, ← heul, projectivePlaneLineForm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hlam i]
      ring
    rw [mul_assoc, ← h2, ← mul_assoc, ← map_natCast C, ← map_mul, inv_mul_cancel₀ hd0, map_one,
      one_mul]
  have hA : (C ((d : k)⁻¹) * projectivePlaneLineForm lam).IsHomogeneous 1 := by
    simpa using
      (isHomogeneous_C (Fin 3) ((d : k)⁻¹)).mul (isHomogeneous_projectivePlaneLineForm lam)
  have hA0 : C ((d : k)⁻¹) * projectivePlaneLineForm lam ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfac
    exact hFirr.ne_zero hfac
  have hB0 : pderiv j₀ F ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfac
    exact hFirr.ne_zero hfac
  rcases hFirr.isUnit_or_isUnit hfac with hu | hu
  · exact not_isUnit_of_isHomogeneous hA hA0 one_pos hu
  · exact not_isUnit_of_isHomogeneous hF.pderiv hB0 (by omega) hu

/-- **A nonsingular curve of degree less than two is its own tangent line**: the linear form of
`T_P` divides `F` at every point `P` of the curve. -/
theorem projectivePlaneLineForm_tangentLine_dvd_of_lt_two
    (hns : (planeCurveVariety hF hFirr).Nonsingular) {P : ProjectiveSpace k (Fin 3)}
    (hPY : P ∈ projZeroSet ({F} : Set (MvPolynomial (Fin 3) k))) (hd : d < 2) :
    projectivePlaneLineForm (planeCurveTangentLine F P).rep ∣ F := by
  set a : Fin 3 → k := fun l => eval P.rep (pderiv l F) with ha
  have hgrad : a ≠ 0 := gradient_ne_zero_of_nonsingular hF hFirr hns ⟨P, hPY⟩
  have hconst : ∀ j, pderiv j F = C (a j) := fun j => by
    have h0 : (pderiv j F).totalDegree = 0 := by
      have := (hF.pderiv (i := j)).totalDegree_le
      omega
    show pderiv j F = C (eval P.rep (pderiv j F))
    rw [totalDegree_eq_zero_iff_eq_C.1 h0, eval_C]
  have hd1 : d = 1 := by have := pos_of_isHomogeneous_irreducible hF hFirr; omega
  have hlin : F = projectivePlaneLineForm a := by
    have heul := hF.sum_X_mul_pderiv
    rw [hd1, one_smul] at heul
    rw [← heul, projectivePlaneLineForm]
    exact Finset.sum_congr rfl fun i _ => by rw [hconst i, mul_comm]
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep k a hgrad
  have hbu : (planeCurveTangentLine F P).rep = (u : k) • a := by
    rw [planeCurveTangentLine_of_ne hgrad, ← hu, Units.smul_def]
  have hsm : projectivePlaneLineForm ((u : k) • a) = C (u : k) * projectivePlaneLineForm a := by
    simp only [projectivePlaneLineForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul,
      mul_assoc]
  refine ⟨C (u : k)⁻¹, ?_⟩
  rw [hbu, hsm, ← hlin, mul_comm (C (u : k)) F, mul_assoc, ← map_mul, mul_inv_cancel₀ u.ne_zero,
    map_one, mul_one]

/-- **Finitely many inflection points.**  A nonsingular plane curve over an algebraically closed
field of characteristic zero has only finitely many inflection points (none if it is a line). -/
theorem finite_planeCurveInflectionPoints [CharZero k]
    (hns : (planeCurveVariety hF hFirr).Nonsingular) :
    (planeCurveInflectionPoints F).Finite := by
  classical
  by_cases hd : 2 ≤ d
  swap
  · refine Set.finite_empty.subset ?_
    rintro P ⟨hPY, hndvd, -⟩
    exact hndvd (projectivePlaneLineForm_tangentLine_dvd_of_lt_two hF hFirr hns hPY (by omega))
  obtain ⟨P₀, hP₀Y, j₀, hj₀⟩ := exists_mem_planeCurve_pderiv_ne_zero hF hFirr
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 P₀.rep_nonzero
  set w : Fin 3 → k := Pi.single i₀ 1 with hw
  have hw0 : w ≠ 0 := by
    intro h
    have := congrFun h i₀
    simp [hw] at this
  have hndw : ¬ F ∣ projectivePlaneLineForm w :=
    not_dvd_of_isHomogeneous_lt hF hFirr.ne_zero (isHomogeneous_projectivePlaneLineForm w)
      (projectivePlaneLineForm_ne_zero hw0) (by omega)
  have hP₀w : (⟨P₀, hP₀Y⟩ : (planeCurveVariety hF hFirr).carrier) ∈
      planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm w) :=
    (mem_planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm w) ⟨P₀, hP₀Y⟩).2
      (by rw [eval_projectivePlaneLineForm_eq_dotProduct, single_one_dotProduct]; exact hi₀)
  have hndK := not_dvd_planeFlexForm hF hFirr hns hd (P₀ := ⟨P₀, hP₀Y⟩) hj₀ hP₀w
  refine ((finite_inter_projZeroSet hF hFirr (isHomogeneous_projectivePlaneLineForm w)
    hndw).union (finite_inter_projZeroSet hF hFirr (isHomogeneous_planeFlexForm hF w)
      hndK)).subset ?_
  rintro P ⟨hPY, -, hP3⟩
  by_cases hPw : eval P.rep (projectivePlaneLineForm w) = 0
  · exact Or.inl ⟨hPY, (mem_projZeroSet_singleton_iff
      (isHomogeneous_projectivePlaneLineForm w) P).2 hPw⟩
  · refine Or.inr ⟨hPY, (mem_projZeroSet_singleton_iff (isHomogeneous_planeFlexForm hF w) P).2 ?_⟩
    rw [eval_planeFlexForm, eval_planeTangentField]
    have hgrad : (fun l => eval P.rep (pderiv l F)) ≠ 0 :=
      gradient_ne_zero_of_nonsingular hF hFirr hns ⟨P, hPY⟩
    have hwv : w ⬝ᵥ P.rep ≠ 0 := by rwa [eval_projectivePlaneLineForm_eq_dotProduct] at hPw
    have heuler : P.rep ⬝ᵥ (fun l => eval P.rep (pderiv l F)) = 0 :=
      sum_mul_eval_pderiv_eq_zero hF ((mem_projZeroSet_singleton_iff hF P).1 hPY)
    have hc0 : crossProduct (fun l => eval P.rep (pderiv l F)) w ≠ 0 := by
      intro h0
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hgrad
      apply hwv
      rw [eq_smul_of_cross_eq_zero h0 hj, smul_dotProduct, dotProduct_comm, heuler, smul_zero]
    refine (three_le_tangent_multiplicity_iff hF hPY hgrad ?_ ?_).1 hP3
    · have := dot_self_cross (fun l => eval P.rep (pderiv l F)) w
      rw [dotProduct_comm] at this
      exact this
    · intro s t hst
      have h1 := congrArg (w ⬝ᵥ ·) hst
      simp only [dotProduct_add, dotProduct_smul, dot_cross_self, smul_eq_mul, mul_zero,
        add_zero, dotProduct_zero] at h1
      have hs : s = 0 := (mul_eq_zero.1 h1).resolve_right hwv
      refine ⟨hs, ?_⟩
      rw [hs, zero_smul, zero_add] at hst
      exact (smul_eq_zero.1 hst).resolve_right hc0

end Finite

section Main

variable {k : Type} [Field k] [IsAlgClosed k]

/-- **Hartshorne, Exercise IV.2.3(a).**  Let `X = Z(F) ⊆ ℙ²` be a nonsingular plane curve over an
algebraically closed field of characteristic zero, and let `L` (a point of the dual plane, standing
for the line `L₀x₀ + L₁x₁ + L₂x₂ = 0`) be a line not tangent to `X`.

* `P ↦ T_P(X) ∩ L` is a morphism `φ : X → L`: the point `φ(P)` of `L` lies on `T_P(X)`.
* `φ` is ramified at `P` exactly when `P ∈ L` or `(T_P(X) · X)_P ≥ 3`.
* Consequently `X` has only finitely many inflection points, a flex being a point whose tangent
  line is not a component of `X` and meets `X` there with multiplicity at least three. -/
theorem planeCurve_gaussPencil_ramification [CharZero k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (hFirr : Irreducible F)
    (hns : (Variety.ofProjective (isProjVariety_planeCurve hF hFirr)).Nonsingular)
    (L : ProjectiveSpace k (Fin 3))
    (hL : ∀ P ∈ projZeroSet ({F} : Set (MvPolynomial (Fin 3) k)), planeCurveTangentLine F P ≠ L) :
    ∃ φ : VarietyHom (Variety.ofProjective (isProjVariety_planeCurve hF hFirr))
        (Variety.ofProjective (isProjVariety_planeCurve
          (isHomogeneous_projectivePlaneLineForm L.rep)
          (irreducible_projectivePlaneLineForm L.rep_nonzero))),
      (∀ P, (Subtype.val (φ P) : ProjectiveSpace k (Fin 3)) ∈
        projZeroSet ({projectivePlaneLineForm
          (planeCurveTangentLine F (Subtype.val P : ProjectiveSpace k (Fin 3))).rep} :
            Set (MvPolynomial (Fin 3) k))) ∧
      (∀ P, φ.IsRamifiedAt P ↔
        (Subtype.val P : ProjectiveSpace k (Fin 3)) ∈
            projZeroSet ({projectivePlaneLineForm L.rep} : Set (MvPolynomial (Fin 3) k)) ∨
          3 ≤ projectivePlaneLocalIntersectionMultiplicity
            (projectivePlaneLineForm
              (planeCurveTangentLine F (Subtype.val P : ProjectiveSpace k (Fin 3))).rep) F
            (Subtype.val P : ProjectiveSpace k (Fin 3))) ∧
      (planeCurveInflectionPoints F).Finite := by
  obtain ⟨φ, hφ⟩ := exists_planeGaussPencil hF hFirr hns L hL
  refine ⟨φ, fun P => ?_, isRamifiedAt_planeGaussPencil_iff hF hFirr hns L hL φ hφ,
    finite_planeCurveInflectionPoints hF hFirr hns⟩
  have hgrad := gradient_ne_zero_of_nonsingular hF hFirr hns P
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep k _ hgrad
  rw [hφ P, mem_projZeroSet_singleton_mk_iff (isHomogeneous_projectivePlaneLineForm _),
    planeCurveTangentLine_of_ne hgrad, ← hu, eval_projectivePlaneLineForm_eq_dotProduct,
    Units.smul_def, smul_dotProduct, eval_planeTangentField, dot_self_cross, smul_zero]

end Main

end
end Hartshorne
