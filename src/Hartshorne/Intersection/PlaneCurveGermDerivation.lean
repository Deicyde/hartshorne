/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.PlaneCurveDual
import Hartshorne.Curve.LocalDVR
import Hartshorne.Curve.Cofinite
import Hartshorne.Rational.AffineOpenBasis
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.RingTheory.Derivation.Lie

/-!
# Derivations along a projective plane curve

For a projective plane curve `Y = Z(F) ⊆ ℙ²`, a constant vector `w` gives the polynomial vector
field `t = ∇F × w`, which is tangent to `Y` (`∑ⱼ tⱼ ∂F/∂xⱼ = 0` identically).  Differentiating
local quotients `G/H` of homogeneous polynomials of equal degree along `t`, and dividing by a
suitable power of a linear form `h₀`, gives a `k`-derivation of the local ring `𝒪_{P,Y}` at every
point `P` with `h₀(P) ≠ 0`.

Evaluated at `P`, such a derivation detects the square of the maximal ideal: at a nonsingular
point, where `𝒪_{P,Y}` is a discrete valuation ring, a germ vanishing at `P` lies in `𝔪_P²`
exactly when its derivative vanishes at `P`, as soon as the derivation is nonzero on `𝔪_P`.  In
characteristic zero, a germ vanishing at `P` and killed by such a derivation is zero.

These are the local computations behind Hartshorne, Exercise IV.2.3(a).

## Main definitions

* `Hartshorne.planeTangentField`: the vector field `∇F × w`.
* `Hartshorne.planeCurveGermDeriv`: the derivation of `𝒪_{P,Y}` along it.
* `Hartshorne.planeCurveQuotGerm`: the germ of a quotient of homogeneous polynomials.

## Main results

* `Hartshorne.mem_sq_iff_planeCurveGermDeriv_eq_zero`
* `Hartshorne.irreducible_planeCurveQuotGerm_linear`
* `Hartshorne.eq_zero_of_planeCurveGermDeriv_eq_zero`
-/

namespace Hartshorne
open MvPolynomial TopologicalSpace IsLocalRing

noncomputable section
universe u

section Poly

variable {k : Type u} [Field k]

theorem pderiv_pderiv_comm {σ R : Type*} [CommRing R] (i j : σ) (f : MvPolynomial σ R) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  have h : ⁅(pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)), pderiv j⁆ =
      (0 : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) := by
    refine derivation_ext fun l => ?_
    classical
    simp only [Derivation.commutator_apply, pderiv_X, Derivation.zero_apply]
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> simp
  have := congrArg (fun D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R) => D f) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

/-- The derivation `G ↦ ∑ⱼ tⱼ ∂G/∂xⱼ` along a polynomial vector field `t`. -/
def vectorFieldDeriv (t : Fin 3 → MvPolynomial (Fin 3) k) :
    Derivation k (MvPolynomial (Fin 3) k) (MvPolynomial (Fin 3) k) :=
  ∑ j, t j • pderiv j

theorem vectorFieldDeriv_apply (t : Fin 3 → MvPolynomial (Fin 3) k) (G : MvPolynomial (Fin 3) k) :
    vectorFieldDeriv t G = ∑ j, t j * pderiv j G := by
  change (Derivation.coeFnAddMonoidHom (∑ j, t j • pderiv j)) G = _
  rw [map_sum, Finset.sum_apply]
  simp [Derivation.smul_apply]

theorem eval_vectorFieldDeriv (t : Fin 3 → MvPolynomial (Fin 3) k) (G : MvPolynomial (Fin 3) k)
    (x : Fin 3 → k) :
    eval x (vectorFieldDeriv t G) = ∑ j, eval x (t j) * eval x (pderiv j G) := by
  simp [vectorFieldDeriv_apply]

/-- The tangent vector field `∇F × w` of the plane curve `F = 0`. -/
def planeTangentField (F : MvPolynomial (Fin 3) k) (w : Fin 3 → k) :
    Fin 3 → MvPolynomial (Fin 3) k :=
  crossProduct (fun j => pderiv j F) (fun j => C (w j))

theorem eval_planeTangentField (F : MvPolynomial (Fin 3) k) (w x : Fin 3 → k) :
    (fun j => eval x (planeTangentField F w j)) =
      crossProduct (fun j => eval x (pderiv j F)) w := by
  funext j
  fin_cases j <;> simp [planeTangentField, cross_apply]

theorem vectorFieldDeriv_planeTangentField_self (F : MvPolynomial (Fin 3) k) (w : Fin 3 → k) :
    vectorFieldDeriv (planeTangentField F w) F = 0 := by
  rw [vectorFieldDeriv_apply]
  have h := dot_self_cross (fun j => pderiv j F) (fun j => C (w j))
  rw [dotProduct_comm] at h
  simpa [dotProduct, planeTangentField] using h

theorem isHomogeneous_planeTangentField {F : MvPolynomial (Fin 3) k} {d : ℕ}
    (hF : F.IsHomogeneous d) (w : Fin 3 → k) (j : Fin 3) :
    (planeTangentField F w j).IsHomogeneous (d - 1) := by
  have h : ∀ a b : Fin 3, (pderiv a F * C (w b)).IsHomogeneous (d - 1) := fun a b => by
    simpa using hF.pderiv.mul (isHomogeneous_C (Fin 3) (w b))
  fin_cases j
  · simpa [planeTangentField, cross_apply] using (h 1 2).sub (h 2 1)
  · simpa [planeTangentField, cross_apply] using (h 2 0).sub (h 0 2)
  · simpa [planeTangentField, cross_apply] using (h 0 1).sub (h 1 0)

theorem pderiv_eq_zero_of_isHomogeneous_zero {G : MvPolynomial (Fin 3) k}
    (hG : G.IsHomogeneous 0) (j : Fin 3) : pderiv j G = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, G = C c := by
    rcases eq_or_ne G 0 with rfl | h0
    · exact ⟨0, by simp⟩
    · exact ⟨_, totalDegree_eq_zero_iff_eq_C.1 (hG.totalDegree h0)⟩
  exact pderiv_C

theorem isHomogeneous_vectorFieldDeriv {t : Fin 3 → MvPolynomial (Fin 3) k} {m n : ℕ}
    (ht : ∀ j, (t j).IsHomogeneous m) {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous n) :
    (vectorFieldDeriv t G).IsHomogeneous (m + (n - 1)) := by
  rw [vectorFieldDeriv_apply]
  exact IsHomogeneous.sum _ _ _ fun j _ => (ht j).mul hG.pderiv

variable (F : MvPolynomial (Fin 3) k) (d : ℕ) (w h₀ : Fin 3 → k)

/-- The numerator of the derivative of `G/H` along `∇F × w`, rescaled by `h₀`. -/
def planeDerivNum (G H : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  (vectorFieldDeriv (planeTangentField F w) G * H -
      G * vectorFieldDeriv (planeTangentField F w) H) * projectivePlaneLineForm h₀ ^ 2

/-- The denominator of the derivative of `G/H` along `∇F × w`, rescaled by `h₀`. -/
def planeDerivDen (H : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  H ^ 2 * projectivePlaneLineForm h₀ ^ d

/-- The value at `x` of the derivative of `G/H` along `∇F × w`, rescaled by `h₀`. -/
def planeDerivVal (G H : MvPolynomial (Fin 3) k) (x : Fin 3 → k) : k :=
  eval x (planeDerivNum F w h₀ G H) / eval x (planeDerivDen d h₀ H)

variable {F d}

theorem isHomogeneous_planeDerivNum (hF : F.IsHomogeneous d) (hd : 0 < d)
    {G H : MvPolynomial (Fin 3) k} {n : ℕ} (hG : G.IsHomogeneous n) (hH : H.IsHomogeneous n) :
    (planeDerivNum F w h₀ G H).IsHomogeneous (2 * n + d) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hG0 : vectorFieldDeriv (planeTangentField F w) G = 0 := by
      rw [vectorFieldDeriv_apply]; simp [pderiv_eq_zero_of_isHomogeneous_zero hG]
    have hH0 : vectorFieldDeriv (planeTangentField F w) H = 0 := by
      rw [vectorFieldDeriv_apply]; simp [pderiv_eq_zero_of_isHomogeneous_zero hH]
    simp only [planeDerivNum, hG0, hH0, zero_mul, mul_zero, sub_zero]
    exact isHomogeneous_zero _ _ _
  · have hDG := isHomogeneous_vectorFieldDeriv (isHomogeneous_planeTangentField hF w) hG
    have hDH := isHomogeneous_vectorFieldDeriv (isHomogeneous_planeTangentField hF w) hH
    have h3 := hG.mul hDH
    rw [show n + (d - 1 + (n - 1)) = d - 1 + (n - 1) + n by omega] at h3
    have h1 := (hDG.mul hH).sub h3
    have h2 := h1.mul ((isHomogeneous_projectivePlaneLineForm h₀).pow 2)
    rw [show 2 * n + d = d - 1 + (n - 1) + n + 1 * 2 by omega]
    exact h2

theorem isHomogeneous_planeDerivDen {H : MvPolynomial (Fin 3) k} {n : ℕ}
    (hH : H.IsHomogeneous n) : (planeDerivDen d h₀ H).IsHomogeneous (2 * n + d) := by
  have := (hH.pow 2).mul ((isHomogeneous_projectivePlaneLineForm h₀).pow d)
  simp only [planeDerivDen]
  convert this using 1
  ring

theorem eval_planeDerivDen_ne_zero {H : MvPolynomial (Fin 3) k} {x : Fin 3 → k}
    (hH : eval x H ≠ 0) (hh : eval x (projectivePlaneLineForm h₀) ≠ 0) :
    eval x (planeDerivDen d h₀ H) ≠ 0 := by
  simp only [planeDerivDen, map_mul, map_pow]
  exact mul_ne_zero (pow_ne_zero _ hH) (pow_ne_zero _ hh)

/-- **The derivative of a quotient only depends on the quotient along the curve.**  If
`G₁/H₁ = G₂/H₂` modulo `F`, the two derivatives agree at every point of `F = 0`. -/
theorem planeDerivVal_eq_of_dvd {G₁ H₁ G₂ H₂ : MvPolynomial (Fin 3) k}
    (hdvd : F ∣ G₁ * H₂ - G₂ * H₁) {x : Fin 3 → k} (hx : eval x F = 0)
    (h₁ : eval x H₁ ≠ 0) (h₂ : eval x H₂ ≠ 0) :
    planeDerivVal F d w h₀ G₁ H₁ x = planeDerivVal F d w h₀ G₂ H₂ x := by
  obtain ⟨R, hR⟩ := hdvd
  set D := vectorFieldDeriv (planeTangentField F w)
  have hD : D (G₁ * H₂ - G₂ * H₁) = F * D R := by
    rw [hR, Derivation.leibniz, vectorFieldDeriv_planeTangentField_self, smul_zero, add_zero,
      smul_eq_mul]
  have e1 := congrArg (eval x) hD
  have e0 := congrArg (eval x) hR
  simp only [Derivation.leibniz, map_sub, map_add, smul_eq_mul, map_mul, hx, zero_mul] at e1 e0
  rcases eq_or_ne (eval x (projectivePlaneLineForm h₀)) 0 with he | he
  · simp only [planeDerivVal, planeDerivDen, map_mul, map_pow, he]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [planeDerivNum, he]
    · simp [zero_pow hd.ne']
  · simp only [planeDerivVal, planeDerivNum, planeDerivDen, map_mul, map_sub, map_pow]
    rw [div_eq_div_iff (by simp [h₁, he]) (by simp [h₂, he])]
    linear_combination (eval x (projectivePlaneLineForm h₀) ^ 2 *
      eval x (projectivePlaneLineForm h₀) ^ d) *
      (eval x H₁ * eval x H₂ * e1 -
        (eval x (D H₁) * eval x H₂ + eval x (D H₂) * eval x H₁) * e0)

theorem vectorFieldDeriv_projectivePlaneLineForm (t : Fin 3 → MvPolynomial (Fin 3) k)
    (m : Fin 3 → k) :
    vectorFieldDeriv t (projectivePlaneLineForm m) = ∑ j, t j * C (m j) := by
  rw [vectorFieldDeriv_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  simp only [projectivePlaneLineForm, map_sum, pderiv_C_mul]
  rw [Fintype.sum_eq_single j (fun i hi => by rw [pderiv_X_of_ne hi, mul_zero]), pderiv_X_self,
    mul_one]

theorem planeDerivVal_add {G₁ H₁ G₂ H₂ : MvPolynomial (Fin 3) k} {x : Fin 3 → k}
    (h₁ : eval x H₁ ≠ 0) (h₂ : eval x H₂ ≠ 0) :
    planeDerivVal F d w h₀ (G₁ * H₂ + G₂ * H₁) (H₁ * H₂) x =
      planeDerivVal F d w h₀ G₁ H₁ x + planeDerivVal F d w h₀ G₂ H₂ x := by
  rcases eq_or_ne (eval x (projectivePlaneLineForm h₀)) 0 with he | he
  · simp [planeDerivVal, planeDerivNum, he]
  · simp only [planeDerivVal, planeDerivNum, planeDerivDen, Derivation.leibniz, smul_eq_mul,
      map_add, map_mul, map_sub, map_pow]
    field_simp
    ring

theorem planeDerivVal_mul {G₁ H₁ G₂ H₂ : MvPolynomial (Fin 3) k} {x : Fin 3 → k}
    (h₁ : eval x H₁ ≠ 0) (h₂ : eval x H₂ ≠ 0) :
    planeDerivVal F d w h₀ (G₁ * G₂) (H₁ * H₂) x =
      eval x G₁ / eval x H₁ * planeDerivVal F d w h₀ G₂ H₂ x +
        eval x G₂ / eval x H₂ * planeDerivVal F d w h₀ G₁ H₁ x := by
  rcases eq_or_ne (eval x (projectivePlaneLineForm h₀)) 0 with he | he
  · simp [planeDerivVal, planeDerivNum, he]
  · simp only [planeDerivVal, planeDerivNum, planeDerivDen, Derivation.leibniz, smul_eq_mul,
      map_add, map_mul, map_sub, map_pow]
    field_simp
    ring

theorem planeDerivVal_C_one (c : k) (x : Fin 3 → k) :
    planeDerivVal F d w h₀ (C c) 1 x = 0 := by
  simp [planeDerivVal, planeDerivNum]

/-- At a zero of `G`, the derivative of `G/H` vanishes exactly when that of `G` does. -/
theorem planeDerivVal_eq_zero_iff {G H : MvPolynomial (Fin 3) k} {x : Fin 3 → k}
    (hG : eval x G = 0) (hH : eval x H ≠ 0) (he : eval x (projectivePlaneLineForm h₀) ≠ 0) :
    planeDerivVal F d w h₀ G H x = 0 ↔
      eval x (vectorFieldDeriv (planeTangentField F w) G) = 0 := by
  simp only [planeDerivVal, planeDerivNum, planeDerivDen, map_mul, map_sub, map_pow, hG,
    zero_mul, sub_zero]
  rw [div_eq_zero_iff]
  simp [hH, he]

/-- Euler's formula at a zero of `F`: the gradient of `F` at `v` is orthogonal to `v`. -/
theorem sum_mul_eval_pderiv_eq_zero {F : MvPolynomial (Fin 3) k} {d : ℕ}
    (hF : F.IsHomogeneous d) {v : Fin 3 → k} (hv : eval v F = 0) :
    ∑ j, v j * eval v (pderiv j F) = 0 := by
  have h := congrArg (eval v) hF.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, map_nsmul, hv, smul_zero] at h
  exact h

theorem eval_projectivePlaneLineForm_eq_dotProduct (a x : Fin 3 → k) :
    eval x (projectivePlaneLineForm a) = a ⬝ᵥ x := by
  rw [eval_projectivePlaneLineForm]
  rfl

theorem eval_vectorFieldDeriv_planeTangentField_lineForm (F : MvPolynomial (Fin 3) k)
    (w m x : Fin 3 → k) :
    eval x (vectorFieldDeriv (planeTangentField F w) (projectivePlaneLineForm m)) =
      crossProduct (fun j => eval x (pderiv j F)) w ⬝ᵥ m := by
  rw [vectorFieldDeriv_projectivePlaneLineForm, ← eval_planeTangentField]
  simp [dotProduct]

end Poly

section DVR

variable {k : Type u} [Field k] {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **A point derivation detects `𝔪²` in a discrete valuation ring.**  Let `ev : R → k` be a ring
map with kernel the maximal ideal and `δ` a derivation at `ev`.  If `δ` does not vanish on some
`s ∈ 𝔪`, then `s` is a uniformizer, and an element of `𝔪` lies in `𝔪²` exactly when `δ` kills it.
-/
theorem irreducible_and_mem_sq_iff_of_pointDeriv (ev : R →+* k)
    (hev : ∀ a, a ∈ maximalIdeal R ↔ ev a = 0) (δ : R →+ k)
    (hδ : ∀ a b, δ (a * b) = ev a * δ b + ev b * δ a) {s : R} (hs : s ∈ maximalIdeal R)
    (hδs : δ s ≠ 0) :
    Irreducible s ∧ ∀ g ∈ maximalIdeal R, (g ∈ maximalIdeal R ^ 2 ↔ δ g = 0) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : maximalIdeal R = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hϖm : ev ϖ = 0 := (hev ϖ).1 (hm ▸ Ideal.mem_span_singleton_self ϖ)
  have key : ∀ g ∈ maximalIdeal R, ∃ r, g = ϖ * r ∧ δ g = ev r * δ ϖ := by
    intro g hg
    rw [hm, Ideal.mem_span_singleton'] at hg
    obtain ⟨r, rfl⟩ := hg
    refine ⟨r, mul_comm _ _, ?_⟩
    rw [hδ, hϖm, zero_mul, add_zero]
  obtain ⟨r', hs', hδs'⟩ := key s hs
  have hδϖ : δ ϖ ≠ 0 := fun h => hδs (by rw [hδs', h, mul_zero])
  have hr' : IsUnit r' := by
    by_contra hu
    have : ev r' = 0 := (hev r').1 ((mem_maximalIdeal _).2 hu)
    exact hδs (by rw [hδs', this, zero_mul])
  refine ⟨?_, fun g hg => ?_⟩
  · rw [hs']
    exact (associated_mul_unit_right ϖ r' hr').irreducible hϖ
  · obtain ⟨r, rfl, hδg⟩ := key g hg
    rw [hδg, mul_eq_zero, or_iff_left hδϖ, ← hev, hm, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton, pow_two,
      mul_dvd_mul_iff_left hϖ.ne_zero]

/-- **A derivation killing a germ vanishing at the point kills only zero**, in characteristic
zero, as soon as it maps some uniformizer to a unit. -/
theorem eq_zero_of_derivation_eq_zero [Algebra k R] [CharZero k] (D : Derivation k R R)
    {s : R} (hs : Irreducible s) (hDs : IsUnit (D s)) {h : R} (hh : h ∈ maximalIdeal R)
    (hDh : D h = 0) : h = 0 := by
  by_contra h0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hs
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hh
    exact (mem_maximalIdeal _).1 hh u.isUnit
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Derivation.leibniz, Derivation.leibniz_pow, Nat.succ_sub_one] at hDh
  simp only [smul_eq_mul, nsmul_eq_mul] at hDh
  have hunit : IsUnit ((u : R) * ((m.succ : ℕ) : R) * D s) := by
    refine (u.isUnit.mul ?_).mul hDs
    rw [← map_natCast (algebraMap k R)]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m))).map _
  have hsm : s ^ m ≠ 0 := pow_ne_zero _ hs.ne_zero
  have heq : s ^ m * ((u : R) * ((m.succ : ℕ) : R) * D s + s * D u) = 0 := by
    rw [← hDh, pow_succ]
    ring
  have h2 : (u : R) * ((m.succ : ℕ) : R) * D s + s * D u = 0 :=
    (mul_eq_zero.1 heq).resolve_left hsm
  have h3 : IsUnit (s * D u) := by
    rw [show s * D u = -((u : R) * ((m.succ : ℕ) : R) * D s) by linear_combination h2]
    exact hunit.neg
  exact hs.not_isUnit (isUnit_of_mul_isUnit_left h3)

end DVR

section Germ

variable {k : Type u} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
variable (hF : F.IsHomogeneous d) (hFirr : Irreducible F)

/-- The plane curve `Z(F)`, as a variety. -/
abbrev planeCurveVariety : Variety k :=
  Variety.ofProjective (isProjVariety_planeCurve hF hFirr)

omit [IsAlgClosed k] in
theorem isClosed_projZeroSet_singleton {E : MvPolynomial (Fin 3) k} {m : ℕ}
    (hE : E.IsHomogeneous m) : IsClosed (projZeroSet ({E} : Set (MvPolynomial (Fin 3) k))) :=
  isClosed_iff_isProjAlgebraicSet.2
    ⟨{E}, fun f hf => ⟨m, by rw [Set.mem_singleton_iff.1 hf]; exact hE⟩, rfl⟩

theorem eval_rep_eq_zero_of_mem (x : (planeCurveVariety hF hFirr).carrier) :
    eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep F = 0 :=
  (mem_projZeroSet_singleton_iff hF _).1 x.2

/-- The points of the curve where a homogeneous polynomial does not vanish form an open set. -/
def planeCurveNonvanishing {E : MvPolynomial (Fin 3) k} {m : ℕ} (hE : E.IsHomogeneous m) :
    Opens (planeCurveVariety hF hFirr).carrier :=
  ⟨(fun x : (planeCurveVariety hF hFirr).carrier => (Subtype.val x : ProjectiveSpace k (Fin 3)))
      ⁻¹' (projZeroSet ({E} : Set (MvPolynomial (Fin 3) k)))ᶜ,
    IsOpen.preimage continuous_subtype_val (isClosed_projZeroSet_singleton hE).isOpen_compl⟩

theorem mem_planeCurveNonvanishing {E : MvPolynomial (Fin 3) k} {m : ℕ}
    (hE : E.IsHomogeneous m) (x : (planeCurveVariety hF hFirr).carrier) :
    x ∈ planeCurveNonvanishing hF hFirr hE ↔
      eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep E ≠ 0 := by
  show (Subtype.val x : ProjectiveSpace k (Fin 3)) ∉ projZeroSet _ ↔ _
  rw [mem_projZeroSet_singleton_iff hE]

/-- A homogeneous polynomial vanishing on a nonempty open subset of the curve `F = 0` is divisible
by `F`. -/
theorem dvd_of_eval_eq_zero_on_open {E : MvPolynomial (Fin 3) k} {m : ℕ}
    (hE : E.IsHomogeneous m) {V : Set (planeCurveVariety hF hFirr).carrier} (hV : IsOpen V)
    (hne : V.Nonempty)
    (hvan : ∀ x ∈ V, eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep E = 0) : F ∣ E := by
  have hZ : IsClosed {x : (planeCurveVariety hF hFirr).carrier |
      eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep E = 0} := by
    have h : {x : (planeCurveVariety hF hFirr).carrier |
        eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep E = 0} =
        (planeCurveNonvanishing hF hFirr hE : Set _)ᶜ := by
      ext x
      simp [mem_planeCurveNonvanishing]
    rw [h, isClosed_compl_iff]
    exact (planeCurveNonvanishing hF hFirr hE).isOpen
  have hall : ∀ x : (planeCurveVariety hF hFirr).carrier,
      eval (Subtype.val x : ProjectiveSpace k (Fin 3)).rep E = 0 := fun x =>
    closure_minimal hvan hZ ((hV.dense hne).closure_eq ▸ Set.mem_univ x)
  have hmem : E ∈ homogeneousVanishingIdeal (projZeroSet ({F} : Set (MvPolynomial (Fin 3) k))) :=
    Ideal.subset_span ⟨⟨m, hE⟩, fun Q hQ => hall ⟨Q, hQ⟩⟩
  rw [homogeneousVanishingIdeal_planeCurve hF hFirr] at hmem
  exact Ideal.mem_span_singleton.1 hmem

/-- `G/H` represents `f` on the part of its domain lying in `O`. -/
def IsQuotRepOn {U : Opens (planeCurveVariety hF hFirr).carrier} (f : U → k)
    (O : Set (planeCurveVariety hF hFirr).carrier) (n : ℕ) (G H : MvPolynomial (Fin 3) k) :
    Prop :=
  IsOpen O ∧ G.IsHomogeneous n ∧ H.IsHomogeneous n ∧
    ∀ z : U, z.1 ∈ O → eval (Subtype.val z.1 : ProjectiveSpace k (Fin 3)).rep H ≠ 0 ∧
      f z = eval (Subtype.val z.1 : ProjectiveSpace k (Fin 3)).rep G /
        eval (Subtype.val z.1 : ProjectiveSpace k (Fin 3)).rep H

/-- `G/H` represents `f` near `x`. -/
def IsQuotRepAt {U : Opens (planeCurveVariety hF hFirr).carrier} (f : U → k) (x : U) (n : ℕ)
    (G H : MvPolynomial (Fin 3) k) : Prop :=
  ∃ O, x.1 ∈ O ∧ IsQuotRepOn hF hFirr f O n G H

theorem exists_isQuotRepAt {U : Opens (planeCurveVariety hF hFirr).carrier} {f : U → k}
    (hf : f ∈ (planeCurveVariety hF hFirr).regular U) (x : U) :
    ∃ n G H, IsQuotRepAt hF hFirr f x n G H := by
  obtain ⟨W, hW, hxW, n, G, H, hG, hH, hne, he⟩ := (mem_projRegularSubalgebra.1 hf) x
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hW
  exact ⟨n, G, H, O, hxW, hO, hG, hH, fun z hz => ⟨hne z hz, he z hz⟩⟩

/-- **Two quotient representatives have the same derivative.** -/
theorem planeDerivVal_eq_of_isQuotRepAt (w h₀ : Fin 3 → k)
    {U : Opens (planeCurveVariety hF hFirr).carrier} {f : U → k} {x : U}
    {n₁ n₂ : ℕ} {G₁ H₁ G₂ H₂ : MvPolynomial (Fin 3) k}
    (h₁ : IsQuotRepAt hF hFirr f x n₁ G₁ H₁) (h₂ : IsQuotRepAt hF hFirr f x n₂ G₂ H₂) :
    planeDerivVal F d w h₀ G₁ H₁ (Subtype.val x.1 : ProjectiveSpace k (Fin 3)).rep =
      planeDerivVal F d w h₀ G₂ H₂ (Subtype.val x.1 : ProjectiveSpace k (Fin 3)).rep := by
  obtain ⟨O₁, hx₁, hO₁, hG₁, hH₁, hr₁⟩ := h₁
  obtain ⟨O₂, hx₂, hO₂, hG₂, hH₂, hr₂⟩ := h₂
  have hE : (G₁ * H₂ - G₂ * H₁).IsHomogeneous (n₁ + n₂) :=
    (hG₁.mul hH₂).sub (by rw [add_comm]; exact hG₂.mul hH₁)
  have hdvd : F ∣ G₁ * H₂ - G₂ * H₁ := by
    refine dvd_of_eval_eq_zero_on_open hF hFirr hE (V := (U : Set _) ∩ (O₁ ∩ O₂))
      (U.isOpen.inter (hO₁.inter hO₂)) ⟨x.1, x.2, hx₁, hx₂⟩ ?_
    rintro y ⟨hyU, hy₁, hy₂⟩
    obtain ⟨hn₁, he₁⟩ := hr₁ ⟨y, hyU⟩ hy₁
    obtain ⟨hn₂, he₂⟩ := hr₂ ⟨y, hyU⟩ hy₂
    rw [he₁, div_eq_div_iff hn₁ hn₂] at he₂
    simp only [map_sub, map_mul]
    linear_combination he₂
  exact planeDerivVal_eq_of_dvd w h₀ hdvd (eval_rep_eq_zero_of_mem hF hFirr x.1)
    (hr₁ x hx₁).1 (hr₂ x hx₂).1

open Classical in
/-- The derivative along `∇F × w`, rescaled by `h₀`, of a function on an open subset of the
curve, computed from any local quotient representative (and `0` if there is none). -/
def planeRegDeriv (w h₀ : Fin 3 → k) {U : Opens (planeCurveVariety hF hFirr).carrier}
    (f : U → k) (x : U) : k :=
  if h : ∃ c : k, ∃ n G H, IsQuotRepAt hF hFirr f x n G H ∧
      c = planeDerivVal F d w h₀ G H (Subtype.val x.1 : ProjectiveSpace k (Fin 3)).rep then
    h.choose
  else 0

theorem planeRegDeriv_eq (w h₀ : Fin 3 → k) {U : Opens (planeCurveVariety hF hFirr).carrier}
    {f : U → k} {x : U} {n : ℕ} {G H : MvPolynomial (Fin 3) k}
    (h : IsQuotRepAt hF hFirr f x n G H) :
    planeRegDeriv hF hFirr w h₀ f x =
      planeDerivVal F d w h₀ G H (Subtype.val x.1 : ProjectiveSpace k (Fin 3)).rep := by
  have hex : ∃ c : k, ∃ n G H, IsQuotRepAt hF hFirr f x n G H ∧
      c = planeDerivVal F d w h₀ G H (Subtype.val x.1 : ProjectiveSpace k (Fin 3)).rep :=
    ⟨_, n, G, H, h, rfl⟩
  rw [planeRegDeriv, dif_pos hex]
  obtain ⟨n', G', H', h', hc⟩ := hex.choose_spec
  rw [hc]
  exact planeDerivVal_eq_of_isQuotRepAt hF hFirr w h₀ h' h

theorem isQuotRepAt_of_isQuotRepOn {U : Opens (planeCurveVariety hF hFirr).carrier} {f : U → k}
    {O : Set (planeCurveVariety hF hFirr).carrier} {n : ℕ} {G H : MvPolynomial (Fin 3) k}
    (h : IsQuotRepOn hF hFirr f O n G H) {x : U} (hx : x.1 ∈ O) :
    IsQuotRepAt hF hFirr f x n G H :=
  ⟨O, hx, h⟩

variable (w h₀ : Fin 3 → k) {P : (planeCurveVariety hF hFirr).carrier}

/-- The derivative of a germ representative, on the part of its domain where `h₀ ≠ 0`. -/
def planeGermDerivRep
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (r : Variety.GermRep (planeCurveVariety hF hFirr) P) :
    Variety.GermRep (planeCurveVariety hF hFirr) P where
  U := r.U ⊓ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀)
  mem_U := ⟨r.mem_U, hP⟩
  toFun y := planeRegDeriv hF hFirr w h₀ r.toFun ⟨y.1, y.2.1⟩
  regular := by
    refine mem_projRegularSubalgebra.2 fun y => ?_
    obtain ⟨n, G, H, O, hyO, hO, hG, hH, hrep⟩ :=
      exists_isQuotRepAt hF hFirr r.regular ⟨y.1, y.2.1⟩
    have hd : 0 < d := pos_of_isHomogeneous_irreducible hF hFirr
    refine ⟨{z | z.1 ∈ O}, hO.preimage continuous_subtype_val, hyO, 2 * n + d,
      planeDerivNum F w h₀ G H, planeDerivDen d h₀ H,
      isHomogeneous_planeDerivNum w h₀ hF hd hG hH, isHomogeneous_planeDerivDen h₀ hH,
      fun z hz => ?_, fun z hz => ?_⟩
    · exact eval_planeDerivDen_ne_zero h₀ (hrep ⟨z.1, z.2.1⟩ hz).1
        ((mem_planeCurveNonvanishing hF hFirr _ _).1 z.2.2)
    · exact planeRegDeriv_eq hF hFirr w h₀
        (isQuotRepAt_of_isQuotRepOn hF hFirr ⟨hO, hG, hH, hrep⟩ (x := ⟨z.1, z.2.1⟩) hz)

theorem planeGermDerivRep_rel
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    {r s : Variety.GermRep (planeCurveVariety hF hFirr) P} (h : r.Rel s) :
    (planeGermDerivRep hF hFirr w h₀ hP r).Rel (planeGermDerivRep hF hFirr w h₀ hP s) := by
  intro x hr hs
  obtain ⟨n, G, H, O, hxO, hO, hG, hH, hrep⟩ :=
    exists_isQuotRepAt hF hFirr r.regular ⟨x, hr.1⟩
  have hrep' : IsQuotRepOn hF hFirr s.toFun (O ∩ r.U) n G H := by
    refine ⟨hO.inter r.U.isOpen, hG, hH, fun z hz => ?_⟩
    obtain ⟨h1, h2⟩ := hrep ⟨z.1, hz.2⟩ hz.1
    exact ⟨h1, (h z.1 hz.2 z.2).symm.trans h2⟩
  change planeRegDeriv hF hFirr w h₀ r.toFun ⟨x, hr.1⟩ =
    planeRegDeriv hF hFirr w h₀ s.toFun ⟨x, hs.1⟩
  rw [planeRegDeriv_eq hF hFirr w h₀ ⟨O, hxO, hO, hG, hH, hrep⟩,
    planeRegDeriv_eq hF hFirr w h₀ (isQuotRepAt_of_isQuotRepOn hF hFirr hrep' ⟨hxO, hr.1⟩)]

/-- The derivative along `∇F × w`, rescaled by `h₀`, as a map `𝒪_{P,Y} → 𝒪_{P,Y}`. -/
def planeCurveGermDerivFun
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀)) :
    Variety.LocalRingAt (planeCurveVariety hF hFirr) P →
      Variety.LocalRingAt (planeCurveVariety hF hFirr) P :=
  Quotient.map (planeGermDerivRep hF hFirr w h₀ hP) fun _ _ h =>
    planeGermDerivRep_rel hF hFirr w h₀ hP h

theorem planeCurveGermDerivFun_add
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (a b : Variety.LocalRingAt (planeCurveVariety hF hFirr) P) :
    planeCurveGermDerivFun hF hFirr w h₀ hP (a + b) =
      planeCurveGermDerivFun hF hFirr w h₀ hP a + planeCurveGermDerivFun hF hFirr w h₀ hP b := by
  refine Quotient.inductionOn₂ a b fun r s => Quotient.sound fun x h₁ h₂ => ?_
  change planeRegDeriv hF hFirr w h₀ (r.add s).toFun ⟨x, h₁.1⟩ =
    planeRegDeriv hF hFirr w h₀ r.toFun ⟨x, h₂.1.1⟩ +
      planeRegDeriv hF hFirr w h₀ s.toFun ⟨x, h₂.2.1⟩
  obtain ⟨n₁, G₁, H₁, O₁, hx₁, hO₁, hG₁, hH₁, hr₁⟩ :=
    exists_isQuotRepAt hF hFirr r.regular ⟨x, h₂.1.1⟩
  obtain ⟨n₂, G₂, H₂, O₂, hx₂, hO₂, hG₂, hH₂, hr₂⟩ :=
    exists_isQuotRepAt hF hFirr s.regular ⟨x, h₂.2.1⟩
  have hsum : IsQuotRepOn hF hFirr (r.add s).toFun (O₁ ∩ O₂) (n₁ + n₂) (G₁ * H₂ + G₂ * H₁)
      (H₁ * H₂) := by
    refine ⟨hO₁.inter hO₂, (hG₁.mul hH₂).add (by rw [add_comm]; exact hG₂.mul hH₁),
      hH₁.mul hH₂, fun z hz => ?_⟩
    obtain ⟨e₁, f₁⟩ := hr₁ ⟨z.1, z.2.1⟩ hz.1
    obtain ⟨e₂, f₂⟩ := hr₂ ⟨z.1, z.2.2⟩ hz.2
    refine ⟨by simpa using mul_ne_zero e₁ e₂, ?_⟩
    change r.toFun ⟨z.1, z.2.1⟩ + s.toFun ⟨z.1, z.2.2⟩ = _
    rw [f₁, f₂]
    simp only [map_add, map_mul]
    field_simp
  rw [planeRegDeriv_eq hF hFirr w h₀ (isQuotRepAt_of_isQuotRepOn hF hFirr hsum ⟨hx₁, hx₂⟩),
    planeRegDeriv_eq hF hFirr w h₀ ⟨O₁, hx₁, hO₁, hG₁, hH₁, hr₁⟩,
    planeRegDeriv_eq hF hFirr w h₀ ⟨O₂, hx₂, hO₂, hG₂, hH₂, hr₂⟩]
  exact planeDerivVal_add w h₀ (hr₁ _ hx₁).1 (hr₂ _ hx₂).1

theorem planeCurveGermDerivFun_mul
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (a b : Variety.LocalRingAt (planeCurveVariety hF hFirr) P) :
    planeCurveGermDerivFun hF hFirr w h₀ hP (a * b) =
      a * planeCurveGermDerivFun hF hFirr w h₀ hP b +
        b * planeCurveGermDerivFun hF hFirr w h₀ hP a := by
  refine Quotient.inductionOn₂ a b fun r s => Quotient.sound fun x h₁ h₂ => ?_
  change planeRegDeriv hF hFirr w h₀ (r.mul s).toFun ⟨x, h₁.1⟩ =
    r.toFun ⟨x, h₂.1.1⟩ * planeRegDeriv hF hFirr w h₀ s.toFun ⟨x, h₂.1.2.1⟩ +
      s.toFun ⟨x, h₂.2.1⟩ * planeRegDeriv hF hFirr w h₀ r.toFun ⟨x, h₂.2.2.1⟩
  obtain ⟨n₁, G₁, H₁, O₁, hx₁, hO₁, hG₁, hH₁, hr₁⟩ :=
    exists_isQuotRepAt hF hFirr r.regular ⟨x, h₂.1.1⟩
  obtain ⟨n₂, G₂, H₂, O₂, hx₂, hO₂, hG₂, hH₂, hr₂⟩ :=
    exists_isQuotRepAt hF hFirr s.regular ⟨x, h₂.2.1⟩
  have hprod : IsQuotRepOn hF hFirr (r.mul s).toFun (O₁ ∩ O₂) (n₁ + n₂) (G₁ * G₂)
      (H₁ * H₂) := by
    refine ⟨hO₁.inter hO₂, hG₁.mul hG₂, hH₁.mul hH₂, fun z hz => ?_⟩
    obtain ⟨e₁, f₁⟩ := hr₁ ⟨z.1, z.2.1⟩ hz.1
    obtain ⟨e₂, f₂⟩ := hr₂ ⟨z.1, z.2.2⟩ hz.2
    refine ⟨by simpa using mul_ne_zero e₁ e₂, ?_⟩
    change r.toFun ⟨z.1, z.2.1⟩ * s.toFun ⟨z.1, z.2.2⟩ = _
    rw [f₁, f₂]
    simp only [map_mul]
    field_simp
  rw [planeRegDeriv_eq hF hFirr w h₀ (isQuotRepAt_of_isQuotRepOn hF hFirr hprod ⟨hx₁, hx₂⟩),
    planeRegDeriv_eq hF hFirr w h₀ ⟨O₁, hx₁, hO₁, hG₁, hH₁, hr₁⟩,
    planeRegDeriv_eq hF hFirr w h₀ ⟨O₂, hx₂, hO₂, hG₂, hH₂, hr₂⟩,
    (hr₁ ⟨x, h₂.1.1⟩ hx₁).2, (hr₂ ⟨x, h₂.2.1⟩ hx₂).2]
  exact planeDerivVal_mul w h₀ (hr₁ _ hx₁).1 (hr₂ _ hx₂).1

theorem planeCurveGermDerivFun_algebraMap
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (c : k) :
    planeCurveGermDerivFun hF hFirr w h₀ hP
      (algebraMap k (Variety.LocalRingAt (planeCurveVariety hF hFirr) P) c) = 0 := by
  refine Quotient.sound fun x h₁ _ => ?_
  change planeRegDeriv hF hFirr w h₀ (Variety.GermRep.const P c).toFun ⟨x, h₁.1⟩ = 0
  have hrep : IsQuotRepOn hF hFirr (Variety.GermRep.const P c).toFun Set.univ 0 (C c) 1 :=
    ⟨isOpen_univ, isHomogeneous_C _ _, isHomogeneous_one _ _, fun z _ => by simp; rfl⟩
  rw [planeRegDeriv_eq hF hFirr w h₀ (isQuotRepAt_of_isQuotRepOn hF hFirr hrep trivial)]
  exact planeDerivVal_C_one w h₀ c _

/-- **The derivation of `𝒪_{P,Y}` along `∇F × w`**, rescaled by the linear form `h₀`, at a point
`P` of the curve where `h₀(P) ≠ 0`. -/
def planeCurveGermDeriv
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀)) :
    Derivation k (Variety.LocalRingAt (planeCurveVariety hF hFirr) P)
      (Variety.LocalRingAt (planeCurveVariety hF hFirr) P) where
  toFun := planeCurveGermDerivFun hF hFirr w h₀ hP
  map_add' := planeCurveGermDerivFun_add hF hFirr w h₀ hP
  map_smul' c a := by
    rw [Algebra.smul_def, planeCurveGermDerivFun_mul, planeCurveGermDerivFun_algebraMap,
      mul_zero, add_zero, RingHom.id_apply, Algebra.smul_def]
  map_one_eq_zero' := by
    have := planeCurveGermDerivFun_algebraMap hF hFirr w h₀ hP 1
    rwa [map_one] at this
  leibniz' a b := by
    rw [smul_eq_mul, smul_eq_mul]
    exact planeCurveGermDerivFun_mul hF hFirr w h₀ hP a b

theorem evalAtPoint_planeCurveGermDeriv_mk
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (r : Variety.GermRep (planeCurveVariety hF hFirr) P) :
    Variety.evalAtPoint (planeCurveGermDeriv hF hFirr w h₀ hP (Quotient.mk _ r)) =
      planeRegDeriv hF hFirr w h₀ r.toFun ⟨P, r.mem_U⟩ :=
  rfl

/-- The germ at `P` of the quotient `G/H` of homogeneous polynomials of equal degree, `H(P) ≠ 0`.
-/
def planeCurveQuotGerm {n : ℕ} {G H : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous n)
    (hH : H.IsHomogeneous n) (hP : P ∈ planeCurveNonvanishing hF hFirr hH) :
    Variety.LocalRingAt (planeCurveVariety hF hFirr) P :=
  Quotient.mk _
    { U := planeCurveNonvanishing hF hFirr hH
      mem_U := hP
      toFun := fun z => eval (Subtype.val z.1 : ProjectiveSpace k (Fin 3)).rep G /
        eval (Subtype.val z.1 : ProjectiveSpace k (Fin 3)).rep H
      regular := mem_projRegularSubalgebra.2 fun _ =>
        ⟨Set.univ, isOpen_univ, trivial, n, G, H, hG, hH,
          fun z _ => (mem_planeCurveNonvanishing hF hFirr hH _).1 z.2, fun _ _ => rfl⟩ }

theorem evalAtPoint_planeCurveQuotGerm {n : ℕ} {G H : MvPolynomial (Fin 3) k}
    (hG : G.IsHomogeneous n) (hH : H.IsHomogeneous n)
    (hP : P ∈ planeCurveNonvanishing hF hFirr hH) :
    Variety.evalAtPoint (planeCurveQuotGerm hF hFirr hG hH hP) =
      eval (Subtype.val P : ProjectiveSpace k (Fin 3)).rep G /
        eval (Subtype.val P : ProjectiveSpace k (Fin 3)).rep H :=
  rfl

theorem evalAtPoint_planeCurveGermDeriv_quotGerm
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    {n : ℕ} {G H : MvPolynomial (Fin 3) k}
    (hG : G.IsHomogeneous n) (hH : H.IsHomogeneous n)
    (hPH : P ∈ planeCurveNonvanishing hF hFirr hH) :
    Variety.evalAtPoint (planeCurveGermDeriv hF hFirr w h₀ hP
      (planeCurveQuotGerm hF hFirr hG hH hPH)) =
      planeDerivVal F d w h₀ G H (Subtype.val P : ProjectiveSpace k (Fin 3)).rep := by
  rw [planeCurveQuotGerm, evalAtPoint_planeCurveGermDeriv_mk]
  exact planeRegDeriv_eq hF hFirr w h₀
    (isQuotRepAt_of_isQuotRepOn hF hFirr ⟨isOpen_univ, hG, hH,
      fun z _ => ⟨(mem_planeCurveNonvanishing hF hFirr hH _).1 z.2, rfl⟩⟩ trivial)

end Germ

section Nonsingular

/- The comparison of local rings with discrete valuation rings used below is available for
varieties over a field in the base universe. -/
variable {k : Type} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
variable (hF : F.IsHomogeneous d) (hFirr : Irreducible F)

theorem isCurve_planeCurveVariety : (planeCurveVariety hF hFirr).IsCurve :=
  projDim_planeCurve hF hFirr

theorem isDiscreteValuationRing_planeCurve {P : (planeCurveVariety hF hFirr).carrier}
    (hns : (planeCurveVariety hF hFirr).NonsingularAt P) :
    IsDiscreteValuationRing (Variety.LocalRingAt (planeCurveVariety hF hFirr) P) :=
  (Variety.hasAffineOpenBasis_ofProjective
    (isProjVariety_planeCurve hF hFirr)).isDiscreteValuationRing_localRingAt_of_nonsingularAt
    (isCurve_planeCurveVariety hF hFirr) P hns

theorem exists_pderiv_ne_zero_of_nonsingularAt {P : (planeCurveVariety hF hFirr).carrier}
    (hns : (planeCurveVariety hF hFirr).NonsingularAt P) :
    ∃ j, eval (Subtype.val P : ProjectiveSpace k (Fin 3)).rep (pderiv j F) ≠ 0 :=
  (nonsingularAt_planeCurve_iff hF hFirr P).1 hns

variable (w h₀ : Fin 3 → k) {P : (planeCurveVariety hF hFirr).carrier}

/-- Evaluation at `P` of the derivation, as a point derivation. -/
def planeCurvePointDeriv
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀)) :
    Variety.LocalRingAt (planeCurveVariety hF hFirr) P →+ k where
  toFun a := Variety.evalAtPoint (planeCurveGermDeriv hF hFirr w h₀ hP a)
  map_zero' := by simp
  map_add' a b := by simp

theorem planeCurvePointDeriv_apply
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (a : Variety.LocalRingAt (planeCurveVariety hF hFirr) P) :
    planeCurvePointDeriv hF hFirr w h₀ hP a =
      Variety.evalAtPoint (planeCurveGermDeriv hF hFirr w h₀ hP a) :=
  rfl

theorem planeCurvePointDeriv_mul
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (a b : Variety.LocalRingAt (planeCurveVariety hF hFirr) P) :
    planeCurvePointDeriv hF hFirr w h₀ hP (a * b) =
      Variety.evalAtPoint a * planeCurvePointDeriv hF hFirr w h₀ hP b +
        Variety.evalAtPoint b * planeCurvePointDeriv hF hFirr w h₀ hP a := by
  simp [planeCurvePointDeriv, Derivation.leibniz, smul_eq_mul]

theorem mem_maximalIdeal_iff_evalAtPoint (a : Variety.LocalRingAt (planeCurveVariety hF hFirr) P) :
    a ∈ maximalIdeal (Variety.LocalRingAt (planeCurveVariety hF hFirr) P) ↔
      Variety.evalAtPoint a = 0 := by
  rw [Variety.maximalIdeal_eq_ker, RingHom.mem_ker]

/-- Where `v ⬝ w ≠ 0`, the derivation along `∇F × w` is nonzero on the maximal ideal. -/
theorem exists_planeCurveGermDeriv_ne_zero (hns : (planeCurveVariety hF hFirr).NonsingularAt P)
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (hw : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm w)) :
    ∃ s ∈ maximalIdeal (Variety.LocalRingAt (planeCurveVariety hF hFirr) P),
      planeCurvePointDeriv hF hFirr w h₀ hP s ≠ 0 := by
  classical
  set v := (Subtype.val P : ProjectiveSpace k (Fin 3)).rep with hv
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero_of_nonsingularAt hF hFirr hns
  set m : Fin 3 → k := crossProduct (Pi.single j 1) v with hm
  have hmv : eval v (projectivePlaneLineForm m) = 0 := by
    rw [eval_projectivePlaneLineForm_eq_dotProduct, dotProduct_comm]
    exact dot_cross_self _ _
  have hwv : w ⬝ᵥ v ≠ 0 := by
    have := (mem_planeCurveNonvanishing hF hFirr _ _).1 hw
    rwa [eval_projectivePlaneLineForm_eq_dotProduct] at this
  have heuler : (fun l => eval v (pderiv l F)) ⬝ᵥ v = 0 := by
    rw [dotProduct_comm]
    exact sum_mul_eval_pderiv_eq_zero hF (eval_rep_eq_zero_of_mem hF hFirr P)
  refine ⟨planeCurveQuotGerm hF hFirr (isHomogeneous_projectivePlaneLineForm m)
    (isHomogeneous_projectivePlaneLineForm h₀) hP, ?_, ?_⟩
  · rw [mem_maximalIdeal_iff_evalAtPoint, evalAtPoint_planeCurveQuotGerm, ← hv, hmv, zero_div]
  · rw [planeCurvePointDeriv_apply, evalAtPoint_planeCurveGermDeriv_quotGerm, ← hv]
    rw [Ne, planeDerivVal_eq_zero_iff w h₀ hmv ((mem_planeCurveNonvanishing hF hFirr _ _).1 hP)
      ((mem_planeCurveNonvanishing hF hFirr _ _).1 hP),
      eval_vectorFieldDeriv_planeTangentField_lineForm, hm, cross_dot_cross, heuler,
      dotProduct_single_one, zero_mul, sub_zero]
    exact mul_ne_zero hj hwv

/-- **The derivation detects `𝔪_P²`.**  At a nonsingular point `P` of the curve with
`h₀(P) ≠ 0` and `w(P) ≠ 0`, a germ vanishing at `P` lies in `𝔪_P²` exactly when its derivative
along `∇F × w` vanishes at `P`. -/
theorem mem_sq_iff_planeCurveGermDeriv_eq_zero
    (hns : (planeCurveVariety hF hFirr).NonsingularAt P)
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (hw : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm w))
    {g : Variety.LocalRingAt (planeCurveVariety hF hFirr) P}
    (hg : g ∈ maximalIdeal (Variety.LocalRingAt (planeCurveVariety hF hFirr) P)) :
    g ∈ maximalIdeal (Variety.LocalRingAt (planeCurveVariety hF hFirr) P) ^ 2 ↔
      Variety.evalAtPoint (planeCurveGermDeriv hF hFirr w h₀ hP g) = 0 := by
  have := isDiscreteValuationRing_planeCurve hF hFirr hns
  obtain ⟨s, hs, hδs⟩ := exists_planeCurveGermDeriv_ne_zero hF hFirr w h₀ hns hP hw
  exact (irreducible_and_mem_sq_iff_of_pointDeriv Variety.evalAtPoint
    (mem_maximalIdeal_iff_evalAtPoint hF hFirr) _
    (planeCurvePointDeriv_mul hF hFirr w h₀ hP) hs hδs).2 g hg

/-- **In characteristic zero, the derivation has no nonzero constants vanishing at `P`.** -/
theorem eq_zero_of_planeCurveGermDeriv_eq_zero [CharZero k]
    (hns : (planeCurveVariety hF hFirr).NonsingularAt P)
    (hP : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h₀))
    (hw : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm w))
    {g : Variety.LocalRingAt (planeCurveVariety hF hFirr) P}
    (hg : g ∈ maximalIdeal (Variety.LocalRingAt (planeCurveVariety hF hFirr) P))
    (hDg : planeCurveGermDeriv hF hFirr w h₀ hP g = 0) : g = 0 := by
  have := isDiscreteValuationRing_planeCurve hF hFirr hns
  obtain ⟨s, hs, hδs⟩ := exists_planeCurveGermDeriv_ne_zero hF hFirr w h₀ hns hP hw
  have hirr := (irreducible_and_mem_sq_iff_of_pointDeriv Variety.evalAtPoint
    (mem_maximalIdeal_iff_evalAtPoint hF hFirr) _
    (planeCurvePointDeriv_mul hF hFirr w h₀ hP) hs hδs).1
  exact eq_zero_of_derivation_eq_zero _ hirr
    ((Variety.isUnit_iff_evalAtPoint_ne_zero _).2 hδs) hg hDg

/-- **Linear uniformizers.**  At a nonsingular point `P` of the curve, the quotient `m/h` of
linear forms, with `m` through `P` and not the tangent line, is a uniformizer of `𝒪_{P,Y}`. -/
theorem irreducible_planeCurveQuotGerm_linear
    (hns : (planeCurveVariety hF hFirr).NonsingularAt P) {m h : Fin 3 → k}
    (hm : eval (Subtype.val P : ProjectiveSpace k (Fin 3)).rep (projectivePlaneLineForm m) = 0)
    (hma : crossProduct m (fun j => eval (Subtype.val P : ProjectiveSpace k (Fin 3)).rep
      (pderiv j F)) ≠ 0)
    (hPh : P ∈ planeCurveNonvanishing hF hFirr (isHomogeneous_projectivePlaneLineForm h)) :
    Irreducible (planeCurveQuotGerm hF hFirr (isHomogeneous_projectivePlaneLineForm m)
      (isHomogeneous_projectivePlaneLineForm h) hPh) := by
  classical
  have := isDiscreteValuationRing_planeCurve hF hFirr hns
  set v := (Subtype.val P : ProjectiveSpace k (Fin 3)).rep with hv
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hma
  refine (irreducible_and_mem_sq_iff_of_pointDeriv Variety.evalAtPoint
    (mem_maximalIdeal_iff_evalAtPoint hF hFirr) _
    (planeCurvePointDeriv_mul hF hFirr (Pi.single j 1) h hPh) ?_ ?_).1
  · rw [mem_maximalIdeal_iff_evalAtPoint, evalAtPoint_planeCurveQuotGerm, ← hv, hm, zero_div]
  · rw [planeCurvePointDeriv_apply, evalAtPoint_planeCurveGermDeriv_quotGerm, ← hv]
    rw [Ne, planeDerivVal_eq_zero_iff _ h hm ((mem_planeCurveNonvanishing hF hFirr _ _).1 hPh)
      ((mem_planeCurveNonvanishing hF hFirr _ _).1 hPh),
      eval_vectorFieldDeriv_planeTangentField_lineForm, dotProduct_comm,
      triple_product_permutation, triple_product_permutation, single_one_dotProduct]
    exact hj

end Nonsingular

end
end Hartshorne
