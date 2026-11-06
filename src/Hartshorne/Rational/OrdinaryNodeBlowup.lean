/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.OrdinaryNodeAlgebra
import Hartshorne.Rational.BlowingUp

/-!
# The strict transform of a plane curve through the origin, chart by chart

Toward Hartshorne, *Algebraic Geometry*, I, Exercise 5.6(b).

Let `g ∈ k[x₀, x₁]` have no constant and no linear term and a nonzero
quadratic term `g₂`, and let `Ỹ` be the strict transform of `Y = Z(g)` in the
blow-up of the plane at the origin.  A point of the blow-up is `(x, [y])`; on
the chart where `y_j ≠ 0` it is `(t • w(u), [w(u)])` with `w(u)` the vector with
`j`-th coordinate `1` and other coordinate `u`.  This file proves

* on that chart, `(t • w(u), [w(u)]) ∈ Ỹ` exactly when `g̃ⱼ(t, u) = 0`, for `g`
  irreducible (the forward implication holds for every `g`);
* the points of `Ỹ` over the origin are exactly the points `(0, [y])` with
  `g₂(y) = 0`.

The inclusion `Ỹ ⊆ {g̃ⱼ = 0}` is obtained from one homogeneous polynomial in
the Segre coordinates vanishing on the punctured part of the inverse image.
The reverse inclusion at `t = 0` uses the Nullstellensatz and the primality of
`g̃ⱼ`.
-/

namespace Hartshorne

namespace OrdinaryNode

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k]

/-! ## Coordinates on the plane -/

/-- The index type of the coordinates of the plane, in the universe of `k`
(the blow-up is set up for coordinate types in the universe of the field). -/
abbrev PlaneIndex : Type u := ULift.{u} (Fin 2)

/-- Read a point of the plane in `Fin 2` coordinates. -/
def lowerVec (x : PlaneIndex.{u} → k) : Fin 2 → k := fun i => x ⟨i⟩

/-- Write a `Fin 2` vector as a point of the plane. -/
def liftVec (v : Fin 2 → k) : PlaneIndex.{u} → k := fun i => v i.down

omit [Field k] in
@[simp]
theorem lowerVec_apply (x : PlaneIndex.{u} → k) (i : Fin 2) : lowerVec x i = x ⟨i⟩ := rfl

omit [Field k] in
@[simp]
theorem liftVec_apply (v : Fin 2 → k) (i : PlaneIndex.{u}) : liftVec v i = v i.down := rfl

omit [Field k] in
@[simp]
theorem lowerVec_liftVec (v : Fin 2 → k) : lowerVec (liftVec.{u} v) = v := rfl

@[simp]
theorem lowerVec_smul (c : k) (x : PlaneIndex.{u} → k) :
    lowerVec (c • x) = c • lowerVec x := rfl

theorem liftVec_ne_zero {v : Fin 2 → k} (hv : v ≠ 0) : liftVec.{u} v ≠ 0 := by
  intro h
  apply hv
  funext i
  simpa using congrFun h ⟨i⟩

theorem lowerVec_ne_zero {x : PlaneIndex.{u} → k} (hx : x ≠ 0) : lowerVec x ≠ 0 := by
  intro h
  apply hx
  funext i
  simpa using congrFun h i.down

theorem eval_rename_up (x : PlaneIndex.{u} → k) (p : MvPolynomial (Fin 2) k) :
    eval x (rename ULift.up p) = eval (lowerVec x) p := by
  rw [eval_rename]
  rfl

/-- The `j`-th chart vector, as a point of the plane. -/
def planeChartVec (j : Fin 2) (u : k) : PlaneIndex.{u} → k := liftVec (chartVec j u)

theorem planeChartVec_ne_zero (j : Fin 2) (u : k) : planeChartVec.{u} j u ≠ 0 :=
  liftVec_ne_zero (chartVec_ne_zero j u)

@[simp]
theorem lowerVec_planeChartVec (j : Fin 2) (u : k) :
    lowerVec (planeChartVec.{u} j u) = chartVec j u := rfl

@[simp]
theorem planeChartVec_self (j : Fin 2) (u : k) : planeChartVec.{u} j u ⟨j⟩ = 1 := by
  simp [planeChartVec]

@[simp]
theorem planeChartVec_rev (j : Fin 2) (u : k) : planeChartVec.{u} j u ⟨j.rev⟩ = u := by
  simp [planeChartVec]

theorem eq_smul_planeChartVec (x : PlaneIndex.{u} → k) {j : Fin 2} (hx : x ⟨j⟩ ≠ 0) :
    x = x ⟨j⟩ • planeChartVec j (x ⟨j.rev⟩ / x ⟨j⟩) := by
  have h := eq_smul_chartVec (lowerVec x) (j := j) hx
  funext i
  have := congrFun h i.down
  simpa [planeChartVec] using this

/-! ## Points of the blow-up in homogeneous coordinates -/

/-- The homogeneous vector `(1, x)` of an affine point. -/
def homVec (x : PlaneIndex.{u} → k) : Option PlaneIndex.{u} → k :=
  fun o => o.elim 1 x

@[simp]
theorem homVec_none (x : PlaneIndex.{u} → k) : homVec x none = 1 := rfl

@[simp]
theorem homVec_some (x : PlaneIndex.{u} → k) (i : PlaneIndex.{u}) :
    homVec x (some i) = x i := rfl

theorem homVec_ne_zero (x : PlaneIndex.{u} → k) : homVec x ≠ 0 := by
  intro h
  simpa using congrFun h none

/-- The point `(x, [y])` of `𝔸² × ℙ¹`, in the Segre coordinates. -/
noncomputable def blowupPt (x y : PlaneIndex.{u} → k) (hy : y ≠ 0) :
    ProjectiveSpace k (Option PlaneIndex.{u} × PlaneIndex.{u}) :=
  Projectivization.mk k (segreVector (homVec x) y)
    (segreVector_ne_zero (homVec_ne_zero x) hy)

theorem exists_rep_blowupPt (x y : PlaneIndex.{u} → k) (hy : y ≠ 0) :
    ∃ a : kˣ, (blowupPt x y hy).rep = a • segreVector (homVec x) y := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k
    (segreVector (homVec x) y) (segreVector_ne_zero (homVec_ne_zero x) hy)
  exact ⟨a, ha.symm⟩

theorem blowupPt_eq_of_smul (x : PlaneIndex.{u} → k) {y y' : PlaneIndex.{u} → k}
    (hy : y ≠ 0) (hy' : y' ≠ 0) {c : k} (hc : c ≠ 0) (h : y = c • y') :
    blowupPt x y hy = blowupPt x y' hy' := by
  unfold blowupPt
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 c hc, ?_⟩
  funext p
  simp only [h, segreVector, Pi.smul_apply, Units.smul_def, smul_eq_mul, Units.val_mk0]
  ring

theorem homogeneousVanish_blowupPt_iff
    {f : MvPolynomial (Option PlaneIndex.{u} × PlaneIndex.{u}) k}
    {n : ℕ} (hf : f.IsHomogeneous n) (x y : PlaneIndex.{u} → k) (hy : y ≠ 0) :
    HomogeneousVanish f (blowupPt x y hy) ↔ eval (segreVector (homVec x) y) f = 0 :=
  homogeneousVanish_iff_of_isHomogeneous hf _

theorem blowupPt_mem (x y : PlaneIndex.{u} → k) (hy : y ≠ 0)
    (hinc : ∀ i i', x i * y i' = x i' * y i) :
    blowupPt x y hy ∈ blowupSet (k := k) (σ := PlaneIndex.{u}) := by
  refine ⟨?_, ?_⟩
  · rw [blowupAmbient, mem_segreProduct_iff]
    refine ⟨Projectivization.mk k (homVec x) (homVec_ne_zero x), ?_,
      Projectivization.mk k y hy, Set.mem_univ _, ?_⟩
    · change ¬ HomogeneousVanish _ _
      rw [homogeneousVanish_X_iff]
      simp
    · rw [segreMap_mk_mk]
      rfl
  · intro f hf
    obtain ⟨i, i', rfl⟩ := hf
    rw [homogeneousVanish_blowupPt_iff (blowupEquation_isHomogeneous i i')]
    simp [blowupEquation, segreVector, hinc i i']

section Projection

variable [IsAlgClosed k]

/-- The blow-up of the plane at the origin, as a quasi-projective set. -/
abbrev planeBlowupQ : IsQuasiProjVariety (blowupSet (k := k) (σ := PlaneIndex.{u})) :=
  isQuasiProjVariety_blowupSet (k := k) (σ := PlaneIndex.{u})

/-- The projection of a point of the blow-up to the plane. -/
noncomputable abbrev proj (R : blowupSet (k := k) (σ := PlaneIndex.{u})) :
    PlaneIndex.{u} → k :=
  (blowupProjectionAffine (planeBlowupQ (k := k)) R).1

omit [IsAlgClosed k] in
theorem rep_eq_smul_segreVector (R : blowupSet (k := k) (σ := PlaneIndex.{u})) :
    ∃ a : kˣ, R.1.rep = a • segreVector (blowupFirst R).1.rep (blowupSecond R).rep := by
  have hseg : segreMap (blowupFirst R).1 (blowupSecond R) = R.1 :=
    segreMap_fst_snd (blowupAsAmbient R)
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k
    (segreVector (blowupFirst R).1.rep (blowupSecond R).rep)
    (segreVector_ne_zero (blowupFirst R).1.rep_nonzero (blowupSecond R).rep_nonzero)
  refine ⟨a, ?_⟩
  rw [← hseg]
  exact ha.symm

theorem proj_apply_eq (R : blowupSet (k := k) (σ := PlaneIndex.{u})) (i : PlaneIndex.{u}) :
    proj R i = (blowupFirst R).1.rep (some i) / (blowupFirst R).1.rep none := by
  let R' : (Variety.ofQuasiProjective (planeBlowupQ (k := k))).carrier := ⟨R.1, R.2⟩
  change (blowupProjectionAffine (planeBlowupQ (k := k)) R').1 i = _
  rw [blowupProjectionAffine_apply]
  rfl

/-- The blow-up projection in homogeneous coordinates. -/
theorem proj_eq_div (R : blowupSet (k := k) (σ := PlaneIndex.{u})) {b : PlaneIndex.{u}}
    (hb : R.1.rep (none, b) ≠ 0) (i : PlaneIndex.{u}) :
    proj R i = R.1.rep (some i, b) / R.1.rep (none, b) := by
  rw [proj_apply_eq]
  obtain ⟨a, hrep⟩ := rep_eq_smul_segreVector R
  have hPn : (blowupFirst R).1.rep none ≠ 0 :=
    rep_ne_zero_of_mem_standardChart (blowupFirst R).2
  rw [hrep] at hb ⊢
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, segreVector] at hb ⊢
  have hQb : (blowupSecond R).rep b ≠ 0 := by
    intro h
    apply hb
    simp [h]
  field_simp

theorem proj_blowupPt (x y : PlaneIndex.{u} → k) (hy : y ≠ 0)
    (hmem : blowupPt x y hy ∈ blowupSet (k := k) (σ := PlaneIndex.{u})) :
    proj ⟨blowupPt x y hy, hmem⟩ = x := by
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hy
  have hb0 : y b ≠ 0 := hb
  obtain ⟨a, ha⟩ := exists_rep_blowupPt x y hy
  have hb' : (blowupPt x y hy).rep (none, b) ≠ 0 := by
    rw [ha]
    simp [segreVector, Units.smul_def, hb0]
  funext i
  rw [proj_eq_div ⟨blowupPt x y hy, hmem⟩ hb' i]
  change (blowupPt x y hy).rep (some i, b) / (blowupPt x y hy).rep (none, b) = x i
  rw [ha]
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, segreVector, homVec_some,
    homVec_none, one_mul]
  field_simp

omit [IsAlgClosed k] in
theorem second_blowupPt (x y : PlaneIndex.{u} → k) (hy : y ≠ 0)
    (hmem : blowupPt x y hy ∈ blowupSet (k := k) (σ := PlaneIndex.{u})) :
    blowupSecond ⟨blowupPt x y hy, hmem⟩ = Projectivization.mk k y hy := by
  let R : blowupSet (k := k) (σ := PlaneIndex.{u}) := ⟨blowupPt x y hy, hmem⟩
  have hseg : segreMap (blowupFirst R).1 (blowupSecond R) = R.1 :=
    segreMap_fst_snd (blowupAsAmbient R)
  have hPn : (blowupFirst R).1.rep none ≠ 0 :=
    rep_ne_zero_of_mem_standardChart (blowupFirst R).2
  change segreMap (blowupFirst R).1 (blowupSecond R) = blowupPt x y hy at hseg
  unfold segreMap blowupPt at hseg
  rw [Projectivization.mk_eq_mk_iff] at hseg
  obtain ⟨c, hc⟩ := hseg
  symm
  apply projectivization_eq_of_raw_minors hy
  intro a b
  have ha := congrFun hc (none, a)
  have hb := congrFun hc (none, b)
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, segreVector, homVec_none,
    one_mul] at ha hb
  apply mul_left_cancel₀ hPn
  change (blowupFirst R).1.rep none * (y a * (blowupSecond R).rep b) =
    (blowupFirst R).1.rep none * (y b * (blowupSecond R).rep a)
  linear_combination y b * ha - y a * hb

/-- Every point of the blow-up is `(x, [y])` with `x` its projection and `[y]`
its direction. -/
theorem eq_blowupPt (R : blowupSet (k := k) (σ := PlaneIndex.{u})) :
    R.1 = blowupPt (proj R) (blowupSecond R).rep (blowupSecond R).rep_nonzero := by
  have hseg : segreMap (blowupFirst R).1 (blowupSecond R) = R.1 :=
    segreMap_fst_snd (blowupAsAmbient R)
  have hPn : (blowupFirst R).1.rep none ≠ 0 :=
    rep_ne_zero_of_mem_standardChart (blowupFirst R).2
  rw [← hseg]
  unfold segreMap blowupPt
  rw [Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 _ hPn, ?_⟩
  funext p
  rcases p with ⟨_ | i, b⟩
  · simp [segreVector]
  · simp only [segreVector, Pi.smul_apply, Units.smul_def, smul_eq_mul, Units.val_mk0,
      homVec_some]
    rw [proj_apply_eq]
    field_simp

/-- The incidence relation between the projection and the direction. -/
theorem proj_incidence (R : blowupSet (k := k) (σ := PlaneIndex.{u})) (a b : PlaneIndex.{u}) :
    proj R a * (blowupSecond R).rep b = proj R b * (blowupSecond R).rep a := by
  have h := blowup_chart_incidence_flat R a b
  rw [proj_apply_eq, proj_apply_eq]
  exact h

end Projection

/-! ## The blow-up charts -/

/-- The point `(t • w(u), [w(u)])` of the `j`-th chart. -/
noncomputable def chartPt (j : Fin 2) (t u : k) :
    ProjectiveSpace k (Option PlaneIndex.{u} × PlaneIndex.{u}) :=
  blowupPt (t • planeChartVec j u) (planeChartVec j u) (planeChartVec_ne_zero j u)

theorem chartPt_mem (j : Fin 2) (t u : k) :
    chartPt.{u} j t u ∈ blowupSet (k := k) (σ := PlaneIndex.{u}) := by
  apply blowupPt_mem
  intro i i'
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The `j`-th chart of `ℙ(Option × PlaneIndex)` used for the blow-up chart. -/
abbrev chartIndex (j : Fin 2) : Option PlaneIndex.{u} × PlaneIndex.{u} := (none, ⟨j⟩)

theorem chartPt_mem_standardChart (j : Fin 2) (t u : k) :
    chartPt.{u} j t u ∈ standardChart (chartIndex.{u} j) := by
  rw [mem_standardChart_iff]
  obtain ⟨a, ha⟩ := exists_rep_blowupPt (t • planeChartVec.{u} j u) (planeChartVec j u)
    (planeChartVec_ne_zero j u)
  rw [chartPt, ha]
  simp [segreVector, Units.ne_zero, Units.smul_def]

theorem some_ne_chartIndex (j : Fin 2) :
    ((some ⟨j⟩, ⟨j⟩) : Option PlaneIndex.{u} × PlaneIndex.{u}) ≠ chartIndex.{u} j := by
  simp [chartIndex]

theorem none_rev_ne_chartIndex (j : Fin 2) :
    ((none, ⟨j.rev⟩) : Option PlaneIndex.{u} × PlaneIndex.{u}) ≠ chartIndex.{u} j := by
  simp [chartIndex, fin_two_rev_ne j]

/-- The polynomial coordinates of the chart point, as polynomials in
`(t, u) = (X 0, X 1)`. -/
noncomputable def chartSegrePoly (j : Fin 2) :
    Option PlaneIndex.{u} × PlaneIndex.{u} → MvPolynomial (Fin 2) k :=
  fun p => (p.1.elim 1 fun i => X 0 * chartPoly j i.down) * chartPoly j p.2.down

theorem eval_chartSegrePoly (j : Fin 2) (v : Fin 2 → k)
    (p : Option PlaneIndex.{u} × PlaneIndex.{u}) :
    eval v (chartSegrePoly j p) =
      segreVector (homVec (v 0 • planeChartVec j (v 1))) (planeChartVec j (v 1)) p := by
  rcases p with ⟨_ | i, b⟩ <;>
    simp [chartSegrePoly, segreVector, eval_chartPoly, planeChartVec]

theorem chartMap_chartPt (j : Fin 2) (t u : k) (p : {p // p ≠ chartIndex.{u} j}) :
    chartMap (chartIndex j) (chartPt j t u) p =
      segreVector (homVec (t • planeChartVec j u)) (planeChartVec j u) p.1 := by
  rw [chartPt, blowupPt, chartMap_mk]
  simp [segreVector]

theorem chartMap_chartPt_some (j : Fin 2) (t u : k) :
    chartMap (chartIndex j) (chartPt.{u} j t u) ⟨(some ⟨j⟩, ⟨j⟩), some_ne_chartIndex j⟩ = t := by
  rw [chartMap_chartPt]
  simp [segreVector]

theorem chartMap_chartPt_none (j : Fin 2) (t u : k) :
    chartMap (chartIndex j) (chartPt.{u} j t u) ⟨(none, ⟨j.rev⟩), none_rev_ne_chartIndex j⟩ =
      u := by
  rw [chartMap_chartPt]
  simp [segreVector]

section ChartProjection

variable [IsAlgClosed k]

theorem proj_chartPt (j : Fin 2) (t u : k) :
    proj ⟨chartPt.{u} j t u, chartPt_mem j t u⟩ = t • planeChartVec j u :=
  proj_blowupPt _ _ _ _

omit [IsAlgClosed k] in
theorem second_chartPt (j : Fin 2) (t u : k) :
    blowupSecond ⟨chartPt.{u} j t u, chartPt_mem j t u⟩ =
      Projectivization.mk k (planeChartVec j u) (planeChartVec_ne_zero j u) :=
  second_blowupPt _ _ _ _

/-- A point of the blow-up whose direction has nonzero `j`-th coordinate lies on
the `j`-th chart. -/
theorem eq_chartPt (R : blowupSet (k := k) (σ := PlaneIndex.{u})) {j : Fin 2}
    (hj : (blowupSecond R).rep ⟨j⟩ ≠ 0) :
    R.1 = chartPt j (proj R ⟨j⟩)
      ((blowupSecond R).rep ⟨j.rev⟩ / (blowupSecond R).rep ⟨j⟩) := by
  set x := proj R with hxdef
  set y := (blowupSecond R).rep with hydef
  rw [eq_blowupPt R, chartPt]
  have hyw : y = y ⟨j⟩ • planeChartVec j (y ⟨j.rev⟩ / y ⟨j⟩) := eq_smul_planeChartVec y hj
  rw [blowupPt_eq_of_smul x (blowupSecond R).rep_nonzero (planeChartVec_ne_zero j _) hj hyw]
  have hx : x = x ⟨j⟩ • planeChartVec j (y ⟨j.rev⟩ / y ⟨j⟩) := by
    funext i
    rcases i with ⟨i⟩
    rcases fin_two_eq_or_eq_rev i j with rfl | rfl
    · simp
    · simp only [Pi.smul_apply, smul_eq_mul, planeChartVec_rev]
      have hinc := proj_incidence R ⟨j.rev⟩ ⟨j⟩
      rw [← hxdef, ← hydef] at hinc
      field_simp
      linear_combination hinc
  rw [← hx]

/-- A point of the blow-up in the `j`-th chart is the chart point with the
corresponding chart coordinates. -/
theorem eq_chartPt_chartMap (R : blowupSet (k := k) (σ := PlaneIndex.{u})) {j : Fin 2}
    (hR : R.1 ∈ standardChart (chartIndex.{u} j)) :
    R.1 = chartPt j
      (chartMap (chartIndex j) R.1 ⟨(some ⟨j⟩, ⟨j⟩), some_ne_chartIndex j⟩)
      (chartMap (chartIndex j) R.1 ⟨(none, ⟨j.rev⟩), none_rev_ne_chartIndex j⟩) := by
  have hj : (blowupSecond R).rep ⟨j⟩ ≠ 0 := by
    have hc := rep_ne_zero_of_mem_standardChart hR
    obtain ⟨a, hrep⟩ := rep_eq_smul_segreVector R
    rw [hrep] at hc
    intro h
    apply hc
    simp [segreVector, chartIndex, h]
  have h := eq_chartPt R hj
  conv_lhs => rw [h]
  rw [h, chartMap_chartPt_some, chartMap_chartPt_none]

end ChartProjection

/-! ## A homogeneous test polynomial -/

section Test

variable (j : Fin 2) (g : MvPolynomial (Fin 2) k)

/-- A homogeneous polynomial in the Segre coordinates which, on the `j`-th chart,
restricts to the chart equation `g̃ⱼ`. -/
noncomputable def chartTestPoly : MvPolynomial (Option PlaneIndex.{u} × PlaneIndex.{u}) k :=
  ∑ d ∈ Finset.Ico 2 (g.totalDegree + 1),
    rename (fun b : Fin 2 => ((none : Option PlaneIndex.{u}), (⟨b⟩ : PlaneIndex.{u})))
        (homogeneousComponent d g) *
      X ((some ⟨j⟩ : Option PlaneIndex.{u}), (⟨j⟩ : PlaneIndex.{u})) ^ (d - 2) *
      X ((none : Option PlaneIndex.{u}), (⟨j⟩ : PlaneIndex.{u})) ^
        (2 * g.totalDegree + 2 - 2 * d)

theorem chartTestPoly_isHomogeneous :
    (chartTestPoly.{u} j g).IsHomogeneous (2 * g.totalDegree) := by
  apply IsHomogeneous.sum
  intro d hd
  have hd' := Finset.mem_Ico.1 hd
  have h := (((homogeneousComponent_isHomogeneous d g).rename_isHomogeneous
      (f := fun b : Fin 2 => ((none : Option PlaneIndex.{u}), (⟨b⟩ : PlaneIndex.{u})))).mul
    ((isHomogeneous_X k ((some ⟨j⟩ : Option PlaneIndex.{u}), (⟨j⟩ : PlaneIndex.{u}))).pow
      (d - 2))).mul
    ((isHomogeneous_X k ((none : Option PlaneIndex.{u}), (⟨j⟩ : PlaneIndex.{u}))).pow
      (2 * g.totalDegree + 2 - 2 * d))
  convert h using 1
  omega

theorem eval_chartTestPoly (x y : PlaneIndex.{u} → k) :
    eval (segreVector (homVec x) y) (chartTestPoly j g) =
      ∑ d ∈ Finset.Ico 2 (g.totalDegree + 1),
        eval (lowerVec y) (homogeneousComponent d g) * (x ⟨j⟩ * y ⟨j⟩) ^ (d - 2) *
          y ⟨j⟩ ^ (2 * g.totalDegree + 2 - 2 * d) := by
  simp only [chartTestPoly, map_sum, map_mul, map_pow, eval_X, eval_rename]
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 3
  · congr 1
    funext b
    simp [segreVector]
  · simp [segreVector]

theorem eval_chartTestPoly_self (hg0 : homogeneousComponent 0 g = 0)
    (hg1 : homogeneousComponent 1 g = 0) (x : PlaneIndex.{u} → k) :
    eval (segreVector (homVec x) x) (chartTestPoly j g) =
      x ⟨j⟩ ^ (2 * g.totalDegree - 2) * eval (lowerVec x) g := by
  rw [eval_chartTestPoly, eval_eq_sum_Ico g hg0 hg1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := Finset.mem_Ico.1 hd
  have hexp : 2 * (d - 2) + (2 * g.totalDegree + 2 - 2 * d) = 2 * g.totalDegree - 2 := by
    omega
  rw [← hexp, pow_add, pow_mul, ← sq]
  ring

theorem eval_chartTestPoly_chartPt (t u : k) :
    eval (segreVector (homVec (t • planeChartVec j u)) (planeChartVec j u))
        (chartTestPoly.{u} j g) =
      eval ![t, u] (chartEq j g) := by
  rw [eval_chartTestPoly, eval_chartEq]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, planeChartVec_self, mul_one, one_pow,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    lowerVec_planeChartVec]
  ring

end Test

/-! ## The strict transform in the charts -/

section StrictTransform

variable [IsAlgClosed k]

/-- The curve `g = 0` in the plane. -/
abbrev planeZeroSet (g : MvPolynomial (Fin 2) k) : Set (PlaneIndex.{u} → k) :=
  zeroSet {rename ULift.up g}

omit [IsAlgClosed k] in
theorem mem_planeZeroSet_iff (g : MvPolynomial (Fin 2) k) (x : PlaneIndex.{u} → k) :
    x ∈ planeZeroSet g ↔ eval (lowerVec x) g = 0 := by
  simp [planeZeroSet, eval_rename_up]

/-- The inverse image of `Y \ {0}` consists of the points `(x, [x])`. -/
theorem strictTransformOrdinary_eq (Y : Set (PlaneIndex.{u} → k))
    (R : blowupSet (k := k) (σ := PlaneIndex.{u}))
    (hR : R ∈ strictTransformOrdinary (k := k) Y) :
    ∃ (x : PlaneIndex.{u} → k) (hx : x ≠ 0), x ∈ Y ∧ R.1 = blowupPt x x hx := by
  refine ⟨proj R, hR.2, hR.1, ?_⟩
  have hinv := blowupInversePoint_projection (planeBlowupQ (k := k)) R hR.2
  have hsec : blowupSecond R = Projectivization.mk k (proj R) hR.2 := by
    rw [← blowupSecond_inversePoint (proj R) hR.2]
    exact congrArg blowupSecond hinv.symm
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k (proj R) hR.2
  rw [eq_blowupPt R]
  apply blowupPt_eq_of_smul (proj R) _ _ (Units.ne_zero a)
  rw [hsec, ← ha]
  rfl

variable (g : MvPolynomial (Fin 2) k)

theorem homogeneousVanish_chartTestPoly
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0) (j : Fin 2)
    {R : ProjectiveSpace k (Option PlaneIndex.{u} × PlaneIndex.{u})}
    (hR : R ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g)) :
    HomogeneousVanish (chartTestPoly j g) R := by
  have hclosed : IsClosed (projZeroSet ({chartTestPoly j g} :
      Set (MvPolynomial (Option PlaneIndex.{u} × PlaneIndex.{u}) k))) := by
    apply isClosed_iff_isProjAlgebraicSet.2
    refine ⟨{chartTestPoly j g}, ?_, rfl⟩
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    exact ⟨_, hf ▸ chartTestPoly_isHomogeneous j g⟩
  have hsub : ((↑) '' strictTransformOrdinary (k := k) (planeZeroSet g) :
      Set (ProjectiveSpace k (Option PlaneIndex.{u} × PlaneIndex.{u}))) ⊆
      projZeroSet {chartTestPoly j g} := by
    rintro _ ⟨R, hR, rfl⟩
    obtain ⟨x, hx, hxY, hRx⟩ := strictTransformOrdinary_eq _ R hR
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    rw [hRx, homogeneousVanish_blowupPt_iff (chartTestPoly_isHomogeneous j g),
      eval_chartTestPoly_self j g hg0 hg1, (mem_planeZeroSet_iff g x).1 hxY, mul_zero]
  exact closure_minimal hsub hclosed hR.2 _ rfl

/-- On the `j`-th chart, the strict transform lies in `g̃ⱼ = 0`. -/
theorem eval_chartEq_of_mem
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (j : Fin 2) (t u : k)
    (h : chartPt.{u} j t u ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g)) :
    eval ![t, u] (chartEq j g) = 0 := by
  have hv := homogeneousVanish_chartTestPoly g hg0 hg1 j h
  rw [chartPt, homogeneousVanish_blowupPt_iff (chartTestPoly_isHomogeneous j g),
    eval_chartTestPoly_chartPt] at hv
  exact hv

theorem chartPt_mem_ordinary
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (j : Fin 2) {t u : k} (ht : t ≠ 0) (h : eval ![t, u] (chartEq j g) = 0) :
    (⟨chartPt.{u} j t u, chartPt_mem j t u⟩ : blowupSet (k := k) (σ := PlaneIndex.{u})) ∈
      strictTransformOrdinary (k := k) (planeZeroSet g) := by
  have hproj := proj_chartPt (k := k) j t u
  refine ⟨?_, ?_⟩
  · change proj _ ∈ _
    rw [hproj, mem_planeZeroSet_iff]
    have := eval_smul_chartVec j g hg0 hg1 ![t, u]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
    rw [lowerVec_smul, lowerVec_planeChartVec, this, h, mul_zero]
  · change proj _ ≠ 0
    rw [hproj]
    intro h0
    have := congrFun h0 ⟨j⟩
    simp [ht] at this

theorem chartPt_zero_mem_closure (hg : Irreducible g)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (hg2 : homogeneousComponent 2 g ≠ 0)
    (j : Fin 2) {u : k} (h : eval ![0, u] (chartEq j g) = 0) :
    chartPt.{u} j 0 u ∈ closure ((↑) '' strictTransformOrdinary (k := k) (planeZeroSet g) :
      Set (ProjectiveSpace k (Option PlaneIndex.{u} × PlaneIndex.{u}))) := by
  set S : Set (ProjectiveSpace k (Option PlaneIndex.{u} × PlaneIndex.{u})) :=
    (↑) '' strictTransformOrdinary (k := k) (planeZeroSet g)
  obtain ⟨T, hT, hTeq⟩ := isClosed_iff_isProjAlgebraicSet.1 (isClosed_closure (s := S))
  rw [hTeq]
  by_contra hnot
  simp only [projZeroSet, Set.mem_ofPred_eq, not_forall] at hnot
  obtain ⟨F, hF, hFR⟩ := hnot
  obtain ⟨e, hFe⟩ := hT F hF
  set E := chartEq j g
  have hEirr : Irreducible E := irreducible_chartEq j hg hg0 hg1 hg2
  have hEprime : Prime E := UniqueFactorizationMonoid.irreducible_iff_prime.1 hEirr
  let φ : MvPolynomial (Fin 2) k := aeval (chartSegrePoly j) F
  have hφ : ∀ v : Fin 2 → k, eval v φ =
      eval (segreVector (homVec (v 0 • planeChartVec j (v 1))) (planeChartVec j (v 1))) F := by
    intro v
    simp only [φ, eval_aeval_eq, eval_chartSegrePoly]
  have hvan : ∀ v ∈ zeroLocus k (Ideal.span {E}), eval v (X 0 * φ) = 0 := by
    intro v hv
    have hvE : eval v E = 0 := hv E (Ideal.subset_span rfl)
    rw [map_mul, eval_X]
    by_cases h0 : v 0 = 0
    · rw [h0, zero_mul]
    · have hv' : v = ![v 0, v 1] := by
        funext i
        fin_cases i <;> rfl
      have hmem := chartPt_mem_ordinary g hg0 hg1 j h0 (u := v 1) (by rw [← hv']; exact hvE)
      have hS : chartPt j (v 0) (v 1) ∈ projZeroSet T := by
        rw [← hTeq]
        exact subset_closure ⟨_, hmem, rfl⟩
      have := hS F hF
      rw [chartPt, homogeneousVanish_blowupPt_iff hFe] at this
      rw [hφ, this, mul_zero]
  obtain ⟨r, -, hr⟩ := exists_pow_mem_of_forall_eval_eq_zero hvan
  rw [Ideal.mem_span_singleton] at hr
  rcases hEprime.dvd_or_dvd (hEprime.dvd_of_dvd_pow hr) with hX | hφE
  · have hassoc := (hEirr.dvd_irreducible_iff_associated
      (X_prime (σ := Fin 2) (R := k) (i := 0)).irreducible).1 hX
    exact not_X_zero_dvd_chartEq j g hg2 hassoc.symm.dvd
  · obtain ⟨c, hc⟩ := hφE
    have := congrArg (eval ![0, u]) hc
    rw [map_mul, h, zero_mul, hφ] at this
    apply hFR
    rw [chartPt, homogeneousVanish_blowupPt_iff hFe]
    simpa using this

/-- **The strict transform in the `j`-th chart is `g̃ⱼ = 0`.** -/
theorem chartPt_mem_strictTransform_iff (hg : Irreducible g)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (hg2 : homogeneousComponent 2 g ≠ 0) (j : Fin 2) (t u : k) :
    chartPt.{u} j t u ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ↔
      eval ![t, u] (chartEq j g) = 0 := by
  refine ⟨eval_chartEq_of_mem g hg0 hg1 j t u, fun h => ?_⟩
  refine ⟨chartPt_mem j t u, ?_⟩
  by_cases ht : t = 0
  · subst ht
    exact chartPt_zero_mem_closure g hg hg0 hg1 hg2 j h
  · exact subset_closure ⟨_, chartPt_mem_ordinary g hg0 hg1 j ht h, rfl⟩

/-! ## The fibre over the origin -/

/-- A point of the strict transform over the origin has a direction on the
tangent cone `g₂ = 0`. -/
theorem eval_second_of_mem_fibre
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (R : blowupSet (k := k) (σ := PlaneIndex.{u}))
    (hR : R.1 ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g))
    (h0 : proj R = 0) :
    eval (lowerVec (blowupSecond R).rep) (homogeneousComponent 2 g) = 0 := by
  obtain ⟨⟨j⟩, hj⟩ := Function.ne_iff.1 (blowupSecond R).rep_nonzero
  have hRj := eq_chartPt R hj
  rw [h0] at hRj
  simp only [Pi.zero_apply] at hRj
  rw [hRj] at hR
  have hE := eval_chartEq_of_mem g hg0 hg1 j _ _ hR
  rw [eval_chartEq_of_eq_zero j g _ (by simp)] at hE
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at hE
  rw [eq_smul_planeChartVec (blowupSecond R).rep hj, lowerVec_smul,
    (homogeneousComponent_isHomogeneous 2 g).eval_smul, lowerVec_planeChartVec, hE, mul_zero]

/-- Every direction on the tangent cone gives a point of the strict transform
over the origin. -/
theorem blowupPt_zero_mem (hg : Irreducible g)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (hg2 : homogeneousComponent 2 g ≠ 0) {y : PlaneIndex.{u} → k} (hy : y ≠ 0)
    (hy2 : eval (lowerVec y) (homogeneousComponent 2 g) = 0) :
    blowupPt 0 y hy ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) := by
  obtain ⟨⟨j⟩, hj⟩ := Function.ne_iff.1 hy
  have hyw := eq_smul_planeChartVec y hj
  rw [blowupPt_eq_of_smul 0 hy (planeChartVec_ne_zero j _) hj hyw]
  have : blowupPt 0 (planeChartVec j (y ⟨j.rev⟩ / y ⟨j⟩)) (planeChartVec_ne_zero j _) =
      chartPt j 0 (y ⟨j.rev⟩ / y ⟨j⟩) := by
    rw [chartPt, zero_smul]
  rw [this, chartPt_mem_strictTransform_iff g hg hg0 hg1 hg2,
    eval_chartEq_of_eq_zero j g _ (by simp)]
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hyw, lowerVec_smul, (homogeneousComponent_isHomogeneous 2 g).eval_smul,
    lowerVec_planeChartVec] at hy2
  exact (mul_eq_zero.1 hy2).resolve_left (pow_ne_zero _ hj)

end StrictTransform

end OrdinaryNode

end Hartshorne
