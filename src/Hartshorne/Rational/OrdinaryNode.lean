/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.OrdinaryNodeBlowup
import Hartshorne.Nonsingular.HypersurfaceSingularLocus
import Hartshorne.Nonsingular.IntrinsicNonsingular
import Hartshorne.Morphism.ChartIso
import Hartshorne.Morphism.OpenSubvariety

/-!
# Ordinary nodes and their two branches

Hartshorne, *Algebraic Geometry*, I, Exercise 5.6(b) (p. 37).

Let `Y = Z(f) ⊆ 𝔸²` be a plane curve and `P ∈ 𝔸²`.  Write `g(x) = f(P + x)` for
the local equation of `Y` at `P` and `g = g₀ + g₁ + g₂ + ⋯` for its decomposition
into homogeneous components.  The point `P` has multiplicity two when
`g₀ = g₁ = 0 ≠ g₂`, and it is an *ordinary node* when moreover the quadratic
initial form `g₂` is the product of two non-associated linear forms; their zero
lines are the two tangent directions.

Blowing up at `P` means blowing up the plane at the origin after the
translation moving `P` to the origin, and taking the strict transform of the
translated curve.

## Main definitions

* `Hartshorne.planeLocalEquation f P`: the local equation `f(P + x)`.
* `Hartshorne.IsPlaneDoublePoint f P`: `P` has multiplicity two on `f = 0`.
* `Hartshorne.IsOrdinaryNode f P`: `P` is an ordinary node of `f = 0`.

## Main results

* `Hartshorne.ordinaryNode_blowup`: blowing up an ordinary node of an
  irreducible plane curve gives exactly two points over the node, one on each
  tangent direction, and both are nonsingular points of the blown-up curve.
* `Hartshorne.isOrdinaryNode_of_two_blowup_points`: conversely, a double point
  over which the blown-up curve has two distinct points is an ordinary node.

## Implementation notes

The blow-up of the plane is the incidence construction of
`Hartshorne.Rational.BlowingUp`, whose coordinate type must live in the universe
of `k`; the plane is therefore indexed by `ULift (Fin 2)`, and polynomials in
`Fin 2` variables are read on it through `lowerVec`.  Nonsingularity of the two
points is proved on the blow-up chart containing each of them: the chart piece of
the strict transform is isomorphic to the plane curve `g̃ⱼ = 0`, whose partial
derivative in the chart coordinate along the exceptional curve does not vanish at
a simple root of the initial form.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace OrdinaryNode
open scoped Hartshorne

universe u

variable {k : Type u} [Field k]

/-! ## Definitions -/

/-- The local equation `f(P + x)` of the plane curve `f = 0` at `P`. -/
noncomputable def planeLocalEquation (f : MvPolynomial (Fin 2) k) (P : Fin 2 → k) :
    MvPolynomial (Fin 2) k :=
  aeval (fun i => X i + C (P i)) f

/-- `P` is a point of multiplicity two of the plane curve `f = 0`: the local
equation at `P` has no constant and no linear term, and a nonzero quadratic
term. -/
def IsPlaneDoublePoint (f : MvPolynomial (Fin 2) k) (P : Fin 2 → k) : Prop :=
  homogeneousComponent 0 (planeLocalEquation f P) = 0 ∧
    homogeneousComponent 1 (planeLocalEquation f P) = 0 ∧
    homogeneousComponent 2 (planeLocalEquation f P) ≠ 0

/-- **Ordinary node** (Hartshorne I, Exercise 5.6(b)).  `P` is an ordinary node
of the plane curve `f = 0` when it has multiplicity two and the quadratic initial
form of the local equation at `P` is the product of two distinct (non-associated)
linear forms, the two tangent directions. -/
def IsOrdinaryNode (f : MvPolynomial (Fin 2) k) (P : Fin 2 → k) : Prop :=
  IsPlaneDoublePoint f P ∧
    ∃ l₁ l₂ : MvPolynomial (Fin 2) k, l₁.IsHomogeneous 1 ∧ l₂.IsHomogeneous 1 ∧
      ¬ Associated l₁ l₂ ∧ homogeneousComponent 2 (planeLocalEquation f P) = l₁ * l₂

/-- The plane curve `f = 0` moved by the translation taking `P` to the origin,
as a subset of the affine plane of the blow-up. -/
def translatedPlaneCurve (f : MvPolynomial (Fin 2) k) (P : Fin 2 → k) :
    Set (PlaneIndex.{u} → k) :=
  {x | lowerVec x + P ∈ zeroSet ({f} : Set (MvPolynomial (Fin 2) k))}

namespace OrdinaryNode

theorem translatedPlaneCurve_eq (f : MvPolynomial (Fin 2) k) (P : Fin 2 → k) :
    translatedPlaneCurve.{u} f P = planeZeroSet (planeLocalEquation f P) := by
  ext x
  rw [mem_planeZeroSet_iff, planeLocalEquation, eval_aeval_eq]
  have h : (fun i => eval (lowerVec x) (X i + C (P i))) = lowerVec x + P := by
    funext i
    simp
  rw [h]
  simp [translatedPlaneCurve]

/-- Translation is an automorphism of the polynomial ring. -/
noncomputable def translateEquiv (P : Fin 2 → k) :
    MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
  AlgEquiv.ofAlgHom (aeval fun i => X i + C (P i)) (aeval fun i => X i - C (P i))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simp)

theorem irreducible_planeLocalEquation {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    (P : Fin 2 → k) : Irreducible (planeLocalEquation f P) :=
  hf.map (translateEquiv P)

theorem irreducible_rename_up {g : MvPolynomial (Fin 2) k} (hg : Irreducible g) :
    Irreducible (rename (ULift.up : Fin 2 → PlaneIndex.{u}) g) :=
  hg.map (renameEquiv k (Equiv.ulift.{u, 0}.symm : Fin 2 ≃ PlaneIndex.{u}))

theorem isGlobalRegular_eval {ι : Type*} {Y : Set (ι → k)}
    (hY : IsQuasiAffineVariety Y) (q : MvPolynomial ι k) :
    (Variety.ofQuasiAffine hY).IsGlobalRegular (fun y => eval y.1 q) := by
  intro _
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, q, 1, by simp, by simp⟩

/-- Nonsingularity at a point of an open quasi-projective subset. -/
theorem nonsingularAt_iff_of_open_subset {σ : Type*} {Y Z : Set (ProjectiveSpace k σ)}
    (hY : IsQuasiProjVariety Y) (hZ : IsQuasiProjVariety Z) (hZY : Z ⊆ Y)
    (hopen : IsOpen {y : Y | y.1 ∈ Z}) (P : (Variety.ofQuasiProjective hZ).carrier) :
    Variety.NonsingularAt (Variety.ofQuasiProjective hY) (inclHom hY hZ hZY P) ↔
      Variety.NonsingularAt (Variety.ofQuasiProjective hZ) P :=
  isRegularLocalRing_iff_of_ringEquiv
    (RingEquiv.ofBijective _ (bijective_localRingHom_inclHom hY hZ hZY hopen P))

/-! ## Nonsingularity on a chart -/

section Nonsingular

variable [IsAlgClosed k]

theorem vanishingIdeal_zeroSet_singleton {E : MvPolynomial (Fin 2) k} (hE : Irreducible E) :
    vanishingIdeal k (zeroSet ({E} : Set (MvPolynomial (Fin 2) k))) = Ideal.span {E} := by
  have hprime : (Ideal.span {E}).IsPrime :=
    (Ideal.span_singleton_prime hE.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.1 hE)
  have hspan : zeroSet ({E} : Set (MvPolynomial (Fin 2) k)) =
      zeroSet ((Ideal.span {E} : Ideal (MvPolynomial (Fin 2) k)) : Set _) := by
    rw [zeroSet_eq_zeroLocus_span, zeroLocus_eq_zeroSet]
  rw [hspan, vanishingIdeal_zeroSet_eq_radical, hprime.radical]

/-- A point of an irreducible plane curve where some partial derivative of the
equation is nonzero is an affine nonsingular point. -/
theorem isAffineNonsingularAt_of_pderiv {E : MvPolynomial (Fin 2) k} (hE : Irreducible E)
    (P : zeroSet ({E} : Set (MvPolynomial (Fin 2) k))) {i : Fin 2}
    (hi : eval (P : Fin 2 → k) (pderiv i E) ≠ 0) :
    IsAffineNonsingularAt (zeroSet ({E} : Set (MvPolynomial (Fin 2) k))) P := by
  obtain ⟨r, hcard, hdim⟩ := exists_dim_zeroSet_irreducible hE
  rw [isAffineNonsingularAt_iff_of_dim_eq P hdim]
  have hvi : Ideal.span (Set.range (fun _ : Fin 1 => E)) =
      vanishingIdeal k (zeroSet ({E} : Set (MvPolynomial (Fin 2) k))) := by
    rw [vanishingIdeal_zeroSet_singleton hE]
    congr 1
    ext q
    simp
  rw [← jacobianMatrix_rank_eq_jacobianRank P (fun _ : Fin 1 => E) hvi]
  set A := jacobianMatrix (P : Fin 2 → k) (fun _ : Fin 1 => E)
  have hrow : A 0 ≠ 0 := by
    intro h
    apply hi
    have := congrFun h i
    simpa [A, jacobianMatrix] using this
  have hrank : A.rank = 1 := by
    rw [Matrix.rank_eq_finrank_span_row]
    have hrange : Set.range A.row = {A 0} := by
      ext v
      constructor
      · rintro ⟨l, rfl⟩
        rw [Subsingleton.elim l 0]
        rfl
      · rintro rfl
        exact ⟨0, rfl⟩
    rw [hrange, finrank_span_singleton hrow]
  rw [hrank]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

variable (g : MvPolynomial (Fin 2) k) (hg : Irreducible g)
  (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
  (hg2 : homogeneousComponent 2 g ≠ 0)

/-- The irreducible chart curve `g̃ⱼ = 0`. -/
abbrev chartCurve (j : Fin 2) : Set (Fin 2 → k) := zeroSet {chartEq j g}

include hg hg0 hg1 hg2 in
theorem isAffineVariety_chartCurve (j : Fin 2) : IsAffineVariety (chartCurve g j) :=
  isAffineVariety_zeroSet_singleton_of_irreducible (irreducible_chartEq j hg hg0 hg1 hg2)

variable (hY : IsAffineVariety (planeZeroSet.{u} g))
  (hne : (affineSubvarietyPunctured (planeZeroSet.{u} g)).Nonempty)

/-- The strict transform as a quasi-projective variety. -/
abbrev strictQ (hY : IsAffineVariety (planeZeroSet.{u} g))
    (hne : (affineSubvarietyPunctured (planeZeroSet.{u} g)).Nonempty) :
    IsQuasiProjVariety (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g)) :=
  isQuasiProjVariety_strictTransform hY hne

include hg0 hg1 in
/-- The chart coordinates of a point of the chart piece of the strict transform
lie on the chart curve. -/
theorem chartTarget_mem_chartCurve (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty)
    (c : (chartTarget k (chartIndex j) (strictQ g hY hne) hneC).carrier) :
    ![c.1 ⟨(some ⟨j⟩, ⟨j⟩), some_ne_chartIndex j⟩,
        c.1 ⟨(none, ⟨j.rev⟩), none_rev_ne_chartIndex j⟩] ∈ chartCurve g j ∧
      chartPt j (c.1 ⟨(some ⟨j⟩, ⟨j⟩), some_ne_chartIndex j⟩)
          (c.1 ⟨(none, ⟨j.rev⟩), none_rev_ne_chartIndex j⟩) =
        (Classical.choose c.2) := by
  obtain ⟨⟨hRY, hRc⟩, hRc'⟩ := Classical.choose_spec c.2
  set R := Classical.choose c.2
  have hR := eq_chartPt_chartMap ⟨R, strictTransform_subset_blowup _ hRY⟩ hRc
  simp only at hR
  rw [hRc'] at hR
  refine ⟨?_, hR.symm⟩
  intro f hf
  rw [Set.mem_singleton_iff] at hf
  subst hf
  rw [hR] at hRY
  exact eval_chartEq_of_mem g hg0 hg1 j _ _ hRY

/-- The chart coordinates of the chart piece of the strict transform, landing on
the chart curve. -/
noncomputable def chartToCurveFun (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty) :
    (chartTarget k (chartIndex j) (strictQ g hY hne) hneC).carrier →
      (Variety.ofQuasiAffine
        (isAffineVariety_chartCurve g hg hg0 hg1 hg2 j).isQuasiAffineVariety).carrier :=
  fun c => ⟨_, (chartTarget_mem_chartCurve g hg0 hg1 hY hne j hneC c).1⟩

/-- The chart point of a point of the chart curve. -/
noncomputable def curveToChartFun (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty) :
    (Variety.ofQuasiAffine
        (isAffineVariety_chartCurve g hg hg0 hg1 hg2 j).isQuasiAffineVariety).carrier →
      (chartTarget k (chartIndex j) (strictQ g hY hne) hneC).carrier :=
  fun v => ⟨chartMap (chartIndex j) (chartPt j (v.1 0) (v.1 1)), chartPt j (v.1 0) (v.1 1),
    ⟨(chartPt_mem_strictTransform_iff g hg hg0 hg1 hg2 j _ _).2 (by
        have h := v.2 _ rfl
        rwa [show (v.1 : Fin 2 → k) = ![v.1 0, v.1 1] from
          fin_two_vec_ext rfl rfl] at h),
      chartPt_mem_standardChart j _ _⟩, rfl⟩

theorem exists_chartToCurveHom (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty) :
    ∃ ρ : VarietyHom (chartTarget k (chartIndex j) (strictQ g hY hne) hneC)
      (Variety.ofQuasiAffine
        (isAffineVariety_chartCurve g hg hg0 hg1 hg2 j).isQuasiAffineVariety),
      ρ.toFun = chartToCurveFun g hg hg0 hg1 hg2 hY hne j hneC := by
  apply (exists_varietyHom_iff_coords_regular _ _).2
  intro i
  fin_cases i
  · exact affineCoordinate_isGlobalRegular_on
      (isQuasiAffineVariety_chartMap_image (chartIndex j) (strictQ g hY hne) hneC)
      ⟨(some ⟨j⟩, ⟨j⟩), some_ne_chartIndex j⟩
  · exact affineCoordinate_isGlobalRegular_on
      (isQuasiAffineVariety_chartMap_image (chartIndex j) (strictQ g hY hne) hneC)
      ⟨(none, ⟨j.rev⟩), none_rev_ne_chartIndex j⟩

theorem exists_curveToChartHom (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty) :
    ∃ ρ : VarietyHom
      (Variety.ofQuasiAffine
        (isAffineVariety_chartCurve g hg hg0 hg1 hg2 j).isQuasiAffineVariety)
      (chartTarget k (chartIndex j) (strictQ g hY hne) hneC),
      ρ.toFun = curveToChartFun g hg hg0 hg1 hg2 hY hne j hneC := by
  apply (exists_varietyHom_iff_coords_regular _ _).2
  intro p
  have h : (fun v => (curveToChartFun g hg hg0 hg1 hg2 hY hne j hneC v).1 p) =
      fun v => eval v.1 (chartSegrePoly j p.1) := by
    funext v
    change chartMap (chartIndex j) (chartPt j (v.1 0) (v.1 1)) p = _
    rw [chartMap_chartPt, eval_chartSegrePoly]
  rw [h]
  exact isGlobalRegular_eval _ _

/-- The chart coordinates, as a morphism to the chart curve. -/
noncomputable def chartToCurveHom (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty) :
    VarietyHom (chartTarget k (chartIndex j) (strictQ g hY hne) hneC)
      (Variety.ofQuasiAffine
        (isAffineVariety_chartCurve g hg hg0 hg1 hg2 j).isQuasiAffineVariety) :=
  Classical.choose (exists_chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC)

/-- The chart point, as a morphism from the chart curve. -/
noncomputable def curveToChartHom (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty) :
    VarietyHom
      (Variety.ofQuasiAffine
        (isAffineVariety_chartCurve g hg hg0 hg1 hg2 j).isQuasiAffineVariety)
      (chartTarget k (chartIndex j) (strictQ g hY hne) hneC) :=
  Classical.choose (exists_curveToChartHom g hg hg0 hg1 hg2 hY hne j hneC)

theorem chartToCurveHom_apply (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty)
    (c : (chartTarget k (chartIndex j) (strictQ g hY hne) hneC).carrier) :
    chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC c = chartToCurveFun g hg hg0 hg1 hg2 hY hne j hneC c :=
  congrFun (Classical.choose_spec (exists_chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC)) c

theorem curveToChartHom_apply (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty)
    (v : (Variety.ofQuasiAffine
        (isAffineVariety_chartCurve g hg hg0 hg1 hg2 j).isQuasiAffineVariety).carrier) :
    curveToChartHom g hg hg0 hg1 hg2 hY hne j hneC v =
      curveToChartFun g hg hg0 hg1 hg2 hY hne j hneC v :=
  congrFun (Classical.choose_spec (exists_curveToChartHom g hg hg0 hg1 hg2 hY hne j hneC)) v

/-- **The chart piece of the strict transform is isomorphic to the chart
curve.** -/
theorem isIso_chartToCurveHom (j : Fin 2)
    (hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty) :
    (chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC).IsIso := by
  refine ⟨curveToChartHom g hg hg0 hg1 hg2 hY hne j hneC, ?_, ?_⟩
  · apply VarietyHom.ext
    funext c
    change curveToChartHom g hg hg0 hg1 hg2 hY hne j hneC
      (chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC c) = c
    rw [chartToCurveHom_apply, curveToChartHom_apply]
    apply Subtype.ext
    change chartMap (chartIndex j) (chartPt j (c.1 ⟨(some ⟨j⟩, ⟨j⟩), some_ne_chartIndex j⟩)
      (c.1 ⟨(none, ⟨j.rev⟩), none_rev_ne_chartIndex j⟩)) = c.1
    have h := (chartTarget_mem_chartCurve g hg0 hg1 hY hne j hneC c).2
    obtain ⟨-, hRc'⟩ := Classical.choose_spec c.2
    rw [h, hRc']
  · apply VarietyHom.ext
    funext v
    change chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC
      (curveToChartHom g hg hg0 hg1 hg2 hY hne j hneC v) = v
    rw [chartToCurveHom_apply, curveToChartHom_apply]
    apply Subtype.ext
    change ![chartMap (chartIndex j) (chartPt j (v.1 0) (v.1 1)) _,
      chartMap (chartIndex j) (chartPt j (v.1 0) (v.1 1)) _] = v.1
    rw [chartMap_chartPt_some, chartMap_chartPt_none]
    exact fin_two_vec_ext rfl rfl

include hg hg0 hg1 hg2 in
/-- **A chart point of the strict transform at which the chart equation has a
nonzero partial derivative is a nonsingular point.** -/
theorem nonsingularAt_chartPt (j : Fin 2) (t u : k)
    (hmem : chartPt j t u ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g))
    {i : Fin 2} (hi : eval ![t, u] (pderiv i (chartEq j g)) ≠ 0) :
    Variety.NonsingularAt (Variety.ofQuasiProjective (strictQ g hY hne)) ⟨chartPt j t u, hmem⟩ := by
  have hRc := chartPt_mem_standardChart (k := k) j t u
  have hneC : (strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) ∩
      standardChart (chartIndex.{u} j)).Nonempty := ⟨_, hmem, hRc⟩
  let R' : (chartVariety k (chartIndex j) (strictQ g hY hne) hneC).carrier :=
    ⟨chartPt j t u, hmem, hRc⟩
  have h1 : Variety.NonsingularAt (Variety.ofQuasiProjective (strictQ g hY hne))
      ⟨chartPt j t u, hmem⟩ ↔
      Variety.NonsingularAt (chartVariety k (chartIndex j) (strictQ g hY hne) hneC) R' :=
    nonsingularAt_iff_of_open_subset (strictQ g hY hne)
      (isQuasiProjVariety_inter_standardChart k (chartIndex j) (strictQ g hY hne) hneC)
      Set.inter_subset_left (isOpen_inter_standardChart_in k (chartIndex j)) R'
  rw [h1, Variety.nonsingularAt_iff_of_isIso (isIso_chartHom k _ _ hneC) R',
    Variety.nonsingularAt_iff_of_isIso (isIso_chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC),
    nonsingularAt_affine_iff (isAffineVariety_chartCurve g hg hg0 hg1 hg2 j)]
  apply isAffineNonsingularAt_of_pderiv (irreducible_chartEq j hg hg0 hg1 hg2) _ (i := i)
  have hpt : ((chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC
      (chartHom k (chartIndex j) (strictQ g hY hne) hneC R')).1 : Fin 2 → k) = ![t, u] := by
    rw [chartToCurveHom_apply]
    change ![chartMap (chartIndex j) (chartPt j t u) _,
      chartMap (chartIndex j) (chartPt j t u) _] = _
    rw [chartMap_chartPt_some, chartMap_chartPt_none]
  change eval ((chartToCurveHom g hg hg0 hg1 hg2 hY hne j hneC
      (chartHom k (chartIndex j) (strictQ g hY hne) hneC R')).1 : Fin 2 → k) _ ≠ 0
  rw [hpt]
  exact hi

end Nonsingular

/-! ## The two points over a node -/

theorem blowupPt_zero_eq_chartPt {y : PlaneIndex.{u} → k} (hy : y ≠ 0) {j : Fin 2}
    (hj : y ⟨j⟩ ≠ 0) : blowupPt 0 y hy = chartPt j 0 (y ⟨j.rev⟩ / y ⟨j⟩) := by
  rw [blowupPt_eq_of_smul 0 hy (planeChartVec_ne_zero j _) hj (eq_smul_planeChartVec y hj),
    chartPt, zero_smul]

theorem blowupPt_zero_mem_blowupSet (y : PlaneIndex.{u} → k) (hy : y ≠ 0) :
    blowupPt 0 y hy ∈ blowupSet (k := k) (σ := PlaneIndex.{u}) :=
  blowupPt_mem 0 y hy fun i i' => by simp

theorem ne_zero_of_mul_eq {q l₁ l₂ : MvPolynomial (Fin 2) k} (hq : q ≠ 0) (h : q = l₁ * l₂) :
    l₁ ≠ 0 := by
  rintro rfl
  exact hq (by rw [h, zero_mul])

theorem coeff_ne_zero_of_ne_zero {l : MvPolynomial (Fin 2) k} (hl : l.IsHomogeneous 1)
    (hl0 : l ≠ 0) :
    coeff (Finsupp.single 0 1) l ≠ 0 ∨ coeff (Finsupp.single 1 1) l ≠ 0 := by
  by_contra h
  push Not at h
  apply hl0
  rw [eq_linear_of_isHomogeneous_one hl, h.1, h.2]
  simp

theorem eval_linear_eq {l : MvPolynomial (Fin 2) k} (hl : l.IsHomogeneous 1) (y : Fin 2 → k) :
    eval y l = coeff (Finsupp.single 0 1) l * y 0 + coeff (Finsupp.single 1 1) l * y 1 := by
  conv_lhs => rw [eq_linear_of_isHomogeneous_one hl]
  simp

theorem associated_of_common_zero' {l₁ l₂ : MvPolynomial (Fin 2) k} (hl₁ : l₁.IsHomogeneous 1)
    (hl₂ : l₂.IsHomogeneous 1) (hl₁0 : l₁ ≠ 0) (hl₂0 : l₂ ≠ 0) {y : Fin 2 → k} (hy : y ≠ 0)
    (h₁ : eval y l₁ = 0) (h₂ : eval y l₂ = 0) : Associated l₁ l₂ := by
  rw [eq_linear_of_isHomogeneous_one hl₁, eq_linear_of_isHomogeneous_one hl₂]
  rw [eval_linear_eq hl₁] at h₁
  rw [eval_linear_eq hl₂] at h₂
  exact associated_of_common_zero (coeff_ne_zero_of_ne_zero hl₁ hl₁0)
    (coeff_ne_zero_of_ne_zero hl₂ hl₂0) hy h₁ h₂

/-- Two nonzero zeros of a nonzero binary linear form are proportional. -/
theorem exists_smul_of_linear_zero {l : MvPolynomial (Fin 2) k} (hl : l.IsHomogeneous 1)
    (hl0 : l ≠ 0) {y y' : Fin 2 → k} (hy : y ≠ 0) (hy' : y' ≠ 0)
    (h : eval y l = 0) (h' : eval y' l = 0) : ∃ c : k, c ≠ 0 ∧ y = c • y' := by
  rw [eval_linear_eq hl] at h h'
  exact exists_smul_of_minor_eq hy hy'
    (minor_eq_zero_of_linear (coeff_ne_zero_of_ne_zero hl hl0) h h')

omit [Field k] in
theorem liftVec_lowerVec (x : PlaneIndex.{u} → k) : liftVec (lowerVec x) = x := by
  funext i
  rfl

section Main

variable [IsAlgClosed k]

/-- The point of the strict transform over the origin in a direction on which a
simple factor of the initial form vanishes is nonsingular. -/
theorem nonsingularAt_blowupPt_zero (g : MvPolynomial (Fin 2) k) (hg : Irreducible g)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (hg2 : homogeneousComponent 2 g ≠ 0)
    (hY : IsAffineVariety (planeZeroSet.{u} g))
    (hne : (affineSubvarietyPunctured (planeZeroSet.{u} g)).Nonempty)
    {l₁ l₂ : MvPolynomial (Fin 2) k} (hl₁ : l₁.IsHomogeneous 1) (hl₂ : l₂.IsHomogeneous 1)
    (hdist : ¬ Associated l₁ l₂) (hfac : homogeneousComponent 2 g = l₁ * l₂)
    {y : PlaneIndex.{u} → k} (hy : y ≠ 0) (hy₁ : eval (lowerVec y) l₁ = 0)
    (hmem : blowupPt 0 y hy ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g)) :
    Variety.NonsingularAt (Variety.ofQuasiProjective (strictQ g hY hne)) ⟨_, hmem⟩ := by
  obtain ⟨⟨j⟩, hj⟩ := Function.ne_iff.1 hy
  set u := y ⟨j.rev⟩ / y ⟨j⟩
  have heq := blowupPt_zero_eq_chartPt hy hj
  have hmem' : chartPt j 0 u ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) :=
    heq ▸ hmem
  have hpt : (⟨_, hmem⟩ : (Variety.ofQuasiProjective (strictQ g hY hne)).carrier) =
      ⟨chartPt j 0 u, hmem'⟩ := Subtype.ext heq
  rw [hpt]
  have hl₁0 : l₁ ≠ 0 := ne_zero_of_mul_eq hg2 hfac
  have hl₂0 : l₂ ≠ 0 := ne_zero_of_mul_eq hg2 (hfac.trans (mul_comm _ _))
  have hlow : lowerVec y = y ⟨j⟩ • chartVec j u := by
    have := congrArg lowerVec (eq_smul_planeChartVec y hj)
    simpa using this
  have hw₁ : eval (chartVec j u) l₁ = 0 := by
    rw [hlow, hl₁.eval_smul, pow_one] at hy₁
    exact (mul_eq_zero.1 hy₁).resolve_left hj
  apply nonsingularAt_chartPt g hg hg0 hg1 hg2 hY hne j 0 u hmem' (i := 1)
  rw [eval_pderiv_chartEq_of_eq_zero j g _ (by simp), hfac,
    eval_pderiv_aeval_mul j l₁ l₂ u hw₁]
  refine mul_ne_zero ?_ ?_
  · intro hw₂
    exact hdist (associated_of_common_zero' hl₁ hl₂ hl₁0 hl₂0 (chartVec_ne_zero j u) hw₁ hw₂)
  · have hform := eq_linear_of_isHomogeneous_one hl₁
    rw [hform, eval_pderiv_aeval_linear]
    rw [eval_linear_eq hl₁] at hw₁
    have hcoeff := coeff_ne_zero_of_ne_zero hl₁ hl₁0
    fin_cases j
    · simp only [Fin.zero_eta, if_true]
      intro hb
      simp only [Fin.zero_eta, chartVec_self, mul_one] at hw₁
      rw [hb, zero_mul, add_zero] at hw₁
      exact hcoeff.elim (fun h => h hw₁) (fun h => h hb)
    · simp only [Fin.mk_one, one_ne_zero, if_false]
      intro ha
      have h0 : chartVec (1 : Fin 2) u 0 = u := by simp [chartVec]
      simp only [Fin.mk_one, chartVec_self, h0, mul_one] at hw₁
      rw [ha, zero_mul, zero_add] at hw₁
      exact hcoeff.elim (fun h => h ha) (fun h => h hw₁)

/-- The forward statement for a curve through the origin. -/
theorem ordinaryNode_blowup_aux (g : MvPolynomial (Fin 2) k) (hg : Irreducible g)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (hg2 : homogeneousComponent 2 g ≠ 0)
    {l₁ l₂ : MvPolynomial (Fin 2) k} (hl₁ : l₁.IsHomogeneous 1) (hl₂ : l₂.IsHomogeneous 1)
    (hdist : ¬ Associated l₁ l₂) (hfac : homogeneousComponent 2 g = l₁ * l₂) :
    ∃ (hY : IsAffineVariety (planeZeroSet.{u} g))
      (hne : (affineSubvarietyPunctured (planeZeroSet.{u} g)).Nonempty)
      (R₁ R₂ : (Variety.ofQuasiProjective (isQuasiProjVariety_strictTransform hY hne)).carrier),
      R₁ ≠ R₂ ∧
      (∀ R : (Variety.ofQuasiProjective (isQuasiProjVariety_strictTransform hY hne)).carrier,
        (blowupProjectionAffine (isQuasiProjVariety_blowupSet (k := k) (σ := PlaneIndex.{u}))
          ⟨R.1, strictTransform_subset_blowup _ R.2⟩).1 = 0 ↔ R = R₁ ∨ R = R₂) ∧
      HomogeneousVanish (rename ULift.up l₁)
        (blowupSecond ⟨R₁.1, strictTransform_subset_blowup _ R₁.2⟩) ∧
      HomogeneousVanish (rename ULift.up l₂)
        (blowupSecond ⟨R₂.1, strictTransform_subset_blowup _ R₂.2⟩) ∧
      Variety.NonsingularAt
        (Variety.ofQuasiProjective (isQuasiProjVariety_strictTransform hY hne)) R₁ ∧
      Variety.NonsingularAt
        (Variety.ofQuasiProjective (isQuasiProjVariety_strictTransform hY hne)) R₂ := by
  have hY : IsAffineVariety (planeZeroSet.{u} g) :=
    isAffineVariety_zeroSet_singleton_of_irreducible (irreducible_rename_up hg)
  have hl₁0 : l₁ ≠ 0 := ne_zero_of_mul_eq hg2 hfac
  have hl₂0 : l₂ ≠ 0 := ne_zero_of_mul_eq hg2 (hfac.trans (mul_comm _ _))
  -- A nonzero zero of each linear factor.
  have hzero : ∀ l : MvPolynomial (Fin 2) k, l.IsHomogeneous 1 → l ≠ 0 →
      ∃ w : Fin 2 → k, w ≠ 0 ∧ eval w l = 0 := by
    intro l hl hl0
    refine ⟨![-coeff (Finsupp.single 1 1) l, coeff (Finsupp.single 0 1) l], ?_, ?_⟩
    · intro h
      apply hl0
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.zero_apply, neg_eq_zero] at h0 h1
      rw [eq_linear_of_isHomogeneous_one hl, h0, h1]
      simp
    · rw [eval_linear_eq hl]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      ring
  obtain ⟨w₁, hw₁0, hw₁⟩ := hzero l₁ hl₁ hl₁0
  obtain ⟨w₂, hw₂0, hw₂⟩ := hzero l₂ hl₂ hl₂0
  set v₁ : PlaneIndex.{u} → k := liftVec w₁
  set v₂ : PlaneIndex.{u} → k := liftVec w₂
  have hv₁ : v₁ ≠ 0 := liftVec_ne_zero hw₁0
  have hv₂ : v₂ ≠ 0 := liftVec_ne_zero hw₂0
  have hmem₁ : blowupPt 0 v₁ hv₁ ∈
      strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) :=
    blowupPt_zero_mem g hg hg0 hg1 hg2 hv₁ (by
      rw [hfac, map_mul, lowerVec_liftVec, hw₁, zero_mul])
  have hmem₂ : blowupPt 0 v₂ hv₂ ∈
      strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) :=
    blowupPt_zero_mem g hg hg0 hg1 hg2 hv₂ (by
      rw [hfac, map_mul, lowerVec_liftVec, hw₂, mul_zero])
  have hne : (affineSubvarietyPunctured (planeZeroSet.{u} g)).Nonempty := by
    by_contra h
    have hempty := strictTransform_eq_empty_of_punctured_not_nonempty (k := k) _ h
    rw [hempty] at hmem₁
    exact hmem₁
  refine ⟨hY, hne, ⟨_, hmem₁⟩, ⟨_, hmem₂⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The two points have different directions.
    intro h
    have hsec : Projectivization.mk k v₁ hv₁ = Projectivization.mk k v₂ hv₂ := by
      rw [← second_blowupPt 0 v₁ hv₁ (blowupPt_zero_mem_blowupSet v₁ hv₁),
        ← second_blowupPt 0 v₂ hv₂ (blowupPt_zero_mem_blowupSet v₂ hv₂)]
      have hval : blowupPt 0 v₁ hv₁ = blowupPt 0 v₂ hv₂ := congrArg Subtype.val h
      congr 1
      exact Subtype.ext hval
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' k _ _ hv₁ hv₂).1 hsec
    have hwc : w₁ = c • w₂ := by
      rw [← lowerVec_liftVec w₁, ← lowerVec_liftVec w₂]
      change lowerVec v₁ = c • lowerVec v₂
      rw [← hc]
      rfl
    apply hdist
    refine associated_of_common_zero' hl₁ hl₂ hl₁0 hl₂0 hw₁0 hw₁ ?_
    rw [hwc, hl₂.eval_smul, hw₂, mul_zero]
  · intro R
    let R' : blowupSet (k := k) (σ := PlaneIndex.{u}) :=
      ⟨R.1, strictTransform_subset_blowup _ R.2⟩
    constructor
    · intro h0
      change proj R' = 0 at h0
      have hY2 := eval_second_of_mem_fibre g hg0 hg1 R' R.2 h0
      set y := (blowupSecond R').rep
      have hy0 : lowerVec y ≠ 0 := lowerVec_ne_zero (blowupSecond R').rep_nonzero
      have hR : R.1 = blowupPt 0 y (blowupSecond R').rep_nonzero := by
        have := eq_blowupPt R'
        rw [h0] at this
        exact this
      rw [hfac, map_mul] at hY2
      rcases mul_eq_zero.1 hY2 with h | h
      · left
        obtain ⟨c, hc, hyc⟩ := exists_smul_of_linear_zero hl₁ hl₁0 hy0 hw₁0 h hw₁
        apply Subtype.ext
        change R.1 = blowupPt 0 v₁ hv₁
        rw [hR]
        apply blowupPt_eq_of_smul 0 _ hv₁ hc
        rw [← liftVec_lowerVec y, hyc]
        rfl
      · right
        obtain ⟨c, hc, hyc⟩ := exists_smul_of_linear_zero hl₂ hl₂0 hy0 hw₂0 h hw₂
        apply Subtype.ext
        change R.1 = blowupPt 0 v₂ hv₂
        rw [hR]
        apply blowupPt_eq_of_smul 0 _ hv₂ hc
        rw [← liftVec_lowerVec y, hyc]
        rfl
    · rintro (rfl | rfl)
      · exact proj_blowupPt 0 v₁ hv₁ _
      · exact proj_blowupPt 0 v₂ hv₂ _
  · change HomogeneousVanish _ (blowupSecond ⟨blowupPt 0 v₁ hv₁, _⟩)
    rw [second_blowupPt, homogeneousVanish_iff_of_isHomogeneous hl₁.rename_isHomogeneous,
      eval_rename_up, lowerVec_liftVec, hw₁]
  · change HomogeneousVanish _ (blowupSecond ⟨blowupPt 0 v₂ hv₂, _⟩)
    rw [second_blowupPt, homogeneousVanish_iff_of_isHomogeneous hl₂.rename_isHomogeneous,
      eval_rename_up, lowerVec_liftVec, hw₂]
  · exact nonsingularAt_blowupPt_zero g hg hg0 hg1 hg2 hY hne hl₁ hl₂ hdist hfac hv₁
      (by rw [lowerVec_liftVec, hw₁]) hmem₁
  · exact nonsingularAt_blowupPt_zero g hg hg0 hg1 hg2 hY hne hl₂ hl₁
      (fun h => hdist h.symm) (hfac.trans (mul_comm _ _)) hv₂
      (by rw [lowerVec_liftVec, hw₂]) hmem₂

/-- The converse for a curve through the origin. -/
theorem isOrdinaryNode_aux (g : MvPolynomial (Fin 2) k)
    (hg0 : homogeneousComponent 0 g = 0) (hg1 : homogeneousComponent 1 g = 0)
    (hg2 : homogeneousComponent 2 g ≠ 0)
    (R₁ R₂ : blowupSet (k := k) (σ := PlaneIndex.{u}))
    (h₁ : R₁.1 ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g))
    (h₂ : R₂.1 ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g))
    (h₁0 : proj R₁ = 0) (h₂0 : proj R₂ = 0) (hne : R₁ ≠ R₂) :
    ∃ l₁ l₂ : MvPolynomial (Fin 2) k, l₁.IsHomogeneous 1 ∧ l₂.IsHomogeneous 1 ∧
      ¬ Associated l₁ l₂ ∧ homogeneousComponent 2 g = l₁ * l₂ := by
  obtain ⟨l₁, l₂, hl₁, hl₂, hfac⟩ :=
    exists_linear_factors (homogeneousComponent_isHomogeneous 2 g)
  refine ⟨l₁, l₂, hl₁, hl₂, ?_, hfac⟩
  rintro ⟨w, hw⟩
  have hl₁0 : l₁ ≠ 0 := ne_zero_of_mul_eq hg2 hfac
  -- Every point over the origin has its direction on `l₁ = 0`.
  have hdir : ∀ R : blowupSet (k := k) (σ := PlaneIndex.{u}),
      R.1 ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (planeZeroSet g) → proj R = 0 →
      eval (lowerVec (blowupSecond R).rep) l₁ = 0 := by
    intro R hR hR0
    have h := eval_second_of_mem_fibre g hg0 hg1 R hR hR0
    rw [hfac, ← hw, map_mul, map_mul] at h
    have hu : eval (lowerVec (blowupSecond R).rep) (w : MvPolynomial (Fin 2) k) ≠ 0 :=
      ((w.isUnit).map (eval (lowerVec (blowupSecond R).rep))).ne_zero
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h hu
  have hy₁ := hdir R₁ h₁ h₁0
  have hy₂ := hdir R₂ h₂ h₂0
  obtain ⟨c, hc, hyc⟩ := exists_smul_of_linear_zero hl₁ hl₁0
    (lowerVec_ne_zero (blowupSecond R₁).rep_nonzero)
    (lowerVec_ne_zero (blowupSecond R₂).rep_nonzero) hy₁ hy₂
  apply hne
  apply Subtype.ext
  have e₁ := eq_blowupPt R₁
  have e₂ := eq_blowupPt R₂
  rw [h₁0] at e₁
  rw [h₂0] at e₂
  rw [e₁, e₂]
  apply blowupPt_eq_of_smul 0 _ _ hc
  rw [← liftVec_lowerVec (blowupSecond R₁).rep, hyc]
  rfl

end Main

end OrdinaryNode

/-! ## Hartshorne I, Exercise 5.6(b) -/

/-- **Blowing up an ordinary node** (Hartshorne I, Exercise 5.6(b)).  Let `P` be
an ordinary node of the irreducible plane curve `f = 0`, with the quadratic
initial form of the local equation at `P` the product of the non-associated
linear forms `l₁` and `l₂`.  Blow up the plane at `P` (that is, at the origin,
after the translation moving `P` there) and take the strict transform `Ỹ` of the
curve.  Then the fibre of `Ỹ` over `P` consists of exactly two distinct points
`R₁`, `R₂`; the direction of `Rᵢ` lies on the tangent line `lᵢ = 0`; and both
points are nonsingular points of `Ỹ`. -/
theorem ordinaryNode_blowup [IsAlgClosed k] {f : MvPolynomial (Fin 2) k} (hf : Irreducible f)
    {P : Fin 2 → k} (hP : IsPlaneDoublePoint f P) {l₁ l₂ : MvPolynomial (Fin 2) k}
    (hl₁ : l₁.IsHomogeneous 1) (hl₂ : l₂.IsHomogeneous 1) (hdist : ¬ Associated l₁ l₂)
    (hfac : homogeneousComponent 2 (planeLocalEquation f P) = l₁ * l₂) :
    ∃ (hY : IsAffineVariety (translatedPlaneCurve.{u} f P))
      (hne : (affineSubvarietyPunctured (translatedPlaneCurve.{u} f P)).Nonempty)
      (R₁ R₂ : (Variety.ofQuasiProjective (isQuasiProjVariety_strictTransform hY hne)).carrier),
      R₁ ≠ R₂ ∧
      (∀ R : (Variety.ofQuasiProjective (isQuasiProjVariety_strictTransform hY hne)).carrier,
        (blowupProjectionAffine (isQuasiProjVariety_blowupSet (k := k) (σ := PlaneIndex.{u}))
          ⟨R.1, strictTransform_subset_blowup _ R.2⟩).1 = 0 ↔ R = R₁ ∨ R = R₂) ∧
      HomogeneousVanish (rename ULift.up l₁)
        (blowupSecond ⟨R₁.1, strictTransform_subset_blowup _ R₁.2⟩) ∧
      HomogeneousVanish (rename ULift.up l₂)
        (blowupSecond ⟨R₂.1, strictTransform_subset_blowup _ R₂.2⟩) ∧
      Variety.NonsingularAt
        (Variety.ofQuasiProjective (isQuasiProjVariety_strictTransform hY hne)) R₁ ∧
      Variety.NonsingularAt
        (Variety.ofQuasiProjective (isQuasiProjVariety_strictTransform hY hne)) R₂ := by
  rw [translatedPlaneCurve_eq]
  exact ordinaryNode_blowup_aux _ (irreducible_planeLocalEquation hf P) hP.1 hP.2.1 hP.2.2
    hl₁ hl₂ hdist hfac

/-- **Recognizing an ordinary node by its two branches** (a converse that
supplements Hartshorne I, Exercise 5.6(b), which states only the forward
direction).  If `P` is a double point of the plane curve
`f = 0` and the strict transform of the curve under the blow-up at `P` has two
distinct points over `P`, then `P` is an ordinary node. -/
theorem isOrdinaryNode_of_two_blowup_points [IsAlgClosed k] {f : MvPolynomial (Fin 2) k}
    {P : Fin 2 → k} (hP : IsPlaneDoublePoint f P)
    {R₁ R₂ : blowupSet (k := k) (σ := PlaneIndex.{u})}
    (h₁ : R₁.1 ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (translatedPlaneCurve f P))
    (h₂ : R₂.1 ∈ strictTransform (k := k) (σ := PlaneIndex.{u}) (translatedPlaneCurve f P))
    (h₁0 : (blowupProjectionAffine
      (isQuasiProjVariety_blowupSet (k := k) (σ := PlaneIndex.{u})) R₁).1 = 0)
    (h₂0 : (blowupProjectionAffine
      (isQuasiProjVariety_blowupSet (k := k) (σ := PlaneIndex.{u})) R₂).1 = 0)
    (hne : R₁ ≠ R₂) : IsOrdinaryNode f P := by
  rw [translatedPlaneCurve_eq] at h₁ h₂
  exact ⟨hP, isOrdinaryNode_aux _ hP.1 hP.2.1 hP.2.2 R₁ R₂ h₁ h₂ h₁0 h₂0 hne⟩

end Hartshorne
