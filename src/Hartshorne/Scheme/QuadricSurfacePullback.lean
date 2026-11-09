/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuadricSurfaceProduct
import Hartshorne.Scheme.QuadricSurfaceHyperplane
import Hartshorne.Scheme.CartierDivisorPullback
import Hartshorne.Scheme.RegularLocalFactorial

/-!
# Pullback from the two factors of `Q ≅ ℙ¹ × ℙ¹` on class groups

Let `Q = quadricSurface k` be the split quadric, identified with `ℙ¹_k ×_k ℙ¹_k` by
`Hartshorne.quadricSurfaceIsoSegreSource`. The two projections, followed by the comparison
`ℙ¹_{Spec k} ≅ Proj k[x₀, x₁]`, are `Hartshorne.quadricProjOne`, `Hartshorne.quadricProjTwo :
Q ⟶ ℙ¹_k`. Both schemes are regular, hence locally factorial, so `Cl ≅ Pic` on both, and the
Picard pullback (Exercise II.6.8(a)) defines the pullbacks `pᵢ^* : Cl ℙ¹_k ⟶ Cl Q`
(`Hartshorne.quadricClassGroupPullbackOne`, `Hartshorne.quadricClassGroupPullbackTwo`).

The main result `Hartshorne.quadricClassGroupPullbackEquiv` is the isomorphism
`Cl ℙ¹_k × Cl ℙ¹_k ≅ Cl Q`, `(a, b) ↦ p₁^* a + p₂^* b`: under `Cl ℙ¹_k ≅ ℤ` and
`quadricSurfaceClassGroupEquiv : Cl Q ≅ ℤ × ℤ` it is the identity of `ℤ × ℤ`, because `p₁^*` sends
the class of the point `x₀ = 0` to the class of the line `L₁ = {s₀ = 0}` and `p₂^*` sends it to the
class of `L₂ = {u₀ = 0}`.

## Proof

On the chart `D₊(sᵢuⱼ)` the first projection is the chart map to `D₊(xᵢ)` sending `x_a / xᵢ` to
`s_a uⱼ / sᵢ uⱼ` (`Hartshorne.awayι_comp_quadricProjOne`), so it pulls `x₀ / x₁` back to
`s₀u₀ / s₁u₀`. The point `x₀ = 0` is the divisor of `x₀ / x₁` on `D₊(x₁)` and of `1` on `D₊(x₀)`;
`L₁` is the divisor of `s₀u₀ / s₁u₀` on `D₊(s₁uⱼ)` and of `1` on `D₊(s₀uⱼ)`. The pullback formula
for Picard classes of such local data (`AlgebraicGeometry.Scheme.picPullback_weilClassEquivPicard`)
gives `p₁^*[x₀ = 0] = [L₁]`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "𝒬" => quadricGrading k

local notation "𝒮" => homogeneousSubmodule (Fin (1 + 1)) k

section Projections

/-- The comparison `Proj k[x₀, x₁] ≅ ℙ¹_{Spec k}` with the coordinates in their given order. -/
abbrev projectiveLineIso : Proj 𝒮 ≅ projectiveSpaceOverScheme 1 (Spec (.of k)) :=
  projectiveSpaceOverSpecIso k 1 (Equiv.refl _)

/-- **The first projection** `p₁ : Q ≅ ℙ¹_k ×_k ℙ¹_k ⟶ ℙ¹_k = Proj k[x₀, x₁]`. -/
def quadricProjOne : quadricSurface k ⟶ Proj 𝒮 :=
  (quadricSurfaceIsoSegreSource k).inv ≫ pullback.fst _ _ ≫ (projectiveLineIso k).inv

/-- **The second projection** `p₂ : Q ≅ ℙ¹_k ×_k ℙ¹_k ⟶ ℙ¹_k = Proj k[x₀, x₁]`. -/
def quadricProjTwo : quadricSurface k ⟶ Proj 𝒮 :=
  (quadricSurfaceIsoSegreSource k).inv ≫ pullback.snd _ _ ≫ (projectiveLineIso k).inv

/-- The constants of a chart ring of `Q`. -/
abbrev quadricAwayConst {f : QuadricRing k} : k →+* Away 𝒬 f :=
  (HomogeneousLocalization.fromZeroRingHom 𝒬 _).comp (algebraMap k (𝒬 0))

/-- On a chart `D₊(f)` of `Q`, the ring map `x_a ↦ s_a uⱼ / f` describing the first projection
(on the chart `D₊(sᵢuⱼ)` with `f = sᵢuⱼ`). -/
def quadricFstChartHom {f : QuadricRing k} (f_deg : f ∈ 𝒬 1) (j : Fin 2) :
    MvPolynomial (Fin (1 + 1)) k →+* Away 𝒬 f :=
  eval₂Hom (quadricAwayConst k) fun a =>
    Away.mk 𝒬 f_deg 1 (quadricChart k a j) (by simpa using quadricChart_mem k a j)

/-- On a chart `D₊(f)` of `Q`, the ring map `x_b ↦ sᵢ u_b / f` describing the second projection
(on the chart `D₊(sᵢuⱼ)` with `f = sᵢuⱼ`). -/
def quadricSndChartHom {f : QuadricRing k} (f_deg : f ∈ 𝒬 1) (i : Fin 2) :
    MvPolynomial (Fin (1 + 1)) k →+* Away 𝒬 f :=
  eval₂Hom (quadricAwayConst k) fun b =>
    Away.mk 𝒬 f_deg 1 (quadricChart k i b) (by simpa using quadricChart_mem k i b)

theorem away_mk_eq_one {f a : QuadricRing k} (f_deg : f ∈ 𝒬 1) (ha : a ∈ 𝒬 (1 • 1)) (h : a = f) :
    Away.mk 𝒬 f_deg 1 a ha = 1 := by
  subst h
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_one]
  convert Localization.mk_self (⟨a, 1, pow_one _⟩ : Submonoid.powers a) using 2
  exact Subtype.ext (pow_one _)

theorem away_mk_congr {f a b : QuadricRing k} (f_deg : f ∈ 𝒬 1) (ha : a ∈ 𝒬 (1 • 1))
    (hb : b ∈ 𝒬 (1 • 1)) (h : a = b) : Away.mk 𝒬 f_deg 1 a ha = Away.mk 𝒬 f_deg 1 b hb := by
  subst h
  rfl

theorem quadricFstChartHom_X_self (i j : Fin 2) :
    quadricFstChartHom k (quadricChart_mem k i j) j (X i) = 1 := by
  rw [quadricFstChartHom, eval₂Hom_X', away_mk_eq_one k _ _ rfl]

theorem quadricSndChartHom_X_self (i j : Fin 2) :
    quadricSndChartHom k (quadricChart_mem k i j) i (X j) = 1 := by
  rw [quadricSndChartHom, eval₂Hom_X', away_mk_eq_one k _ _ rfl]

theorem isUnit_quadricFstChartHom_segre (c : Fin (1 + 1) × Fin (1 + 1)) :
    IsUnit (quadricFstChartHom k (quadricSegreHom_X_mem k c) c.2 (X c.1)) := by
  rw [quadricFstChartHom, eval₂Hom_X',
    away_mk_eq_one k _ _ (quadricSegreHom_X_segreIndex k c.1 c.2).symm]
  exact isUnit_one

theorem quadricSurfaceIsoSegreSource_inv :
    (quadricSurfaceIsoSegreSource k).inv = quadricSurfaceToSegreSource k :=
  rfl

@[reassoc]
theorem quadricSurfaceToSegreSource_toInt :
    quadricSurfaceToSegreSource k ≫ relativeSegreSourceToInt 1 1 (Spec (.of k)) =
      quadricToSegreSource k :=
  IsPullback.lift_snd _ _ _ _

theorem relativeSegreSourceToInt_fst :
    relativeSegreSourceToInt 1 1 (Spec (.of k)) ≫ segreFst 1 1 =
      pullback.fst _ _ ≫ pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- **The first projection on a chart.** On `D₊(sᵢuⱼ)`, `p₁` is the chart map to `D₊(xᵢ)` given by
`x_a ↦ s_a uⱼ / sᵢ uⱼ`. -/
theorem quadricSegreCover_comp_projOne (c : Fin (1 + 1) × Fin (1 + 1)) :
    (quadricSegreCover k).f c ≫ quadricProjOne k =
      projChartMap (quadricFstChartHom k (quadricSegreHom_X_mem k c) c.2)
        (X_mem_homogeneousSubmodule_one k c.1) Nat.one_pos
        (isUnit_quadricFstChartHom_segre k c) := by
  rw [← cancel_mono (projectiveLineIso k).hom]
  simp only [quadricProjOne, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    quadricSurfaceIsoSegreSource_inv]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [projectiveSpaceOverSpecIso_hom, projToProjectiveSpaceOverSpec_fst]
    have h1 : quadricSurfaceToSegreSource k ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
        quadricToSegreSource k ≫ segreFst 1 1 := by
      rw [← quadricSurfaceToSegreSource_toInt, Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _).symm
    rw [h1]
    have h2 : (quadricSegreCover k).f c ≫ quadricToSegreSource k =
        quadricChartToSegreChart k c ≫ segreRetractToSource 1 1 c.1 c.2 := by
      rw [quadricToSegreSource, Scheme.Cover.ι_glueMorphisms]
      rfl
    have hG : IsUnit (((CommRingCat.ofHom (Away.map (quadricSegreHom k)
        (X (segreIndex 1 1 c)))).hom.comp (segreFstRetractRingMap 1 1 c.1 c.2)) (X c.1)) := by
      rw [RingHom.comp_apply, segreFstRetractRingMap_X_self, map_one]
      exact isUnit_one
    have hL : (quadricSegreCover k).f c ≫ quadricToSegreSource k ≫ segreFst 1 1 =
        projChartMap (((CommRingCat.ofHom (Away.map (quadricSegreHom k)
          (X (segreIndex 1 1 c)))).hom.comp (segreFstRetractRingMap 1 1 c.1 c.2)))
          (X_mem_homogeneousSubmodule_one _ c.1) Nat.one_pos hG := by
      rw [← Category.assoc, h2, Category.assoc, segreRetractToSource_fst, SpecMap_projChartMap]
    refine hL.trans ?_
    have hu : IsUnit (quadricFstChartHom k (quadricSegreHom_X_mem k c) c.2
        (projectiveSpaceComparisonHom k 1 (Equiv.refl _) (X c.1))) := by
      rw [projectiveSpaceComparisonHom_X]
      exact isUnit_quadricFstChartHom_segre k c
    rw [projChartMap_eq _ (X_mem_homogeneousSubmodule_one k c.1) Nat.one_pos _
      ((projectiveSpaceComparisonHom k 1 (Equiv.refl _)).map_mem
        (X_mem_homogeneousSubmodule_one _ c.1)) Nat.one_pos hu,
      projChartMap, projChartMap]
    refine Eq.trans ?_ ((congrArg (_ ≫ ·)
      (awayι_comp_toProjectiveSpaceInt k 1 (Equiv.refl _) c.1)).symm.trans
        (Category.assoc _ _ _).symm)
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext1
    apply chart_ringHom_ext c.1
    · intro r
      exact chartConst_ext _ _ _ r
    · intro a
      have hF1 : quadricFstChartHom k (quadricSegreHom_X_mem k c) c.2
          (projectiveSpaceComparisonHom k 1 (Equiv.refl _) (X c.1)) = 1 := by
        rw [projectiveSpaceComparisonHom_X, Equiv.refl_apply, quadricFstChartHom, eval₂Hom_X',
          away_mk_eq_one k _ _ (quadricSegreHom_X_segreIndex k c.1 c.2).symm]
      have key := awayLift_mk (𝒜 := 𝒮) (quadricFstChartHom k (quadricSegreHom_X_mem k c) c.2) hu
        ((projectiveSpaceComparisonHom k 1 (Equiv.refl _)).map_mem
          (X_mem_homogeneousSubmodule_one _ c.1)) 1
        (projectiveSpaceComparisonHom k 1 (Equiv.refl _) (X a))
        (by simpa using projectiveSpaceComparisonHom_X_mem k 1 (Equiv.refl _) a)
      rw [hF1, one_pow] at key
      replace key := (mul_one _).symm.trans key
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      rw [away_map_comparison_chartRatio]
      refine Eq.trans ?_ key.symm
      rw [awayLift_chartRatio _ _ _ (by
        rw [RingHom.comp_apply, segreFstRetractRingMap_X_self, map_one]), RingHom.comp_apply,
        projectiveSpaceComparisonHom_X]
      simp only [segreFstRetractRingMap, eval₂Hom_X', chartRatio, Away.map_mk,
        quadricFstChartHom, Equiv.refl_apply]
      exact away_mk_congr k _ _ _ (quadricSegreHom_X_segreIndex k a c.2)
  · have h3 : quadricSurfaceToSegreSource k ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
        quadricSurfaceToSpec k := by
      rw [← quadricSurfaceToProjectiveSpace_projection, ← quadricSurfaceToSegreSource_comp,
        Category.assoc, relativeSegre_projection]
    simp only [Category.assoc, projectiveSpaceOverSpecIso_hom,
      projToProjectiveSpaceOverSpec_projection]
    rw [h3, quadricSurfaceToSpec, projChartMap, Category.assoc, Proj.awayι_toSpecZero_assoc,
      Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [awayLift_fromZeroRingHom (𝒜 := 𝒮)]
    exact (eval₂Hom_C (quadricAwayConst k) _ r).symm

theorem isUnit_quadricSndChartHom_segre (c : Fin (1 + 1) × Fin (1 + 1)) :
    IsUnit (quadricSndChartHom k (quadricSegreHom_X_mem k c) c.1 (X c.2)) := by
  rw [quadricSndChartHom, eval₂Hom_X',
    away_mk_eq_one k _ _ (quadricSegreHom_X_segreIndex k c.1 c.2).symm]
  exact isUnit_one

/-- **The second projection on a chart.** On `D₊(sᵢuⱼ)`, `p₂` is the chart map to `D₊(xⱼ)` given
by `x_b ↦ sᵢ u_b / sᵢ uⱼ`. -/
theorem quadricSegreCover_comp_projTwo (c : Fin (1 + 1) × Fin (1 + 1)) :
    (quadricSegreCover k).f c ≫ quadricProjTwo k =
      projChartMap (quadricSndChartHom k (quadricSegreHom_X_mem k c) c.1)
        (X_mem_homogeneousSubmodule_one k c.2) Nat.one_pos
        (isUnit_quadricSndChartHom_segre k c) := by
  rw [← cancel_mono (projectiveLineIso k).hom]
  simp only [quadricProjTwo, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    quadricSurfaceIsoSegreSource_inv]
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [projectiveSpaceOverSpecIso_hom, projToProjectiveSpaceOverSpec_fst]
    have h1 : quadricSurfaceToSegreSource k ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
        quadricToSegreSource k ≫ segreSnd 1 1 := by
      rw [← quadricSurfaceToSegreSource_toInt, Category.assoc]
      exact congrArg _ (pullback.lift_snd _ _ _).symm
    rw [h1]
    have h2 : (quadricSegreCover k).f c ≫ quadricToSegreSource k =
        quadricChartToSegreChart k c ≫ segreRetractToSource 1 1 c.1 c.2 := by
      rw [quadricToSegreSource, Scheme.Cover.ι_glueMorphisms]
      rfl
    have hG : IsUnit (((CommRingCat.ofHom (Away.map (quadricSegreHom k)
        (X (segreIndex 1 1 c)))).hom.comp (segreSndRetractRingMap 1 1 c.1 c.2)) (X c.2)) := by
      rw [RingHom.comp_apply, segreSndRetractRingMap_X_self, map_one]
      exact isUnit_one
    have hL : (quadricSegreCover k).f c ≫ quadricToSegreSource k ≫ segreSnd 1 1 =
        projChartMap (((CommRingCat.ofHom (Away.map (quadricSegreHom k)
          (X (segreIndex 1 1 c)))).hom.comp (segreSndRetractRingMap 1 1 c.1 c.2)))
          (X_mem_homogeneousSubmodule_one _ c.2) Nat.one_pos hG := by
      rw [← Category.assoc, h2, Category.assoc, segreRetractToSource_snd, SpecMap_projChartMap]
    refine hL.trans ?_
    have hu : IsUnit (quadricSndChartHom k (quadricSegreHom_X_mem k c) c.1
        (projectiveSpaceComparisonHom k 1 (Equiv.refl _) (X c.2))) := by
      rw [projectiveSpaceComparisonHom_X]
      exact isUnit_quadricSndChartHom_segre k c
    rw [projChartMap_eq _ (X_mem_homogeneousSubmodule_one k c.2) Nat.one_pos _
      ((projectiveSpaceComparisonHom k 1 (Equiv.refl _)).map_mem
        (X_mem_homogeneousSubmodule_one _ c.2)) Nat.one_pos hu,
      projChartMap, projChartMap]
    refine Eq.trans ?_ ((congrArg (_ ≫ ·)
      (awayι_comp_toProjectiveSpaceInt k 1 (Equiv.refl _) c.2)).symm.trans
        (Category.assoc _ _ _).symm)
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext1
    apply chart_ringHom_ext c.2
    · intro r
      exact chartConst_ext _ _ _ r
    · intro a
      have hF1 : quadricSndChartHom k (quadricSegreHom_X_mem k c) c.1
          (projectiveSpaceComparisonHom k 1 (Equiv.refl _) (X c.2)) = 1 := by
        rw [projectiveSpaceComparisonHom_X, Equiv.refl_apply, quadricSndChartHom, eval₂Hom_X',
          away_mk_eq_one k _ _ (quadricSegreHom_X_segreIndex k c.1 c.2).symm]
      have key := awayLift_mk (𝒜 := 𝒮) (quadricSndChartHom k (quadricSegreHom_X_mem k c) c.1) hu
        ((projectiveSpaceComparisonHom k 1 (Equiv.refl _)).map_mem
          (X_mem_homogeneousSubmodule_one _ c.2)) 1
        (projectiveSpaceComparisonHom k 1 (Equiv.refl _) (X a))
        (by simpa using projectiveSpaceComparisonHom_X_mem k 1 (Equiv.refl _) a)
      rw [hF1, one_pow] at key
      replace key := (mul_one _).symm.trans key
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      rw [away_map_comparison_chartRatio]
      refine Eq.trans ?_ key.symm
      rw [awayLift_chartRatio _ _ _ (by
        rw [RingHom.comp_apply, segreSndRetractRingMap_X_self, map_one]), RingHom.comp_apply,
        projectiveSpaceComparisonHom_X]
      simp only [segreSndRetractRingMap, eval₂Hom_X', chartRatio, Away.map_mk,
        quadricSndChartHom, Equiv.refl_apply]
      exact away_mk_congr k _ _ _ (quadricSegreHom_X_segreIndex k c.1 a)
  · have h3 : quadricSurfaceToSegreSource k ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
        quadricSurfaceToSpec k := by
      rw [← pullback.condition, ← quadricSurfaceToProjectiveSpace_projection, ← quadricSurfaceToSegreSource_comp,
        Category.assoc, relativeSegre_projection]
    simp only [Category.assoc, projectiveSpaceOverSpecIso_hom,
      projToProjectiveSpaceOverSpec_projection]
    rw [h3, quadricSurfaceToSpec, projChartMap, Category.assoc, Proj.awayι_toSpecZero_assoc,
      Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [awayLift_fromZeroRingHom (𝒜 := 𝒮)]
    exact (eval₂Hom_C (quadricAwayConst k) _ r).symm

end Projections

end Hartshorne
