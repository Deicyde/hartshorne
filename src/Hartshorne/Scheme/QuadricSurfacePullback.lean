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

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "𝒬" => quadricGrading k

local notation "𝒮" => homogeneousSubmodule (Fin (1 + 1)) k

section Charts

theorem isUnit_quadricFstChartHom (i j : Fin 2) :
    IsUnit (quadricFstChartHom k (quadricChart_mem k i j) j (X i)) := by
  rw [quadricFstChartHom_X_self]
  exact isUnit_one

theorem isUnit_quadricSndChartHom (i j : Fin 2) :
    IsUnit (quadricSndChartHom k (quadricChart_mem k i j) i (X j)) := by
  rw [quadricSndChartHom_X_self]
  exact isUnit_one

/-- **The first projection on the chart `D₊(sᵢuⱼ)`.** -/
theorem awayι_comp_quadricProjOne (i j : Fin 2) :
    Proj.awayι 𝒬 (quadricChart k i j) (quadricChart_mem k i j) Nat.one_pos ≫ quadricProjOne k =
      projChartMap (quadricFstChartHom k (quadricChart_mem k i j) j)
        (X_mem_homogeneousSubmodule_one k i) Nat.one_pos (isUnit_quadricFstChartHom k i j) := by
  have key : ∀ (f : QuadricRing k) (_ : quadricSegreHom k (X (segreIndex 1 1 (i, j))) = f)
      (f_deg : f ∈ 𝒬 1) (hu : IsUnit (quadricFstChartHom k f_deg j (X i))),
      Proj.awayι 𝒬 f f_deg Nat.one_pos ≫ quadricProjOne k =
        projChartMap (quadricFstChartHom k f_deg j) (X_mem_homogeneousSubmodule_one k i)
          Nat.one_pos hu := by
    intro f hf
    subst hf
    intro f_deg hu
    exact quadricSegreCover_comp_projOne k (i, j)
  exact key _ (quadricSegreHom_X_segreIndex k i j) _ _

/-- **The second projection on the chart `D₊(sᵢuⱼ)`.** -/
theorem awayι_comp_quadricProjTwo (i j : Fin 2) :
    Proj.awayι 𝒬 (quadricChart k i j) (quadricChart_mem k i j) Nat.one_pos ≫ quadricProjTwo k =
      projChartMap (quadricSndChartHom k (quadricChart_mem k i j) i)
        (X_mem_homogeneousSubmodule_one k j) Nat.one_pos (isUnit_quadricSndChartHom k i j) := by
  have key : ∀ (f : QuadricRing k) (_ : quadricSegreHom k (X (segreIndex 1 1 (i, j))) = f)
      (f_deg : f ∈ 𝒬 1) (hu : IsUnit (quadricSndChartHom k f_deg i (X j))),
      Proj.awayι 𝒬 f f_deg Nat.one_pos ≫ quadricProjTwo k =
        projChartMap (quadricSndChartHom k f_deg i) (X_mem_homogeneousSubmodule_one k j)
          Nat.one_pos hu := by
    intro f hf
    subst hf
    intro f_deg hu
    exact quadricSegreCover_comp_projTwo k (i, j)
  exact key _ (quadricSegreHom_X_segreIndex k i j) _ _

theorem basicOpen_le_preimage_quadricProjOne (i j : Fin 2) :
    Proj.basicOpen 𝒬 (quadricChart k i j) ≤
      quadricProjOne k ⁻¹ᵁ Proj.basicOpen 𝒮 (X i) := by
  intro x hx
  obtain ⟨y, rfl⟩ := quadric_exists_chart_point k hx
  change (Proj.awayι 𝒬 (quadricChart k i j) (quadricChart_mem k i j) Nat.one_pos ≫
    quadricProjOne k).base y ∈ Proj.basicOpen 𝒮 (X i)
  rw [awayι_comp_quadricProjOne, projChartMap]
  exact projChartι_base_mem 𝒮 (X_mem_homogeneousSubmodule_one k i) Nat.one_pos _

theorem basicOpen_le_preimage_quadricProjTwo (i j : Fin 2) :
    Proj.basicOpen 𝒬 (quadricChart k i j) ≤
      quadricProjTwo k ⁻¹ᵁ Proj.basicOpen 𝒮 (X j) := by
  intro x hx
  obtain ⟨y, rfl⟩ := quadric_exists_chart_point k hx
  change (Proj.awayι 𝒬 (quadricChart k i j) (quadricChart_mem k i j) Nat.one_pos ≫
    quadricProjTwo k).base y ∈ Proj.basicOpen 𝒮 (X j)
  rw [awayι_comp_quadricProjTwo, projChartMap]
  exact projChartι_base_mem 𝒮 (X_mem_homogeneousSubmodule_one k j) Nat.one_pos _

end Charts

section Generic

theorem SpecMap_base_genericPoint {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S] (φ : R ⟶ S)
    (hφ : Function.Injective φ) :
    (Spec.map φ).base (genericPoint (Spec S)) = genericPoint (Spec R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  refine PrimeSpectrum.ext ?_
  exact Ideal.comap_bot_of_injective φ.hom hφ

theorem genericFunctionFieldMap_SpecMap_algebraMap {R S : CommRingCat.{u}} [IsDomain R]
    [IsDomain S] (φ : R ⟶ S)
    (h : (Spec.map φ).base (genericPoint (Spec S)) = genericPoint (Spec R)) (r : R) :
    (Spec.map φ).genericFunctionFieldMap h (algebraMap R (Spec R).functionField r) =
      algebraMap S (Spec S).functionField (φ r) := by
  set ξ := genericPoint (Spec S)
  have e1 := spec_algebraMap_stalk_toStalk (A := R) ((Spec.map φ).base ξ) r
  have e2 := (Spec.map φ).genericFunctionFieldMap_algebraMap h ξ
    (StructureSheaf.toStalk R ((Spec.map φ).base ξ) r)
  have e3 : (Spec.map φ).stalkMap ξ (StructureSheaf.toStalk R ((Spec.map φ).base ξ) r) =
      StructureSheaf.toStalk S ξ (φ r) :=
    stalkMap_toStalk_apply φ ξ r
  have e4 := spec_algebraMap_stalk_toStalk (A := S) ξ (φ r)
  rw [← e1, e2, e3, e4]

end Generic

section Dominance

theorem fin_two_subtype_subsingleton (i : Fin (1 + 1)) (a b : {a : Fin (1 + 1) // a ≠ i}) :
    a = b := by
  revert i a b
  decide

theorem fin_two_eq_rev {i a : Fin 2} (h : a ≠ i) : a = i.rev := by
  revert i a
  decide

theorem quadricChartToPoly_awayLift_fst (i j : Fin 2) :
    ((quadricChartToPoly k i j).comp (awayLift (𝒜 := 𝒮)
        (quadricFstChartHom k (quadricChart_mem k i j) j) (X i)
        (isUnit_quadricFstChartHom k i j))).comp (chartOfPoly k i) =
      (rename fun _ => (0 : Fin 2)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, chartOfPoly, eval₂Hom_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, rename_C]
    rw [chartConst, RingHom.comp_apply, awayLift_fromZeroRingHom (𝒜 := 𝒮)]
    change quadricChartToPoly k i j (quadricFstChartHom k _ j (C r)) = C r
    rw [quadricFstChartHom, eval₂Hom_C]
    have h := RingHom.congr_fun (quadricChartToPoly_comp_chartOfPoly k i j) (C r)
    rw [RingHom.comp_apply, quadricChartOfPoly, eval₂Hom_C] at h
    exact h
  · rintro ⟨a, ha⟩
    obtain rfl := fin_two_eq_rev ha
    simp only [RingHom.comp_apply, chartOfPoly, eval₂Hom_X', AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, rename_X]
    rw [awayLift_chartRatio _ _ _ (quadricFstChartHom_X_self k i j), quadricFstChartHom,
      eval₂Hom_X', quadricChartToPoly_mk, quadricChart, quadricDehom_single]
    simp [quadricChartExp, pi_single_rev]

theorem quadricChartToPoly_awayLift_snd (i j : Fin 2) :
    ((quadricChartToPoly k i j).comp (awayLift (𝒜 := 𝒮)
        (quadricSndChartHom k (quadricChart_mem k i j) i) (X j)
        (isUnit_quadricSndChartHom k i j))).comp (chartOfPoly k j) =
      (rename fun _ => (1 : Fin 2)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, chartOfPoly, eval₂Hom_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, rename_C]
    rw [chartConst, RingHom.comp_apply, awayLift_fromZeroRingHom (𝒜 := 𝒮)]
    change quadricChartToPoly k i j (quadricSndChartHom k _ i (C r)) = C r
    rw [quadricSndChartHom, eval₂Hom_C]
    have h := RingHom.congr_fun (quadricChartToPoly_comp_chartOfPoly k i j) (C r)
    rw [RingHom.comp_apply, quadricChartOfPoly, eval₂Hom_C] at h
    exact h
  · rintro ⟨b, hb⟩
    obtain rfl := fin_two_eq_rev hb
    simp only [RingHom.comp_apply, chartOfPoly, eval₂Hom_X', AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, rename_X]
    rw [awayLift_chartRatio _ _ _ (quadricSndChartHom_X_self k i j), quadricSndChartHom,
      eval₂Hom_X', quadricChartToPoly_mk, quadricChart, quadricDehom_single]
    simp [quadricChartExp, pi_single_rev]

theorem injective_awayLift_quadricFstChartHom (i j : Fin 2) :
    Function.Injective (awayLift (𝒜 := 𝒮) (quadricFstChartHom k (quadricChart_mem k i j) j) (X i)
      (isUnit_quadricFstChartHom k i j)) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ : ∃ p, chartOfPoly k i p = x :=
    ⟨chartToPoly k i x, RingHom.congr_fun (chartOfPoly_comp_chartToPoly k i) x⟩
  obtain ⟨q, rfl⟩ : ∃ q, chartOfPoly k i q = y :=
    ⟨chartToPoly k i y, RingHom.congr_fun (chartOfPoly_comp_chartToPoly k i) y⟩
  have h := congrArg (quadricChartToPoly k i j) hxy
  have hp := RingHom.congr_fun (quadricChartToPoly_awayLift_fst k i j) p
  have hq := RingHom.congr_fun (quadricChartToPoly_awayLift_fst k i j) q
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp hq
  rw [hp, hq] at h
  rw [rename_injective _ (fun a b _ => fin_two_subtype_subsingleton i a b) h]

theorem injective_awayLift_quadricSndChartHom (i j : Fin 2) :
    Function.Injective (awayLift (𝒜 := 𝒮) (quadricSndChartHom k (quadricChart_mem k i j) i) (X j)
      (isUnit_quadricSndChartHom k i j)) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ : ∃ p, chartOfPoly k j p = x :=
    ⟨chartToPoly k j x, RingHom.congr_fun (chartOfPoly_comp_chartToPoly k j) x⟩
  obtain ⟨q, rfl⟩ : ∃ q, chartOfPoly k j q = y :=
    ⟨chartToPoly k j y, RingHom.congr_fun (chartOfPoly_comp_chartToPoly k j) y⟩
  have h := congrArg (quadricChartToPoly k i j) hxy
  have hp := RingHom.congr_fun (quadricChartToPoly_awayLift_snd k i j) p
  have hq := RingHom.congr_fun (quadricChartToPoly_awayLift_snd k i j) q
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hp hq
  rw [hp, hq] at h
  rw [rename_injective _ (fun a b _ => fin_two_subtype_subsingleton j a b) h]

theorem quadricProjOne_genericPoint :
    (quadricProjOne k).base (genericPoint (quadricSurface k)) = genericPoint (Proj 𝒮) := by
  have : IsDomain (projChart 𝒬 (quadricChart k 0 0)) :=
    isDomain_projChart 𝒬 (quadricChart_ne_zero k 0 0)
  have : IsDomain (projChart 𝒮 (X 0)) := isDomain_projChart 𝒮 (X_ne_zero 0)
  rw [← projChartι_genericPoint 𝒬 (quadricChart_mem k 0 0) Nat.one_pos]
  have e := congrArg (fun φ => φ.base (genericPoint (Spec (projChart 𝒬 (quadricChart k 0 0)))))
    (awayι_comp_quadricProjOne k 0 0)
  refine e.trans ?_
  refine (congrArg (Proj.awayι 𝒮 (X 0) (X_mem_homogeneousSubmodule_one k 0) Nat.one_pos).base
    (SpecMap_base_genericPoint (R := projChart 𝒮 (X 0)) (S := projChart 𝒬 (quadricChart k 0 0)) _
      (injective_awayLift_quadricFstChartHom k 0 0))).trans ?_
  exact projChartι_genericPoint 𝒮 _ _

theorem quadricProjTwo_genericPoint :
    (quadricProjTwo k).base (genericPoint (quadricSurface k)) = genericPoint (Proj 𝒮) := by
  have : IsDomain (projChart 𝒬 (quadricChart k 0 0)) :=
    isDomain_projChart 𝒬 (quadricChart_ne_zero k 0 0)
  have : IsDomain (projChart 𝒮 (X 0)) := isDomain_projChart 𝒮 (X_ne_zero 0)
  rw [← projChartι_genericPoint 𝒬 (quadricChart_mem k 0 0) Nat.one_pos]
  have e := congrArg (fun φ => φ.base (genericPoint (Spec (projChart 𝒬 (quadricChart k 0 0)))))
    (awayι_comp_quadricProjTwo k 0 0)
  refine e.trans ?_
  refine (congrArg (Proj.awayι 𝒮 (X 0) (X_mem_homogeneousSubmodule_one k 0) Nat.one_pos).base
    (SpecMap_base_genericPoint (R := projChart 𝒮 (X 0)) (S := projChart 𝒬 (quadricChart k 0 0)) _
      (injective_awayLift_quadricSndChartHom k 0 0))).trans ?_
  exact projChartι_genericPoint 𝒮 _ _

end Dominance

section FunctionField

theorem homogeneousLocalization_mk_X_eq_chartRatio (a b : Fin (1 + 1)) :
    (HomogeneousLocalization.mk ⟨1, ⟨X a, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X k a)⟩,
      ⟨X b, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X k b)⟩, ⟨1, pow_one _⟩⟩ :
        Away 𝒮 (X b)) = chartRatio k b a := by
  apply HomogeneousLocalization.val_injective
  rw [chartRatio, Away.val_mk, HomogeneousLocalization.val_mk]
  congr 1
  exact Subtype.ext (pow_one _).symm

theorem away_mk_eq_projDehom {f a : QuadricRing k} (f_deg : f ∈ 𝒬 1) (ha : a ∈ 𝒬 1)
    (ha' : a ∈ 𝒬 (1 • 1)) : Away.mk 𝒬 f_deg 1 a ha' = projDehom 𝒬 f_deg ha := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, projDehom, HomogeneousLocalization.val_mk]

/-- **`p₁` pulls `x₀ / x₁` back to `s₀u₀ / s₁u₀`.** -/
theorem quadricProjOne_homogeneousFraction :
    (quadricProjOne k).genericFunctionFieldMap (quadricProjOne_genericPoint k)
        (homogeneousFraction (isHomogeneous_X k (0 : Fin (1 + 1))) (isHomogeneous_X k 1)
          (X_ne_zero 1)) =
      projHomogeneousFraction 𝒬 (quadricChart_mem k 0 0) (quadricChart_mem k 1 0)
        (quadricChart_ne_zero k 1 0) := by
  have : IsDomain (projChart 𝒬 (quadricChart k 1 0)) :=
    isDomain_projChart 𝒬 (quadricChart_ne_zero k 1 0)
  have : IsDomain (projChart 𝒮 (X 1)) := isDomain_projChart 𝒮 (X_ne_zero 1)
  have hιQ := projChartι_genericPoint 𝒬 (quadricChart_mem k 1 0) Nat.one_pos
  have hιP := projChartι_genericPoint 𝒮 (X_mem_homogeneousSubmodule_one k 1) Nat.one_pos
  have hφ := SpecMap_base_genericPoint (R := projChart 𝒮 (X 1))
    (S := projChart 𝒬 (quadricChart k 1 0)) _ (injective_awayLift_quadricFstChartHom k 1 0)
  have hcomp : (projChartι 𝒬 (quadricChart_mem k 1 0) Nat.one_pos ≫ quadricProjOne k).base
      (genericPoint _) = genericPoint (Proj 𝒮) := by
    exact (congrArg (quadricProjOne k).base hιQ).trans (quadricProjOne_genericPoint k)
  have hcomp' : (Spec.map (CommRingCat.ofHom (awayLift (𝒜 := 𝒮)
      (quadricFstChartHom k (quadricChart_mem k 1 0) 0) (X 1)
      (isUnit_quadricFstChartHom k 1 0))) ≫
        projChartι 𝒮 (X_mem_homogeneousSubmodule_one k 1) Nat.one_pos).base
      (genericPoint _) = genericPoint (Proj 𝒮) :=
    (congrArg (projChartι 𝒮 (X_mem_homogeneousSubmodule_one k 1) Nat.one_pos).base hφ).trans hιP
  have hEq : projChartι 𝒬 (quadricChart_mem k 1 0) Nat.one_pos ≫ quadricProjOne k =
      Spec.map (CommRingCat.ofHom (awayLift (𝒜 := 𝒮)
        (quadricFstChartHom k (quadricChart_mem k 1 0) 0) (X 1)
        (isUnit_quadricFstChartHom k 1 0))) ≫
        projChartι 𝒮 (X_mem_homogeneousSubmodule_one k 1) Nat.one_pos :=
    awayι_comp_quadricProjOne k 1 0
  apply ((projChartι 𝒬 (quadricChart_mem k 1 0) Nat.one_pos).genericFunctionFieldMap
    hιQ).hom.injective
  have e1 := (Scheme.Hom.genericFunctionFieldMap_comp _ _ hιQ (quadricProjOne_genericPoint k)
    hcomp).symm.trans ((Scheme.Hom.genericFunctionFieldMap_congr hEq hcomp hcomp').trans
      (Scheme.Hom.genericFunctionFieldMap_comp _ _ hφ hιP hcomp'))
  have e2 := congrArg (fun F => F.hom (homogeneousFraction (isHomogeneous_X k (0 : Fin (1 + 1)))
    (isHomogeneous_X k 1) (X_ne_zero 1))) e1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  refine e2.trans ?_
  have hR := genericFunctionFieldMap_projChartι_projHomogeneousFraction 𝒬
    (quadricChart_mem k 1 0) (quadricChart_ne_zero k 1 0) (quadricChart_mem k 0 0)
    (quadricChart_mem k 1 0) (quadricChart_ne_zero k 1 0)
  dsimp only at hR
  rw [hR, projDehom_self]
  erw [map_one]
  rw [div_one, homogeneousFraction, hypersurfaceChartEquation,
    genericFunctionFieldMap_projChartι_germ, homogeneousLocalization_mk_X_eq_chartRatio]
  refine (genericFunctionFieldMap_SpecMap_algebraMap (R := projChart 𝒮 (X 1))
    (S := projChart 𝒬 (quadricChart k 1 0)) (CommRingCat.ofHom (awayLift (𝒜 := 𝒮)
      (quadricFstChartHom k (quadricChart_mem k 1 0) 0) (X 1)
      (isUnit_quadricFstChartHom k 1 0))) hφ (chartRatio k 1 0)).trans ?_
  congr 1
  refine (awayLift_chartRatio (quadricFstChartHom k (quadricChart_mem k 1 0) 0) 1 0
    (quadricFstChartHom_X_self k 1 0) (isUnit_quadricFstChartHom k 1 0)).trans ?_
  rw [quadricFstChartHom, eval₂Hom_X', away_mk_eq_projDehom k _ (quadricChart_mem k 0 0)]

/-- **`p₂` pulls `x₀ / x₁` back to `s₀u₀ / s₀u₁`.** -/
theorem quadricProjTwo_homogeneousFraction :
    (quadricProjTwo k).genericFunctionFieldMap (quadricProjTwo_genericPoint k)
        (homogeneousFraction (isHomogeneous_X k (0 : Fin (1 + 1))) (isHomogeneous_X k 1)
          (X_ne_zero 1)) =
      projHomogeneousFraction 𝒬 (quadricChart_mem k 0 0) (quadricChart_mem k 0 1)
        (quadricChart_ne_zero k 0 1) := by
  have : IsDomain (projChart 𝒬 (quadricChart k 0 1)) :=
    isDomain_projChart 𝒬 (quadricChart_ne_zero k 0 1)
  have : IsDomain (projChart 𝒮 (X 1)) := isDomain_projChart 𝒮 (X_ne_zero 1)
  have hιQ := projChartι_genericPoint 𝒬 (quadricChart_mem k 0 1) Nat.one_pos
  have hιP := projChartι_genericPoint 𝒮 (X_mem_homogeneousSubmodule_one k 1) Nat.one_pos
  have hφ := SpecMap_base_genericPoint (R := projChart 𝒮 (X 1))
    (S := projChart 𝒬 (quadricChart k 0 1)) _ (injective_awayLift_quadricSndChartHom k 0 1)
  have hcomp : (projChartι 𝒬 (quadricChart_mem k 0 1) Nat.one_pos ≫ quadricProjTwo k).base
      (genericPoint _) = genericPoint (Proj 𝒮) := by
    exact (congrArg (quadricProjTwo k).base hιQ).trans (quadricProjTwo_genericPoint k)
  have hcomp' : (Spec.map (CommRingCat.ofHom (awayLift (𝒜 := 𝒮)
      (quadricSndChartHom k (quadricChart_mem k 0 1) 0) (X 1)
      (isUnit_quadricSndChartHom k 0 1))) ≫
        projChartι 𝒮 (X_mem_homogeneousSubmodule_one k 1) Nat.one_pos).base
      (genericPoint _) = genericPoint (Proj 𝒮) :=
    (congrArg (projChartι 𝒮 (X_mem_homogeneousSubmodule_one k 1) Nat.one_pos).base hφ).trans hιP
  have hEq : projChartι 𝒬 (quadricChart_mem k 0 1) Nat.one_pos ≫ quadricProjTwo k =
      Spec.map (CommRingCat.ofHom (awayLift (𝒜 := 𝒮)
        (quadricSndChartHom k (quadricChart_mem k 0 1) 0) (X 1)
        (isUnit_quadricSndChartHom k 0 1))) ≫
        projChartι 𝒮 (X_mem_homogeneousSubmodule_one k 1) Nat.one_pos :=
    awayι_comp_quadricProjTwo k 0 1
  apply ((projChartι 𝒬 (quadricChart_mem k 0 1) Nat.one_pos).genericFunctionFieldMap
    hιQ).hom.injective
  have e1 := (Scheme.Hom.genericFunctionFieldMap_comp _ _ hιQ (quadricProjTwo_genericPoint k)
    hcomp).symm.trans ((Scheme.Hom.genericFunctionFieldMap_congr hEq hcomp hcomp').trans
      (Scheme.Hom.genericFunctionFieldMap_comp _ _ hφ hιP hcomp'))
  have e2 := congrArg (fun F => F.hom (homogeneousFraction (isHomogeneous_X k (0 : Fin (1 + 1)))
    (isHomogeneous_X k 1) (X_ne_zero 1))) e1
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  refine e2.trans ?_
  have hR := genericFunctionFieldMap_projChartι_projHomogeneousFraction 𝒬
    (quadricChart_mem k 0 1) (quadricChart_ne_zero k 0 1) (quadricChart_mem k 0 0)
    (quadricChart_mem k 0 1) (quadricChart_ne_zero k 0 1)
  dsimp only at hR
  rw [hR, projDehom_self]
  erw [map_one]
  rw [div_one, homogeneousFraction, hypersurfaceChartEquation,
    genericFunctionFieldMap_projChartι_germ, homogeneousLocalization_mk_X_eq_chartRatio]
  refine (genericFunctionFieldMap_SpecMap_algebraMap (R := projChart 𝒮 (X 1))
    (S := projChart 𝒬 (quadricChart k 0 1)) (CommRingCat.ofHom (awayLift (𝒜 := 𝒮)
      (quadricSndChartHom k (quadricChart_mem k 0 1) 0) (X 1)
      (isUnit_quadricSndChartHom k 0 1))) hφ (chartRatio k 1 0)).trans ?_
  congr 1
  refine (awayLift_chartRatio (quadricSndChartHom k (quadricChart_mem k 0 1) 0) 1 0
    (quadricSndChartHom_X_self k 0 1) (isUnit_quadricSndChartHom k 0 1)).trans ?_
  rw [quadricSndChartHom, eval₂Hom_X', away_mk_eq_projDehom k _ (quadricChart_mem k 0 0)]

end FunctionField

section Lines

theorem quadricChart_mem_lineOne (b : Fin 2) :
    quadricChart k 0 b ∈ (quadricLineOne k).asHomogeneousIdeal :=
  single_mem_quadricLineIdeal k quadricExpS (by fin_cases b <;> decide) 1

theorem quadricChart_notMem_lineOne (b : Fin 2) :
    quadricChart k 1 b ∉ (quadricLineOne k).asHomogeneousIdeal := fun h =>
  (mem_quadricLineIdeal_iff k quadricExpS _).mp h (quadricChartExp 1 b)
    (by simp [quadricChart, AddMonoidAlgebra.coeff_single]) (by fin_cases b <;> rfl)

theorem quadricChart_mem_lineTwo (a : Fin 2) :
    quadricChart k a 0 ∈ (quadricLineTwo k).asHomogeneousIdeal :=
  single_mem_quadricLineIdeal k quadricExpU (by fin_cases a <;> decide) 1

theorem quadricChart_notMem_lineTwo (a : Fin 2) :
    quadricChart k a 1 ∉ (quadricLineTwo k).asHomogeneousIdeal := fun h =>
  (mem_quadricLineIdeal_iff k quadricExpU _).mp h (quadricChartExp a 1)
    (by simp [quadricChart, AddMonoidAlgebra.coeff_single]) (by fin_cases a <;> rfl)

theorem quadricLineOne_eq_of_mem {j : Fin 2} {z : quadricSurface k}
    (hz : z ∈ Proj.basicOpen 𝒬 (quadricChart k 1 j)) (hz1 : Order.coheight z = 1)
    (hmem : quadricChart k 0 j ∈ z.asHomogeneousIdeal) : z = quadricLineOne k := by
  have hz' := (Proj.mem_basicOpen 𝒬 _ _).mp hz
  have h00 : quadricChart k 0 0 ∈ z.asHomogeneousIdeal := by
    obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · exact hmem
    · have hprod : quadricChart k 0 0 * quadricChart k 1 1 ∈ z.asHomogeneousIdeal := by
        rw [quadricChart_mul_swap k 0 1 1 0]
        exact z.asHomogeneousIdeal.toIdeal.mul_mem_right _ hmem
      exact (z.isPrime.mem_or_mem hprod).resolve_right hz'
  rcases eq_quadricLine_of_notMem_basicOpen k hz1
      (fun h => (Proj.mem_basicOpen 𝒬 _ _).mp h h00) with h | h
  · exact h
  · exfalso
    subst h
    obtain rfl | rfl : j = 0 ∨ j = 1 := by fin_cases j <;> simp
    · exact hz' (quadricChart_mem_lineTwo k 1)
    · exact quadricChart_notMem_lineTwo k 0 hmem

theorem quadricLineTwo_eq_of_mem {i : Fin 2} {z : quadricSurface k}
    (hz : z ∈ Proj.basicOpen 𝒬 (quadricChart k i 1)) (hz1 : Order.coheight z = 1)
    (hmem : quadricChart k i 0 ∈ z.asHomogeneousIdeal) : z = quadricLineTwo k := by
  have hz' := (Proj.mem_basicOpen 𝒬 _ _).mp hz
  have h00 : quadricChart k 0 0 ∈ z.asHomogeneousIdeal := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · exact hmem
    · have hprod : quadricChart k 0 0 * quadricChart k 1 1 ∈ z.asHomogeneousIdeal := by
        rw [quadricChart_mul_swap k 0 1 1 0]
        exact z.asHomogeneousIdeal.toIdeal.mul_mem_left _ hmem
      exact (z.isPrime.mem_or_mem hprod).resolve_right hz'
  rcases eq_quadricLine_of_notMem_basicOpen k hz1
      (fun h => (Proj.mem_basicOpen 𝒬 _ _).mp h h00) with h | h
  · exfalso
    subst h
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · exact hz' (quadricChart_mem_lineOne k 1)
    · exact quadricChart_notMem_lineOne k 0 hmem
  · exact h

/-- On `D₊(s₁uⱼ)`, the line `L₁` is the divisor of `s₀u₀ / s₁u₀`. -/
theorem quadricLineOne_apply_eq_ord (j : Fin 2) {z : quadricSurface k}
    (hz : z ∈ Proj.basicOpen 𝒬 (quadricChart k 1 j)) (hz1 : Order.coheight z = 1) :
    (quadricLineOneDivisor k).toWeilDivisor.1 z =
      (quadricSurface k).ord (projHomogeneousFraction 𝒬 (quadricChart_mem k 0 0)
        (quadricChart_mem k 1 0) (quadricChart_ne_zero k 1 0)) z := by
  by_cases hzL : z = quadricLineOne k
  · subst hzL
    exact ((quadricLineOneDivisor k).toWeilDivisor_apply_self).trans
      (ord_quadricLineOne_projHomogeneousFraction k).symm
  · rw [(quadricLineOneDivisor k).toWeilDivisor_apply_of_ne hzL]
    have hsj : quadricChart k 0 j ∉ z.asHomogeneousIdeal := fun h =>
      hzL (quadricLineOne_eq_of_mem k hz hz1 h)
    rw [projHomogeneousFraction_eq_of_mul_eq 𝒬 (quadricChart_mem k 0 0) (quadricChart_mem k 1 0)
      (quadricChart_ne_zero k 1 0) (quadricChart_mem k 0 j) (quadricChart_mem k 1 j)
      (quadricChart_ne_zero k 1 j) (quadricChart_mul_swap k 0 1 j 0)]
    obtain ⟨y, rfl⟩ := quadric_exists_chart_point k hz
    have h := ord_projHomogeneousFraction_quadricChart k (quadricChart_mem k 0 j)
      (quadricChart_ne_zero k 0 j) hz1
    dsimp only at h
    rw [h]
    exact (ord_quadric_projDehom_eq_zero k (quadricChart_mem k 0 j) (quadricChart_ne_zero k 0 j)
      hz1 hsj).symm

/-- On `D₊(sᵢu₁)`, the line `L₂` is the divisor of `s₀u₀ / s₀u₁`. -/
theorem quadricLineTwo_apply_eq_ord (i : Fin 2) {z : quadricSurface k}
    (hz : z ∈ Proj.basicOpen 𝒬 (quadricChart k i 1)) (hz1 : Order.coheight z = 1) :
    (quadricLineTwoDivisor k).toWeilDivisor.1 z =
      (quadricSurface k).ord (projHomogeneousFraction 𝒬 (quadricChart_mem k 0 0)
        (quadricChart_mem k 0 1) (quadricChart_ne_zero k 0 1)) z := by
  by_cases hzL : z = quadricLineTwo k
  · subst hzL
    exact ((quadricLineTwoDivisor k).toWeilDivisor_apply_self).trans
      (ord_quadricLineTwo_projHomogeneousFraction k).symm
  · rw [(quadricLineTwoDivisor k).toWeilDivisor_apply_of_ne hzL]
    have hsi : quadricChart k i 0 ∉ z.asHomogeneousIdeal := fun h =>
      hzL (quadricLineTwo_eq_of_mem k hz hz1 h)
    rw [projHomogeneousFraction_eq_of_mul_eq 𝒬 (quadricChart_mem k 0 0) (quadricChart_mem k 0 1)
      (quadricChart_ne_zero k 0 1) (quadricChart_mem k i 0) (quadricChart_mem k i 1)
      (quadricChart_ne_zero k i 1) ((quadricChart_mul_swap k 0 i 1 0).trans (mul_comm _ _))]
    obtain ⟨y, rfl⟩ := quadric_exists_chart_point k hz
    have h := ord_projHomogeneousFraction_quadricChart k (quadricChart_mem k i 0)
      (quadricChart_ne_zero k i 0) hz1
    dsimp only at h
    rw [h]
    exact (ord_quadric_projDehom_eq_zero k (quadricChart_mem k i 0) (quadricChart_ne_zero k i 0)
      hz1 hsi).symm

theorem quadricLineOne_apply_of_mem (j : Fin 2) {z : quadricSurface k}
    (hz : z ∈ Proj.basicOpen 𝒬 (quadricChart k 0 j)) :
    (quadricLineOneDivisor k).toWeilDivisor.1 z = 0 := by
  refine (quadricLineOneDivisor k).toWeilDivisor_apply_of_ne fun h => ?_
  rw [h] at hz
  exact (Proj.mem_basicOpen 𝒬 _ _).mp hz (quadricChart_mem_lineOne k j)

theorem quadricLineTwo_apply_of_mem (i : Fin 2) {z : quadricSurface k}
    (hz : z ∈ Proj.basicOpen 𝒬 (quadricChart k i 0)) :
    (quadricLineTwoDivisor k).toWeilDivisor.1 z = 0 := by
  refine (quadricLineTwoDivisor k).toWeilDivisor_apply_of_ne fun h => ?_
  rw [h] at hz
  exact (Proj.mem_basicOpen 𝒬 _ _).mp hz (quadricChart_mem_lineTwo k i)

end Lines

section Hyperplane

/-- The point `x₀ = 0` of `ℙ¹_k`, as a prime divisor. -/
abbrev projectiveLinePointZero : (Proj 𝒮).PrimeDivisor :=
  projectiveHyperplanePrimeDivisor (k := k) (n := 1) Nat.one_pos
    (isHomogeneous_X k (0 : Fin (1 + 1))) (X_ne_zero 0)

/-- On `D₊(x₁)`, the point `x₀ = 0` is the divisor of `x₀ / x₁`. -/
theorem projectiveLinePointZero_apply_eq_ord {y : Proj 𝒮} (hy : y ∈ Proj.basicOpen 𝒮 (X 1))
    (hy1 : Order.coheight y = 1) :
    (projectiveLinePointZero k).toWeilDivisor.1 y = (Proj 𝒮).ord
      (homogeneousFraction (isHomogeneous_X k (0 : Fin (1 + 1))) (isHomogeneous_X k 1)
        (X_ne_zero 1)) y := by
  have h := toWeilDivisor_apply_primeDivisor (projectiveLinePointZero k) ⟨y, hy1⟩
  refine h.trans ?_
  rw [ord_homogeneousFraction_irreducible (n := 1) Nat.one_pos (isHomogeneous_X k 0)
    (irreducible_of_isHomogeneous_one (isHomogeneous_X k 0) (X_ne_zero 0)) (isHomogeneous_X k 1)
    (X_ne_zero 1) ⟨y, hy1⟩ hy]
  rfl

theorem projectiveLinePointZero_apply_of_mem {y : Proj 𝒮} (hy : y ∈ Proj.basicOpen 𝒮 (X 0)) :
    (projectiveLinePointZero k).toWeilDivisor.1 y = 0 := by
  refine (projectiveLinePointZero k).toWeilDivisor_apply_of_ne fun h => ?_
  rw [h] at hy
  exact (Proj.mem_basicOpen 𝒮 _ _).mp hy (Ideal.mem_span_singleton_self _)

end Hyperplane

section ClassGroup

theorem quadricSurface_isLocallyFactorial : (quadricSurface k).IsLocallyFactorial :=
  Scheme.isLocallyFactorial_of_isRegularLocalRing _ (quadricSurface_isRegular k).2

theorem projectiveLine_isLocallyFactorial : (Proj 𝒮).IsLocallyFactorial :=
  Scheme.isLocallyFactorial_of_isRegularLocalRing _ (projectiveSpace_isRegular (k := k) (n := 1)).2

local notation "hQ" => quadricSurface_satisfiesConditionStar k

local notation "hP" => projectiveSpace_satisfiesConditionStar (k := k) (n := 1)

/-- **The pullback `p₁^* : Cl ℙ¹_k ⟶ Cl Q`**: `Cl ℙ¹_k ≅ Pic ℙ¹_k ⟶ Pic Q ≅ Cl Q`, through the
Picard pullback along the first projection. -/
def quadricClassGroupPullbackOne : (Proj 𝒮).WeilClassGroup hP →+ (quadricSurface k).WeilClassGroup hQ :=
  ((Scheme.weilClassEquivPicard (quadricSurface_isLocallyFactorial k)).symm.toAddMonoidHom.comp
    (Ringed.Pic.pullback (quadricProjOne k)).toAdditive).comp
      (Scheme.weilClassEquivPicard (projectiveLine_isLocallyFactorial k)).toAddMonoidHom

/-- **The pullback `p₂^* : Cl ℙ¹_k ⟶ Cl Q`**: `Cl ℙ¹_k ≅ Pic ℙ¹_k ⟶ Pic Q ≅ Cl Q`, through the
Picard pullback along the second projection. -/
def quadricClassGroupPullbackTwo : (Proj 𝒮).WeilClassGroup hP →+ (quadricSurface k).WeilClassGroup hQ :=
  ((Scheme.weilClassEquivPicard (quadricSurface_isLocallyFactorial k)).symm.toAddMonoidHom.comp
    (Ringed.Pic.pullback (quadricProjTwo k)).toAdditive).comp
      (Scheme.weilClassEquivPicard (projectiveLine_isLocallyFactorial k)).toAddMonoidHom

/-- **`p₁^*` of a point is a ruling line**: `p₁^*` sends the class of the point `x₀ = 0` of `ℙ¹_k`
to the class of the line `L₁ = {s₀ = 0}`, its fibre. -/
theorem quadricClassGroupPullbackOne_pointZero :
    quadricClassGroupPullbackOne k ((Proj 𝒮).weilDivisorClassHom hP
        (projectiveLinePointZero k).toWeilDivisor) =
      (quadricSurface k).weilDivisorClassHom hQ (quadricLineOneDivisor k).toWeilDivisor := by
  apply (Scheme.weilClassEquivPicard (quadricSurface_isLocallyFactorial k)).injective
  simp only [quadricClassGroupPullbackOne, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  have h := Scheme.picPullback_weilClassEquivPicard (quadricProjOne k)
    (quadricProjOne_genericPoint k) (quadricSurface_isLocallyFactorial k)
    (projectiveLine_isLocallyFactorial k) (projectiveLinePointZero k).toWeilDivisor
    (quadricLineOneDivisor k).toWeilDivisor ?_
  · exact congrArg Additive.ofMul h
  intro x
  have hx : x ∈ ⨆ ij : Fin 2 × Fin 2, Proj.basicOpen 𝒬 (quadricChart k ij.1 ij.2) := by
    rw [quadricSurface_iSup_basicOpen]
    trivial
  obtain ⟨⟨i, j⟩, hxij⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  · refine ⟨Proj.basicOpen 𝒮 (X 0), Proj.basicOpen 𝒬 (quadricChart k 0 j), 1, hxij,
      basicOpen_le_preimage_quadricProjOne k 0 j, fun y hy _ => ?_, fun z hz _ => ?_⟩
    · rw [projectiveLinePointZero_apply_of_mem k hy, Units.val_one, Scheme.ord_one_eq_zero]
    · rw [quadricLineOne_apply_of_mem k j hz, Units.val_one, map_one, Scheme.ord_one_eq_zero]
  · refine ⟨Proj.basicOpen 𝒮 (X 1), Proj.basicOpen 𝒬 (quadricChart k 1 j),
      homogeneousFractionUnit (isHomogeneous_X k (0 : Fin (1 + 1))) (isHomogeneous_X k 1)
        (X_ne_zero 1) (X_ne_zero 0), hxij,
      basicOpen_le_preimage_quadricProjOne k 1 j, fun y hy hy1 => ?_, fun z hz hz1 => ?_⟩
    · exact projectiveLinePointZero_apply_eq_ord k hy hy1
    · rw [homogeneousFractionUnit, Units.val_mk0, quadricProjOne_homogeneousFraction]
      exact quadricLineOne_apply_eq_ord k j hz hz1

end ClassGroup

end Hartshorne
