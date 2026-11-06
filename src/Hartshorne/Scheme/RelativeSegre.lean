/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjChartMorphism
import Hartshorne.Scheme.ProjectiveSpaceOverScheme

/-!
# The relative Segre embedding

Hartshorne, *Algebraic Geometry*, II.4, Exercise 4.9.

For natural numbers `r, s` we construct the Segre morphism
`ℙʳ_ℤ ×_ℤ ℙˢ_ℤ ⟶ ℙ^{rs+r+s}_ℤ` with homogeneous coordinates `z_{ij} = xᵢ yⱼ`, where the
coordinates of `ℙ^{rs+r+s}` are indexed by pairs `(i, j)` through `segreIndex`.

* On the chart `D₊(xᵢ) ×_ℤ D₊(yⱼ)` the morphism is `Spec` of the ring map sending `z_{kl}` to
  `(xₖ/xᵢ)(yₗ/yⱼ)` (`segreChartRingMap`); these chart morphisms agree on overlaps by the cocycle
  identity for coordinate ratios, and glue to `segreMorphismInt`.
* The preimage of `D₊(z_{ij})` is exactly `D₊(xᵢ) ×_ℤ D₊(yⱼ)`
  (`segreMorphismInt_preimage_basicOpen`), and there the pullback of `z_{kl}/z_{ij}` is
  `(xₖ/xᵢ)(yₗ/yⱼ)` (`segreMorphismInt_appLE_chartRatio`).
* Over `D₊(z_{ij})` the morphism has the retraction given by `xₖ/xᵢ ↦ z_{kj}/z_{ij}` and
  `yₗ/yⱼ ↦ z_{il}/z_{ij}`; a section of a separated morphism is a closed immersion, and closed
  immersions are local on the target, so the Segre morphism is a closed immersion.

For a scheme `Y`, the relative Segre morphism `relativeSegre r s Y : ℙʳ_Y ×_Y ℙˢ_Y ⟶ ℙ^{rs+r+s}_Y`
is the base change of the morphism over the integers (`relativeSegre_isPullback`); it is a
closed immersion over `Y`, and it is compatible with arbitrary base change `Y' ⟶ Y`
(`relativeSegre_baseChange`). The main statement is `relativeSegre_spec`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomogeneousLocalization MvPolynomial

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ulift_int_ringHom_ext {B : Type*} [Ring B] (f g : ULift.{u} ℤ →+* B) : f = g := by
  ext ⟨n⟩
  have h : (ULift.up n : ULift.{u} ℤ) = ((n : ℤ) : ULift.{u} ℤ) := by
    apply ULift.down_injective
    simp
  rw [h, map_intCast, map_intCast]

/-- The polynomial grading on the homogeneous coordinate ring of projective `n`-space over
the integers. -/
abbrev segreGrading (n : ℕ) :=
  homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)

/-- The product `ℙʳ ×_ℤ ℙˢ` of projective spaces over the integers. -/
abbrev segreSource (r s : ℕ) : Scheme.{u} :=
  pullback (projectiveSpaceOverIntegersMap.{u} r) (projectiveSpaceOverIntegersMap.{u} s)

/-- The indexing of the coordinates of `ℙ^{rs+r+s}` by pairs. -/
def segreIndex (r s : ℕ) : Fin (r + 1) × Fin (s + 1) ≃ Fin (r * s + r + s + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

variable (r s : ℕ)

/-- The first projection `ℙʳ ×_ℤ ℙˢ ⟶ ℙʳ`, typed as a morphism to `Proj`. -/
abbrev segreFst : segreSource.{u} r s ⟶ Proj (segreGrading.{u} r) :=
  pullback.fst _ _

/-- The second projection `ℙʳ ×_ℤ ℙˢ ⟶ ℙˢ`, typed as a morphism to `Proj`. -/
abbrev segreSnd : segreSource.{u} r s ⟶ Proj (segreGrading.{u} s) :=
  pullback.snd _ _

/-- The open chart `D₊(xᵢ) ×_ℤ D₊(yⱼ)` of the product. -/
def segreChartOpen (i : Fin (r + 1)) (j : Fin (s + 1)) : (segreSource.{u} r s).Opens :=
  segreFst r s ⁻¹ᵁ Proj.basicOpen (segreGrading r) (X i) ⊓
    segreSnd r s ⁻¹ᵁ Proj.basicOpen (segreGrading s) (X j)




section SegreCharts

variable (r s : ℕ)

/-- The coordinate ratios `xₖ/xᵢ` of the first factor, pulled back to the chart `(i, j)`. -/
def segreFstSection (i : Fin (r + 1)) (j : Fin (s + 1)) :
    Away (segreGrading.{u} r) (X i) →+* Γ(segreSource.{u} r s, segreChartOpen r s i j) :=
  (Proj.awayToSection (segreGrading r) (X i) ≫
    (segreFst r s).appLE _ (segreChartOpen r s i j) inf_le_left).hom

/-- The coordinate ratios `yₗ/yⱼ` of the second factor, pulled back to the chart `(i, j)`. -/
def segreSndSection (i : Fin (r + 1)) (j : Fin (s + 1)) :
    Away (segreGrading.{u} s) (X j) →+* Γ(segreSource.{u} r s, segreChartOpen r s i j) :=
  (Proj.awayToSection (segreGrading s) (X j) ≫
    (segreSnd r s).appLE _ (segreChartOpen r s i j) inf_le_right).hom

/-- On the chart `(i, j)`, the Segre map sends `z_{kl}` to `(xₖ/xᵢ)(yₗ/yⱼ)`. -/
def segreChartRingMap (i : Fin (r + 1)) (j : Fin (s + 1)) :
    MvPolynomial (Fin (r * s + r + s + 1)) (ULift.{u} ℤ) →+*
      Γ(segreSource.{u} r s, segreChartOpen r s i j) :=
  eval₂Hom ((segreFstSection r s i j).comp (chartConst _ i)) fun c =>
    segreFstSection r s i j (chartRatio _ i ((segreIndex r s).symm c).1) *
      segreSndSection r s i j (chartRatio _ j ((segreIndex r s).symm c).2)

theorem segreChartRingMap_X (i : Fin (r + 1)) (j : Fin (s + 1)) (k : Fin (r + 1))
    (l : Fin (s + 1)) :
    segreChartRingMap.{u} r s i j (X (segreIndex r s (k, l))) =
      segreFstSection r s i j (chartRatio _ i k) * segreSndSection r s i j (chartRatio _ j l) := by
  simp [segreChartRingMap]

theorem segreChartRingMap_X_self (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreChartRingMap.{u} r s i j (X (segreIndex r s (i, j))) = 1 := by
  rw [segreChartRingMap_X, chartRatio_self, chartRatio_self, map_one, map_one, mul_one]

theorem isUnit_segreChartRingMap_X_self (i : Fin (r + 1)) (j : Fin (s + 1)) :
    IsUnit (segreChartRingMap.{u} r s i j (X (segreIndex r s (i, j)))) := by
  rw [segreChartRingMap_X_self]
  exact isUnit_one

/-- The Segre map on the chart `D₊(xᵢ) ×_ℤ D₊(yⱼ)`, landing in `D₊(z_{ij})`. -/
def segreChart (i : Fin (r + 1)) (j : Fin (s + 1)) :
    (segreChartOpen.{u} r s i j).toScheme ⟶ Proj (segreGrading.{u} (r * s + r + s)) :=
  (segreChartOpen r s i j).toSpecΓ ≫
    chartMap (segreChartRingMap r s i j) (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos
      (isUnit_segreChartRingMap_X_self r s i j)

theorem segreChartOpen_iSup :
    TopologicalSpace.IsOpenCover (fun c : Fin (r + 1) × Fin (s + 1) =>
      segreChartOpen.{u} r s c.1 c.2) := by
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ => ?_)
  have h1 : segreFst r s x ∈ ⨆ i, Proj.basicOpen (segreGrading.{u} r) (X i) := by
    rw [iSup_proj_basicOpen_X_eq_top]
    trivial
  have h2 : segreSnd r s x ∈ ⨆ j, Proj.basicOpen (segreGrading.{u} s) (X j) := by
    rw [iSup_proj_basicOpen_X_eq_top]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h1
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp h2
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), ⟨hi, hj⟩⟩

theorem segreFst_cocycle (i : Fin (r + 1)) (j : Fin (s + 1)) (k : Fin (r + 1))
    (l : Fin (s + 1)) (m : Fin (r + 1)) :
    (segreSource.{u} r s).presheaf.map
        (homOfLE (inf_le_right : segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _)).op
        (segreFstSection r s k l (chartRatio _ k m)) =
      (segreSource.{u} r s).presheaf.map
          (homOfLE (inf_le_right : segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _)).op
          (segreFstSection r s k l (chartRatio _ k i)) *
        (segreSource.{u} r s).presheaf.map
          (homOfLE (inf_le_left : segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _)).op
          (segreFstSection r s i j (chartRatio _ i m)) :=
  appLE_chartRatio_cocycle (segreFst r s) inf_le_left inf_le_right inf_le_left inf_le_left m

theorem segreSnd_cocycle (i : Fin (r + 1)) (j : Fin (s + 1)) (k : Fin (r + 1))
    (l : Fin (s + 1)) (m : Fin (s + 1)) :
    (segreSource.{u} r s).presheaf.map
        (homOfLE (inf_le_right : segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _)).op
        (segreSndSection r s k l (chartRatio _ l m)) =
      (segreSource.{u} r s).presheaf.map
          (homOfLE (inf_le_right : segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _)).op
          (segreSndSection r s k l (chartRatio _ l j)) *
        (segreSource.{u} r s).presheaf.map
          (homOfLE (inf_le_left : segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _)).op
          (segreSndSection r s i j (chartRatio _ j m)) :=
  appLE_chartRatio_cocycle (segreSnd r s) inf_le_left inf_le_right inf_le_right inf_le_right m

theorem segreChart_compat (c c' : Fin (r + 1) × Fin (s + 1)) :
    (segreSource.{u} r s).homOfLE
        (inf_le_left : segreChartOpen r s c.1 c.2 ⊓ segreChartOpen r s c'.1 c'.2 ≤ _) ≫
        segreChart r s c.1 c.2 =
      (segreSource.{u} r s).homOfLE
        (inf_le_right : segreChartOpen r s c.1 c.2 ⊓ segreChartOpen r s c'.1 c'.2 ≤ _) ≫
        segreChart r s c'.1 c'.2 := by
  obtain ⟨i, j⟩ := c
  obtain ⟨k, l⟩ := c'
  dsimp only
  set ρ := (segreSource.{u} r s).presheaf.map
    (homOfLE (inf_le_left : segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _)).op with hρ
  set ρ' := (segreSource.{u} r s).presheaf.map
    (homOfLE (inf_le_right : segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _)).op with hρ'
  -- units on the overlap
  have hu1 : IsUnit (ρ (segreFstSection r s i j (chartRatio _ i k))) := by
    have h := appLE_chartRatio_cocycle (segreFst r s) (inf_le_right :
      segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _) inf_le_left inf_le_left inf_le_left i
    change ρ (segreFstSection r s i j (chartRatio _ i i)) =
      ρ (segreFstSection r s i j (chartRatio _ i k)) *
        ρ' (segreFstSection r s k l (chartRatio _ k i)) at h
    rw [chartRatio_self, map_one, map_one] at h
    exact IsUnit.of_mul_eq_one _ h.symm
  have hu2 : IsUnit (ρ (segreSndSection r s i j (chartRatio _ j l))) := by
    have h := appLE_chartRatio_cocycle (segreSnd r s) (inf_le_right :
      segreChartOpen r s i j ⊓ segreChartOpen r s k l ≤ _) inf_le_left inf_le_right
        inf_le_right j
    change ρ (segreSndSection r s i j (chartRatio _ j j)) =
      ρ (segreSndSection r s i j (chartRatio _ j l)) *
        ρ' (segreSndSection r s k l (chartRatio _ l j)) at h
    rw [chartRatio_self, map_one, map_one] at h
    exact IsUnit.of_mul_eq_one _ h.symm
  have hunit_c : IsUnit ((ρ.hom.comp (segreChartRingMap r s i j)) (X (segreIndex r s (i, j)))) := by
    simp [segreChartRingMap_X_self]
  have hunit_c' : IsUnit ((ρ'.hom.comp (segreChartRingMap r s k l))
      (X (segreIndex r s (k, l)))) := by
    simp [segreChartRingMap_X_self]
  have hunit_x : IsUnit ((ρ.hom.comp (segreChartRingMap r s i j))
      (X (segreIndex r s (k, l)))) := by
    rw [RingHom.comp_apply, segreChartRingMap_X, map_mul]
    exact hu1.mul hu2
  simp only [segreChart]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, SpecMap_chartMap _ _ _ _ _ hunit_c,
    SpecMap_chartMap _ _ _ _ _ hunit_c']
  congr 1
  rw [chartMap_eq _ _ _ hunit_c (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos hunit_x]
  symm
  apply chartMap_eq_of_scale _ _ (ρ' (segreChartRingMap r s k l (X (segreIndex r s (i, j)))))
  intro n a ha
  have hgen : ∀ d, (ρ'.hom.comp (segreChartRingMap r s k l)) (X d) =
      ρ' (segreChartRingMap r s k l (X (segreIndex r s (i, j)))) *
        (ρ.hom.comp (segreChartRingMap r s i j)) (X d) := by
    intro d
    obtain ⟨⟨m, m'⟩, rfl⟩ := (segreIndex r s).surjective d
    rw [RingHom.comp_apply, RingHom.comp_apply, segreChartRingMap_X, segreChartRingMap_X,
      segreChartRingMap_X]
    change ρ' _ = ρ' _ * ρ _
    rw [map_mul, map_mul, map_mul, segreFst_cocycle r s i j k l m,
      segreSnd_cocycle r s i j k l m']
    ring
  have hcoef : (ρ'.hom.comp (segreChartRingMap r s k l)).comp C =
      (ρ.hom.comp (segreChartRingMap r s i j)).comp C := ulift_int_ringHom_ext _ _
  have hhom : a.IsHomogeneous n := (mem_homogeneousSubmodule n a).1 ha
  have e1 : (ρ'.hom.comp (segreChartRingMap r s k l)) a =
      eval₂ ((ρ.hom.comp (segreChartRingMap r s i j)).comp C)
        (fun d => ρ' (segreChartRingMap r s k l (X (segreIndex r s (i, j)))) *
          (ρ.hom.comp (segreChartRingMap r s i j)) (X d)) a := by
    conv_lhs => rw [← eval₂_eta a]
    rw [eval₂_comp_left, hcoef]
    congr 1
    funext d
    exact hgen d
  have e2 : (ρ.hom.comp (segreChartRingMap r s i j)) a =
      eval₂ ((ρ.hom.comp (segreChartRingMap r s i j)).comp C)
        (fun d => (ρ.hom.comp (segreChartRingMap r s i j)) (X d)) a := by
    conv_lhs => rw [← eval₂_eta a]
    rw [eval₂_comp_left]
    rfl
  rw [e1, e2, isHomogeneous_eval₂_mul_left hhom]

end SegreCharts

section SegreInt

variable (r s : ℕ)

/-- The Segre morphism `ℙʳ ×_ℤ ℙˢ ⟶ ℙ^{rs+r+s}` over the integers. -/
def segreMorphismInt : segreSource.{u} r s ⟶ Proj (segreGrading.{u} (r * s + r + s)) :=
  glueOpens (fun c : Fin (r + 1) × Fin (s + 1) => segreChartOpen r s c.1 c.2)
    (segreChartOpen_iSup r s) (fun c => segreChart r s c.1 c.2) (segreChart_compat r s)

@[reassoc (attr := simp)]
theorem ι_segreMorphismInt (i : Fin (r + 1)) (j : Fin (s + 1)) :
    (segreChartOpen r s i j).ι ≫ segreMorphismInt.{u} r s = segreChart r s i j :=
  ι_glueOpens (fun c : Fin (r + 1) × Fin (s + 1) => segreChartOpen r s c.1 c.2)
    (segreChartOpen_iSup r s) (fun c => segreChart r s c.1 c.2) (segreChart_compat r s) (i, j)

theorem ι_segreFst (k : Fin (r + 1)) (l : Fin (s + 1)) :
    (segreChartOpen r s k l).ι ≫ segreFst.{u} r s = (segreChartOpen r s k l).toSpecΓ ≫
      chartMap (chartPolyMap k (segreFstSection r s k l)) (X_mem_homogeneousSubmodule_one _ _)
        Nat.one_pos (isUnit_chartPolyMap_X_self _ _) := by
  rw [ι_comp_eq_toSpecΓ_SpecMap (segreFst r s) (segreChartOpen r s k l)
    (X_mem_homogeneousSubmodule_one _ k) Nat.one_pos (by exact inf_le_left), chartMap,
    ← eq_awayLift_chartPolyMap]
  rfl

theorem ι_segreSnd (k : Fin (r + 1)) (l : Fin (s + 1)) :
    (segreChartOpen r s k l).ι ≫ segreSnd.{u} r s = (segreChartOpen r s k l).toSpecΓ ≫
      chartMap (chartPolyMap l (segreSndSection r s k l)) (X_mem_homogeneousSubmodule_one _ _)
        Nat.one_pos (isUnit_chartPolyMap_X_self _ _) := by
  rw [ι_comp_eq_toSpecΓ_SpecMap (segreSnd r s) (segreChartOpen r s k l)
    (X_mem_homogeneousSubmodule_one _ l) Nat.one_pos (by exact inf_le_right), chartMap,
    ← eq_awayLift_chartPolyMap]
  rfl

theorem ι_preimage_segreFst_preimage (k i : Fin (r + 1)) (l : Fin (s + 1)) :
    (segreChartOpen r s k l).ι ⁻¹ᵁ segreFst.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X i) =
      (segreChartOpen r s k l).ι ⁻¹ᵁ
        (segreSource r s).basicOpen (segreFstSection r s k l (chartRatio _ k i)) := by
  rw [← Scheme.Hom.comp_preimage, ι_segreFst, Scheme.Hom.comp_preimage,
    chartMap_preimage_basicOpen _ _ _ _ (X_mem_homogeneousSubmodule_one _ i) Nat.one_pos,
    Scheme.Opens.toSpecΓ_preimage_basicOpen]
  simp [chartPolyMap]

theorem ι_preimage_segreSnd_preimage (k : Fin (r + 1)) (l j : Fin (s + 1)) :
    (segreChartOpen r s k l).ι ⁻¹ᵁ segreSnd.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X j) =
      (segreChartOpen r s k l).ι ⁻¹ᵁ
        (segreSource r s).basicOpen (segreSndSection r s k l (chartRatio _ l j)) := by
  rw [← Scheme.Hom.comp_preimage, ι_segreSnd, Scheme.Hom.comp_preimage,
    chartMap_preimage_basicOpen _ _ _ _ (X_mem_homogeneousSubmodule_one _ j) Nat.one_pos,
    Scheme.Opens.toSpecΓ_preimage_basicOpen]
  simp [chartPolyMap]

/-- The Segre morphism pulls the coordinate chart `D₊(z_{ij})` back to `D₊(xᵢ) ×_ℤ D₊(yⱼ)`. -/
theorem segreMorphismInt_preimage_basicOpen (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreMorphismInt.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X (segreIndex r s (i, j))) =
      segreChartOpen r s i j := by
  apply opens_eq_of_cover _ (segreChartOpen_iSup r s)
  rintro ⟨k, l⟩
  dsimp only
  rw [← Scheme.Hom.comp_preimage, ι_segreMorphismInt, segreChart, Scheme.Hom.comp_preimage,
    chartMap_preimage_basicOpen _ _ _ _ (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos,
    Scheme.Opens.toSpecΓ_preimage_basicOpen, segreChartRingMap_X, Scheme.basicOpen_mul]
  have hW : segreChartOpen r s i j = segreFst.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X i) ⊓
      segreSnd.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X j) := rfl
  rw [hW, Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, ι_preimage_segreFst_preimage,
    ι_preimage_segreSnd_preimage]

end SegreInt

section SegreClosed

variable (r s : ℕ)

/-- The coordinate ratios `z_{kj}/z_{ij}` give the first projection on `D₊(z_{ij})`. -/
def segreFstRetractRingMap (i : Fin (r + 1)) (j : Fin (s + 1)) :
    MvPolynomial (Fin (r + 1)) (ULift.{u} ℤ) →+*
      Away (segreGrading.{u} (r * s + r + s)) (X (segreIndex r s (i, j))) :=
  eval₂Hom (chartConst _ _) fun k => chartRatio _ (segreIndex r s (i, j)) (segreIndex r s (k, j))

/-- The coordinate ratios `z_{il}/z_{ij}` give the second projection on `D₊(z_{ij})`. -/
def segreSndRetractRingMap (i : Fin (r + 1)) (j : Fin (s + 1)) :
    MvPolynomial (Fin (s + 1)) (ULift.{u} ℤ) →+*
      Away (segreGrading.{u} (r * s + r + s)) (X (segreIndex r s (i, j))) :=
  eval₂Hom (chartConst _ _) fun l => chartRatio _ (segreIndex r s (i, j)) (segreIndex r s (i, l))

theorem segreFstRetractRingMap_X_self (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreFstRetractRingMap.{u} r s i j (X i) = 1 := by
  simp [segreFstRetractRingMap, chartRatio_self]

theorem segreSndRetractRingMap_X_self (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreSndRetractRingMap.{u} r s i j (X j) = 1 := by
  simp [segreSndRetractRingMap, chartRatio_self]

/-- The morphism `D₊(z_{ij}) ⟶ ℙʳ ×_ℤ ℙˢ` given by the two projections. -/
def segreRetractToSource (i : Fin (r + 1)) (j : Fin (s + 1)) :
    Spec (.of (Away (segreGrading.{u} (r * s + r + s)) (X (segreIndex r s (i, j))))) ⟶
      segreSource.{u} r s :=
  pullback.lift
    (chartMap (segreFstRetractRingMap r s i j) (X_mem_homogeneousSubmodule_one _ i) Nat.one_pos
      (by rw [segreFstRetractRingMap_X_self]; exact isUnit_one))
    (chartMap (segreSndRetractRingMap r s i j) (X_mem_homogeneousSubmodule_one _ j) Nat.one_pos
      (by rw [segreSndRetractRingMap_X_self]; exact isUnit_one))
    (specULiftZIsTerminal.{u}.hom_ext _ _)

@[reassoc]
theorem segreRetractToSource_fst (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreRetractToSource.{u} r s i j ≫ segreFst r s =
      chartMap (segreFstRetractRingMap r s i j) (X_mem_homogeneousSubmodule_one _ i)
        Nat.one_pos (by rw [segreFstRetractRingMap_X_self]; exact isUnit_one) :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem segreRetractToSource_snd (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreRetractToSource.{u} r s i j ≫ segreSnd r s =
      chartMap (segreSndRetractRingMap r s i j) (X_mem_homogeneousSubmodule_one _ j)
        Nat.one_pos (by rw [segreSndRetractRingMap_X_self]; exact isUnit_one) :=
  pullback.lift_snd _ _ _

theorem segreRetractToSource_preimage (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreRetractToSource.{u} r s i j ⁻¹ᵁ segreChartOpen r s i j = ⊤ := by
  have hW : segreChartOpen r s i j = segreFst.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X i) ⊓
      segreSnd.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X j) := rfl
  rw [hW, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    segreRetractToSource_fst, segreRetractToSource_snd,
    chartMap_preimage_basicOpen _ _ _ _ (X_mem_homogeneousSubmodule_one _ i) Nat.one_pos,
    chartMap_preimage_basicOpen _ _ _ _ (X_mem_homogeneousSubmodule_one _ j) Nat.one_pos,
    segreFstRetractRingMap_X_self, segreSndRetractRingMap_X_self]
  have h1 : PrimeSpectrum.basicOpen (1 : Away (segreGrading.{u} (r * s + r + s))
      (X (segreIndex r s (i, j)))) = ⊤ := PrimeSpectrum.basicOpen_one
  exact (congrArg₂ (· ⊓ ·) h1 h1).trans (inf_top_eq _)

/-- The retraction `D₊(z_{ij}) ⟶ D₊(xᵢ) ×_ℤ D₊(yⱼ)`. -/
def segreRetract (i : Fin (r + 1)) (j : Fin (s + 1)) :
    Spec (.of (Away (segreGrading.{u} (r * s + r + s)) (X (segreIndex r s (i, j))))) ⟶
      (segreChartOpen.{u} r s i j).toScheme :=
  IsOpenImmersion.lift (segreChartOpen r s i j).ι (segreRetractToSource r s i j) (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx : x ∈ segreRetractToSource.{u} r s i j ⁻¹ᵁ segreChartOpen r s i j := by
      rw [segreRetractToSource_preimage]
      trivial
    exact hx)

@[reassoc (attr := simp)]
theorem segreRetract_ι (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreRetract.{u} r s i j ≫ (segreChartOpen r s i j).ι = segreRetractToSource r s i j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The Segre map on the chart `(i, j)`, as a morphism to `Spec` of the chart ring of
`D₊(z_{ij})`. -/
def segreChartSpec (i : Fin (r + 1)) (j : Fin (s + 1)) :
    (segreChartOpen.{u} r s i j).toScheme ⟶
      Spec (.of (Away (segreGrading.{u} (r * s + r + s)) (X (segreIndex r s (i, j))))) :=
  (segreChartOpen r s i j).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (awayLift (𝒜 := segreGrading (r * s + r + s)) (segreChartRingMap r s i j) _
      (isUnit_segreChartRingMap_X_self r s i j)))

theorem segreChart_eq (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreChart.{u} r s i j = segreChartSpec r s i j ≫
      Proj.awayι _ _ (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos := by
  simp [segreChart, segreChartSpec, chartMap]

theorem segreChartSpec_retract (i : Fin (r + 1)) (j : Fin (s + 1)) :
    segreChartSpec.{u} r s i j ≫ segreRetract r s i j = 𝟙 _ := by
  rw [← cancel_mono (segreChartOpen r s i j).ι, Category.assoc, segreRetract_ι,
    Category.id_comp]
  have hF1 := segreChartRingMap_X_self.{u} r s i j
  have hring1 : (awayLift (𝒜 := segreGrading (r * s + r + s)) (segreChartRingMap r s i j) _
      (isUnit_segreChartRingMap_X_self r s i j)).comp (segreFstRetractRingMap r s i j) =
      chartPolyMap i (segreFstSection r s i j) := by
    apply MvPolynomial.ringHom_ext'
    · exact ulift_int_ringHom_ext _ _
    · intro k
      simp only [RingHom.comp_apply, segreFstRetractRingMap, chartPolyMap, coe_eval₂Hom,
        eval₂_X]
      rw [awayLift_chartRatio _ _ _ hF1, segreChartRingMap_X, chartRatio_self, map_one,
        mul_one]
  have hring2 : (awayLift (𝒜 := segreGrading (r * s + r + s)) (segreChartRingMap r s i j) _
      (isUnit_segreChartRingMap_X_self r s i j)).comp (segreSndRetractRingMap r s i j) =
      chartPolyMap j (segreSndSection r s i j) := by
    apply MvPolynomial.ringHom_ext'
    · exact ulift_int_ringHom_ext _ _
    · intro l
      simp only [RingHom.comp_apply, segreSndRetractRingMap, chartPolyMap, coe_eval₂Hom,
        eval₂_X]
      rw [awayLift_chartRatio _ _ _ hF1, segreChartRingMap_X, chartRatio_self, map_one,
        one_mul]
  apply pullback.hom_ext
  · change segreChartSpec r s i j ≫ segreRetractToSource r s i j ≫ segreFst r s =
      (segreChartOpen r s i j).ι ≫ segreFst r s
    rw [segreRetractToSource_fst, ι_segreFst, segreChartSpec, Category.assoc,
      SpecMap_chartMap _ _ _ _ _ (by rw [CommRingCat.hom_ofHom, hring1]; exact isUnit_chartPolyMap_X_self _ _)]
    exact congrArg _ (chartMap_congr hring1 _ _ _ _)
  · change segreChartSpec r s i j ≫ segreRetractToSource r s i j ≫ segreSnd r s =
      (segreChartOpen r s i j).ι ≫ segreSnd r s
    rw [segreRetractToSource_snd, ι_segreSnd, segreChartSpec, Category.assoc,
      SpecMap_chartMap _ _ _ _ _ (by rw [CommRingCat.hom_ofHom, hring2]; exact isUnit_chartPolyMap_X_self _ _)]
    exact congrArg _ (chartMap_congr hring2 _ _ _ _)

instance (i : Fin (r + 1)) (j : Fin (s + 1)) : IsClosedImmersion (segreChartSpec.{u} r s i j) := by
  have : IsSeparated (segreRetract.{u} r s i j ≫ (segreChartOpen r s i j).toSpecΓ) :=
    inferInstance
  have : IsSeparated (segreRetract.{u} r s i j) :=
    IsSeparated.of_comp _ (segreChartOpen r s i j).toSpecΓ
  have : IsClosedImmersion (segreChartSpec.{u} r s i j ≫ segreRetract r s i j) := by
    rw [segreChartSpec_retract]
    infer_instance
  exact IsClosedImmersion.of_comp _ (segreRetract r s i j)

/-- The Segre morphism over the integers is a closed immersion. -/
instance segreMorphismInt_isClosedImmersion : IsClosedImmersion (segreMorphismInt.{u} r s) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (projCoordinateAffineOpenCover (ULift.{u} ℤ) (σ := Fin (r * s + r + s + 1))).openCover
  intro c
  obtain ⟨⟨i, j⟩, rfl⟩ := (segreIndex r s).surjective c
  have h : IsPullback (segreChartOpen r s i j).ι (segreChartSpec r s i j) (segreMorphismInt r s)
      (Proj.awayι _ _ (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos) := by
    refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
    · rw [ι_segreMorphismInt, segreChart_eq]
    · rw [Proj.opensRange_awayι, Scheme.Opens.opensRange_ι,
        segreMorphismInt_preimage_basicOpen]
  change IsClosedImmersion (pullback.snd (segreMorphismInt r s)
    (Proj.awayι (segreGrading _) (X (segreIndex r s (i, j)))
      (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos))
  rw [← h.isoPullback_inv_snd]
  infer_instance

end SegreClosed

section Coordinates

variable (r s : ℕ)

/-- **Coordinates of the Segre morphism.** On the chart `D₊(xᵢ) ×_ℤ D₊(yⱼ)`, which is the
preimage of `D₊(z_{ij})`, the Segre morphism pulls the coordinate ratio `z_{kl}/z_{ij}` back to
`(xₖ/xᵢ)(yₗ/yⱼ)`; that is, `z_{kl} = xₖ yₗ`. -/
theorem segreMorphismInt_appLE_chartRatio (i : Fin (r + 1)) (j : Fin (s + 1))
    (k : Fin (r + 1)) (l : Fin (s + 1)) :
    (segreMorphismInt.{u} r s).appLE (Proj.basicOpen _ (X (segreIndex r s (i, j))))
        (segreChartOpen r s i j) (segreMorphismInt_preimage_basicOpen r s i j).ge
        (Proj.awayToSection _ _ (chartRatio _ (segreIndex r s (i, j)) (segreIndex r s (k, l)))) =
      segreFstSection r s i j (chartRatio _ i k) * segreSndSection r s i j (chartRatio _ j l) := by
  have h1 := ι_comp_eq_toSpecΓ_SpecMap (segreMorphismInt.{u} r s) (segreChartOpen r s i j)
    (X_mem_homogeneousSubmodule_one _ (segreIndex r s (i, j))) Nat.one_pos
    (segreMorphismInt_preimage_basicOpen r s i j).ge
  rw [ι_segreMorphismInt, segreChart_eq, segreChartSpec, Category.assoc] at h1
  simp only [← Category.assoc] at h1
  rw [cancel_mono] at h1
  have h2 := congrArg (fun φ => φ.hom (chartRatio _ (segreIndex r s (i, j))
    (segreIndex r s (k, l)))) (toSpecΓ_SpecMap_injective _ h1)
  simp only [CommRingCat.hom_ofHom] at h2
  rw [awayLift_chartRatio _ _ _ (segreChartRingMap_X_self r s i j), segreChartRingMap_X] at h2
  exact h2.symm

end Coordinates

section Relative

variable (r s : ℕ)

/-- The fibre product `ℙʳ_Y ×_Y ℙˢ_Y`. -/
abbrev relativeSegreSource (Y : Scheme.{u}) : Scheme.{u} :=
  pullback (projectiveSpaceOverSchemeProjection r Y) (projectiveSpaceOverSchemeProjection s Y)

/-- The structure morphism `ℙʳ_Y ×_Y ℙˢ_Y ⟶ Y`. -/
abbrev relativeSegreSourceProjection (Y : Scheme.{u}) : relativeSegreSource r s Y ⟶ Y :=
  pullback.fst _ _ ≫ projectiveSpaceOverSchemeProjection r Y

/-- The comparison morphism `ℙʳ_Y ×_Y ℙˢ_Y ⟶ ℙʳ_ℤ ×_ℤ ℙˢ_ℤ`. -/
def relativeSegreSourceToInt (Y : Scheme.{u}) : relativeSegreSource r s Y ⟶ segreSource.{u} r s :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
    (specULiftZIsTerminal.{u}.hom_ext _ _)

/-- `ℙʳ_Y ×_Y ℙˢ_Y` is the base change of `ℙʳ_ℤ ×_ℤ ℙˢ_ℤ` along `Y ⟶ Spec ℤ`. -/
theorem relativeSegreSource_isPullback (Y : Scheme.{u}) :
    IsPullback (relativeSegreSourceProjection r s Y) (relativeSegreSourceToInt r s Y)
      (schemeToSpecZ Y) (specULiftZIsTerminal.{u}.from (segreSource.{u} r s)) := by
  refine IsPullback.of_isLimit' ⟨specULiftZIsTerminal.{u}.hom_ext _ _⟩ ?_
  refine PullbackCone.IsLimit.mk _
    (fun c => pullback.lift
      (pullback.lift (c.snd ≫ pullback.fst _ _) c.fst (specULiftZIsTerminal.{u}.hom_ext _ _))
      (pullback.lift (c.snd ≫ pullback.snd _ _) c.fst (specULiftZIsTerminal.{u}.hom_ext _ _))
      (by rw [pullback.lift_snd, pullback.lift_snd])) ?_ ?_ ?_
  · intro c
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  · intro c
    apply pullback.hom_ext
    all_goals simp only [Category.assoc, relativeSegreSourceToInt, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  · intro c m h1 h2
    have h1' : m ≫ pullback.fst _ _ ≫ projectiveSpaceOverSchemeProjection r Y = c.fst := h1
    have h2' : m ≫ relativeSegreSourceToInt r s Y = c.snd := h2
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [pullback.lift_fst, ← h2', Category.assoc, relativeSegreSourceToInt]
      · simp only [pullback.lift_fst, pullback.lift_snd, Category.assoc, h1']
    · apply pullback.hom_ext
      · simp only [pullback.lift_snd, pullback.lift_fst, ← h2', Category.assoc,
          relativeSegreSourceToInt]
      · simp only [pullback.lift_snd, Category.assoc]
        rw [← pullback.condition, h1']

/-- **The relative Segre embedding** `ℙʳ_Y ×_Y ℙˢ_Y ⟶ ℙ^{rs+r+s}_Y`: the base change of the
Segre morphism over the integers. -/
def relativeSegre (Y : Scheme.{u}) :
    relativeSegreSource r s Y ⟶ projectiveSpaceOverScheme (r * s + r + s) Y :=
  pullback.lift (relativeSegreSourceToInt r s Y ≫ segreMorphismInt r s)
    (relativeSegreSourceProjection r s Y) (specULiftZIsTerminal.{u}.hom_ext _ _)

/-- The relative Segre morphism is a morphism over `Y`. -/
@[reassoc (attr := simp)]
theorem relativeSegre_projection (Y : Scheme.{u}) :
    relativeSegre r s Y ≫ projectiveSpaceOverSchemeProjection (r * s + r + s) Y =
      relativeSegreSourceProjection r s Y :=
  pullback.lift_snd _ _ _

/-- The coordinates of the relative Segre morphism are those of the Segre morphism over the
integers. -/
@[reassoc]
theorem relativeSegre_fst (Y : Scheme.{u}) :
    relativeSegre r s Y ≫ pullback.fst _ _ =
      relativeSegreSourceToInt r s Y ≫ segreMorphismInt r s :=
  pullback.lift_fst _ _ _

/-- The relative Segre morphism is the base change of the Segre morphism over the integers. -/
theorem relativeSegre_isPullback (Y : Scheme.{u}) :
    IsPullback (relativeSegre r s Y) (relativeSegreSourceToInt r s Y)
      (pullback.fst (projectiveSpaceOverIntegersMap (r * s + r + s)) (schemeToSpecZ Y))
      (segreMorphismInt r s) := by
  refine IsPullback.of_right (h₁₂ := projectiveSpaceOverSchemeProjection (r * s + r + s) Y)
    (h₂₂ := projectiveSpaceOverIntegersMap (r * s + r + s)) (v₁₃ := schemeToSpecZ Y) ?_
    (relativeSegre_fst r s Y) (IsPullback.of_hasPullback _ _).flip
  rw [relativeSegre_projection]
  convert relativeSegreSource_isPullback r s Y using 1
  exact specULiftZIsTerminal.{u}.hom_ext _ _

instance (Y : Scheme.{u}) : IsClosedImmersion (relativeSegre r s Y) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (relativeSegre_isPullback r s Y).flip
    (segreMorphismInt_isClosedImmersion r s)

/-- The morphism `ℙⁿ_{Y'} ⟶ ℙⁿ_Y` induced by a morphism `Y' ⟶ Y`. -/
def projectiveSpaceOverSchemeMap (n : ℕ) {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    projectiveSpaceOverScheme n Y' ⟶ projectiveSpaceOverScheme n Y :=
  pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) (by simp) (specULiftZIsTerminal.{u}.hom_ext _ _)

@[reassoc (attr := simp)]
theorem projectiveSpaceOverSchemeMap_fst (n : ℕ) {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    projectiveSpaceOverSchemeMap n g ≫ pullback.fst _ _ = pullback.fst _ _ :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc (attr := simp)]
theorem projectiveSpaceOverSchemeMap_projection (n : ℕ) {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    projectiveSpaceOverSchemeMap n g ≫ projectiveSpaceOverSchemeProjection n Y =
      projectiveSpaceOverSchemeProjection n Y' ≫ g :=
  pullback.lift_snd _ _ _

/-- The morphism `ℙʳ_{Y'} ×_{Y'} ℙˢ_{Y'} ⟶ ℙʳ_Y ×_Y ℙˢ_Y` induced by a morphism `Y' ⟶ Y`. -/
def relativeSegreSourceMap {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    relativeSegreSource r s Y' ⟶ relativeSegreSource r s Y :=
  pullback.map _ _ _ _ (projectiveSpaceOverSchemeMap r g) (projectiveSpaceOverSchemeMap s g) g
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem relativeSegreSourceMap_fst {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    relativeSegreSourceMap r s g ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ projectiveSpaceOverSchemeMap r g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem relativeSegreSourceMap_snd {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    relativeSegreSourceMap r s g ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ projectiveSpaceOverSchemeMap s g :=
  pullback.lift_snd _ _ _

theorem relativeSegreSourceMap_toInt {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    relativeSegreSourceMap r s g ≫ relativeSegreSourceToInt r s Y =
      relativeSegreSourceToInt r s Y' := by
  apply pullback.hom_ext <;>
    simp only [relativeSegreSourceToInt, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      relativeSegreSourceMap_fst_assoc, relativeSegreSourceMap_snd_assoc,
      projectiveSpaceOverSchemeMap_fst]

/-- **Compatibility with base change.** For every morphism `Y' ⟶ Y`, the relative Segre
morphism over `Y'` is the base change of the one over `Y`: the square formed with the induced
maps `ℙʳ_{Y'} ×_{Y'} ℙˢ_{Y'} ⟶ ℙʳ_Y ×_Y ℙˢ_Y` and `ℙ^{rs+r+s}_{Y'} ⟶ ℙ^{rs+r+s}_Y` commutes
and is a pullback square. -/
theorem relativeSegre_baseChange {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsPullback (relativeSegre r s Y') (relativeSegreSourceMap r s g)
      (projectiveSpaceOverSchemeMap (r * s + r + s) g) (relativeSegre r s Y) := by
  have hcomm : relativeSegre r s Y' ≫ projectiveSpaceOverSchemeMap (r * s + r + s) g =
      relativeSegreSourceMap r s g ≫ relativeSegre r s Y := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, projectiveSpaceOverSchemeMap_fst, relativeSegre_fst,
        relativeSegre_fst]
      exact (congrArg (fun φ => φ ≫ segreMorphismInt r s)
        (relativeSegreSourceMap_toInt r s g)).symm.trans (Category.assoc _ _ _)
    · rw [Category.assoc, Category.assoc, projectiveSpaceOverSchemeMap_projection,
        relativeSegre_projection, relativeSegre_projection_assoc]
      simp only [relativeSegreSourceProjection, relativeSegreSourceMap_fst_assoc,
        projectiveSpaceOverSchemeMap_projection]
  refine IsPullback.of_bot ?_ hcomm (relativeSegre_isPullback r s Y)
  rw [relativeSegreSourceMap_toInt, projectiveSpaceOverSchemeMap_fst]
  exact relativeSegre_isPullback r s Y'

/-- **The relative Segre embedding** (Hartshorne II, Exercise 4.9). For every scheme `Y` and
`r, s : ℕ`, the morphism `relativeSegre r s Y : ℙʳ_Y ×_Y ℙˢ_Y ⟶ ℙ^{rs+r+s}_Y`

* is a closed immersion;
* is a morphism over `Y`;
* has homogeneous coordinates `z_{ij} = xᵢ yⱼ`: it is pulled back from the Segre morphism over
  the integers, which maps `D₊(xᵢ) ×_ℤ D₊(yⱼ)` onto the preimage of `D₊(z_{ij})` and pulls
  `z_{kl}/z_{ij}` back to `(xₖ/xᵢ)(yₗ/yⱼ)`;
* is compatible with arbitrary base change `Y' ⟶ Y`: the square formed with the induced maps
  on `ℙʳ ×ℙˢ` and on `ℙ^{rs+r+s}` is a pullback square. -/
theorem relativeSegre_spec (Y : Scheme.{u}) :
    IsClosedImmersion (relativeSegre r s Y) ∧
      relativeSegre r s Y ≫ projectiveSpaceOverSchemeProjection (r * s + r + s) Y =
        relativeSegreSourceProjection r s Y ∧
      relativeSegre r s Y ≫ pullback.fst _ _ =
        relativeSegreSourceToInt r s Y ≫ segreMorphismInt r s ∧
      (∀ (i : Fin (r + 1)) (j : Fin (s + 1)),
        ∃ h : segreMorphismInt.{u} r s ⁻¹ᵁ Proj.basicOpen _ (X (segreIndex r s (i, j))) =
            segreChartOpen r s i j,
          ∀ (k : Fin (r + 1)) (l : Fin (s + 1)),
            (segreMorphismInt.{u} r s).appLE (Proj.basicOpen _ (X (segreIndex r s (i, j))))
                (segreChartOpen r s i j) h.ge
                (Proj.awayToSection _ _
                  (chartRatio _ (segreIndex r s (i, j)) (segreIndex r s (k, l)))) =
              segreFstSection r s i j (chartRatio _ i k) *
                segreSndSection r s i j (chartRatio _ j l)) ∧
      ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y),
        IsPullback (relativeSegre r s Y') (relativeSegreSourceMap r s g)
          (projectiveSpaceOverSchemeMap (r * s + r + s) g) (relativeSegre r s Y) :=
  ⟨inferInstance, relativeSegre_projection r s Y, relativeSegre_fst r s Y,
    fun i j => ⟨segreMorphismInt_preimage_basicOpen r s i j,
      segreMorphismInt_appLE_chartRatio r s i j⟩,
    fun g => relativeSegre_baseChange r s g⟩

end Relative

end Hartshorne
