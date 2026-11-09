/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QuadricSurfaceSegre
import Hartshorne.Scheme.ProjectiveSpaceOverSpec
import Hartshorne.Scheme.RelativeProj

/-!
# The split quadric surface is `ℙ¹ × ℙ¹`

Let `k` be a field and `Q = Proj` of the Segre ring (`Hartshorne.quadricSurface k`). The Segre
coordinates `z_{ij} = sᵢuⱼ` (indexed by `segreIndex 1 1`) give a closed immersion
`Q ⟶ ℙ³_{Spec k}` (`Hartshorne.quadricSurfaceToProjectiveSpace`), and the relative Segre
embedding `ℙ¹_k ×_k ℙ¹_k ⟶ ℙ³_{Spec k}` factors through it by an isomorphism
`ℙ¹_k ×_k ℙ¹_k ≅ Q` (`Hartshorne.quadricSurfaceIsoSegreSource`).

Both factorizations are built chart by chart and glued, using that the two maps to `ℙ³_{Spec k}`
are monomorphisms.

* From `Q`: on `D₊(sᵢuⱼ)` the map to `ℙ¹_ℤ ×_ℤ ℙ¹_ℤ` is the chart map `D₊(sᵢuⱼ) ⟶ D₊(z_{ij})`
  followed by the retraction of the Segre chart (`segreRetractToSource`); the key identity is
  `(z_{kj}/z_{ij})(z_{il}/z_{ij}) = z_{kl}/z_{ij}` on `Q`.
* From `ℙ¹_k ×_k ℙ¹_k`: on the preimage of `D₊(xᵢ) ×_ℤ D₊(yⱼ)` the map to `D₊(sᵢuⱼ)` sends the
  monomial `s^e u^g` to `∏ (xₐ/xᵢ)^{eₐ} (y_b/yⱼ)^{g_b}`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AddMonoidAlgebra MvPolynomial
  HomogeneousLocalization

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

local notation "𝒬" => quadricGrading k

section Coordinates

/-- The Segre coordinates `z_{ij} = sᵢuⱼ` on `Q`, indexed through `segreIndex 1 1`. -/
def quadricSegreCoordinates (l : Fin (1 * 1 + 1 + 1 + 1)) : QuadricRing k :=
  quadricChart k ((segreIndex 1 1).symm l).1 ((segreIndex 1 1).symm l).2

theorem quadricSegreCoordinates_segreIndex (i j : Fin (1 + 1)) :
    quadricSegreCoordinates k (segreIndex 1 1 (i, j)) = quadricChart k i j := by
  simp [quadricSegreCoordinates]

theorem quadricSegreCoordinates_mem (l : Fin (1 * 1 + 1 + 1 + 1)) :
    quadricSegreCoordinates k l ∈ 𝒬 1 :=
  quadricChart_mem k _ _

theorem adjoin_quadricSegreCoordinates :
    Algebra.adjoin (𝒬 0) (Set.range (quadricSegreCoordinates k)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨P, rfl⟩ := quadricCoordinateAlgHom_surjective k x
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : algebraMap k (QuadricRing k) c =
        algebraMap (𝒬 0) (QuadricRing k) ⟨_, SetLike.algebraMap_mem_graded 𝒬 c⟩ := rfl
    rw [quadricCoordinateAlgHom, aeval_C, h]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p l hp =>
    rw [map_mul, quadricCoordinateAlgHom_X]
    refine mul_mem hp (Algebra.subset_adjoin ?_)
    fin_cases l
    · exact ⟨segreIndex 1 1 (0, 0), quadricSegreCoordinates_segreIndex k 0 0⟩
    · exact ⟨segreIndex 1 1 (1, 1), quadricSegreCoordinates_segreIndex k 1 1⟩
    · exact ⟨segreIndex 1 1 (0, 1), quadricSegreCoordinates_segreIndex k 0 1⟩
    · exact ⟨segreIndex 1 1 (1, 0), quadricSegreCoordinates_segreIndex k 1 0⟩

/-- The graded homomorphism `ℤ[z₀₀, z₀₁, z₁₀, z₁₁] → ` Segre ring, `z_{ij} ↦ sᵢuⱼ`. -/
abbrev quadricSegreHom : segreGrading.{u} (1 * 1 + 1 + 1) →+*ᵍ 𝒬 :=
  GeneratedProj.evalGradedHom 𝒬 (quadricSegreCoordinates_mem k)

theorem quadricSegreHom_X (l : Fin (1 * 1 + 1 + 1 + 1)) :
    quadricSegreHom k (X l) = quadricSegreCoordinates k l :=
  GeneratedProj.evalRingHom_X _ _

theorem quadricSegreHom_X_segreIndex (i j : Fin (1 + 1)) :
    quadricSegreHom k (X (segreIndex 1 1 (i, j))) = quadricChart k i j := by
  rw [quadricSegreHom_X, quadricSegreCoordinates_segreIndex]

theorem quadricSegreHom_X_mem (c : Fin (1 + 1) × Fin (1 + 1)) :
    quadricSegreHom k (X (segreIndex 1 1 c)) ∈ 𝒬 1 :=
  (quadricSegreHom k).map_mem (X_mem_homogeneousSubmodule_one _ _)

/-- The degree-zero part of the Segre ring is `k`. -/
theorem bijective_algebraMap_quadricGrading_zero :
    Function.Bijective (algebraMap k (𝒬 0)) := by
  have hval : ∀ c : k, ((algebraMap k (𝒬 0) c : 𝒬 0) : QuadricRing k) = single 0 c :=
    fun c => rfl
  refine ⟨fun c d h => ?_, fun a => ⟨(a : QuadricRing k).coeff 0, ?_⟩⟩
  · have h' := congrArg (fun x : 𝒬 0 => (x : QuadricRing k).coeff 0) h
    simpa only [hval, coeff_single, Finsupp.single_eq_same] using h'
  · apply Subtype.ext
    rw [hval]
    have ha : ∀ p ∈ (a : QuadricRing k).coeff.support, p = 0 := by
      intro p hp
      have h1 := (mem_quadricGrading_iff k 0 a.1).mp a.2 p hp
      have h2 := quadricDegree_eq_snd p
      rw [quadricDegree_apply] at h1
      rw [quadricDegree_apply, h1] at h2
      apply Subtype.ext
      apply Prod.ext <;> funext i <;> fin_cases i
      all_goals
        simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, ZeroMemClass.coe_zero, Prod.fst_zero,
          Prod.snd_zero, Pi.zero_apply]
        omega
    ext p
    rw [coeff_single, Finsupp.single_apply]
    split_ifs with hp
    · rw [hp]
    · by_contra h
      exact hp (ha p (Finsupp.mem_support_iff.mpr (Ne.symm h))).symm

instance : IsIso (CommRingCat.ofHom (algebraMap k (𝒬 0))) :=
  (RingEquiv.ofBijective _ (bijective_algebraMap_quadricGrading_zero k)).toCommRingCatIso.isIso_hom

end Coordinates

section Embedding

/-- The morphism `Q ⟶ ℙ³_ℤ` given by the Segre coordinates `z_{ij} = sᵢuⱼ`. -/
def quadricSurfaceToProjectiveSpaceInt :
    quadricSurface k ⟶ Proj (segreGrading.{u} (1 * 1 + 1 + 1)) :=
  GeneratedProj.toProjectiveSpaceInt 𝒬 (quadricSegreCoordinates_mem k)
    (adjoin_quadricSegreCoordinates k)

/-- The structure morphism `Q ⟶ Spec k`. -/
def quadricSurfaceToSpec : quadricSurface k ⟶ Spec (.of k) :=
  Proj.toSpecZero 𝒬 ≫ Spec.map (CommRingCat.ofHom (algebraMap k (𝒬 0)))

/-- **The quadric in `ℙ³_k`**: the morphism `Q ⟶ ℙ³_{Spec k}` over `Spec k` given by the Segre
coordinates `z_{ij} = sᵢuⱼ`, i.e. `x = z₀₀`, `y = z₁₁`, `z = z₀₁`, `w = z₁₀`. -/
def quadricSurfaceToProjectiveSpace :
    quadricSurface k ⟶ projectiveSpaceOverScheme (1 * 1 + 1 + 1) (Spec (.of k)) :=
  pullback.lift (quadricSurfaceToProjectiveSpaceInt k) (quadricSurfaceToSpec k)
    (specULiftZIsTerminal.hom_ext _ _)

@[reassoc (attr := simp)]
theorem quadricSurfaceToProjectiveSpace_fst :
    quadricSurfaceToProjectiveSpace k ≫ pullback.fst _ _ = quadricSurfaceToProjectiveSpaceInt k :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem quadricSurfaceToProjectiveSpace_projection :
    quadricSurfaceToProjectiveSpace k ≫ projectiveSpaceOverSchemeProjection _ _ =
      quadricSurfaceToSpec k :=
  pullback.lift_snd _ _ _

theorem quadricSurfaceToProjectiveSpace_eq :
    quadricSurfaceToProjectiveSpace k =
      GeneratedProj.toProjectiveSpace 𝒬 (quadricSegreCoordinates_mem k)
          (adjoin_quadricSegreCoordinates k) ≫
        projectiveSpaceOverSchemeMap _ (Spec.map (CommRingCat.ofHom (algebraMap k (𝒬 0)))) := by
  apply pullback.hom_ext
  · rw [quadricSurfaceToProjectiveSpace_fst, Category.assoc, projectiveSpaceOverSchemeMap_fst,
      GeneratedProj.toProjectiveSpace_fst]
    rfl
  · rw [quadricSurfaceToProjectiveSpace_projection, Category.assoc,
      projectiveSpaceOverSchemeMap_projection, ← Category.assoc,
      GeneratedProj.toProjectiveSpace_projection]
    rfl

instance : IsClosedImmersion (quadricSurfaceToProjectiveSpace k) := by
  rw [quadricSurfaceToProjectiveSpace_eq]
  have := GeneratedProj.isClosedImmersion_toProjectiveSpace 𝒬 (quadricSegreCoordinates_mem k)
    (adjoin_quadricSegreCoordinates k)
  have : IsIso (projectiveSpaceOverSchemeMap (1 * 1 + 1 + 1)
      (Spec.map (CommRingCat.ofHom (algebraMap k (𝒬 0))))) := by
    unfold projectiveSpaceOverSchemeMap
    infer_instance
  infer_instance

end Embedding

section FromQuadric

theorem quadricChart_mul_swap (a i b j : Fin 2) :
    quadricChart k a j * quadricChart k i b = quadricChart k a b * quadricChart k i j := by
  simp only [quadricChart, single_mul_single, mul_one]
  congr 1
  apply Subtype.ext
  simp only [quadricChartExp, AddSubmonoid.coe_add, Prod.mk_add_mk]
  rw [add_comm (Pi.single j 1 : Fin 2 → ℕ)]

/-- The affine open cover of `Q` by the charts `D₊(sᵢuⱼ)`, indexed by `(i, j)`. -/
def quadricSegreAffineCover : (quadricSurface k).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan 𝒬
    (fun c : Fin (1 + 1) × Fin (1 + 1) => quadricSegreHom k (X (segreIndex 1 1 c)))
    (quadricSegreHom_X_mem k) (fun _ => Nat.one_pos) (by
      have h : (fun c : Fin (1 + 1) × Fin (1 + 1) => quadricSegreHom k (X (segreIndex 1 1 c))) =
          fun ij : Fin 2 × Fin 2 => quadricChart k ij.1 ij.2 :=
        funext fun c => quadricSegreHom_X_segreIndex k c.1 c.2
      rw [h]
      exact quadric_irrelevant_le_span k)

/-- The open cover of `Q` by the charts `D₊(sᵢuⱼ)`, with its data exposed reducibly. -/
abbrev quadricSegreCover : (quadricSurface k).OpenCover where
  I₀ := Fin (1 + 1) × Fin (1 + 1)
  X c := Spec (.of (Away 𝒬 (quadricSegreHom k (X (segreIndex 1 1 c)))))
  f c := Proj.awayι 𝒬 _ (quadricSegreHom_X_mem k c) Nat.one_pos
  mem₀ := (quadricSegreAffineCover k).openCover.mem₀

/-- The ring map `Γ(D₊(xᵢ) ×_ℤ D₊(yⱼ)) → ℤ[z]_(z_{ij})` of the retraction of the Segre chart. -/
def segreRetractRing (i j : Fin (1 + 1)) :
    Γ(segreSource.{u} 1 1, segreChartOpen 1 1 i j) ⟶
      CommRingCat.of (Away (segreGrading.{u} (1 * 1 + 1 + 1)) (X (segreIndex 1 1 (i, j)))) :=
  Spec.preimage (segreRetract 1 1 i j ≫ (segreChartOpen 1 1 i j).toSpecΓ)

theorem segreRetractRing_fst (i j a : Fin (1 + 1)) :
    (segreRetractRing.{u} i j).hom (segreFstSection 1 1 i j (chartRatio _ i a)) =
      chartRatio _ (segreIndex 1 1 (i, j)) (segreIndex 1 1 (a, j)) := by
  have h1 := segreRetract_ι_assoc.{u} 1 1 i j (segreFst 1 1)
  rw [segreRetractToSource_fst, ι_segreFst, ← Category.assoc,
    ← Spec.map_preimage (segreRetract 1 1 i j ≫ (segreChartOpen 1 1 i j).toSpecΓ),
    SpecMap_projChartMap _ _ _ _ _ (by
      rw [RingHom.comp_apply, chartPolyMap_X_self, map_one]; exact isUnit_one)] at h1
  unfold projChartMap at h1
  rw [cancel_mono, Spec.map_inj] at h1
  have h2 := congrArg (fun φ => φ.hom (chartRatio _ i a)) h1
  simp only [CommRingCat.hom_ofHom] at h2
  rw [awayLift_chartRatio _ _ _ (by rw [RingHom.comp_apply, chartPolyMap_X_self, map_one]),
    awayLift_chartRatio _ _ _ (segreFstRetractRingMap_X_self 1 1 i j)] at h2
  simpa [chartPolyMap, segreFstRetractRingMap, segreRetractRing] using h2

theorem segreRetractRing_snd (i j b : Fin (1 + 1)) :
    (segreRetractRing.{u} i j).hom (segreSndSection 1 1 i j (chartRatio _ j b)) =
      chartRatio _ (segreIndex 1 1 (i, j)) (segreIndex 1 1 (i, b)) := by
  have h1 := segreRetract_ι_assoc.{u} 1 1 i j (segreSnd 1 1)
  rw [segreRetractToSource_snd, ι_segreSnd, ← Category.assoc,
    ← Spec.map_preimage (segreRetract 1 1 i j ≫ (segreChartOpen 1 1 i j).toSpecΓ),
    SpecMap_projChartMap _ _ _ _ _ (by
      rw [RingHom.comp_apply, chartPolyMap_X_self, map_one]; exact isUnit_one)] at h1
  unfold projChartMap at h1
  rw [cancel_mono, Spec.map_inj] at h1
  have h2 := congrArg (fun φ => φ.hom (chartRatio _ j b)) h1
  simp only [CommRingCat.hom_ofHom] at h2
  rw [awayLift_chartRatio _ _ _ (by rw [RingHom.comp_apply, chartPolyMap_X_self, map_one]),
    awayLift_chartRatio _ _ _ (segreSndRetractRingMap_X_self 1 1 i j)] at h2
  simpa [chartPolyMap, segreSndRetractRingMap, segreRetractRing] using h2

theorem quadric_away_ratio_mul (i j a b : Fin (1 + 1)) :
    Away.map (quadricSegreHom k) (X (segreIndex 1 1 (i, j)))
        (chartRatio _ (segreIndex 1 1 (i, j)) (segreIndex 1 1 (a, j))) *
      Away.map (quadricSegreHom k) (X (segreIndex 1 1 (i, j)))
        (chartRatio _ (segreIndex 1 1 (i, j)) (segreIndex 1 1 (i, b))) =
    Away.map (quadricSegreHom k) (X (segreIndex 1 1 (i, j)))
      (chartRatio _ (segreIndex 1 1 (i, j)) (segreIndex 1 1 (a, b))) := by
  apply HomogeneousLocalization.val_injective
  simp only [chartRatio, Away.map_mk, HomogeneousLocalization.val_mul, Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, pow_one,
    quadricSegreHom_X_segreIndex]
  rw [quadricChart_mul_swap]
  ring

theorem segreRetract_toSpecΓ (i j : Fin (1 + 1)) :
    segreRetract.{u} 1 1 i j ≫ (segreChartOpen 1 1 i j).toSpecΓ =
      Spec.map (segreRetractRing.{u} i j) :=
  (Spec.map_preimage _).symm

/-- The chart map `D₊(sᵢuⱼ) ⟶ D₊(z_{ij})` of `Q ⟶ ℙ³_ℤ`, as a morphism of spectra. -/
abbrev quadricChartToSegreChart (c : Fin (1 + 1) × Fin (1 + 1)) :
    Spec (.of (Away 𝒬 (quadricSegreHom k (X (segreIndex 1 1 c))))) ⟶
      Spec (.of (Away (segreGrading.{u} (1 * 1 + 1 + 1)) (X (segreIndex 1 1 c)))) :=
  Spec.map (CommRingCat.ofHom (Away.map (quadricSegreHom k) (X (segreIndex 1 1 c))))

theorem quadricSegreCover_comp (c : Fin (1 + 1) × Fin (1 + 1)) :
    (quadricSegreCover k).f c ≫ quadricSurfaceToProjectiveSpaceInt k =
      quadricChartToSegreChart k c ≫ Proj.awayι _ (X (segreIndex 1 1 c))
        (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos :=
  Proj.awayι_comp_map _ _ Nat.one_pos _ (X_mem_homogeneousSubmodule_one _ _)

/-- On the chart `D₊(sᵢuⱼ)` of `Q`, the map to `ℙ¹_ℤ ×_ℤ ℙ¹_ℤ`: the chart map to `D₊(z_{ij})`
followed by the retraction of the Segre chart. -/
def quadricToSegreSourceChart (c : Fin (1 + 1) × Fin (1 + 1)) :
    Spec (.of (Away 𝒬 (quadricSegreHom k (X (segreIndex 1 1 c))))) ⟶ segreSource.{u} 1 1 :=
  quadricChartToSegreChart k c ≫ segreRetractToSource 1 1 c.1 c.2

theorem quadricToSegreSourceChart_comp (c : Fin (1 + 1) × Fin (1 + 1)) :
    quadricToSegreSourceChart k c ≫ segreMorphismInt 1 1 =
      quadricChartToSegreChart k c ≫ Proj.awayι _ (X (segreIndex 1 1 c))
        (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos := by
  obtain ⟨i, j⟩ := c
  have hu1 : IsUnit (((segreRetractRing.{u} i j).hom.comp (segreChartRingMap 1 1 i j))
      (X (segreIndex 1 1 (i, j)))) := by
    rw [RingHom.comp_apply, segreChartRingMap_X_self, map_one]; exact isUnit_one
  have hG : ((CommRingCat.ofHom (Away.map (quadricSegreHom k) (X (segreIndex 1 1 (i, j))))).hom.comp
      ((segreRetractRing.{u} i j).hom.comp (segreChartRingMap 1 1 i j)))
        (X (segreIndex 1 1 (i, j))) = 1 := by
    rw [RingHom.comp_apply, RingHom.comp_apply, segreChartRingMap_X_self, map_one, map_one]
  rw [quadricToSegreSourceChart, Category.assoc, ← segreRetract_ι, Category.assoc,
    ι_segreMorphismInt, segreChart, ← Category.assoc (segreRetract 1 1 i j),
    segreRetract_toSpecΓ, SpecMap_projChartMap _ _ _ _ _ hu1,
    SpecMap_projChartMap _ _ _ _ _ (by rw [hG]; exact isUnit_one), projChartMap]
  congr 3
  apply chart_ringHom_ext (segreIndex 1 1 (i, j))
  · intro r
    exact chartConst_ext _ _ _ r
  · intro m
    rw [awayLift_chartRatio _ _ _ hG]
    obtain ⟨⟨a, b⟩, rfl⟩ := (segreIndex 1 1).surjective m
    simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, segreChartRingMap_X, map_mul]
    rw [segreRetractRing_fst, segreRetractRing_snd]
    exact quadric_away_ratio_mul k i j a b

/-- The morphism `Q ⟶ ℙ¹_ℤ ×_ℤ ℙ¹_ℤ`, glued from the charts. -/
def quadricToSegreSource : quadricSurface k ⟶ segreSource.{u} 1 1 :=
  (quadricSegreCover k).glueMorphisms (fun c => quadricToSegreSourceChart k c) (by
    intro x y
    rw [← cancel_mono (segreMorphismInt.{u} 1 1), Category.assoc, Category.assoc,
      quadricToSegreSourceChart_comp, quadricToSegreSourceChart_comp, ← quadricSegreCover_comp,
      ← quadricSegreCover_comp, pullback.condition_assoc])

theorem quadricToSegreSource_comp :
    quadricToSegreSource k ≫ segreMorphismInt 1 1 = quadricSurfaceToProjectiveSpaceInt k :=
  (quadricSegreCover k).hom_ext _ _ fun c => by
    rw [quadricToSegreSource, Scheme.Cover.ι_glueMorphisms_assoc,
      quadricToSegreSourceChart_comp, quadricSegreCover_comp]

/-- The morphism `Q ⟶ ℙ¹_k ×_k ℙ¹_k` through which `Q ⟶ ℙ³_{Spec k}` factors. -/
def quadricSurfaceToSegreSource : quadricSurface k ⟶ relativeSegreSource 1 1 (Spec (.of k)) :=
  (relativeSegre_isPullback 1 1 (Spec (.of k))).lift (quadricSurfaceToProjectiveSpace k)
    (quadricToSegreSource k)
    ((quadricSurfaceToProjectiveSpace_fst k).trans (quadricToSegreSource_comp k).symm)

@[reassoc (attr := simp)]
theorem quadricSurfaceToSegreSource_comp :
    quadricSurfaceToSegreSource k ≫ relativeSegre 1 1 (Spec (.of k)) =
      quadricSurfaceToProjectiveSpace k :=
  IsPullback.lift_fst _ _ _ _

end FromQuadric

section ToQuadric

/-- The chart `V_{ij}` of `ℙ¹_k ×_k ℙ¹_k`: the preimage of `D₊(xᵢ) ×_ℤ D₊(yⱼ)`. -/
def segreSourceChart (c : Fin (1 + 1) × Fin (1 + 1)) :
    (relativeSegreSource 1 1 (Spec (.of k))).Opens :=
  relativeSegreSourceToInt 1 1 (Spec (.of k)) ⁻¹ᵁ segreChartOpen 1 1 c.1 c.2

theorem segreSourceChart_isOpenCover : TopologicalSpace.IsOpenCover (segreSourceChart k) := by
  refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ => ?_)
  have hx : relativeSegreSourceToInt 1 1 (Spec (.of k)) x ∈
      ⨆ c : Fin (1 + 1) × Fin (1 + 1), segreChartOpen.{u} 1 1 c.1 c.2 := by
    rw [(segreChartOpen_iSup 1 1).iSup_eq_top]
    trivial
  obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c, hc⟩

/-- The ratio `xₐ/xᵢ` on the chart `V_{ij}`. -/
def segreSourceFst (c : Fin (1 + 1) × Fin (1 + 1)) (a : Fin (1 + 1)) :
    Γ(relativeSegreSource 1 1 (Spec (.of k)), segreSourceChart k c) :=
  (relativeSegreSourceToInt 1 1 (Spec (.of k))).appLE (segreChartOpen 1 1 c.1 c.2)
    (segreSourceChart k c) le_rfl (segreFstSection 1 1 c.1 c.2 (chartRatio _ c.1 a))

/-- The ratio `y_b/yⱼ` on the chart `V_{ij}`. -/
def segreSourceSnd (c : Fin (1 + 1) × Fin (1 + 1)) (b : Fin (1 + 1)) :
    Γ(relativeSegreSource 1 1 (Spec (.of k)), segreSourceChart k c) :=
  (relativeSegreSourceToInt 1 1 (Spec (.of k))).appLE (segreChartOpen 1 1 c.1 c.2)
    (segreSourceChart k c) le_rfl (segreSndSection 1 1 c.1 c.2 (chartRatio _ c.2 b))

theorem segreSourceFst_self (c : Fin (1 + 1) × Fin (1 + 1)) : segreSourceFst k c c.1 = 1 := by
  rw [segreSourceFst, chartRatio_self, map_one, map_one]

theorem segreSourceSnd_self (c : Fin (1 + 1) × Fin (1 + 1)) : segreSourceSnd k c c.2 = 1 := by
  rw [segreSourceSnd, chartRatio_self, map_one, map_one]

/-- The scalars `k → Γ(V_{ij})`. -/
def segreSourceScalar (c : Fin (1 + 1) × Fin (1 + 1)) :
    k →+* Γ(relativeSegreSource 1 1 (Spec (.of k)), segreSourceChart k c) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ (relativeSegreSourceProjection 1 1 (Spec (.of k))).appLE ⊤
    (segreSourceChart k c) (show _ ≤ _ ⁻¹ᵁ ⊤ from le_top)).hom

/-- The monomial `s^e u^g ↦ ∏ (xₐ/xᵢ)^{eₐ} (y_b/yⱼ)^{g_b}` on the chart `V_{ij}`. -/
def segreSourceMonomial (c : Fin (1 + 1) × Fin (1 + 1)) :
    Multiplicative quadricExponents →*
      Γ(relativeSegreSource 1 1 (Spec (.of k)), segreSourceChart k c) where
  toFun p := segreSourceFst k c 0 ^ p.toAdd.1.1 0 * segreSourceFst k c 1 ^ p.toAdd.1.1 1 *
    segreSourceSnd k c 0 ^ p.toAdd.1.2 0 * segreSourceSnd k c 1 ^ p.toAdd.1.2 1
  map_one' := by simp
  map_mul' p q := by
    simp only [toAdd_mul, AddSubmonoid.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, pow_add]
    ring

/-- The ring map from the Segre ring to `Γ(V_{ij})` of the chart map `V_{ij} ⟶ D₊(sᵢuⱼ)`. -/
def segreSourceRingHom (c : Fin (1 + 1) × Fin (1 + 1)) :
    QuadricRing k →+* Γ(relativeSegreSource 1 1 (Spec (.of k)), segreSourceChart k c) :=
  liftNCRingHom (segreSourceScalar k c) (segreSourceMonomial k c) fun _ _ => Commute.all _ _

theorem segreSourceRingHom_quadricChart (c : Fin (1 + 1) × Fin (1 + 1)) (a b : Fin (1 + 1)) :
    segreSourceRingHom k c (quadricChart k a b) = segreSourceFst k c a * segreSourceSnd k c b := by
  rw [segreSourceRingHom, quadricChart, liftNCRingHom_single, map_one, one_mul]
  fin_cases a <;> fin_cases b <;> simp [segreSourceMonomial, quadricChartExp]

theorem segreSourceRingHom_algebraMap (c : Fin (1 + 1) × Fin (1 + 1)) (r : k) :
    segreSourceRingHom k c (algebraMap k (QuadricRing k) r) = segreSourceScalar k c r := by
  rw [segreSourceRingHom, coe_algebraMap, Function.comp_apply, liftNCRingHom_single, ofAdd_zero,
    map_one, mul_one]
  rfl

theorem segreSourceRingHom_X_segreIndex (c : Fin (1 + 1) × Fin (1 + 1)) (a b : Fin (1 + 1)) :
    segreSourceRingHom k c (quadricSegreHom k (X (segreIndex 1 1 (a, b)))) =
      segreSourceFst k c a * segreSourceSnd k c b := by
  rw [quadricSegreHom_X_segreIndex, segreSourceRingHom_quadricChart]

theorem segreSourceRingHom_X_self (c : Fin (1 + 1) × Fin (1 + 1)) :
    segreSourceRingHom k c (quadricSegreHom k (X (segreIndex 1 1 c))) = 1 := by
  obtain ⟨i, j⟩ := c
  rw [segreSourceRingHom_X_segreIndex]
  exact (congrArg₂ (· * ·) (segreSourceFst_self k (i, j)) (segreSourceSnd_self k (i, j))).trans
    (mul_one 1)

theorem isUnit_segreSourceRingHom_X_self (c : Fin (1 + 1) × Fin (1 + 1)) :
    IsUnit (segreSourceRingHom k c (quadricSegreHom k (X (segreIndex 1 1 c)))) := by
  rw [segreSourceRingHom_X_self]
  exact isUnit_one

/-- The chart map `V_{ij} ⟶ D₊(sᵢuⱼ) ⊆ Q`. -/
def segreSourceToQuadricChart (c : Fin (1 + 1) × Fin (1 + 1)) :
    (segreSourceChart k c).toScheme ⟶ quadricSurface k :=
  (segreSourceChart k c).toSpecΓ ≫ projChartMap (segreSourceRingHom k c) (quadricSegreHom_X_mem k c)
    Nat.one_pos (isUnit_segreSourceRingHom_X_self k c)

theorem quadric_away_map_chartRatio (l m : Fin (1 * 1 + 1 + 1 + 1)) :
    Away.map (quadricSegreHom k) (X l) (chartRatio _ l m) =
      Away.mk 𝒬 ((quadricSegreHom k).map_mem (X_mem_homogeneousSubmodule_one _ l)) 1
        (quadricSegreHom k (X m))
        (by simpa using (quadricSegreHom k).map_mem (X_mem_homogeneousSubmodule_one _ m)) := by
  rw [chartRatio, Away.map_mk]

theorem quadricAwayι_comp (c : Fin (1 + 1) × Fin (1 + 1)) :
    Proj.awayι 𝒬 _ (quadricSegreHom_X_mem k c) Nat.one_pos ≫ quadricSurfaceToProjectiveSpaceInt k =
      quadricChartToSegreChart k c ≫ Proj.awayι _ (X (segreIndex 1 1 c))
        (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos :=
  quadricSegreCover_comp k c

theorem segreSourceToQuadricChart_comp_int (c : Fin (1 + 1) × Fin (1 + 1)) :
    segreSourceToQuadricChart k c ≫ quadricSurfaceToProjectiveSpaceInt k =
      (segreSourceChart k c).ι ≫ relativeSegreSourceToInt 1 1 (Spec (.of k)) ≫
        segreMorphismInt 1 1 := by
  obtain ⟨i, j⟩ := c
  have hle : segreSourceChart k (i, j) ≤
      (relativeSegreSourceToInt 1 1 (Spec (.of k)) ≫ segreMorphismInt 1 1) ⁻¹ᵁ
        Proj.basicOpen _ (X (segreIndex 1 1 (i, j))) := by
    rw [Scheme.Hom.comp_preimage, segreMorphismInt_preimage_basicOpen]
    exact le_rfl
  rw [ι_comp_eq_toSpecΓ_SpecMap _ _ (X_mem_homogeneousSubmodule_one _ _) Nat.one_pos hle,
    segreSourceToQuadricChart, projChartMap, Category.assoc, Category.assoc, quadricAwayι_comp,
    ← Category.assoc (Spec.map _), ← Spec.map_comp]
  congr 3
  ext1
  apply chart_ringHom_ext (segreIndex 1 1 (i, j))
  · intro r
    exact chartConst_ext _ _ _ r
  · intro m
    obtain ⟨⟨a, b⟩, rfl⟩ := (segreIndex 1 1).surjective m
    have key := awayLift_mk (𝒜 := 𝒬) (segreSourceRingHom k (i, j))
      (isUnit_segreSourceRingHom_X_self k (i, j)) (quadricSegreHom_X_mem k (i, j)) 1
      (quadricSegreHom k (X (segreIndex 1 1 (a, b))))
      (by simpa using quadricSegreHom_X_mem k (a, b))
    rw [segreSourceRingHom_X_self, one_pow, mul_one, segreSourceRingHom_X_segreIndex] at key
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [quadric_away_map_chartRatio, key, ← Scheme.Hom.appLE_comp_appLE _ _ _
      (segreChartOpen 1 1 i j) (segreSourceChart k (i, j))
      (segreMorphismInt_preimage_basicOpen 1 1 i j).ge
      (show segreSourceChart k (i, j) ≤ _ ⁻¹ᵁ segreChartOpen 1 1 i j from le_rfl),
      CommRingCat.hom_comp, RingHom.comp_apply, segreMorphismInt_appLE_chartRatio, map_mul]
    rfl

theorem segreSourceToQuadricChart_comp_toSpec (c : Fin (1 + 1) × Fin (1 + 1)) :
    segreSourceToQuadricChart k c ≫ quadricSurfaceToSpec k =
      (segreSourceChart k c).ι ≫ relativeSegreSourceProjection 1 1 (Spec (.of k)) := by
  rw [ι_comp_eq_toSpecΓ_SpecMap_of_Spec _ _ (show _ ≤ _ ⁻¹ᵁ ⊤ from le_top),
    segreSourceToQuadricChart, projChartMap, quadricSurfaceToSpec, Category.assoc, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext r
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rw [awayLift_fromZeroRingHom (𝒜 := 𝒬)]
  exact segreSourceRingHom_algebraMap k c r

theorem segreSourceToQuadricChart_comp (c : Fin (1 + 1) × Fin (1 + 1)) :
    segreSourceToQuadricChart k c ≫ quadricSurfaceToProjectiveSpace k =
      (segreSourceChart k c).ι ≫ relativeSegre 1 1 (Spec (.of k)) := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg _ (quadricSurfaceToProjectiveSpace_fst k)).trans
      ((segreSourceToQuadricChart_comp_int k c).trans
        ((congrArg _ (relativeSegre_fst 1 1 _)).symm.trans (Category.assoc _ _ _).symm)))
  · exact (Category.assoc _ _ _).trans
      ((congrArg _ (quadricSurfaceToProjectiveSpace_projection k)).trans
      ((segreSourceToQuadricChart_comp_toSpec k c).trans
        ((congrArg _ (relativeSegre_projection 1 1 _)).symm.trans (Category.assoc _ _ _).symm)))

/-- The morphism `ℙ¹_k ×_k ℙ¹_k ⟶ Q`, glued from the charts. -/
def segreSourceToQuadric : relativeSegreSource 1 1 (Spec (.of k)) ⟶ quadricSurface k :=
  glueOpens (segreSourceChart k) (segreSourceChart_isOpenCover k) (segreSourceToQuadricChart k)
    (by
      intro x y
      rw [← cancel_mono (quadricSurfaceToProjectiveSpace k)]
      simp only [Category.assoc, segreSourceToQuadricChart_comp, Scheme.homOfLE_ι_assoc])

theorem ι_segreSourceToQuadric_comp (c : Fin (1 + 1) × Fin (1 + 1)) :
    (segreSourceChart k c).ι ≫ segreSourceToQuadric k ≫ quadricSurfaceToProjectiveSpace k =
      (segreSourceChart k c).ι ≫ relativeSegre 1 1 (Spec (.of k)) := by
  rw [segreSourceToQuadric, ι_glueOpens_assoc, segreSourceToQuadricChart_comp]

@[reassoc (attr := simp)]
theorem segreSourceToQuadric_comp :
    segreSourceToQuadric k ≫ quadricSurfaceToProjectiveSpace k = relativeSegre 1 1 (Spec (.of k)) :=
  (Scheme.openCoverOfIsOpenCover _ (segreSourceChart k) (segreSourceChart_isOpenCover k)).hom_ext
    _ _ fun c => ι_segreSourceToQuadric_comp k c

end ToQuadric

section Comparison

/-- The renumbering of the coordinates: the Segre coordinate `z_{ij}` (index `segreIndex 1 1 (i, j)`)
is the coordinate of `k[x, y, z, w]` with `x = z₀₀`, `y = z₁₁`, `z = z₀₁`, `w = z₁₀`. -/
def quadricCoordinateEquiv : Fin (1 * 1 + 1 + 1 + 1) ≃ Fin (1 * 1 + 1 + 1 + 1) where
  toFun := ![0, 2, 3, 1]
  invFun := ![0, 3, 1, 2]
  left_inv := by decide
  right_inv := by decide

theorem quadricCoordinates_quadricCoordinateEquiv (l : Fin (1 * 1 + 1 + 1 + 1)) :
    quadricCoordinates k (quadricCoordinateEquiv l) = quadricSegreCoordinates k l := by
  fin_cases l <;> rfl

theorem quadricCoordinateHom_comp_comparisonHom :
    (quadricCoordinateHom k).comp (projectiveSpaceComparisonHom k (1 * 1 + 1 + 1)
      quadricCoordinateEquiv) = quadricSegreHom k := by
  apply GradedRingHom.ext
  intro P
  induction P using MvPolynomial.induction_on with
  | C r =>
    exact RingHom.congr_fun (ulift_int_ringHom_ext
      (((quadricCoordinateHom k).comp (projectiveSpaceComparisonHom k (1 * 1 + 1 + 1)
        quadricCoordinateEquiv)).toRingHom.comp C) ((quadricSegreHom k).toRingHom.comp C)) r
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p l hp =>
    rw [map_mul, map_mul, hp, GradedRingHom.comp_apply, projectiveSpaceComparisonHom_X,
      quadricCoordinateHom_apply, quadricCoordinateAlgHom_X,
      quadricCoordinates_quadricCoordinateEquiv, quadricSegreHom_X]

/-- **The quadric in `ℙ³_k`.** Under the comparison `Proj k[x, y, z, w] ≅ ℙ³_{Spec k}` (with
`x, y, z, w = z₀₀, z₁₁, z₀₁, z₁₀`), the closed immersion `Q ⟶ Proj k[x, y, z, w]` of the graded
quotient by `xy - zw` is the morphism `Q ⟶ ℙ³_{Spec k}` given by the Segre coordinates. -/
theorem quadricSurfaceι_comp_projectiveSpaceOverSpecIso :
    quadricSurfaceι k ≫ (projectiveSpaceOverSpecIso k (1 * 1 + 1 + 1) quadricCoordinateEquiv).hom =
      quadricSurfaceToProjectiveSpace k := by
  apply pullback.hom_ext
  · have h1 : quadricSurfaceι k ≫ projToProjectiveSpaceInt k (1 * 1 + 1 + 1)
        quadricCoordinateEquiv = quadricSurfaceToProjectiveSpaceInt k := by
      unfold quadricSurfaceι projToProjectiveSpaceInt quadricSurfaceToProjectiveSpaceInt
        GeneratedProj.toProjectiveSpaceInt
      refine (Proj.map_comp ..).symm.trans ?_
      congr 1
      exact quadricCoordinateHom_comp_comparisonHom k
    exact (Category.assoc _ _ _).trans
      ((congrArg _ (projToProjectiveSpaceOverSpec_fst _ _ _)).trans
        (h1.trans (quadricSurfaceToProjectiveSpace_fst k).symm))
  · have h2 : quadricSurfaceι k ≫ Proj.toSpecZero (homogeneousSubmodule (Fin (1 * 1 + 1 + 1 + 1)) k) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (homogeneousSubmodule (Fin (1 * 1 + 1 + 1 + 1)) k 0))) =
        quadricSurfaceToSpec k := by
      rw [quadricSurfaceι, ← Category.assoc, projMap_toSpecZero, Category.assoc, ← Spec.map_comp,
        quadricSurfaceToSpec]
      congr 2
      refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
      simp [quadricCoordinateHom_apply, quadricCoordinateAlgHom]
    exact (Category.assoc _ _ _).trans
      ((congrArg _ (projToProjectiveSpaceOverSpec_projection _ _ _)).trans
        (h2.trans (quadricSurfaceToProjectiveSpace_projection k).symm))

end Comparison

section Main

/-- **The split quadric surface is `ℙ¹ × ℙ¹`.** The isomorphism `ℙ¹_k ×_k ℙ¹_k ≅ Q`. -/
def quadricSurfaceIsoSegreSource : relativeSegreSource 1 1 (Spec (.of k)) ≅ quadricSurface k where
  hom := segreSourceToQuadric k
  inv := quadricSurfaceToSegreSource k
  hom_inv_id := by
    rw [← cancel_mono (relativeSegre 1 1 (Spec (.of k))), Category.assoc,
      quadricSurfaceToSegreSource_comp, segreSourceToQuadric_comp, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (quadricSurfaceToProjectiveSpace k), Category.assoc,
      segreSourceToQuadric_comp, quadricSurfaceToSegreSource_comp, Category.id_comp]

/-- **The split quadric surface is `ℙ¹ × ℙ¹`.** The relative Segre embedding
`ℙ¹_k ×_k ℙ¹_k ⟶ ℙ³_{Spec k}` is the isomorphism `ℙ¹_k ×_k ℙ¹_k ≅ Q` followed by the closed
immersion `Q ⟶ ℙ³_{Spec k}` given by the Segre coordinates `z_{ij} = sᵢuⱼ`. -/
theorem relativeSegre_eq_quadricSurfaceIsoSegreSource_hom_comp :
    relativeSegre 1 1 (Spec (.of k)) =
      (quadricSurfaceIsoSegreSource k).hom ≫ quadricSurfaceToProjectiveSpace k :=
  (segreSourceToQuadric_comp k).symm

/-- **The split quadric surface is `ℙ¹ × ℙ¹`.** With `ℙ³_{Spec k} ≅ Proj k[x, y, z, w]` and
`x, y, z, w = z₀₀, z₁₁, z₀₁, z₁₀`, the relative Segre embedding `ℙ¹_k ×_k ℙ¹_k ⟶ ℙ³_{Spec k}` is
the isomorphism `ℙ¹_k ×_k ℙ¹_k ≅ Q` followed by the closed immersion
`Q = Proj k[x, y, z, w]/(xy - zw) ⟶ Proj k[x, y, z, w]` (`quadricSurfaceι`, whose homogeneous
kernel is `(xy - zw)` by `ker_quadricCoordinateAlgHom`) and the comparison isomorphism. -/
theorem relativeSegre_eq_quadricSurfaceι :
    relativeSegre 1 1 (Spec (.of k)) =
      (quadricSurfaceIsoSegreSource k).hom ≫ quadricSurfaceι k ≫
        (projectiveSpaceOverSpecIso k (1 * 1 + 1 + 1) quadricCoordinateEquiv).hom := by
  rw [quadricSurfaceι_comp_projectiveSpaceOverSpecIso]
  exact relativeSegre_eq_quadricSurfaceIsoSegreSource_hom_comp k

end Main

end Hartshorne
