/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BirationalSectionAlgebraModel
import Hartshorne.Scheme.RelativeProjVeronese

/-!
# The relative homogeneous coordinate algebra of a closed subscheme of `ℙʳ_X`

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.17, Steps 2–3 (pp. 166–167).

Let `i : Z ⟶ ℙʳ_X` be a closed immersion of an integral scheme and `f = π ∘ i`. Over an affine
open `U ⊆ X` the embedding `f⁻¹(U) ⊆ ℙʳ_{Spec Γ(X, U)}` (`SectionAlgebraModel.chartEmbedding`)
has the homogeneous coordinate ring `T(U) = Γ(X, U)[x₀, …, xᵣ] / I_U`. For an integral `Z` the
saturated ideal `I_U` is the homogeneous prime of the image of the generic point of `Z`
(`SectionAlgebraModel.chartIdeal`). This file shows that these rings glue to a quasi-coherent
graded `𝒪_X`-algebra.

* `SectionAlgebraModel.projMap_polyMap_comp_projectiveSpaceOverSpecIso`: naturality of
  `Proj R[x] ≅ ℙʳ_{Spec R}` in `R`.
* `SectionAlgebraModel.homOfLE_chartEmbedding`: the embeddings over `U ⊆ V` are compatible.
* `SectionAlgebraModel.comap_chartIdeal`: `I_V` is the preimage of `I_U` under
  `Γ(X, V)[x] → Γ(X, U)[x]`.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace SectionAlgebraModel

attribute [local instance] MvPolynomial.gradedAlgebra

variable {r : ℕ}

/-! ### Naturality of `Proj R[x] ≅ ℙʳ_{Spec R}` -/

section Naturality

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- `MvPolynomial.map ρ : R[x₀, …, xᵣ] → R'[x₀, …, xᵣ]` as a graded ring homomorphism. -/
def polyMap (ρ : R →+* R') :
    MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R →+*ᵍ
      MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R' where
  __ := MvPolynomial.map ρ
  map_mem {n p} hp := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hp ⊢
    exact hp.map ρ

@[simp]
theorem polyMap_apply (ρ : R →+* R') (p : MvPolynomial (Fin (r + 1)) R) :
    polyMap (r := r) ρ p = MvPolynomial.map ρ p :=
  rfl

theorem polyMap_comp_comparisonHom (ρ : R →+* R') :
    (polyMap (r := r) ρ).comp (projectiveSpaceComparisonHom R r (Equiv.refl _)) =
      projectiveSpaceComparisonHom R' r (Equiv.refl _) := by
  have h : (MvPolynomial.map ρ).comp
      (projectiveSpaceComparisonHom R r (Equiv.refl _)).toRingHom =
        (projectiveSpaceComparisonHom R' r (Equiv.refl _)).toRingHom :=
    MvPolynomial.ringHom_ext (fun c => RingHom.congr_fun (ulift_int_ringHom_ext
      (((MvPolynomial.map ρ).comp
        (projectiveSpaceComparisonHom R r (Equiv.refl _)).toRingHom).comp MvPolynomial.C)
      ((projectiveSpaceComparisonHom R' r (Equiv.refl _)).toRingHom.comp MvPolynomial.C)) c)
      (fun j => by
        change MvPolynomial.map ρ (projectiveSpaceComparisonHom R r (Equiv.refl _)
          (MvPolynomial.X j)) = projectiveSpaceComparisonHom R' r (Equiv.refl _) (MvPolynomial.X j)
        rw [projectiveSpaceComparisonHom_X, projectiveSpaceComparisonHom_X, MvPolynomial.map_X])
  exact GradedRingHom.ext fun p => RingHom.congr_fun h p

theorem irrelevant_le_map_polyMap (ρ : R →+* R') :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R') ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R)).map
        (polyMap ρ) := by
  have h1 := GeneratedProj.irrelevant_le_map_evalGradedHom
    (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R') (projectiveSpaceGenerators_mem R' r _)
    (adjoin_projectiveSpaceGenerators R' r (Equiv.refl _))
  have hle : (HomogeneousIdeal.irrelevant (GeneratedProj.intGrading.{u} r)).map
      (projectiveSpaceComparisonHom R r (Equiv.refl _)) ≤
        HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R) :=
    HomogeneousIdeal.map_le_of_le_comap _ <|
      (HomogeneousIdeal.irrelevant_le (GeneratedProj.intGrading.{u} r)).2
      fun _ hi _ ha => HomogeneousIdeal.mem_irrelevant_of_mem
        (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) R) hi
        ((projectiveSpaceComparisonHom R r (Equiv.refl _)).map_mem ha)
  show (HomogeneousIdeal.irrelevant _).toIdeal ≤ (HomogeneousIdeal.map _ _).toIdeal
  refine h1.trans ?_
  change (HomogeneousIdeal.map (projectiveSpaceComparisonHom R' r (Equiv.refl _))
    (HomogeneousIdeal.irrelevant _)).toIdeal ≤ _
  rw [← polyMap_comp_comparisonHom ρ, HomogeneousIdeal.map_comp]
  exact HomogeneousIdeal.map_mono _ hle

private theorem projMap_congr {A B σ τ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {φ ψ : 𝒜 →+*ᵍ ℬ} (h : φ = ψ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    Proj.map φ hφ = Proj.map ψ hψ := by
  subst h
  rfl

private theorem projectiveSpaceOverSpecIso_hom_fst' (R : Type u) [CommRing R] :
    (projectiveSpaceOverSpecIso R r (Equiv.refl _)).hom ≫
        pullback.fst (projectiveSpaceOverIntegersMap r) (schemeToSpecZ (Spec (.of R))) =
      Proj.map (projectiveSpaceComparisonHom R r (Equiv.refl _))
        (GeneratedProj.irrelevant_le_map_evalGradedHom _ (projectiveSpaceGenerators_mem R r _)
          (adjoin_projectiveSpaceGenerators R r _)) := by
  rw [projectiveSpaceOverSpecIso_hom, projToProjectiveSpaceOverSpec_fst]
  rfl

/-- **Naturality of `Proj R[x₀, …, xᵣ] ≅ ℙʳ_{Spec R}` in `R`.** -/
theorem projMap_polyMap_comp_projectiveSpaceOverSpecIso {R R' : CommRingCat.{u}} (ρ : R ⟶ R') :
    Proj.map (polyMap (r := r) ρ.hom) (irrelevant_le_map_polyMap ρ.hom) ≫
        (projectiveSpaceOverSpecIso R r (Equiv.refl _)).hom =
      (projectiveSpaceOverSpecIso R' r (Equiv.refl _)).hom ≫
        projectiveSpaceOverSchemeMap r (Spec.map ρ) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    erw [projectiveSpaceOverSchemeMap_fst]
    rw [projectiveSpaceOverSpecIso_hom_fst', projectiveSpaceOverSpecIso_hom_fst']
    exact (Proj.map_comp _ _ _ _).symm.trans (projMap_congr (polyMap_comp_comparisonHom ρ.hom) _ _)
  · change _ ≫ _ ≫ projectiveSpaceOverSchemeProjection r _ =
      _ ≫ _ ≫ projectiveSpaceOverSchemeProjection r _
    rw [projectiveSpaceOverSchemeMap_projection, projectiveSpaceOverSpecIso_hom,
      projectiveSpaceOverSpecIso_hom, projToProjectiveSpaceOverSpec_projection,
      projToProjectiveSpaceOverSpec_projection_assoc, ← Category.assoc, projMap_toSpecZero,
      Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext ?_)
    exact MvPolynomial.map_C _ _

end Naturality

/-! ### Compatibility of the embeddings over affine opens -/

section Compat

variable {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X)

/-- For affine opens `U ⊆ V` of `X`, the embedding `f⁻¹(U) ⟶ ℙʳ_{Spec Γ(X, U)}` followed by
`ℙʳ_{Spec Γ(X, U)} ⟶ ℙʳ_{Spec Γ(X, V)}` is `f⁻¹(U) ⊆ f⁻¹(V) ⟶ ℙʳ_{Spec Γ(X, V)}`. -/
theorem homOfLE_chartEmbedding {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) :
    Z.homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono h) ≫
        chartEmbedding i hV =
      chartEmbedding i hU ≫
        projectiveSpaceOverSchemeMap r (Spec.map (X.presheaf.map (homOfLE h).op)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, chartEmbedding_fst, projectiveSpaceOverSchemeMap_fst,
      chartEmbedding_fst, Scheme.homOfLE_ι_assoc]
  · change _ ≫ _ ≫ projectiveSpaceOverSchemeProjection r _ =
      _ ≫ _ ≫ projectiveSpaceOverSchemeProjection r _
    rw [projectiveSpaceOverSchemeMap_projection, chartEmbedding_projection,
      chartEmbedding_projection_assoc, ← cancel_mono hV.fromSpec, Category.assoc,
      Category.assoc, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
      hV.map_fromSpec hU (homOfLE h).op, IsAffineOpen.isoSpec_hom_fromSpec, morphismRestrict_ι,
      morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

/-- The point of `Proj Γ(X, U)[x]` corresponding to a point of `f⁻¹(U)` under the embedding
over `U`. -/
def chartPoint {U : X.Opens} (hU : IsAffineOpen U)
    (z : ((i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U).toScheme) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U)) :=
  (projectiveSpaceOverSpecIso Γ(X, U) r (Equiv.refl _)).inv (chartEmbedding i hU z)

theorem projMap_chartPoint {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) (z : ((i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U).toScheme) :
    Proj.map (polyMap (r := r) (X.presheaf.map (homOfLE h).op).hom)
        (irrelevant_le_map_polyMap _) (chartPoint i hU z) =
      chartPoint i hV
        (Z.homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono h) z) := by
  have hN := projMap_polyMap_comp_projectiveSpaceOverSpecIso (r := r)
    (X.presheaf.map (homOfLE h).op)
  rw [← Iso.eq_comp_inv, Category.assoc] at hN
  have key : chartEmbedding i hU ≫ (projectiveSpaceOverSpecIso Γ(X, U) r (Equiv.refl _)).inv ≫
      Proj.map (polyMap (r := r) (X.presheaf.map (homOfLE h).op).hom)
        (irrelevant_le_map_polyMap _) =
      Z.homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono h) ≫
        chartEmbedding i hV ≫ (projectiveSpaceOverSpecIso Γ(X, V) r (Equiv.refl _)).inv := by
    rw [(Iso.inv_comp_eq _).mpr hN, reassoc_of% homOfLE_chartEmbedding i hU hV h]
  exact congr($key z)

variable [IsIntegral Z]

/-- **The homogeneous ideal of `f⁻¹(U) ⊆ ℙʳ_{Spec Γ(X, U)}`**, for `Z` integral: the homogeneous
prime of the image of the generic point of `Z` (and the unit ideal if `f⁻¹(U)` is empty). -/
def chartIdeal (U : X.Opens) (hU : IsAffineOpen U) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U)) := by
  classical
  exact if h : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U then
    (chartPoint i hU ⟨_, h⟩).asHomogeneousIdeal else ⊤

theorem chartIdeal_of_mem {U : X.Opens} (hU : IsAffineOpen U)
    (h : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U) :
    chartIdeal i U hU = (chartPoint i hU ⟨_, h⟩).asHomogeneousIdeal :=
  dif_pos h

theorem chartIdeal_of_not_mem {U : X.Opens} (hU : IsAffineOpen U)
    (h : genericPoint Z ∉ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U) :
    chartIdeal i U hU = ⊤ :=
  dif_neg h

/-- **Restriction of the homogeneous ideals.** For affine opens `U ⊆ V` with `f⁻¹(U)` nonempty,
`I_V` is the preimage of `I_U` under `Γ(X, V)[x] → Γ(X, U)[x]`. -/
theorem comap_chartIdeal {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V)
    (hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U) :
    (chartIdeal i U hU).comap (polyMap (r := r) (X.presheaf.map (homOfLE h).op).hom) =
      chartIdeal i V hV := by
  have hη' := (i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono h hη
  rw [chartIdeal_of_mem i hU hη, chartIdeal_of_mem i hV hη']
  have := projMap_chartPoint i hU hV h ⟨_, hη⟩
  have hz : Z.homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono h)
      ⟨genericPoint Z, hη⟩ = ⟨genericPoint Z, hη'⟩ := by
    apply Subtype.ext
    exact congr($(Scheme.homOfLE_ι Z ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
      h)) ⟨genericPoint Z, hη⟩)
  rw [hz] at this
  rw [← this]
  rfl

theorem chartIdeal_le_comap {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) :
    chartIdeal i V hV ≤
      (chartIdeal i U hU).comap (polyMap (r := r) (X.presheaf.map (homOfLE h).op).hom) := by
  by_cases hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U
  · exact (comap_chartIdeal i hU hV h hη).ge
  · rw [chartIdeal_of_not_mem i hU hη]
    intro x _
    trivial

end Compat

end SectionAlgebraModel

end Hartshorne
