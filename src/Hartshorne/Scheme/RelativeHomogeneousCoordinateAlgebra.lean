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

/-! ### Localizing a quotient of a polynomial ring -/

section Localization

variable {σ : Type*} {R R' : Type u} [CommRing R] [CommRing R'] (ρ : R →+* R') (g : R)

/-- If `R' = R[1/g]`, every polynomial over `R'` is the image of a polynomial over `R` divided by a
power of `g`. -/
private theorem exists_mul_pow_eq_map (hρ : letI := ρ.toAlgebra; IsLocalization.Away g R')
    (p' : MvPolynomial σ R') :
    ∃ (p : MvPolynomial σ R) (k : ℕ), p' * MvPolynomial.C (ρ g) ^ k = MvPolynomial.map ρ p := by
  let := ρ.toAlgebra
  induction p' using MvPolynomial.induction_on with
  | C c =>
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) c
    refine ⟨MvPolynomial.C a, k, ?_⟩
    rw [MvPolynomial.map_C, ← map_pow, ← map_mul]
    congr 1
    simpa [RingHom.algebraMap_toAlgebra] using h
  | add p q hp hq =>
    obtain ⟨P, k, hP⟩ := hp
    obtain ⟨Q, l, hQ⟩ := hq
    refine ⟨P * MvPolynomial.C g ^ l + Q * MvPolynomial.C g ^ k, k + l, ?_⟩
    simp only [map_add, map_mul, map_pow, MvPolynomial.map_C, ← hP, ← hQ]
    ring
  | mul_X p j hp =>
    obtain ⟨P, k, hP⟩ := hp
    refine ⟨P * MvPolynomial.X j, k, ?_⟩
    rw [map_mul, MvPolynomial.map_X, ← hP]
    ring

/-- **Localizing a graded quotient on the base.** Let `R' = R[1/g]`, `I ⊆ R[x]` and
`J ⊆ R'[x]` with `J ∩ R[x] = I`. Then `R'[x]/J = (R[x]/I)[1/g]`. -/
theorem isLocalizationAway_quotientMap (hρ : letI := ρ.toAlgebra; IsLocalization.Away g R')
    (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial σ R'))
    (hIJ : J.comap (MvPolynomial.map ρ) = I) :
    letI := (Ideal.quotientMap J (MvPolynomial.map ρ) hIJ.ge).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk I (MvPolynomial.C g)) (MvPolynomial σ R' ⧸ J) := by
  let := (Ideal.quotientMap J (MvPolynomial.map ρ) hIJ.ge).toAlgebra
  have halg : ∀ p, algebraMap (MvPolynomial σ R ⧸ I) (MvPolynomial σ R' ⧸ J)
      (Ideal.Quotient.mk I p) = Ideal.Quotient.mk J (MvPolynomial.map ρ p) := fun p =>
    Ideal.quotientMap_mk
  constructor; constructor
  · rintro ⟨_, n, rfl⟩
    change IsUnit (algebraMap _ _ (Ideal.Quotient.mk I (MvPolynomial.C g) ^ n))
    rw [map_pow, halg, MvPolynomial.map_C]
    let := ρ.toAlgebra
    exact (((IsLocalization.Away.algebraMap_isUnit g).map MvPolynomial.C).map
      (Ideal.Quotient.mk J)).pow n
  · intro z
    obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, k, h⟩ := exists_mul_pow_eq_map ρ g hρ p'
    refine ⟨⟨Ideal.Quotient.mk I p, ⟨_, k, rfl⟩⟩, ?_⟩
    simp only [map_pow, halg, MvPolynomial.map_C]
    rw [← map_pow, ← map_mul, h]
  · intro x y e
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨1, ?_⟩
    rw [halg, halg, Ideal.Quotient.eq, ← map_sub] at e
    have : p - q ∈ I := by rw [← hIJ]; exact e
    simp only [OneMemClass.coe_one, one_mul]
    exact Ideal.Quotient.eq.mpr this

/-- A map to the zero ring is the localization at an element mapping to zero. -/
theorem isLocalizationAway_of_subsingleton {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Subsingleton B] {x : A} (hx : x = 0) : IsLocalization.Away x B := by
  constructor; constructor
  · intro _
    exact isUnit_of_subsingleton _
  · intro z
    exact ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
  · intro a b _
    refine ⟨⟨x, 1, pow_one x⟩, ?_⟩
    simp [hx]

end Localization

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

theorem comap_map_chartIdeal {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) (hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U) :
    (chartIdeal i U hU).toIdeal.comap (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom) =
      (chartIdeal i V hV).toIdeal :=
  congrArg HomogeneousIdeal.toIdeal (comap_chartIdeal i hU hV h hη)

theorem chartIdeal_le_comap {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ≤ V) :
    chartIdeal i V hV ≤
      (chartIdeal i U hU).comap (polyMap (r := r) (X.presheaf.map (homOfLE h).op).hom) := by
  by_cases hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U
  · exact (comap_chartIdeal i hU hV h hη).ge
  · rw [chartIdeal_of_not_mem i hU hη]
    intro x _
    trivial

omit [IsIntegral Z] in
/-- **The degree-zero part of `I_U`**: for `z ∈ f⁻¹(U)` and `a ∈ Γ(X, U)`, the constant `a` lies in
the homogeneous prime of `z` iff `f(z) ∉ D(a)`. -/
theorem C_mem_chartPoint_iff {U : X.Opens} (hU : IsAffineOpen U)
    (z : ((i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U).toScheme) (a : Γ(X, U)) :
    MvPolynomial.C a ∈ (chartPoint i hU z).asHomogeneousIdeal ↔
      (i ≫ projectiveSpaceOverSchemeProjection r X) z.1 ∉ X.basicOpen a := by
  let P := projectiveSpaceOverSpecIso Γ(X, U) r (Equiv.refl _)
  have h1 : chartPoint i hU z ∈ Proj.basicOpen _ (MvPolynomial.C a) ↔
      chartPoint i hU z ∈ (P.hom ≫ projectiveSpaceOverSchemeProjection r _) ⁻¹ᵁ
        PrimeSpectrum.basicOpen a := by
    rw [projectiveSpaceOverSpecIso_hom, projToProjectiveSpaceOverSpec_projection,
      toSpecZero_comp_preimage_basicOpen]
    rfl
  have h2 : (P.hom ≫ projectiveSpaceOverSchemeProjection r _) (chartPoint i hU z) =
      hU.isoSpec.hom (((i ≫ projectiveSpaceOverSchemeProjection r X) ∣_ U) z) := by
    have hPP : ∀ y, P.hom (P.inv y) = y := fun y => by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [Scheme.Hom.comp_apply, chartPoint, hPP]
    exact congr($(chartEmbedding_projection i hU) z)
  have h3 : hU.fromSpec (hU.isoSpec.hom (((i ≫ projectiveSpaceOverSchemeProjection r X) ∣_ U) z)) =
      (i ≫ projectiveSpaceOverSchemeProjection r X) z.1 := by
    rw [← Scheme.Hom.comp_apply, IsAffineOpen.isoSpec_hom_fromSpec, ← Scheme.Hom.comp_apply,
      morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  rw [← not_iff_not, not_not, ← Proj.mem_basicOpen, h1]
  change (P.hom ≫ projectiveSpaceOverSchemeProjection r _) (chartPoint i hU z) ∈
    PrimeSpectrum.basicOpen a ↔ _
  rw [h2, ← h3, ← IsAffineOpen.fromSpec_preimage_basicOpen hU]
  rfl

theorem C_mem_chartIdeal_iff {U : X.Opens} (hU : IsAffineOpen U)
    (h : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U) (a : Γ(X, U)) :
    MvPolynomial.C a ∈ chartIdeal i U hU ↔
      (i ≫ projectiveSpaceOverSchemeProjection r X) (genericPoint Z) ∉ X.basicOpen a := by
  rw [chartIdeal_of_mem i hU h]
  exact C_mem_chartPoint_iff i hU ⟨_, h⟩ a

end Compat

/-! ### The quasi-coherent graded algebra `U ↦ Γ(X, U)[x] / I_U` -/

section CoordinateAlgebra

open Scheme.AffineZariskiSite

variable {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X) [IsIntegral Z]

/-- The restriction `Γ(X, V)[x] / I_V → Γ(X, U)[x] / I_U` for affine opens `U ⊆ V`. -/
def coordRestrict {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V) :
    MvPolynomial (Fin (r + 1)) Γ(X, V) ⧸ (chartIdeal i V hV).toIdeal →+*
      MvPolynomial (Fin (r + 1)) Γ(X, U) ⧸ (chartIdeal i U hU).toIdeal :=
  Ideal.quotientMap _ (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom)
    (chartIdeal_le_comap i hU hV h)

theorem coordRestrict_mk {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ≤ V)
    (p : MvPolynomial (Fin (r + 1)) Γ(X, V)) :
    coordRestrict i hU hV h (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (X.presheaf.map (homOfLE h).op).hom p) :=
  Ideal.quotientMap_mk

/-- The functor `U ↦ Γ(X, U)[x] / I_U` on the affine opens of `X`. -/
abbrev coordFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of
    (MvPolynomial (Fin (r + 1)) Γ(X, U.unop.1) ⧸ (chartIdeal i U.unop.1 U.unop.2).toIdeal)
  map f := CommRingCat.ofHom (coordRestrict i _ _ (toOpens_mono f.unop.le))
  map_id U := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_))
    simp only [RingHom.comp_apply, CommRingCat.hom_ofHom, coordRestrict_mk, CommRingCat.hom_id,
      RingHom.id_apply]
    congr 1
    rw [show (homOfLE (toOpens_mono (𝟙 U : U ⟶ U).unop.le)).op = 𝟙 (op U.unop.1) from
      Subsingleton.elim _ _, X.presheaf.map_id, CommRingCat.hom_id, MvPolynomial.map_id]
  map_comp f g := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_))
    simp only [RingHom.comp_apply, CommRingCat.hom_ofHom, coordRestrict_mk, CommRingCat.hom_comp]
    rw [MvPolynomial.map_map, ← CommRingCat.hom_comp, ← X.presheaf.map_comp]
    rfl

variable (r) in
omit [IsIntegral Z] in
private theorem C_mem_zero (U : X.Opens) (a : Γ(X, U)) :
    (MvPolynomial.C a : MvPolynomial (Fin (r + 1)) Γ(X, U)) ∈
      MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U) 0 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ a)

/-- Quasi-coherence of the relative homogeneous coordinate algebra:
`Γ(X, D(g))[x] / I_{D(g)} = (Γ(X, U)[x] / I_U)[1/g]`. -/
theorem coordinateAlgebra_isLocalizationAway (U : X.AffineZariskiSite) (g : Γ(X, U.1)) :
    letI := (coordRestrict i (U.basicOpen g).2 U.2 (X.basicOpen_le g)).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (chartIdeal i U.1 U.2).toIdeal (MvPolynomial.C g))
      (MvPolynomial (Fin (r + 1)) Γ(X, (U.basicOpen g).1) ⧸
        (chartIdeal i (U.basicOpen g).1 (U.basicOpen g).2).toIdeal) := by
  by_cases hη : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ X.basicOpen g
  · exact isLocalizationAway_quotientMap (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g
      (U.2.isLocalization_basicOpen g) (chartIdeal i U.1 U.2).toIdeal
      (chartIdeal i (X.basicOpen g) (U.basicOpen g).2).toIdeal
      (comap_map_chartIdeal i (U.basicOpen g).2 U.2 (X.basicOpen_le g) hη)
  · let := (coordRestrict i (U.basicOpen g).2 U.2 (X.basicOpen_le g)).toAlgebra
    have hJ : chartIdeal i (U.basicOpen g).1 (U.basicOpen g).2 = ⊤ := chartIdeal_of_not_mem i _ hη
    have : Subsingleton (MvPolynomial (Fin (r + 1)) Γ(X, (U.basicOpen g).1) ⧸
        (chartIdeal i (U.basicOpen g).1 (U.basicOpen g).2).toIdeal) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [hJ]; rfl)
    refine isLocalizationAway_of_subsingleton (Ideal.Quotient.eq_zero_iff_mem.mpr ?_)
    by_cases hηU : genericPoint Z ∈ (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1
    · exact (C_mem_chartIdeal_iff i U.2 hηU g).mpr hη
    · rw [chartIdeal_of_not_mem i U.2 hηU]
      trivial

/-- **The relative homogeneous coordinate algebra** of the closed subscheme `Z ⊆ ℙʳ_X` (`Z`
integral): the quasi-coherent graded `𝒪_X`-algebra `U ↦ Γ(X, U)[x₀, …, xᵣ] / I_U`, where `I_U` is
the homogeneous ideal of `f⁻¹(U) ⊆ ℙʳ_{Spec Γ(X, U)}`. Quasi-coherence (`T(D(g)) = T(U)_g`) holds
because `I_{D(g)} ∩ Γ(X, U)[x] = I_U`. -/
abbrev coordinateAlgebra : QuasiCoherentGradedAlgebra X where
  obj := coordFunctor i
  structureMap :=
    { app U := CommRingCat.ofHom ((Ideal.Quotient.mk _).comp MvPolynomial.C)
      naturality U V f := by
        ext a
        change Ideal.Quotient.mk (chartIdeal i V.unop.1 V.unop.2).toIdeal
            (MvPolynomial.C (X.presheaf.map ((toOpensFunctor X).map f.unop).op a)) =
          coordRestrict i V.unop.2 U.unop.2 (toOpens_mono f.unop.le)
            (Ideal.Quotient.mk _ (MvPolynomial.C a))
        rw [coordRestrict_mk, MvPolynomial.map_C]
        rfl }
  coequifibered := coequifibered_iff_forall_isLocalizationAway.mpr fun U g =>
    coordinateAlgebra_isLocalizationAway i U g
  grading U := gradedQuotient (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U.1))
    (chartIdeal i U.1 U.2)
  gradedRing _ := inferInstance
  map_mem f n x hx := by
    obtain ⟨p, hp, rfl⟩ := mem_gradedQuotient_iff.mp hx
    change coordRestrict i _ _ _ (Ideal.Quotient.mk _ p) ∈ _
    rw [coordRestrict_mk]
    exact mk_mem_gradedQuotient ((polyMap (r := r) _).map_mem hp)
  structureMap_mem U a := mk_mem_gradedQuotient (C_mem_zero r U.1 a)

end CoordinateAlgebra

end SectionAlgebraModel

end Hartshorne
