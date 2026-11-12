/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoordinateNonvanishingOpen

/-!
# The projective closed-immersion chart criterion

Hartshorne, *Algebraic Geometry*, II, Proposition 7.2 (pp. 151–152).

Let `Y` be an affine scheme (Hartshorne takes `Y = Spec A`), `X` a scheme over `Y`, `L` an
invertible sheaf on `X` with global sections `s₀, …, sₙ`, and `φ : X ⟶ ℙⁿ_Y` the morphism they
define, characterized (Theorem 7.1) by an isomorphism `φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ`
to `sᵢ`. Then `φ` is a closed immersion iff every `X_{sᵢ} = φ⁻¹(D₊(xᵢ))` is affine and every
coordinate-ring map `A[x₀/xᵢ, …, xₙ/xᵢ] → Γ(X_{sᵢ}, 𝒪_X)`, `xⱼ/xᵢ ↦ sⱼ/sᵢ`, is surjective.

* `isClosedImmersion_iff_isAffineOpen_and_surjective`: the criterion with the coordinate ring of
  `D₊(xᵢ)` written as `Γ(D₊(xᵢ), 𝒪)` and the map induced by `φ`;
* `projectiveSpaceChartPolynomialMap_surjective`: `Γ(D₊(xᵢ), 𝒪)` is generated over
  `A = Γ(Y, 𝒪_Y)` by the ratios `xⱼ/xᵢ`;
* `isClosedImmersion_iff_isAffineOpen_and_surjective_chartSectionPolynomialMap`: the criterion
  with the polynomial ring `A[y₀, …, yₙ]` and the map `yⱼ ↦ sⱼ/sᵢ`.

The proof uses that being a closed immersion is local on the target, applied to the affine cover
of `ℙⁿ_Y` by the `D₊(xᵢ)`: over the affine `D₊(xᵢ)`, a closed subscheme is the spectrum of a
quotient ring, so it is affine with surjective ring map (Exercise II.3.11(b)), and conversely a
surjective ring map gives a closed immersion of spectra (Exercise II.2.18(c)).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

section Charts

variable (n : ℕ) (Y : Scheme.{u})

/-- The standard opens `D₊(xᵢ)` cover `ℙⁿ_Y`. -/
theorem iSup_projectiveSpaceChart : ⨆ i, projectiveSpaceChart n Y i = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨k, hk⟩ := exists_mem_chartPreimage (𝟙 (projectiveSpaceOverScheme n Y)) x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩

/-- Over an affine base, each standard open `D₊(xᵢ)` of `ℙⁿ_Y` is affine. -/
theorem isAffineOpen_projectiveSpaceChart [IsAffine Y] (i : Fin (n + 1)) :
    IsAffineOpen (projectiveSpaceChart n Y i) := by
  have : IsAffineHom (schemeToSpecZ Y) := isAffineHom_of_isAffine _
  have : IsAffineHom (toProjInt n Y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback _ _).flip this
  exact (Proj.isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule_one _ i)
    Nat.one_pos).preimage _

end Charts

section Restrict

/-- For an affine open `U` of the target with preimage `V`, the restriction `f⁻¹(U) ⟶ U` is a
closed immersion iff `V` is affine and `Γ(U, 𝒪) → Γ(V, 𝒪)` is surjective. The forward direction
uses Hartshorne II, Exercise 3.11(b), and the converse Exercise 2.18(c). -/
theorem isClosedImmersion_morphismRestrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (h : f ⁻¹ᵁ U = V) :
    IsClosedImmersion (f ∣_ U) ↔ IsAffineOpen V ∧ Function.Surjective (f.appLE U V h.ge) := by
  subst h
  have : IsAffine U := hU
  have hsurj : Function.Surjective (f ∣_ U).appTop ↔
      Function.Surjective (f.appLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    exact Scheme.Hom.appLE_congr _ _ U.ι_image_top (f ⁻¹ᵁ U).ι_image_top
      (fun g => Function.Surjective g)
  rw [← hsurj]
  refine ⟨fun _ => ?_, fun ⟨hV, h⟩ => ?_⟩
  · -- A closed subscheme of the affine scheme `U ≅ Spec Γ(U, 𝒪)` is `Spec` of a quotient ring.
    obtain ⟨I, e, he⟩ :=
      (IsClosedImmersion.Spec_iff (f := (f ∣_ U) ≫ U.toScheme.isoSpec.hom)).mp inferInstance
    refine ⟨.of_isIso e.hom, ?_⟩
    have hq : Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop := by
      have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
      rw [← Iso.eq_comp_inv] at hn
      rw [hn]
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, CommRingCat.hom_ofHom]
      exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2.comp
        (Ideal.Quotient.mk_surjective.comp
          (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2)
    have hg : Function.Surjective ((f ∣_ U) ≫ U.toScheme.isoSpec.hom).appTop := by
      rw [he, Scheme.Hom.comp_appTop]
      exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2.comp hq
    rw [Scheme.Hom.comp_appTop] at hg
    exact Function.Surjective.of_comp (f := (f ∣_ U).appTop) hg
  have : IsAffine (f ⁻¹ᵁ U) := hV
  rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (arrowIsoSpecΓOfIsAffine (f ∣_ U))]
  exact IsClosedImmersion.spec_of_surjective _ h

end Restrict

section Criterion

variable {n : ℕ} {X Y : Scheme.{u}} {L : X.Modules} (hL : L.IsInvertible)
  (s : Fin (n + 1) → Γ(L, ⊤)) (φ : X ⟶ projectiveSpaceOverScheme n Y)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n Y i)) = s i)

include he in
/-- **Hartshorne II, Proposition 7.2.** Let `Y` be affine (Hartshorne takes `Y = Spec A`), and let
`φ : X ⟶ ℙⁿ_Y` be the morphism defined by an invertible sheaf `L` and sections `s₀, …, sₙ`, i.e.
with an isomorphism `φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ` to `sᵢ`. Then `φ` is a closed immersion
iff for every `i`, the open `X_{sᵢ} = φ⁻¹(D₊(xᵢ))` is affine and the ring map
`Γ(D₊(xᵢ), 𝒪) → Γ(X_{sᵢ}, 𝒪_X)` induced by `φ` (which sends `xⱼ/xᵢ` to `sⱼ/sᵢ`) is surjective. -/
theorem isClosedImmersion_iff_isAffineOpen_and_surjective [IsAffine Y] :
    IsClosedImmersion φ ↔ ∀ i, IsAffineOpen (nonvanishingLocusOpens hL (s i)) ∧
      Function.Surjective (φ.appLE (projectiveSpaceChart n Y i) (nonvanishingLocusOpens hL (s i))
        (preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i).ge) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (iSup_projectiveSpaceChart n Y)]
  exact forall_congr' fun i => isClosedImmersion_morphismRestrict_iff φ
    (isAffineOpen_projectiveSpaceChart n Y i)
    (preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i)

end Criterion

section Polynomial

/-- In a pushout square of commutative rings, the images of the two maps into the pushout
generate it as a ring. -/
theorem subring_eq_top_of_isPushout {R A B P : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {inl : A ⟶ P} {inr : B ⟶ P} (h : IsPushout f g inl inr) (S : Subring P)
    (hl : ∀ a, inl a ∈ S) (hr : ∀ b, inr b ∈ S) : S = ⊤ := by
  let l : A ⟶ CommRingCat.of S := CommRingCat.ofHom (inl.hom.codRestrict S hl)
  let r : B ⟶ CommRingCat.of S := CommRingCat.ofHom (inr.hom.codRestrict S hr)
  have hw : f ≫ l = g ≫ r := by
    ext x
    exact congrArg (fun F : R ⟶ P => F.hom x) h.w
  have hd : h.desc l r hw ≫ CommRingCat.ofHom S.subtype = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc, Category.comp_id]
      rfl
    · rw [h.inr_desc_assoc, Category.comp_id]
      rfl
  rw [eq_top_iff]
  intro x _
  have hx : S.subtype ((h.desc l r hw).hom x) = x :=
    congrArg (fun F : P ⟶ P => F.hom x) hd
  rw [← hx]
  exact ((h.desc l r hw).hom x).2

variable (n : ℕ) (Y : Scheme.{u})

/-- The ring map `A[y₀, …, yₙ] → Γ(D₊(xᵢ), 𝒪)` on the standard open `D₊(xᵢ) ⊆ ℙⁿ_Y`, where
`A = Γ(Y, 𝒪_Y)`, sending `a ∈ A` to its pullback and `yⱼ` to `xⱼ/xᵢ`. -/
def projectiveSpaceChartPolynomialMap (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) Γ(Y, ⊤) →+*
      Γ(projectiveSpaceOverScheme n Y, projectiveSpaceChart n Y i) :=
  MvPolynomial.eval₂Hom ((projectiveSpaceOverSchemeProjection n Y).appLE ⊤
    (projectiveSpaceChart n Y i) le_top).hom (projectiveSpaceChartRatio n Y i)

/-- Over an affine base `Y` with `A = Γ(Y, 𝒪_Y)`, the coordinate ring `Γ(D₊(xᵢ), 𝒪)` of the
standard open `D₊(xᵢ) ⊆ ℙⁿ_Y` is generated over `A` by the ratios `xⱼ/xᵢ`: it is
`A[x₀/xᵢ, …, xₙ/xᵢ]`. -/
theorem projectiveSpaceChartPolynomialMap_surjective [IsAffine Y] (i : Fin (n + 1)) :
    Function.Surjective (projectiveSpaceChartPolynomialMap n Y i) := by
  let G := projectiveSpaceChartPolynomialMap n Y i
  let V := projectiveSpaceChart n Y i
  -- Sections pulled back from the chart `D₊(xᵢ)` of `ℙⁿ_ℤ` lie in the image of `G`: that chart
  -- ring is `ℤ[x₀/xᵢ, …, xₙ/xᵢ]`.
  have h1 : ∀ c : Γ(projInt.{u} n, chartInt n i),
      (toProjInt n Y).appLE (chartInt n i) V le_rfl c ∈ G.range := by
    intro c
    obtain ⟨a, rfl⟩ : ∃ a, Proj.awayToSection _ (MvPolynomial.X i) a = c :=
      (Proj.basicOpenIsoAway _ (MvPolynomial.X i) (X_mem_homogeneousSubmodule_one _ i)
        Nat.one_pos).commRingCatIsoToRingEquiv.surjective c
    obtain ⟨q, rfl⟩ : ∃ q, chartOfPoly (ULift.{u} ℤ) i q = a :=
      ⟨chartToPoly _ i a, congrArg (fun F => F a) (chartOfPoly_comp_chartToPoly _ i)⟩
    let K : MvPolynomial {j // j ≠ i} (ULift.{u} ℤ) →+* MvPolynomial (Fin (n + 1)) Γ(Y, ⊤) :=
      MvPolynomial.eval₂Hom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
        fun j => MvPolynomial.X j.1
    let H : MvPolynomial {j // j ≠ i} (ULift.{u} ℤ) →+* Γ(projectiveSpaceOverScheme n Y, V) :=
      ((toProjInt n Y).appLE (chartInt n i) V le_rfl).hom.comp
        ((Proj.awayToSection _ (MvPolynomial.X i)).hom.comp (chartOfPoly _ i))
    have hK : G.comp K = H := by
      apply MvPolynomial.ringHom_ext
      · intro r
        exact congrArg (fun F => F r)
          (ulift_int_ringHom_ext ((G.comp K).comp MvPolynomial.C) (H.comp MvPolynomial.C))
      · intro j
        simp only [RingHom.coe_comp, Function.comp_apply, K, H, G, MvPolynomial.coe_eval₂Hom,
          MvPolynomial.eval₂_X, chartOfPoly, projectiveSpaceChartPolynomialMap]
        rw [projectiveSpaceChartRatio, Scheme.Hom.app_eq_appLE]
        rfl
    exact ⟨K q, congrArg (fun F => F q) hK⟩
  -- Sections pulled back from `Y` lie in the image of `G`.
  have h2 : ∀ c : Γ(Y, ⊤),
      (projectiveSpaceOverSchemeProjection n Y).appLE ⊤ V le_top c ∈ G.range :=
    fun c => ⟨MvPolynomial.C c, MvPolynomial.eval₂_C _ _ _⟩
  -- `D₊(xᵢ) ⊆ ℙⁿ_Y` is the fibre product of `D₊(xᵢ) ⊆ ℙⁿ_ℤ` and `Y` over `Spec ℤ`, so its
  -- coordinate ring is the pushout of the coordinate rings, generated by the two images.
  have hpb := Scheme.Hom.isPullback_resLE
    (IsPullback.of_hasPullback (projectiveSpaceOverIntegersMap.{u} n) (schemeToSpecZ Y))
    (US := ⊤) (UT := ⊤) (UX := chartInt n i) (UY := V) le_top le_top
    (by simp [V, projectiveSpaceChart]; rfl)
  have : IsAffine (Scheme.Opens.toScheme (X := projectiveSpaceScheme (ULift.{u} ℤ) n)
      (chartInt n i)) :=
    Proj.isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule_one _ i) Nat.one_pos
  have : IsAffine (⊤ : Y.Opens).toScheme := isAffineOpen_top Y
  have : IsAffine (⊤ : (Spec (CommRingCat.of (ULift.{u} ℤ))).Opens).toScheme :=
    isAffineOpen_top _
  have htop := subring_eq_top_of_isPushout (isPushout_appTop_of_isPullback hpb)
    (G.range.map V.topIso.inv.hom)
    (fun a => ⟨_, h1 ((chartInt n i).topIso.hom a),
      (ConcreteCategory.congr_hom (Scheme.Hom.resLE_app_top _ _) _).symm⟩)
    (fun b => ⟨_, h2 ((⊤ : Y.Opens).topIso.hom b),
      (ConcreteCategory.congr_hom (Scheme.Hom.resLE_app_top _ _) _).symm⟩)
  intro z
  obtain ⟨w, ⟨q, rfl⟩, hw⟩ :=
    (htop ▸ Subring.mem_top (V.topIso.inv z) : V.topIso.inv z ∈ G.range.map V.topIso.inv.hom)
  exact ⟨q, V.topIso.commRingCatIsoToRingEquiv.symm.injective hw⟩

end Polynomial

section PolynomialCriterion

variable {n : ℕ} {X Y : Scheme.{u}} {L : X.Modules} (hL : L.IsInvertible)
  (s : Fin (n + 1) → Γ(L, ⊤)) (p : X ⟶ Y)

/-- For `X` over `Y` via `p` and `A = Γ(Y, 𝒪_Y)`, the ring map `A[y₀, …, yₙ] → Γ(X_{sᵢ}, 𝒪_X)`
sending `a ∈ A` to its pullback along `p` and `yⱼ` to `sⱼ/sᵢ`. -/
def chartSectionPolynomialMap (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) Γ(Y, ⊤) →+* Γ(X, nonvanishingLocusOpens hL (s i)) :=
  MvPolynomial.eval₂Hom (p.appLE ⊤ (nonvanishingLocusOpens hL (s i)) le_top).hom
    (sectionRatio hL s i)

/-- `chartSectionPolynomialMap` sends `yⱼ` to `sⱼ/sᵢ`: the function `g` on `X_{sᵢ}` with
`sⱼ = g · sᵢ` there. -/
theorem chartSectionPolynomialMap_X_smul (i j : Fin (n + 1)) :
    chartSectionPolynomialMap hL s p i (MvPolynomial.X j) •
        L.presheaf.map (homOfLE (le_top : nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (s i) =
      L.presheaf.map (homOfLE (le_top : nonvanishingLocusOpens hL (s i) ≤ ⊤)).op (s j) := by
  rw [chartSectionPolynomialMap, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
  exact (sectionRatio_spec hL s i j).symm

variable (φ : X ⟶ projectiveSpaceOverScheme n Y)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n Y i)) = s i)

include he in
/-- **Hartshorne II, Proposition 7.2**, with the coordinate rings written as polynomial rings.
Let `X` be a scheme over an affine scheme `Y` via `p` (Hartshorne takes `Y = Spec A`), and let
`φ : X ⟶ ℙⁿ_Y` be the `Y`-morphism defined by an invertible sheaf `L` and sections
`s₀, …, sₙ`, i.e. with an isomorphism `φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ` to `sᵢ`. Then `φ` is a
closed immersion iff for every `i`, the open `X_{sᵢ}` is affine and the ring map
`A[y₀, …, yₙ] → Γ(X_{sᵢ}, 𝒪_X)`, `yⱼ ↦ sⱼ/sᵢ`, is surjective, where `A = Γ(Y, 𝒪_Y)`. -/
theorem isClosedImmersion_iff_isAffineOpen_and_surjective_chartSectionPolynomialMap
    [IsAffine Y] (hp : φ ≫ projectiveSpaceOverSchemeProjection n Y = p) :
    IsClosedImmersion φ ↔ ∀ i, IsAffineOpen (nonvanishingLocusOpens hL (s i)) ∧
      Function.Surjective (chartSectionPolynomialMap hL s p i) := by
  subst hp
  rw [isClosedImmersion_iff_isAffineOpen_and_surjective hL s φ e he]
  refine forall_congr' fun i => and_congr Iff.rfl ?_
  have hfac : chartSectionPolynomialMap hL s (φ ≫ projectiveSpaceOverSchemeProjection n Y) i =
      (φ.appLE (projectiveSpaceChart n Y i) (nonvanishingLocusOpens hL (s i))
        (preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i).ge).hom.comp
        (projectiveSpaceChartPolynomialMap n Y i) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [chartSectionPolynomialMap, projectiveSpaceChartPolynomialMap, RingHom.coe_comp,
        Function.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      exact (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _) a).symm
    · intro j
      refine eq_of_smul_eq hL s i le_rfl ?_
      rw [chartSectionPolynomialMap_X_smul]
      simp only [projectiveSpaceChartPolynomialMap, RingHom.coe_comp, Function.comp_apply,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      exact (appLE_projectiveSpaceChartRatio_smul hL s φ e he i j).symm
  rw [hfac, RingHom.coe_comp]
  exact ⟨fun h => h.comp (projectiveSpaceChartPolynomialMap_surjective n Y i), fun h => h.of_comp⟩

end PolynomialCriterion

end Hartshorne
