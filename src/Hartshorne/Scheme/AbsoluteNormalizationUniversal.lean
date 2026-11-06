/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AbsoluteNormalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# The universal property of normalization

Hartshorne, *Algebraic Geometry*, Exercise II.3.8, p. 91.

If `Z` is a normal integral scheme and `f : Z ⟶ X` is a dominant morphism to an integral
scheme, then `f` factors uniquely through the normalization `X̃ ⟶ X`.

Existence: a normal integral scheme is isomorphic to its own normalization relative to the
generic-point morphism `Spec K(Z) ⟶ Z`, since its affine section rings are integrally closed in
`K(Z)`. Mathlib's universal property of relative normalization, applied to the integral
morphism `Z ×_X X̃ ⟶ Z`, then produces the lift. Uniqueness: two lifts agree on the generic
point, because over an affine chart the sections of `X̃` are fractions of sections of `X`;
they then agree everywhere since `X̃ ⟶ X` is separated and `Z` is reduced.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- On a normal integral scheme, the sections over a nonempty affine open form an integrally
closed domain. -/
theorem isIntegrallyClosed_sections_of_isNormal (Z : Scheme.{u}) [IsIntegral Z] [IsNormal Z]
    {U : Z.Opens} (hU : IsAffineOpen U) [Nonempty U] : IsIntegrallyClosed Γ(Z, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦ ?_
  let y : PrimeSpectrum Γ(Z, U) := ⟨p, inferInstance⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  let _ := TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec y)) p :=
    hU.isLocalization_stalk' y hy
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (Z.presheaf.stalk (hU.fromSpec y))
  exact IsIntegrallyClosed.of_equiv e.symm.toRingEquiv

/-- A dominant morphism of integral schemes sends the generic point to the generic point. -/
theorem map_genericPoint_of_isDominant {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : Z ⟶ X) [IsDominant f] : f (genericPoint Z) = genericPoint X := by
  apply ((genericPoint_spec X).eq _).symm
  have h := (genericPoint_spec Z).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at h
  exact h


/-- A normal integral scheme is its own normalization inside its function field. -/
instance isIso_fromNormalization_of_isNormal (Z : Scheme.{u}) [IsIntegral Z] [IsNormal Z] :
    IsIso (absoluteNormalizationGenericMap Z).fromNormalization := by
  let g := absoluteNormalizationGenericMap Z
  let ι := {U : Z.affineOpens // Nonempty (U : Z.Opens)}
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun i : ι ↦ (i.1 : Z.Opens)) ?_]
  · rintro ⟨⟨U, hU⟩, hne⟩
    rw [MorphismProperty.isomorphisms.iff, isIso_morphismRestrict_iff_isIso_app _ hU,
      g.fromNormalization_app hU]
    let _ := (g.app U).hom.toAlgebra
    suffices IsIso (CommRingCat.ofHom
        (algebraMap Γ(Z, U) (integralClosure Γ(Z, U) Γ(Spec Z.functionField, g ⁻¹ᵁ U)))) from
      inferInstance
    rw [ConcreteCategory.isIso_iff_bijective]
    let e := genericPreimageSectionsAlgEquiv Z U
    have he : ∀ r : Γ(Z, U), e (algebraMap _ _ r) = algebraMap Γ(Z, U) Z.functionField r :=
      e.commutes
    constructor
    · intro r s hrs
      have h := congrArg (fun x ↦ e x.1) hrs
      simp only [CommRingCat.hom_ofHom] at h
      have h' : algebraMap Γ(Z, U) Z.functionField r =
          algebraMap Γ(Z, U) Z.functionField s := by
        rw [← he, ← he]; exact h
      exact Z.germToFunctionField_injective U h'
    · rintro ⟨x, hx⟩
      have : IsFractionRing Γ(Z, U) Z.functionField :=
        functionField_isFractionRing_of_isAffineOpen Z U hU
      have : IsIntegrallyClosed Γ(Z, U) := isIntegrallyClosed_sections_of_isNormal Z hU
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
        ((mem_integralClosure_iff _ _).mp hx |>.map e.toAlgHom)
      refine ⟨y, Subtype.ext (e.injective ?_)⟩
      simpa [he] using hy
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    let V : Z.Opens := (Z.affineCover.f (Z.affineCover.idx x)).opensRange
    have hx : x ∈ V := Z.affineCover.covers x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, isAffineOpen_opensRange _⟩, ⟨⟨x, hx⟩⟩⟩, hx⟩


/-- A dominant morphism of integral schemes is compatible, at the generic points, with a
morphism of function fields. -/
theorem genericMap_comp_eq_SpecMap {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    (f : Z ⟶ X) [IsDominant f] :
    ∃ φ : X.functionField ⟶ Z.functionField,
      absoluteNormalizationGenericMap Z ≫ f =
        Spec.map φ ≫ absoluteNormalizationGenericMap X := by
  have h : f (genericPoint Z) ⤳ genericPoint X := by
    rw [map_genericPoint_of_isDominant f]
  refine ⟨X.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint Z), ?_⟩
  rw [Spec.map_comp, Category.assoc, absoluteNormalizationGenericMap,
    absoluteNormalizationGenericMap, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- Two ring maps into a domain that agree on `ρ`, with `ρ` followed by them injective, agree
when every element of the source becomes a quotient of elements in the image of `ρ`. -/
theorem ringHom_eq_of_cancel {A B T : Type*} [CommRing A] [CommRing B] [CommRing T]
    [IsDomain T] (ρ : A →+* B) (u v : B →+* T) (huv : u.comp ρ = v.comp ρ)
    (hinj : Function.Injective (u.comp ρ))
    (hloc : ∀ t : B, ∃ a s, s ≠ 0 ∧ ρ s * t = ρ a) : u = v := by
  ext t
  obtain ⟨a, s, hs, h⟩ := hloc t
  have hs' : u (ρ s) ≠ 0 := fun h0 ↦ hs (hinj (by simpa using h0))
  have hv : ∀ x, v (ρ x) = u (ρ x) := fun x ↦ (RingHom.congr_fun huv x).symm
  refine mul_left_cancel₀ hs' ?_
  rw [← map_mul, h, ← hv, ← hv, ← map_mul, h]

/-- Two morphisms from the spectrum of a domain agreeing after `p` are equal when they land in
the affine preimage of an affine open over which `p` is a ring extension inside fractions. -/
theorem eq_of_comp_eq_of_isAffineOpen {Y X : Scheme.{u}} (p : Y ⟶ X) {U : X.Opens}
    (hV : IsAffineOpen (p ⁻¹ᵁ U)) {R : CommRingCat.{u}} [IsDomain R] {a₁ a₂ : Spec R ⟶ Y}
    (b : Spec R ⟶ X) (hb₁ : a₁ ≫ p = b) (hb₂ : a₂ ≫ p = b) (hbU : b ⁻¹ᵁ U = ⊤)
    (hinj : Function.Injective (b.appLE U ⊤ hbU.ge))
    (hloc : ∀ t : Γ(Y, p ⁻¹ᵁ U), ∃ a s, s ≠ 0 ∧ p.app U s * t = p.app U a) : a₁ = a₂ := by
  subst hb₁
  have h₁ : a₁ ⁻¹ᵁ p ⁻¹ᵁ U = ⊤ := by rw [← Scheme.Hom.comp_preimage, hbU]
  have h₂ : a₂ ⁻¹ᵁ p ⁻¹ᵁ U = ⊤ := by rw [← Scheme.Hom.comp_preimage, hb₂, hbU]
  have e₁ : p.app U ≫ a₁.appLE (p ⁻¹ᵁ U) ⊤ h₁.ge = (a₁ ≫ p).appLE U ⊤ hbU.ge :=
    (Scheme.Hom.comp_appLE _ _ _ _ _).symm
  have e₂ : p.app U ≫ a₂.appLE (p ⁻¹ᵁ U) ⊤ h₂.ge = (a₁ ≫ p).appLE U ⊤ hbU.ge := by
    refine (Scheme.Hom.comp_appLE _ _ _ _ (by rw [hb₂, hbU])).symm.trans ?_
    congr 1
  have key : a₁.appLE (p ⁻¹ᵁ U) ⊤ h₁.ge = a₂.appLE (p ⁻¹ᵁ U) ⊤ h₂.ge := by
    ext1
    refine ringHom_eq_of_cancel (p.app U).hom _ _ ?_ ?_ hloc
    · rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, e₁, e₂]
    · rw [← CommRingCat.hom_comp, e₁]; exact hinj
  rw [← cancel_epi (Spec R).isoSpec.inv, ← IsAffineOpen.fromSpec_top,
    ← IsAffineOpen.SpecMap_appLE_fromSpec a₁ hV (isAffineOpen_top _) h₁.ge,
    ← IsAffineOpen.SpecMap_appLE_fromSpec a₂ hV (isAffineOpen_top _) h₂.ge, key]


/-- Over a nonempty affine open, every section of the normalization is a quotient of sections
of the base. -/
theorem absoluteNormalizationMap_app_exists_mul_eq (X : Scheme.{u}) [IsIntegral X]
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (t : Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ U)) :
    ∃ a s, s ≠ 0 ∧
      (absoluteNormalizationMap X).app U s * t = (absoluteNormalizationMap X).app U a := by
  let g := absoluteNormalizationGenericMap X
  let _ := (g.app U).hom.toAlgebra
  let e := genericPreimageSectionsAlgEquiv X U
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let i := g.normalizationObjIso hU
  have hν : g.fromNormalization.app U = CommRingCat.ofHom (algebraMap _ _) ≫ i.inv :=
    g.fromNormalization_app hU
  revert t
  change ∀ t : Γ(g.normalization, g.fromNormalization ⁻¹ᵁ U),
    ∃ a s, s ≠ 0 ∧ g.fromNormalization.app U s * t = g.fromNormalization.app U a
  intro t
  let w := i.hom t
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, U)) (e w.1)
  refine ⟨a, s, nonZeroDivisors.ne_zero s.2, ?_⟩
  have h' : algebraMap Γ(X, U) (integralClosure Γ(X, U) Γ(Spec X.functionField, g ⁻¹ᵁ U)) s * w =
      algebraMap _ _ a := by
    apply Subtype.ext
    apply e.injective
    change e (algebraMap _ _ (s : Γ(X, U)) * w.1) = e (algebraMap _ _ a)
    rw [map_mul, e.commutes, e.commutes, mul_comm]
    exact h
  rw [hν, CommRingCat.comp_apply, CommRingCat.comp_apply]
  simp only [CommRingCat.hom_ofHom]
  calc _ = i.inv (algebraMap Γ(X, U) (integralClosure Γ(X, U) Γ(Spec X.functionField, g ⁻¹ᵁ U))
        (s : Γ(X, U)) * w) := by rw [map_mul]; simp [w]
    _ = _ := by rw [h']


/-- Sections over a nonempty open inject into the sections pulled back to the generic point. -/
theorem absoluteNormalizationGenericMap_app_injective (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) [Nonempty U] :
    Function.Injective ((absoluteNormalizationGenericMap X).app U) := by
  let _ := ((absoluteNormalizationGenericMap X).app U).hom.toAlgebra
  intro r s hrs
  apply X.germToFunctionField_injective U
  have h := congrArg (genericPreimageSectionsAlgEquiv X U) hrs
  change genericPreimageSectionsAlgEquiv X U (algebraMap _ _ r) =
    genericPreimageSectionsAlgEquiv X U (algebraMap _ _ s) at h
  rwa [AlgEquiv.commutes, AlgEquiv.commutes] at h

/-- A morphism from the spectrum of a domain that factors through the generic point is injective
on sections over a nonempty open. -/
theorem comp_genericMap_appLE_injective {X : Scheme.{u}} [IsIntegral X]
    {K : CommRingCat.{u}} [IsDomain K] (c : Spec K ⟶ Spec X.functionField) (U : X.Opens)
    [Nonempty U] (h : (c ≫ absoluteNormalizationGenericMap X) ⁻¹ᵁ U = ⊤) :
    Function.Injective ((c ≫ absoluteNormalizationGenericMap X).appLE U ⊤ h.ge) := by
  rw [Scheme.Hom.comp_appLE _ _ U ⊤ h.ge]
  let eR := genericPreimageSectionsRingEquiv X U
  let ψ := ((c.appLE (absoluteNormalizationGenericMap X ⁻¹ᵁ U) ⊤ h.ge).hom).comp
    eR.symm.toRingHom
  intro x y hxy
  apply absoluteNormalizationGenericMap_app_injective X U
  apply eR.injective
  apply ψ.injective
  simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hxy
  exact hxy

/-- The generic-point morphism of an integral scheme is dominant. -/
private theorem absoluteNormalizationGenericMap_isDominant'
    (X : Scheme.{u}) [IsIntegral X] :
    IsDominant (absoluteNormalizationGenericMap X) := by
  constructor
  change Dense (Set.range (absoluteNormalizationGenericMap X))
  rw [dense_iff_inter_open]
  intro U hU hUne
  let V : X.Opens := ⟨U, hU⟩
  let _ : Nonempty V := ⟨⟨hUne.choose, hUne.choose_spec⟩⟩
  let _ : Unique (Spec X.functionField) :=
    inferInstanceAs (Unique (Spec (.of (X.functionField : Type u))))
  let x : Spec X.functionField := default
  have hx : x ∈ absoluteNormalizationGenericMap X ⁻¹ᵁ V := by
    rw [absoluteNormalizationGenericMap_preimage_eq_top]
    trivial
  exact ⟨absoluteNormalizationGenericMap X x, hx, Set.mem_range_self x⟩

/-- **Universal property of normalization** (Hartshorne, Exercise II.3.8): a dominant morphism
from a normal integral scheme to an integral scheme factors uniquely through the
normalization. -/
theorem absoluteNormalization_existsUnique_lift {X Z : Scheme.{u}} [IsIntegral X]
    [IsIntegral Z] [IsNormal Z] (f : Z ⟶ X) [IsDominant f] :
    ∃! g : Z ⟶ absoluteNormalization X, g ≫ absoluteNormalizationMap X = f := by
  obtain ⟨φ, hφ⟩ := genericMap_comp_eq_SpecMap f
  let ηZ := absoluteNormalizationGenericMap Z
  let ηX := absoluteNormalizationGenericMap X
  let ν := absoluteNormalizationMap X
  have hν : ν = ηX.fromNormalization := rfl
  have hlift : ηZ ≫ f = (Spec.map φ ≫ ηX.toNormalization) ≫ ν := by
    rw [hφ]
    change _ = (Spec.map φ ≫ ηX.toNormalization) ≫ ηX.fromNormalization
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
  let l : Spec Z.functionField ⟶ pullback f ν :=
    pullback.lift ηZ (Spec.map φ ≫ ηX.toNormalization) hlift
  let d := ηZ.normalizationDesc l (pullback.fst f ν) (pullback.lift_fst _ _ _).symm
  have uniq : ∀ g₁ g₂ : Z ⟶ absoluteNormalization X, g₁ ≫ ν = f → g₂ ≫ ν = f → g₁ = g₂ := by
    intro g₁ g₂ hg₁ hg₂
    have := absoluteNormalizationGenericMap_isDominant' Z
    let x := genericPoint X
    let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
    have hU : IsAffineOpen U := isAffineOpen_opensRange _
    let _ : Nonempty U := ⟨⟨x, X.affineCover.covers x⟩⟩
    have hbU : (Spec.map φ ≫ ηX) ⁻¹ᵁ U = ⊤ := by
      rw [Scheme.Hom.comp_preimage, absoluteNormalizationGenericMap_preimage_eq_top,
        Scheme.Hom.preimage_top]
    refine ext_of_isDominant_of_isSeparated ν (hg₁.trans hg₂.symm) ηZ ?_
    exact eq_of_comp_eq_of_isAffineOpen ν (hU.preimage ν) (Spec.map φ ≫ ηX)
      (by rw [Category.assoc, hg₁, hφ]) (by rw [Category.assoc, hg₂, hφ]) hbU
      (comp_genericMap_appLE_injective (Spec.map φ) U hbU)
      (absoluteNormalizationMap_app_exists_mul_eq X hU)
  refine ⟨inv ηZ.fromNormalization ≫ d ≫ pullback.snd f ν, ?_, fun g hg ↦ uniq _ _ hg ?_⟩ <;>
  · simp only [Category.assoc]
    rw [← pullback.condition, ηZ.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]

end Hartshorne
