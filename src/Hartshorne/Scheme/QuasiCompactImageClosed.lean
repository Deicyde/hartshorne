/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Closed images and specialization

Hartshorne, *Algebraic Geometry*, II.4, Lemma 4.5, p. 98: for a quasi-compact
morphism of schemes `f : X ⟶ Y`, the image `f(X)` is closed if and only if it
is stable under specialization.

The statement concerns the range of `f` on the whole source. Closedness is
checked on the affine opens of the target; over an affine target the
quasi-compact source is the image of the spectrum of a ring, and the claim
reduces to `PrimeSpectrum.isClosed_range_of_stableUnderSpecialization`.
Mathlib's `AlgebraicGeometry.isClosedMap_iff_specializingMap` is the related
statement about images of all closed subsets.
-/

open CategoryTheory TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- Over an affine target, a morphism from a quasi-compact scheme whose range is
stable under specialization has closed range. -/
theorem isClosed_range_of_stableUnderSpecialization_of_isAffine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] [CompactSpace X]
    (h : StableUnderSpecialization (Set.range f)) : IsClosed (Set.range f) := by
  obtain ⟨R, g, hg⟩ := compactSpace_iff_exists.mp ‹CompactSpace X›
  have hrange : Set.range (g ≫ f) = Set.range f := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, hg.range_comp]
  rw [← hrange] at h ⊢
  have h3 : Set.range (g ≫ f ≫ Y.isoSpec.hom) =
      Y.isoSpec.hom.homeomorph '' Set.range (g ≫ f) := by
    rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rfl
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ f ≫ Y.isoSpec.hom)
  have key : IsClosed (Set.range (g ≫ f ≫ Y.isoSpec.hom)) := by
    rw [← hφ]
    apply PrimeSpectrum.isClosed_range_of_stableUnderSpecialization φ.hom
    have := h3 ▸ h.image Y.isoSpec.hom.homeomorph.isClosedMap.specializingMap
    rw [← hφ] at this
    exact this
  rw [h3] at key
  exact Y.isoSpec.hom.homeomorph.isClosed_image.mp key

/-- Hartshorne II, Lemma 4.5: for a quasi-compact morphism `f : X ⟶ Y`, the image
`f(X)` is closed if and only if it is stable under specialization. -/
theorem isClosed_range_iff_stableUnderSpecialization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsClosed (Set.range f) ↔ StableUnderSpecialization (Set.range f) := by
  refine ⟨IsClosed.stableUnderSpecialization, fun h ↦ ?_⟩
  have hU : IsOpenCover (fun U : Y.affineOpens ↦ (U : Y.Opens)) := iSup_affineOpens_eq_top Y
  rw [hU.isClosed_iff_coe_preimage]
  intro U
  have hr : Set.range (f ∣_ (U : Y.Opens)) = Subtype.val ⁻¹' Set.range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, (morphismRestrict_base_coe f _ x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
      · show f x ∈ (U : Y.Opens)
        rw [hx]
        exact y.2
      · exact (morphismRestrict_base_coe f _ _).trans hx
  have : IsAffine (U : Y.Opens) := U.2
  have : CompactSpace (f ⁻¹ᵁ (U : Y.Opens)) :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ (U : Y.Opens))
  rw [← hr]
  apply isClosed_range_of_stableUnderSpecialization_of_isAffine
  rw [hr]
  exact h.preimage continuous_subtype_val

end Hartshorne
