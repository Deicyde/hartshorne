/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Morphisms locally of finite type

Hartshorne, *Algebraic Geometry*, II.3 (p. 84).

This file compares Hartshorne's definition, which chooses affine covers of the
target and of their inverse images, with Mathlib's `LocallyOfFiniteType` class.
-/

namespace Hartshorne

open CategoryTheory

noncomputable section

universe u

open AlgebraicGeometry

/-- Hartshorne's affine-cover formulation of local finite type.

The target has an affine open cover and, over each member of that cover, the
source has an affine open cover whose induced coordinate-ring maps are of
finite type. This is a proposition recording chosen-cover existence, not a
second typeclass for morphisms. -/
def LocallyOfFiniteTypeOnAffineCovers
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ (𝒰 : Y.AffineOpenCover.{u}), ∀ i,
    ∃ (𝒱 : ((𝒰.openCover.pullback₁ f).X i).AffineOpenCover.{u}), ∀ j,
      ((𝒱.openCover.f j ≫ 𝒰.openCover.pullbackHom f i).appTop).hom.FiniteType

/-- A scheme morphism is locally of finite type in Mathlib's every-affine-pair
sense if and only if it satisfies Hartshorne's existential affine-cover
definition. -/
theorem locallyOfFiniteType_iff_affineCovers
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ LocallyOfFiniteTypeOnAffineCovers f := by
  let _ : HasRingHomProperty
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) (@RingHom.FiniteType) :=
    inferInstance
  let _ : IsZariskiLocalAtTarget
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
      (Q := @RingHom.FiniteType)
  constructor
  · intro hf
    let 𝒰 : Y.AffineOpenCover.{u} := Y.affineOpenCover
    let _ : ∀ i, IsAffine (𝒰.openCover.X i) := fun i ↦ by
      change IsAffine (Spec (𝒰.X i))
      infer_instance
    refine ⟨𝒰, ?_⟩
    intro i
    let _ : IsAffine (𝒰.openCover.X i) := by
      change IsAffine (Spec (𝒰.X i))
      infer_instance
    let 𝒱 : ((𝒰.openCover.pullback₁ f).X i).AffineOpenCover.{u} :=
      ((𝒰.openCover.pullback₁ f).X i).affineOpenCover
    let _ : ∀ j, IsAffine (𝒱.openCover.X j) := fun j ↦ by
      change IsAffine (Spec (𝒱.X j))
      infer_instance
    refine ⟨𝒱, ?_⟩
    exact
      (HasRingHomProperty.iff_of_source_openCover
        (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
        (f := 𝒰.openCover.pullbackHom f i) 𝒱.openCover).mp
        ((IsZariskiLocalAtTarget.iff_of_openCover
          (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
          (f := f) 𝒰.openCover).mp hf i)
  · rintro ⟨𝒰, h𝒰⟩
    let _ : ∀ i, IsAffine (𝒰.openCover.X i) := fun i ↦ by
      change IsAffine (Spec (𝒰.X i))
      infer_instance
    exact
      (IsZariskiLocalAtTarget.iff_of_openCover
        (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
        (f := f) 𝒰.openCover).mpr fun i ↦ by
          let _ : IsAffine (𝒰.openCover.X i) := by
            change IsAffine (Spec (𝒰.X i))
            infer_instance
          obtain ⟨𝒱, h𝒱⟩ := h𝒰 i
          let _ : ∀ j, IsAffine (𝒱.openCover.X j) := fun j ↦ by
            change IsAffine (Spec (𝒱.X j))
            infer_instance
          exact
            (HasRingHomProperty.iff_of_source_openCover
              (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
              (f := 𝒰.openCover.pullbackHom f i) 𝒱.openCover).mpr h𝒱

/-- Hartshorne's formulation of local finite type over every affine open of
the target.

For each affine open `U` of the target, the inverse image of `U` has an affine
open cover on which the induced coordinate-ring maps are of finite type. -/
def LocallyOfFiniteTypeOnEveryAffineTarget
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ U : Y.affineOpens,
    ∃ (𝒱 : ((f ⁻¹ᵁ (U : Y.Opens)).toScheme).AffineOpenCover.{u}), ∀ j,
      ((𝒱.openCover.f j ≫ f ∣_ (U : Y.Opens)).appTop).hom.FiniteType

/-- A scheme morphism is locally of finite type if and only if it satisfies
Hartshorne's affine-target criterion. -/
theorem locallyOfFiniteType_iff_everyAffineTarget
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ LocallyOfFiniteTypeOnEveryAffineTarget f := by
  let _ : HasRingHomProperty
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) (@RingHom.FiniteType) :=
    inferInstance
  let _ : HasAffineProperty (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (sourceAffineLocally (@RingHom.FiniteType)) :=
    HasRingHomProperty.HasAffineProperty
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
  rw [HasAffineProperty.iff_of_iSup_eq_top
    (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
    (Q := sourceAffineLocally (@RingHom.FiniteType))
    (fun U : Y.affineOpens ↦ U) (iSup_affineOpens_eq_top Y)]
  apply forall_congr'
  intro U
  let _ : IsAffine U := U.2
  rw [← HasAffineProperty.iff_of_isAffine
    (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
    (Q := sourceAffineLocally (@RingHom.FiniteType)) (f := f ∣_ (U : Y.Opens))]
  constructor
  · intro hf
    let 𝒱 : ((f ⁻¹ᵁ (U : Y.Opens)).toScheme).AffineOpenCover.{u} :=
      ((f ⁻¹ᵁ (U : Y.Opens)).toScheme).affineOpenCover
    let _ : ∀ j, IsAffine (𝒱.openCover.X j) := fun j ↦ by
      change IsAffine (Spec (𝒱.X j))
      infer_instance
    refine ⟨𝒱, ?_⟩
    exact
      (HasRingHomProperty.iff_of_source_openCover
        (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
        (f := f ∣_ (U : Y.Opens)) 𝒱.openCover).mp hf
  · rintro ⟨𝒱, h𝒱⟩
    let _ : ∀ j, IsAffine (𝒱.openCover.X j) := fun j ↦ by
      change IsAffine (Spec (𝒱.X j))
      infer_instance
    exact
      (HasRingHomProperty.iff_of_source_openCover
        (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
        (f := f ∣_ (U : Y.Opens)) 𝒱.openCover).mpr h𝒱

end

end Hartshorne
