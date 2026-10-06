/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Normal
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Absolute normalization of an integral scheme

Hartshorne, *Algebraic Geometry*, Exercise II.3.8, p. 91.

The absolute normalization of an integral scheme is obtained by applying
Mathlib's relative normalization to the canonical morphism from the spectrum
of its function field.
-/

noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- The canonical morphism from the spectrum of the function field to an
integral scheme. -/
def absoluteNormalizationGenericMap (X : Scheme.{u}) [IsIntegral X] :
    Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

instance absoluteNormalizationGenericMap_quasiCompact
    (X : Scheme.{u}) [IsIntegral X] :
    QuasiCompact (absoluteNormalizationGenericMap X) where
  isCompact_preimage U _ _ := by
    let _ : Unique (Spec X.functionField) :=
      inferInstanceAs (Unique (Spec (.of (X.functionField : Type u))))
    apply Set.Subsingleton.isCompact
    intro x _ y _
    exact Subsingleton.elim x y

instance absoluteNormalizationGenericMap_quasiSeparated
    (X : Scheme.{u}) [IsIntegral X] :
    QuasiSeparated (absoluteNormalizationGenericMap X) := by
  dsimp [absoluteNormalizationGenericMap]
  infer_instance

/-- The normalization of `X` inside its function field. -/
def absoluteNormalization (X : Scheme.{u}) [IsIntegral X] : Scheme.{u} :=
  (absoluteNormalizationGenericMap X).normalization

/-- The normalization morphism `X̃ ⟶ X`. -/
def absoluteNormalizationMap (X : Scheme.{u}) [IsIntegral X] :
    absoluteNormalization X ⟶ X :=
  (absoluteNormalizationGenericMap X).fromNormalization

/-- The canonical affine open cover of the absolute normalization. -/
def absoluteNormalizationOpenCover (X : Scheme.{u}) [IsIntegral X] :
    (absoluteNormalization X).OpenCover :=
  (absoluteNormalizationGenericMap X).normalizationOpenCover

instance absoluteNormalizationMap_isIntegral
    (X : Scheme.{u}) [IsIntegral X] :
    IsIntegralHom (absoluteNormalizationMap X) := by
  change IsIntegralHom (Scheme.Hom.fromNormalization
    (absoluteNormalizationGenericMap X))
  infer_instance

/-- A nonempty open of an integral scheme pulls back to the whole spectrum of
the function field. -/
lemma absoluteNormalizationGenericMap_preimage_eq_top
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    absoluteNormalizationGenericMap X ⁻¹ᵁ U = ⊤ := by
  let _ : Unique (Spec X.functionField) :=
    inferInstanceAs (Unique (Spec (.of (X.functionField : Type u))))
  apply le_antisymm le_top
  intro x _
  change absoluteNormalizationGenericMap X x ∈ U
  rw [show x = closedPoint X.functionField from Subsingleton.elim _ _]
  rw [absoluteNormalizationGenericMap, Scheme.fromSpecStalk_closedPoint]
  exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
    simpa using (inferInstance : Nonempty U))

/-- Sections on the preimage of a nonempty open under the generic-point
morphism identify with the function field. -/
def genericPreimageSectionsRingEquiv
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Γ(Spec X.functionField, absoluteNormalizationGenericMap X ⁻¹ᵁ U) ≃+*
      X.functionField :=
  (((Spec X.functionField).presheaf.mapIso
      (eqToIso (absoluteNormalizationGenericMap_preimage_eq_top X U).symm).op) ≪≫
    Scheme.ΓSpecIso X.functionField).commRingCatIsoToRingEquiv

/-- The preceding identification respects the canonical `Γ(X,U)`-algebra
structures. -/
def genericPreimageSectionsAlgEquiv
    (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) [Nonempty U] :
    letI := ((absoluteNormalizationGenericMap X).app U).hom.toAlgebra
    Γ(Spec X.functionField, absoluteNormalizationGenericMap X ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      X.functionField := by
  letI := ((absoluteNormalizationGenericMap X).app U).hom.toAlgebra
  refine { genericPreimageSectionsRingEquiv X U with commutes' := ?_ }
  intro r
  change genericPreimageSectionsRingEquiv X U
    ((absoluteNormalizationGenericMap X).app U r) = X.germToFunctionField U r
  have hxU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by
      simpa using (inferInstance : Nonempty U))
  let e : Γ(Spec X.functionField,
      absoluteNormalizationGenericMap X ⁻¹ᵁ U) ≅ X.functionField :=
    ((Spec X.functionField).presheaf.mapIso
        (eqToIso (absoluteNormalizationGenericMap_preimage_eq_top X U).symm).op) ≪≫
      Scheme.ΓSpecIso X.functionField
  have hres :
      (Spec X.functionField).presheaf.map (homOfLE le_top).op ≫
          ((Spec X.functionField).presheaf.mapIso
            (eqToIso (absoluteNormalizationGenericMap_preimage_eq_top X U).symm).op).hom =
        𝟙 _ := by
    change (Spec X.functionField).presheaf.map (homOfLE le_top).op ≫
        (Spec X.functionField).presheaf.map
          ((eqToIso (absoluteNormalizationGenericMap_preimage_eq_top X U).symm).op.hom) =
      𝟙 _
    rw [← Functor.map_comp]
    rw [show (homOfLE le_top).op ≫
        (eqToIso (absoluteNormalizationGenericMap_preimage_eq_top X U).symm).op.hom = 𝟙 _ from
      Subsingleton.elim _ _]
    exact (Spec X.functionField).presheaf.map_id _
  have hres' :
      (Spec X.functionField).presheaf.map (homOfLE le_top).op ≫
          ((Spec X.functionField).presheaf.map
            ((eqToIso (absoluteNormalizationGenericMap_preimage_eq_top X U).symm).op.hom) ≫
              (Scheme.ΓSpecIso X.functionField).hom) =
        (Scheme.ΓSpecIso X.functionField).hom := by
    change (Spec X.functionField).presheaf.map (homOfLE le_top).op ≫
        (((Spec X.functionField).presheaf.mapIso
          (eqToIso (absoluteNormalizationGenericMap_preimage_eq_top X U).symm).op).hom ≫
            (Scheme.ΓSpecIso X.functionField).hom) =
      (Scheme.ΓSpecIso X.functionField).hom
    rw [← Category.assoc, hres, Category.id_comp]
  have he : (absoluteNormalizationGenericMap X).app U ≫ e.hom =
      X.germToFunctionField U := by
    rw [show (absoluteNormalizationGenericMap X).app U =
        X.presheaf.germ U (genericPoint X) hxU ≫
          (Scheme.ΓSpecIso X.functionField).inv ≫
            (Spec X.functionField).presheaf.map (homOfLE le_top).op from
      Scheme.fromSpecStalk_app hxU]
    dsimp [e]
    simp only [Category.assoc, hres']
    simp
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) r

/-- On a nonempty affine open, the sections of the absolute normalization are
the integral closure in the function field. -/
def absoluteNormalizationObjIso
    (X : Scheme.{u}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] :
    Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ U) ≅
      CommRingCat.of (integralClosure Γ(X, U) X.functionField) := by
  let g := absoluteNormalizationGenericMap X
  letI := (g.app U).hom.toAlgebra
  exact g.normalizationObjIso hU ≪≫
    ((genericPreimageSectionsAlgEquiv X U).mapIntegralClosure).toRingEquiv.toCommRingCatIso

end Hartshorne
