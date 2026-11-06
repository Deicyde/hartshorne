/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AbsoluteNormalization
import Hartshorne.Scheme.FiniteType
import Hartshorne.Scheme.FiniteIntegralClosureField
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finiteness of the normalization over a field

Hartshorne, *Algebraic Geometry*, Exercise II.3.8(b), p. 91.

If an integral scheme `X` is of finite type over a field `k`, then the
normalization morphism `X̃ ⟶ X` is finite. Over a nonempty affine open `U`, the
sections of `X̃` over the preimage of `U` are the integral closure of the
finitely generated `k`-domain `Γ(X, U)` in the function field, which is a
finite `Γ(X, U)`-module; over the empty open the source ring is zero.
-/

noncomputable section

open CategoryTheory

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- **Hartshorne II, Exercise 3.8(b).** The normalization morphism of an
integral scheme of finite type over a field is finite. -/
theorem isFinite_absoluteNormalizationMap_of_finiteType_field
    (k : Type u) [Field k] (X : Scheme.{u}) [IsIntegral X]
    (s : X ⟶ Spec (.of k)) (hs : FiniteType s) :
    IsFinite (absoluteNormalizationMap X) := by
  have hlft : LocallyOfFiniteType s := hs.1
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  rcases isEmpty_or_nonempty U with hUe | hUne
  · have hbot : U = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hUe.false ⟨x, hx⟩
    subst hbot
    have hpre : absoluteNormalizationMap X ⁻¹ᵁ (⊥ : X.Opens) = ⊥ := by simp
    have : Subsingleton Γ(absoluteNormalization X, absoluteNormalizationMap X ⁻¹ᵁ ⊥) := by
      rw [hpre]; infer_instance
    let := ((absoluteNormalizationMap X).app ⊥).hom.toAlgebra
    exact Module.Finite.of_finite
  · let g := absoluteNormalizationGenericMap X
    let := (g.app U).hom.toAlgebra
    change ((g.fromNormalization).app U).hom.Finite
    rw [g.fromNormalization_app hU]
    refine RingHom.Finite.comp
      (RingHom.Finite.of_surjective _
        (g.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm.surjective)
      ?_
    change (algebraMap Γ(X, U)
      (integralClosure Γ(X, U) Γ(Spec X.functionField, g ⁻¹ᵁ U))).Finite
    rw [RingHom.finite_algebraMap]
    -- `Γ(X, U)` is a finitely generated `k`-algebra.
    let : Algebra k Γ(X, U) :=
      ((s.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
    have : Algebra.FiniteType k Γ(X, U) := by
      change RingHom.FiniteType _
      refine RingHom.FiniteType.comp ?_
        (RingHom.FiniteType.of_surjective _
          (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
      exact s.finiteType_appLE (isAffineOpen_top _) hU le_top
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    have : Module.Finite Γ(X, U) (integralClosure Γ(X, U) X.functionField) :=
      moduleFinite_integralClosure_of_finiteType_of_field k Γ(X, U) X.functionField
        X.functionField
    exact Module.Finite.equiv
      (genericPreimageSectionsAlgEquiv X U).mapIntegralClosure.symm.toLinearEquiv

end Hartshorne
