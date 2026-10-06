/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Calculus of proper morphisms

Hartshorne, *Algebraic Geometry*, II.4, Corollary 4.8.

This file packages the standard closure properties of proper morphisms: closed
immersions are proper, and proper morphisms are stable under composition, base
change, products over a base, cancellation against a separated morphism, and
localization on the target.
-/

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- The standard calculus of proper morphisms from Hartshorne II.4,
Corollary 4.8. The product morphism is represented by
`X ×[S] Y ⟶ X ⟶ S`. -/
theorem properMorphismCalculus :
    ((@IsClosedImmersion : MorphismProperty Scheme.{u}) ≤ @IsProper) ∧
      MorphismProperty.IsStableUnderComposition
        (@IsProper : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsStableUnderBaseChange
        (@IsProper : MorphismProperty Scheme.{u}) ∧
      (∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S),
        IsProper f → IsProper g → IsProper (pullback.fst f g ≫ f)) ∧
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        IsProper (f ≫ g) → IsSeparated g → IsProper f) ∧
      IsZariskiLocalAtTarget (@IsProper : MorphismProperty Scheme.{u}) := by
  refine ⟨?_, inferInstance, inferInstance, ?_, ?_, inferInstance⟩
  · intro X Y f hf
    let _ := hf
    infer_instance
  · intro X Y S f g hf hg
    let _ := hf
    let _ := hg
    infer_instance
  · intro X Y Z f g hfg hg
    let _ := hfg
    let _ := hg
    exact IsProper.of_comp f g

end Hartshorne
