/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Calculus of separated morphisms

Hartshorne, *Algebraic Geometry*, II.4, Corollary 4.6.

This file packages the standard closure properties of separated morphisms:
immersions are separated, and separated morphisms are stable under composition,
base change, products over a base, cancellation, and localization on the target.
-/

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- The standard calculus of separated morphisms from Hartshorne II.4,
Corollary 4.6. The product morphism is represented by
`X ×[S] Y ⟶ X ⟶ S`. -/
theorem separatedMorphismCalculus :
    ((@IsOpenImmersion : MorphismProperty Scheme.{u}) ≤ @IsSeparated) ∧
      ((@IsClosedImmersion : MorphismProperty Scheme.{u}) ≤ @IsSeparated) ∧
      MorphismProperty.IsStableUnderComposition
        (@IsSeparated : MorphismProperty Scheme.{u}) ∧
      MorphismProperty.IsStableUnderBaseChange
        (@IsSeparated : MorphismProperty Scheme.{u}) ∧
      (∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S),
        IsSeparated f → IsSeparated g →
          IsSeparated (pullback.fst f g ≫ f)) ∧
      (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
        IsSeparated (f ≫ g) → IsSeparated f) ∧
      IsZariskiLocalAtTarget (@IsSeparated : MorphismProperty Scheme.{u}) := by
  refine ⟨?_, ?_, inferInstance, inferInstance, ?_, ?_, inferInstance⟩
  · intro X Y f hf
    let _ := hf
    infer_instance
  · intro X Y f hf
    let _ := hf
    infer_instance
  · intro X Y S f g hf hg
    let _ := hf
    let _ := hg
    infer_instance
  · intro X Y Z f g hfg
    let _ := hfg
    exact IsSeparated.of_comp f g

end Hartshorne
