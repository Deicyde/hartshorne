/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SchemesHaveFiberProducts
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth relative-dimension calculus

Hartshorne, *Algebraic Geometry*, III.10, Proposition 10.1 (pp. 268–269).

Open immersions are smooth of relative dimension zero. Smoothness of a fixed
relative dimension is preserved by arbitrary base change, relative dimensions
add under composition, and therefore also add under products over a common
base.
-/

namespace Hartshorne

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/-- An open immersion is smooth of relative dimension zero. -/
theorem openImmersion_smoothOfRelativeDimension_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SmoothOfRelativeDimension 0 f :=
  inferInstance

/-- An arbitrary base change of a morphism smooth of relative dimension `n`
is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_baseChange
    {n : ℕ} {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X} {j : Y' ⟶ Y}
    (sq : IsPullback i f' f j) [hf : SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n f' :=
  (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback sq hf

/-- Relative dimensions of smooth morphisms add under composition. -/
theorem smoothOfRelativeDimension_comp
    {n m : ℕ} {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m g] :
    SmoothOfRelativeDimension (n + m) (f ≫ g) :=
  inferInstance

/-- The product of morphisms smooth of relative dimensions `n` and `m` over a
common base is smooth of relative dimension `n + m`. -/
theorem smoothOfRelativeDimension_product
    {n m : ℕ} {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [hf : SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension m g] :
    SmoothOfRelativeDimension (n + m) (pullback.fst f g ≫ f) := by
  rw [pullback.condition]
  let _ : SmoothOfRelativeDimension n (pullback.snd f g) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
      (IsPullback.of_hasPullback f g) hf
  infer_instance

end Hartshorne
