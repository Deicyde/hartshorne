/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change for relative differentials

Hartshorne, *Algebraic Geometry*, II.8, Proposition 8.10 (p. 175).

Let `X' = X ×_Y Y'`, with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`. The canonical map
`g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` is the composite of the first map `g'^* Ω_{X/Y} ⟶ Ω_{X'/Y}` of the
transitivity sequence for `X' ⟶ X ⟶ Y`, the identification `Ω_{X'/Y}` along
`g' ≫ f = f' ≫ h`, and `Ω_{X'/Y} ⟶ Ω_{X'/Y'}`. It sends `1 ⊗ d b` to `d (g'^♯ b)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (h : Y' ⟶ Y)

/-- **The base-change map** `g'^* Ω_{X/Y} ⟶ Ω_{X'/Y'}` for `X' = X ×_Y Y'`, with
`g' = pullback.fst f h` and `f' = pullback.snd f h`. -/
noncomputable def baseChangeRelativeDifferentialsMap :
    (Modules.pullback (pullback.fst f h)).obj (relativeDifferentials f) ⟶
      relativeDifferentials (pullback.snd f h) :=
  pullbackRelativeDifferentialsToComp (pullback.fst f h) f ≫
    (relativeDifferentialsCongr pullback.condition).hom ≫
    relativeDifferentialsCompToLeft (pullback.snd f h) h

/-- **Compatibility with the universal derivations**: the base-change map sends `1 ⊗ d_{X/Y} b`
to `d_{X'/Y'} (g'^♯ b)`. -/
theorem baseChangeRelativeDifferentialsMap_unit_d (V : X.Opens) (b : X.presheaf.obj (op V)) :
    (baseChangeRelativeDifferentialsMap f h).val.app (op (pullback.fst f h ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction (pullback.fst f h)).unit.app
        (relativeDifferentials f)).val.app (op V) ((relativeDifferentialsDerivation f).d b)) =
      (relativeDifferentialsDerivation (pullback.snd f h)).d
        ((pullback.fst f h).c.app (op V) b) := by
  change (relativeDifferentialsCompToLeft (pullback.snd f h) h).val.app _
    ((relativeDifferentialsCongr pullback.condition).hom.val.app _
      ((pullbackRelativeDifferentialsToComp (pullback.fst f h) f).val.app _ _)) = _
  rw [pullbackRelativeDifferentialsToComp_unit_d, relativeDifferentialsCongr_hom_d,
    relativeDifferentialsCompToLeft_d]

end AlgebraicGeometry.Scheme
