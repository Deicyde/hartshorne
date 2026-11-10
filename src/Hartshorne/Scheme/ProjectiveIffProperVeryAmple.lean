/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeVeryAmple
import Hartshorne.Scheme.ProjectiveSpaceProper

/-!
# Projective iff proper with a relatively very ample sheaf

Hartshorne, *Algebraic Geometry*, II.5, Remark 5.16.1, p. 120.

A morphism `p : X ⟶ Y` is projective (it factors through a closed immersion into some `ℙʳ_Y`)
if and only if it is proper and `X` carries an invertible sheaf very ample relative to `Y`.
Hartshorne assumes `Y` Noetherian; the argument below does not use it.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

/-- **Projective iff proper and relatively very ample** (Hartshorne II.5.16.1, without the
Noetherian hypothesis on `Y`). A morphism `p : X ⟶ Y` is projective if and only if it is proper
and some invertible `𝒪_X`-module is very ample relative to `Y`. -/
theorem projective_iff_isProper_and_exists_isVeryAmpleRelative {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Projective p ↔ IsProper p ∧ ∃ L : X.Modules, IsVeryAmpleRelative p L := by
  constructor
  · intro hp
    refine ⟨hp.isProper, ?_⟩
    obtain ⟨r, i, hi, rfl⟩ := hp
    exact ⟨_, Scheme.Modules.IsInvertible.pullback i
      (isInvertible_projectiveSpaceTwistingSheaf r Y 1), r, i, inferInstance, inferInstance, rfl,
      ⟨Iso.refl _⟩⟩
  · rintro ⟨hp, L, -, r, i, hi, -, rfl, -⟩
    have : IsProper (projectiveSpaceOverSchemeProjection r Y) :=
      projectiveSpaceOverSchemeProjection_isProper r Y
    have : IsProper i := IsProper.of_comp i (projectiveSpaceOverSchemeProjection r Y)
    exact ⟨r, i, IsClosedImmersion.of_isPreimmersion i i.isClosedMap.isClosed_range, rfl⟩

end Hartshorne
