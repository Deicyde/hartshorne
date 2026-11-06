/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ValuationCenter
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Separated schemes have unique valuation centers

Hartshorne, *Algebraic Geometry*, II, Exercise 4.5(a).

Let `X` be an integral scheme of finite type over a field `k`, separated over `k`, and let
`R ⊆ K(X)` be a valuation subring containing (the image of) `k`. Then `R` has at most one center
on `X`:

* `Hartshorne.ValuationCenter.subsingleton_of_isSeparated`: any two centers of `R` on `X`
  (lifts `Spec R ⟶ X` of the generic-point morphism) are equal;
* `Hartshorne.ValuationCenter.point_eq_of_isSeparated`: consequently, any two points of `X` that
  are centers of `R` coincide.

Two centers are lifts in the same valuative square for the structure morphism `X ⟶ Spec k`
(`Hartshorne.ValuationCenter.lift_comp_over`), so they agree by the uniqueness part of the
valuative criterion for the separated morphism `X ⟶ Spec k` (`IsSeparated.valuativeCriterion`).
The finite-type hypotheses on `X ⟶ Spec k` are those of the source; the argument uses only
separatedness.
-/

open AlgebraicGeometry CategoryTheory

namespace Hartshorne

universe u

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k] [X.Over (Spec (CommRingCat.of k))]

/-- **Hartshorne II, Exercise 4.5(a).** Let `X` be an integral scheme of finite type over a field
`k` that is separated over `k`. A valuation subring `R` of `K(X)` containing `k` has at most one
center on `X`. -/
theorem ValuationCenter.subsingleton_of_isSeparated
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (R : ValuationSubring X.functionField) (hk : ∀ a : k, functionFieldBaseHom X k a ∈ R) :
    Subsingleton (ValuationCenter X R) := by
  constructor
  intro c₁ c₂
  let S : ValuativeCommSq (X ↘ Spec (CommRingCat.of k)) :=
    { R := R
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom ((functionFieldBaseHom X k).hom.codRestrict R hk))
      commSq := ⟨by rw [← c₁.lift_fac, Category.assoc, c₁.lift_comp_over hk]⟩ }
  let L : ValuationCenter X R → S.commSq.LiftStruct := fun c =>
    { l := c.lift
      fac_left := c.lift_fac
      fac_right := c.lift_comp_over hk }
  have h := (IsSeparated.valuativeCriterion (X ↘ Spec (CommRingCat.of k)) S).elim (L c₁) (L c₂)
  exact ValuationCenter.ext (congrArg CommSq.LiftStruct.l h)

/-- **Hartshorne II, Exercise 4.5(a)**, pointwise form. Let `X` be an integral scheme of finite
type over a field `k` that is separated over `k`, and let `R` be a valuation subring of `K(X)`
containing `k`. If `x` and `y` are both centers of `R` on `X`, then `x = y`. -/
theorem ValuationCenter.point_eq_of_isSeparated
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    (R : ValuationSubring X.functionField) (hk : ∀ a : k, functionFieldBaseHom X k a ∈ R)
    {x y : X} (hx : ∃ c : ValuationCenter X R, c.point = x)
    (hy : ∃ c : ValuationCenter X R, c.point = y) : x = y := by
  have := ValuationCenter.subsingleton_of_isSeparated R hk
  obtain ⟨c₁, rfl⟩ := hx
  obtain ⟨c₂, rfl⟩ := hy
  rw [Subsingleton.elim c₁ c₂]

end Hartshorne
