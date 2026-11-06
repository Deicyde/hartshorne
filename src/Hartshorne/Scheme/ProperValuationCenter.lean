/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SeparatedValuationCenter
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper schemes have valuation centers

Hartshorne, *Algebraic Geometry*, II, Exercise 4.5(b).

Let `X` be an integral scheme of finite type over a field `k`, proper over `k`, and let
`R ⊆ K(X)` be a valuation subring containing (the image of) `k`. Then `R` has exactly one center
on `X`:

* `Hartshorne.ValuationCenter.nonempty_unique_of_isProper`: there is exactly one center of `R`
  on `X` (lift `Spec R ⟶ X` of the generic-point morphism);
* `Hartshorne.ValuationCenter.existsUnique_point_of_isProper`: exactly one point of `X` is the
  underlying point of a center of `R`;
* `Hartshorne.ValuationCenter.existsUnique_dominates_of_isProper`: exactly one point `x` of `X`
  has local ring `𝒪_{X, x}` dominated by `R` (Hartshorne's formulation of the center).

The generic-point morphism `Spec K(X) ⟶ X` and the morphism `Spec R ⟶ Spec k` induced by
`k ⟶ R` form a valuative square for the structure morphism `X ⟶ Spec k`; it commutes by
`Hartshorne.fromSpecStalk_genericPoint_comp_over`. Since `X ⟶ Spec k` is universally closed,
the existence part of the valuative criterion gives a lift, which is a center. Uniqueness is
`Hartshorne.ValuationCenter.subsingleton_of_isSeparated`, as proper morphisms are separated.
-/

open AlgebraicGeometry CategoryTheory

namespace Hartshorne

universe u

variable {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k] [X.Over (Spec (CommRingCat.of k))]

/-- **Hartshorne II, Exercise 4.5(b).** Let `X` be an integral scheme of finite type over a field
`k` that is proper over `k`. A valuation subring `R` of `K(X)` containing `k` has exactly one
center on `X`. -/
theorem ValuationCenter.nonempty_unique_of_isProper
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (R : ValuationSubring X.functionField) (hk : ∀ a : k, functionFieldBaseHom X k a ∈ R) :
    Nonempty (Unique (ValuationCenter X R)) := by
  have hsub := ValuationCenter.subsingleton_of_isSeparated R hk
  let S : ValuativeCommSq (X ↘ Spec (CommRingCat.of k)) :=
    { R := R
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom ((functionFieldBaseHom X k).hom.codRestrict R hk))
      commSq := ⟨by
        rw [fromSpecStalk_genericPoint_comp_over, ← Spec.map_comp]
        rfl⟩ }
  have hE : ValuativeCriterion.Existence (X ↘ Spec (CommRingCat.of k)) := by
    have h : UniversallyClosed (X ↘ Spec (CommRingCat.of k)) := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨l⟩ := (hE S).exists_lift
  exact ⟨uniqueOfSubsingleton ⟨l.l, l.fac_left⟩⟩

/-- **Hartshorne II, Exercise 4.5(b)**, pointwise form. Let `X` be an integral scheme of finite
type over a field `k` that is proper over `k`, and let `R` be a valuation subring of `K(X)`
containing `k`. Exactly one point of `X` is a center of `R`. -/
theorem ValuationCenter.existsUnique_point_of_isProper
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (R : ValuationSubring X.functionField) (hk : ∀ a : k, functionFieldBaseHom X k a ∈ R) :
    ∃! x : X, ∃ c : ValuationCenter X R, c.point = x := by
  obtain ⟨u⟩ := ValuationCenter.nonempty_unique_of_isProper R hk
  exact ⟨(default : ValuationCenter X R).point, ⟨default, rfl⟩,
    fun y hy => ValuationCenter.point_eq_of_isSeparated R hk hy ⟨default, rfl⟩⟩

/-- **Hartshorne II, Exercise 4.5(b)**, domination form. Let `X` be an integral scheme of finite
type over a field `k` that is proper over `k`, and let `R` be a valuation subring of `K(X)`
containing `k`. There is exactly one point `x` of `X` such that `R` dominates the image of the
local ring `𝒪_{X, x}` in `K(X)`. -/
theorem ValuationCenter.existsUnique_dominates_of_isProper
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsProper (X ↘ Spec (CommRingCat.of k))]
    (R : ValuationSubring X.functionField) (hk : ∀ a : k, functionFieldBaseHom X k a ∈ R) :
    ∃! x : X, LocalSubring.range (algebraMap (X.presheaf.stalk x) X.functionField) ≤
      R.toLocalSubring := by
  simp_rw [← exists_valuationCenter_point_eq_iff]
  exact ValuationCenter.existsUnique_point_of_isProper R hk

end Hartshorne
