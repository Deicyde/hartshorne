/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ValuationSpectrumMaps
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Over
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Centers of valuations

Hartshorne, *Algebraic Geometry*, II, Exercise 4.5 (preamble).

Let `X` be an integral scheme with function field `K = K(X)` and let `R ⊆ K` be a valuation
subring. A *center* of `R` on `X` is a lift `Spec R ⟶ X` of the canonical generic-point morphism
`Spec K ⟶ X` along `Spec K ⟶ Spec R`; its underlying point is the image of the closed point of
`Spec R`.

We record:

* `Hartshorne.ValuationCenter X R`: the centers of `R` on `X`, i.e. the lifts as above;
* `Hartshorne.ValuationCenter.point`: the underlying point of a center;
* `Hartshorne.exists_valuationCenter_point_eq_iff`: a point `x : X` is (the underlying point of)
  a center of `R` exactly when `R` dominates the image of `𝒪_{X, x}` in `K(X)`, with domination
  the order on local subrings of `K(X)`.

In Hartshorne's setting `X` is a scheme over a field `k` and `R` contains `k`. The definition of
a center does not involve `k`; the base field enters through the valuative square for
`X ⟶ Spec k`. We record the canonical map `k ⟶ K(X)` (`Hartshorne.functionFieldBaseHom`) and
show that, when `R` contains its image, every center is a morphism over `Spec k`, i.e. a lift in
the valuative square formed by `Spec K ⟶ X` and `Spec R ⟶ Spec k`
(`Hartshorne.ValuationCenter.lift_comp_over`).
-/

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hartshorne

universe u

variable (X : Scheme.{u}) [IsIntegral X]

/-- A **center** of a valuation subring `R` of the function field `K(X)` of an integral scheme
`X` (Hartshorne II, Exercise 4.5): a lift `Spec R ⟶ X` of the canonical generic-point morphism
`Spec K(X) ⟶ X` along `Spec K(X) ⟶ Spec R`. -/
@[ext]
structure ValuationCenter (R : ValuationSubring X.functionField) where
  /-- The morphism `Spec R ⟶ X`. -/
  lift : Spec (CommRingCat.of R) ⟶ X
  /-- The composite `Spec K(X) ⟶ Spec R ⟶ X` is the canonical generic-point morphism. -/
  lift_fac : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ lift =
    X.fromSpecStalk (genericPoint X)

variable {X} {R : ValuationSubring X.functionField}

/-- The underlying point of a center: the image of the closed point of `Spec R`. -/
noncomputable abbrev ValuationCenter.point (c : ValuationCenter X R) : X :=
  c.lift (closedPoint R)

lemma toLocalSubring_eq_range_algebraMap (R : ValuationSubring X.functionField) :
    R.toLocalSubring = LocalSubring.range (algebraMap R X.functionField) := by
  apply LocalSubring.toSubring_injective
  ext a
  change a ∈ R ↔ a ∈ Set.range (algebraMap R X.functionField)
  exact ⟨fun ha => ⟨⟨a, ha⟩, rfl⟩, by rintro ⟨b, rfl⟩; exact b.2⟩

/-- **Hartshorne II, Exercise 4.5 (preamble).** A point `x` of an integral scheme `X` is the
underlying point of a center of the valuation subring `R ⊆ K(X)` exactly when `R` dominates the
image of the local ring `𝒪_{X, x}` in `K(X)`. -/
theorem exists_valuationCenter_point_eq_iff (x : X) :
    (∃ c : ValuationCenter X R, c.point = x) ↔
      LocalSubring.range (algebraMap (X.presheaf.stalk x) X.functionField) ≤
        R.toLocalSubring := by
  have hspec : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have halg : algebraMap (X.presheaf.stalk x) X.functionField =
      (X.presheaf.stalkSpecializes hspec).hom := rfl
  rw [toLocalSubring_eq_range_algebraMap, halg]
  change _ ↔ LocalSubring.range
      (X.presheaf.stalkSpecializes hspec : X.presheaf.stalk x ⟶ CommRingCat.of X.functionField).hom
      ≤ _
  rw [range_le_range_algebraMap_iff]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨Scheme.stalkClosedPointTo c.lift, inferInstance, ?_⟩
    rw [← Spec.map_inj, ← cancel_mono (X.fromSpecStalk _), Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, c.lift_fac]
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk _).symm
  · rintro ⟨f, hf, hfac⟩
    refine ⟨⟨Spec.map f ≫ X.fromSpecStalk x, ?_⟩, ?_⟩
    · rw [← Category.assoc, ← Spec.map_comp, hfac]
      exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    · change X.fromSpecStalk x (Spec.map f (closedPoint R)) = x
      rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

section Over

variable (X) (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]

/-- For an integral scheme `X` over a field `k`, the canonical map `k ⟶ K(X)`: the composite
`k ≅ Γ(Spec k) ⟶ Γ(X) ⟶ K(X)` of the structure morphism and restriction to the generic
point. -/
noncomputable def functionFieldBaseHom : CommRingCat.of k ⟶ X.functionField :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (X ↘ Spec (CommRingCat.of k)).appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) trivial

/-- The composite `Spec K(X) ⟶ X ⟶ Spec k` of the generic-point morphism and the structure
morphism is induced by the canonical map `k ⟶ K(X)`. -/
lemma fromSpecStalk_genericPoint_comp_over :
    X.fromSpecStalk (genericPoint X) ≫ X ↘ Spec (CommRingCat.of k) =
      Spec.map (functionFieldBaseHom X k) := by
  rw [← Category.comp_id (X ↘ Spec (CommRingCat.of k)),
    ← toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of k), ← Category.assoc (X ↘ _),
    Scheme.toSpecΓ_naturality, Category.assoc, Scheme.fromSpecStalk_toSpecΓ_assoc,
    ← Spec.map_comp, ← Spec.map_comp, functionFieldBaseHom, Category.assoc]

variable {k X}

/-- If the valuation subring `R ⊆ K(X)` contains `k`, every center of `R` is a morphism over
`Spec k`, where `Spec R` lies over `Spec k` through `k ⟶ R`. Together with the defining
factorization, the center is a lift in the valuative square for `X ⟶ Spec k`. -/
theorem ValuationCenter.lift_comp_over (c : ValuationCenter X R)
    (hk : ∀ a : k, functionFieldBaseHom X k a ∈ R) :
    c.lift ≫ X ↘ Spec (CommRingCat.of k) =
      Spec.map (CommRingCat.ofHom ((functionFieldBaseHom X k).hom.codRestrict R hk)) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (c.lift ≫ X ↘ Spec (CommRingCat.of k))
  rw [← hφ, Spec.map_inj]
  have hmono : Mono (CommRingCat.ofHom (algebraMap R X.functionField)) :=
    ConcreteCategory.mono_of_injective _ (IsFractionRing.injective R X.functionField)
  rw [← cancel_mono (CommRingCat.ofHom (algebraMap R X.functionField)), ← Spec.map_inj,
    Spec.map_comp, Spec.map_comp, hφ, ← Category.assoc, c.lift_fac,
    fromSpecStalk_genericPoint_comp_over, ← Spec.map_comp]
  rfl

end Over

end Hartshorne
