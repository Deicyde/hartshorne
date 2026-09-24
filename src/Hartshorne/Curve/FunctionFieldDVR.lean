/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Discrete valuation rings of a function field

Hartshorne, *Algebraic Geometry*, I.6 (pp. 39--42).

We package the discrete valuation rings of a field extension `K / k` as
valuation subrings of the fixed ambient field `K` which contain the image of
`k`. This identifies points having the same local ring, rather than remembering
a choice of an equivalent valuation map.
-/

namespace Hartshorne

universe u v

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

/-- A discrete valuation ring of the field extension `K / k`, represented as
a valuation subring of `K` containing the image of `k`. -/
def FunctionFieldDVR : Type v :=
  { R : ValuationSubring K //
    IsDiscreteValuationRing R ∧ ∀ x : k, algebraMap k K x ∈ R }

namespace FunctionFieldDVR

variable {k K}

/-- The valuation subring underlying a function-field DVR. -/
abbrev toValuationSubring (R : FunctionFieldDVR k K) : ValuationSubring K :=
  R.1

/-- Function-field DVRs are equal when their underlying valuation subrings have
the same elements. -/
@[ext]
theorem ext {R S : FunctionFieldDVR k K}
    (h : ∀ x : K, x ∈ R.toValuationSubring ↔ x ∈ S.toValuationSubring) : R = S := by
  apply Subtype.ext
  exact ValuationSubring.ext _ _ h

instance (R : FunctionFieldDVR k K) :
    IsDiscreteValuationRing R.toValuationSubring :=
  R.2.1

/-- Every element of the base field belongs to a function-field DVR. -/
theorem algebraMap_mem (R : FunctionFieldDVR k K) (x : k) :
    algebraMap k K x ∈ R.toValuationSubring :=
  R.2.2 x

end FunctionFieldDVR

namespace ValuationSubring

variable {k K}

/-- A valuation subring contains the embedded base field exactly when its
associated valuation is trivial on that field. -/
theorem contains_algebraMap_iff_isTrivialOn (R : ValuationSubring K) :
    (∀ x : k, algebraMap k K x ∈ R) ↔
      Valuation.IsTrivialOn k R.valuation := by
  constructor
  · intro h
    apply Valuation.IsTrivialOn.of_le_one
    intro x
    exact (R.valuation_le_one_iff _).2 (h x)
  · intro h
    let _ : Valuation.IsTrivialOn k R.valuation := h
    intro x
    exact (R.valuation_le_one_iff _).1
      (Valuation.IsTrivialOn.valuation_algebraMap_le_one R.valuation x)

end ValuationSubring

namespace FunctionFieldDVR

variable {k K}

instance (R : FunctionFieldDVR k K) :
    Valuation.IsTrivialOn k R.toValuationSubring.valuation :=
  (ValuationSubring.contains_algebraMap_iff_isTrivialOn R.toValuationSubring).mp R.2.2

/-- The base-field embedding with codomain restricted to the DVR. -/
def baseRingHom (R : FunctionFieldDVR k K) : k →+* R.toValuationSubring :=
  (algebraMap k K).codRestrict R.toValuationSubring R.algebraMap_mem

instance (R : FunctionFieldDVR k K) : Algebra k R.toValuationSubring :=
  R.baseRingHom.toAlgebra

/-- The restricted base-field embedding agrees with the given embedding into
the ambient field. -/
@[simp]
theorem coe_algebraMap (R : FunctionFieldDVR k K) (x : k) :
    ((algebraMap k R.toValuationSubring x : R.toValuationSubring) : K) =
      algebraMap k K x :=
  rfl

instance (R : FunctionFieldDVR k K) :
    IsScalarTower k R.toValuationSubring K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- An element has a pole at a function-field DVR when it does not belong to
that valuation subring. -/
def HasPoleAt (R : FunctionFieldDVR k K) (x : K) : Prop :=
  x ∉ R.toValuationSubring

/-- An element vanishes at a function-field DVR when it belongs to the maximal
ideal, viewed inside the ambient field. -/
def VanishesAt (R : FunctionFieldDVR k K) (x : K) : Prop :=
  x ∈ R.toValuationSubring.nonunits

/-- Having a pole is equivalent to having valuation greater than one. -/
theorem hasPoleAt_iff_valuation_one_lt (R : FunctionFieldDVR k K) (x : K) :
    R.HasPoleAt x ↔ 1 < R.toValuationSubring.valuation x := by
  rw [HasPoleAt, ← R.toValuationSubring.valuation_le_one_iff]
  exact not_le

/-- Vanishing is equivalent to having valuation less than one. -/
theorem vanishesAt_iff_valuation_lt_one (R : FunctionFieldDVR k K) (x : K) :
    R.VanishesAt x ↔ R.toValuationSubring.valuation x < 1 :=
  Iff.rfl

/-- Vanishing is membership in the maximal ideal after lifting the ambient
field element into the valuation subring. -/
theorem vanishesAt_iff_exists_mem_maximalIdeal (R : FunctionFieldDVR k K)
    (x : K) :
    R.VanishesAt x ↔
      ∃ hx : x ∈ R.toValuationSubring,
        (⟨x, hx⟩ : R.toValuationSubring) ∈
          IsLocalRing.maximalIdeal R.toValuationSubring :=
  ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal

end FunctionFieldDVR

end Hartshorne
