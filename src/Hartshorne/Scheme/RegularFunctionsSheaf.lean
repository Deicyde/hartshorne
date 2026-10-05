/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.Variety
import Mathlib.Topology.Sheaves.CommRingCat
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The sheaf of regular functions on a variety

Hartshorne, *Algebraic Geometry*, II.1, Example 1.0.1 (p. 62).

The regular functions already carried by `Hartshorne.Variety` form a sheaf of
commutative rings. The sheaf condition is exactly the locality axiom in the
variety structure.
-/

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne.Variety

universe u v

variable {k : Type u} [Field k] (X : Variety.{u, v} k)

/-- Restriction of regular functions along an inclusion of open subsets. -/
def regularRestriction {U V : Opens X.carrier} (h : V ≤ U) :
    X.regular U →+* X.regular V where
  toFun f :=
    ⟨fun x : V => f.1 ⟨x.1, h x.2⟩, X.regular_restrict h f.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
theorem regularRestriction_apply {U V : Opens X.carrier} (h : V ≤ U)
    (f : X.regular U) (x : V) :
    (X.regularRestriction h f).1 x = f.1 ⟨x.1, h x.2⟩ :=
  rfl

/-- Regularity of functions on a variety, expressed as a Mathlib local
predicate. -/
def regularLocalPredicate :
    TopCat.LocalPredicate
      (X := TopCat.of X.carrier) (fun _ => k) where
  pred f := f ∈ X.regular _
  res i f hf := X.regular_restrict i.le hf
  locality f h := X.regular_of_locally fun x => by
    obtain ⟨V, hxV, i, hi⟩ := h x
    exact ⟨V, i.le, hxV, hi⟩

/-- The presheaf of regular functions on a variety. -/
def regularPresheaf :
    (TopCat.of X.carrier).Presheaf
      CommRingCat.{max u v} where
  obj U := CommRingCat.of (X.regular U.unop)
  map i := CommRingCat.ofHom (X.regularRestriction i.unop.le)
  map_id _ := by
    ext f x
    rfl
  map_comp _ _ := by
    ext f x
    rfl

@[simp]
theorem regularPresheaf_obj (U : Opens X.carrier) :
    X.regularPresheaf.obj (op U) = CommRingCat.of (X.regular U) :=
  rfl

@[simp]
theorem regularPresheaf_map_apply {U V : Opens X.carrier} (h : V ≤ U)
    (f : X.regular U) (x : V) :
    (X.regularPresheaf.map (homOfLE h).op f).1 x = f.1 ⟨x.1, h x.2⟩ :=
  rfl

/-- After forgetting the ring structure, the presheaf of regular functions is
the subpresheaf of functions satisfying the regularity local predicate. -/
theorem regularPresheaf_comp_forget :
    X.regularPresheaf ⋙ forget CommRingCat =
      TopCat.subpresheafToTypes (regularLocalPredicate X).toPrelocalPredicate :=
  rfl

/-- **Hartshorne II.1, Example 1.0.1.** Regular functions on open subsets of a
variety form a sheaf of commutative rings. -/
noncomputable def regularSheaf :
    (TopCat.of X.carrier).Sheaf
      CommRingCat.{max u v} := by
  refine ⟨X.regularPresheaf, ?_⟩
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp'
    (forget CommRingCat) X.regularPresheaf).mpr
  rw [regularPresheaf_comp_forget X]
  exact TopCat.subpresheafToTypes.isSheaf (regularLocalPredicate X)

end Hartshorne.Variety
