/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ConstantSheaf
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Sections of a constant sheaf

Hartshorne, *Algebraic Geometry*, Example II.1.0.3 (p. 62).

On a nonempty connected open set, evaluation at a chosen point identifies the sections of a
constant sheaf with its value group. More generally, when connected components are open, sections
are products of copies of the value group indexed by connected components.
-/

namespace Hartshorne

open CategoryTheory TopologicalSpace Opposite Set

universe u

/-- Evaluation at a chosen point identifies constant-sheaf sections on a nonempty preconnected
open set with the value group. The chosen point records nonemptiness explicitly. -/
def constantSheafSectionsEquivOfIsPreconnected
    (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (U : Opens X) (x : U)
    (hU : IsPreconnected (U : Set X)) :
    (constantSheaf X A).obj.obj (op U) ≃+ A := by
  change LocallyConstant U A ≃+ A
  letI : PreconnectedSpace U := Subtype.preconnectedSpace hU
  exact
    { toFun := fun f ↦ f x
      invFun := LocallyConstant.const U
      left_inv := fun f ↦ (f.eq_const x).symm
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }

/-- On a nonempty preconnected open set, there is an additive equivalence from constant-sheaf
sections to the value group which is evaluation at the chosen point. -/
theorem exists_constantSheafSectionsEquivOfIsPreconnected
    (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (U : Opens X) (x : U)
    (hU : IsPreconnected (U : Set X)) :
    ∃ e : (constantSheaf X A).obj.obj (op U) ≃+ A,
      ∀ s : (constantSheaf X A).obj.obj (op U),
        e s = (show LocallyConstant U A from s) x := by
  refine ⟨constantSheafSectionsEquivOfIsPreconnected X A U x hU, ?_⟩
  intro s
  rfl

/-- If the connected components of an open set are open, constant-sheaf sections are the product
of copies of the value group indexed by those components. -/
def constantSheafSectionsEquivConnectedComponents
    (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (U : Opens X)
    (hU : ∀ x : U, IsOpen (connectedComponent x)) :
    (constantSheaf X A).obj.obj (op U) ≃+ (ConnectedComponents U → A) := by
  change LocallyConstant U A ≃+ (ConnectedComponents U → A)
  letI : DiscreteTopology (ConnectedComponents U) :=
    ConnectedComponents.discreteTopology_iff.mpr hU
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  exact
    { toFun := fun f ↦ f.continuous.connectedComponentsLift
      invFun := fun g ↦
        ⟨g ∘ ConnectedComponents.mk,
          (IsLocallyConstant.of_discrete g).comp_continuous ConnectedComponents.continuous_coe⟩
      left_inv := fun f ↦ LocallyConstant.ext fun x ↦
        f.continuous.connectedComponentsLift_apply_coe x
      right_inv := fun g ↦ funext fun c ↦ by
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
        rfl
      map_add' := fun f g ↦ funext fun c ↦ by
        obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
        rfl }

/-- If connected components are open, there is an additive equivalence from constant-sheaf
sections to component-indexed values which recovers every section at every point. -/
theorem exists_constantSheafSectionsEquivConnectedComponents
    (X : TopCat.{u}) (A : AddCommGrpCat.{u}) (U : Opens X)
    (hU : ∀ x : U, IsOpen (connectedComponent x)) :
    ∃ e : (constantSheaf X A).obj.obj (op U) ≃+ (ConnectedComponents U → A),
      ∀ (s : (constantSheaf X A).obj.obj (op U)) (x : U),
        e s (ConnectedComponents.mk x) = (show LocallyConstant U A from s) x := by
  refine ⟨constantSheafSectionsEquivConnectedComponents X A U hU, ?_⟩
  intro s x
  rfl

end Hartshorne
