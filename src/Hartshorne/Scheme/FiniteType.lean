/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LocallyFiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Morphisms of finite type

Hartshorne, *Algebraic Geometry*, II.3 (p. 84) and Exercise II.3.3(a) (p. 91).

Hartshorne's finite-cover condition is represented by quasi-compactness, so a
morphism is of finite type when it is locally of finite type and quasi-compact.
-/

namespace Hartshorne

open CategoryTheory

universe u

open AlgebraicGeometry

/-- A morphism of schemes is of finite type when it is locally of finite type
and quasi-compact. This is a proposition, not a competing typeclass for the two
component properties supplied by Mathlib. -/
def FiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∧ QuasiCompact f

/-- Every closed immersion is a morphism of finite type. -/
theorem closedImmersion_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : FiniteType f :=
  ⟨inferInstance, inferInstance⟩

/-- Every quasi-compact open immersion is a morphism of finite type. -/
theorem quasiCompactOpenImmersion_finiteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] [QuasiCompact f] : FiniteType f :=
  ⟨inferInstance, inferInstance⟩

/-- The composite of two morphisms of finite type is of finite type. -/
theorem finiteType_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : FiniteType f) (hg : FiniteType g) : FiniteType (f ≫ g) := by
  let _ : LocallyOfFiniteType f := hf.1
  let _ : LocallyOfFiniteType g := hg.1
  let _ : QuasiCompact f := hf.2
  let _ : QuasiCompact g := hg.2
  exact ⟨locallyOfFiniteType_comp f g, quasiCompact_comp f g⟩

/-- If `f` is quasi-compact and the composite `f ≫ g` is of finite type,
then `f` is of finite type. -/
theorem finiteType_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : QuasiCompact f) (hfg : FiniteType (f ≫ g)) : FiniteType f := by
  let _ : LocallyOfFiniteType (f ≫ g) := hfg.1
  exact ⟨locallyOfFiniteType_of_comp f g, hf⟩

end Hartshorne
