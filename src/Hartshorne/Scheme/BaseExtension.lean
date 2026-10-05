/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SchemesHaveFiberProducts

/-!
# Base extension

Hartshorne, *Algebraic Geometry*, II.3 (pp. 89–90).

The base extension of a scheme `X ⟶ S` along `S' ⟶ S` is the chosen
pullback `X ×_S S'`, regarded as a scheme over `S'` through its second
projection.
-/

namespace Hartshorne

open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/-- The base extension of `X ⟶ S` along `S' ⟶ S` is their chosen
pullback over `S`. -/
noncomputable def baseExtension {S X S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    Scheme.{u} :=
  pullback f g

/-- The structure morphism from the base extension to the new base. -/
noncomputable def baseExtensionProjection {S X S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    baseExtension f g ⟶ S' :=
  pullback.snd f g

end Hartshorne
