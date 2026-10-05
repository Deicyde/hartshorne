/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Cohen--Macaulay local rings and schemes

Hartshorne, *Algebraic Geometry*, II.8, p. 184.

The depth of a module over a local ring is the extended-natural supremum of
the lengths of its regular sequences lying in the maximal ideal. A Noetherian
local ring is Cohen--Macaulay when its depth as a module over itself equals
its Krull dimension, and a locally Noetherian scheme is Cohen--Macaulay when
all of its local rings are Cohen--Macaulay.
-/

noncomputable section

open IsLocalRing

universe u v

namespace Module

/-- The depth of a module over a local ring, valued in the extended natural
numbers. It is `∞` when the maximal ideal generates the module, and otherwise
is the supremum of the lengths of regular sequences in the maximal ideal. -/
def depth (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] : ℕ∞ :=
  if maximalIdeal R • (⊤ : Submodule R M) = ⊤ then
    ⊤
  else
    ⨆ rs : {rs : List R //
        RingTheory.Sequence.IsRegular M rs ∧
          ∀ r ∈ rs, r ∈ maximalIdeal R},
      (rs.1.length : ℕ∞)

end Module

/-- A Cohen--Macaulay local ring is a Noetherian local ring whose depth equals
its Krull dimension. -/
class IsCohenMacaulayLocalRing (R : Type u) [CommRing R] : Prop
    extends IsLocalRing R, IsNoetherianRing R where
  depth_eq_ringKrullDim :
    (↑(Module.depth R R) : WithBot ℕ∞) = ringKrullDim R

namespace AlgebraicGeometry

/-- A scheme is Cohen--Macaulay when it is locally Noetherian and every local
ring is Cohen--Macaulay. -/
def Scheme.IsCohenMacaulay (X : Scheme.{u}) : Prop :=
  IsLocallyNoetherian X ∧
    ∀ x : X, IsCohenMacaulayLocalRing (X.presheaf.stalk x)

end AlgebraicGeometry
