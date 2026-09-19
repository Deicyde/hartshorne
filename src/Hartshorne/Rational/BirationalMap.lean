/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.RationalMap
import Mathlib.CategoryTheory.Iso

/-!
# Birational maps

Hartshorne, *Algebraic Geometry*, I.4, p. 24.

A birational map is an isomorphism in the category of separated varieties and
dominant rational maps. Two separated varieties are birational when such a map
exists.

## Main definitions

* `Hartshorne.BirationalMap`
* `Hartshorne.Birational`
-/

namespace Hartshorne

open CategoryTheory

universe u v

variable {k : Type u} [Field k]

/-- A birational map between separated varieties is an isomorphism in the
category of separated varieties and dominant rational maps. -/
noncomputable abbrev BirationalMap (X Y : SeparatedVariety.{u, v} k) : Type _ :=
  CategoryTheory.Iso X Y

/-- Two separated varieties are birational when a birational map exists. -/
def Birational (X Y : SeparatedVariety.{u, v} k) : Prop :=
  Nonempty (BirationalMap X Y)

end Hartshorne
