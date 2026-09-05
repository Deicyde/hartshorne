/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyFunctionFieldStructure
import Hartshorne.Morphism.FunctionFieldStructure

/-!
# The two constructions of `K(Y)` agree on an affine variety

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(c).

The counterpart of the corresponding statement for germs. `K(Y)` was built twice,
once in affine coordinates and once over the bundled `Variety`, and for a
quasi-affine `Y` the two are the same field.

As with germs there is nothing to prove: a representative is a nonempty open set
carrying a regular function, and `regular` on `Variety.ofQuasiAffine hY` is by
definition `IsRegularVia` in the affine coordinates. Unlike the germ case there
is no base point, so the instance-search obstacle that forced the point to be
spelled `⟨P.1, P.2⟩` does not arise here.

## Main definitions

* `Hartshorne.functionFieldEquivAffine`
-/

namespace Hartshorne

open TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}
  (hY : IsQuasiAffineVariety Y)

/-- An affine rational representative, over the bundled variety. -/
def ratRepToVariety (r : RationalRep Y) :
    Variety.RationalRep (Variety.ofQuasiAffine hY) where
  U := ⟨r.U, r.isOpen_U⟩
  nonempty_U := r.nonempty_U
  toFun := r.toFun
  regular := r.isRegular

/-- And back again. -/
def ratRepOfVariety (r : Variety.RationalRep (Variety.ofQuasiAffine hY)) :
    RationalRep Y where
  U := (r.U : Set (Variety.ofQuasiAffine hY).carrier)
  isOpen_U := r.U.isOpen
  nonempty_U := r.nonempty_U
  toFun := r.toFun
  isRegular := r.regular

/-- **The abstract `K(Y)` is the affine `K(Y)`.** -/
noncomputable def functionFieldEquivAffine :
    Variety.FunctionField (Variety.ofQuasiAffine hY) ≃+* FunctionField hY.isIrreducible where
  toFun := Quotient.map (ratRepOfVariety hY) fun _ _ h => h
  invFun := Quotient.map (ratRepToVariety hY) fun _ _ h => h
  left_inv := by
    refine Quotient.ind fun r => ?_
    exact Quotient.sound fun _ _ _ => rfl
  right_inv := by
    refine Quotient.ind fun r => ?_
    exact Quotient.sound fun _ _ _ => rfl
  map_mul' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl
  map_add' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl

end Hartshorne
