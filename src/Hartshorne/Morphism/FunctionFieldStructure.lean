/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.LocalRingStructure

/-!
# The function field is a ring

Hartshorne, *Algebraic Geometry*, I.3, p. 16.

`K(Y)` was built as a quotient of rational-function representatives; here it
gets its `k`-algebra structure.

The construction copies the one for `𝒪_{P,Y}`, with one difference that
Hartshorne flags himself: there is no distinguished point to keep the domains
from separating, so nonemptiness of `r.U ∩ s.U` has to come from irreducibility
instead. That is why every operation here takes the irreducibility hypothesis
and the germ operations do not.

## Main definitions

* `Hartshorne.RationalRep.add`, `Hartshorne.RationalRep.mul`,
  `Hartshorne.RationalRep.neg`, `Hartshorne.RationalRep.const`

## Main results

* the `CommRing` and `Algebra k` instances on `Hartshorne.FunctionField`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}

namespace RationalRep

variable (hY : IsIrreducible Y)

/-- The sum of two representatives, on the intersection of their domains. That
intersection is nonempty because `Y` is irreducible. -/
def add (r s : RationalRep Y) : RationalRep Y where
  U := r.U ∩ s.U
  isOpen_U := r.isOpen_U.inter s.isOpen_U
  nonempty_U := inter_nonempty hY r.isOpen_U s.isOpen_U r.nonempty_U s.nonempty_U
  toFun := fun x => r.toFun ⟨x.1, x.2.1⟩ + s.toFun ⟨x.1, x.2.2⟩
  isRegular :=
    IsRegularVia.add (isRegularVia_restrict (fun _ hy => hy.1) r.isRegular)
      (isRegularVia_restrict (fun _ hy => hy.2) s.isRegular)

/-- The product of two representatives, on the intersection of their domains. -/
def mul (r s : RationalRep Y) : RationalRep Y where
  U := r.U ∩ s.U
  isOpen_U := r.isOpen_U.inter s.isOpen_U
  nonempty_U := inter_nonempty hY r.isOpen_U s.isOpen_U r.nonempty_U s.nonempty_U
  toFun := fun x => r.toFun ⟨x.1, x.2.1⟩ * s.toFun ⟨x.1, x.2.2⟩
  isRegular :=
    IsRegularVia.mul (isRegularVia_restrict (fun _ hy => hy.1) r.isRegular)
      (isRegularVia_restrict (fun _ hy => hy.2) s.isRegular)

/-- The negative of a representative, on the same domain. -/
def neg (r : RationalRep Y) : RationalRep Y where
  U := r.U
  isOpen_U := r.isOpen_U
  nonempty_U := r.nonempty_U
  toFun := fun x => -r.toFun x
  isRegular := IsRegularVia.neg r.isRegular

/-- A constant, on all of `Y`. Nonempty because an irreducible space is. -/
def const (c : k) : RationalRep Y where
  U := Set.univ
  isOpen_U := isOpen_univ
  nonempty_U := hY.1.to_subtype.elim fun x => ⟨x, Set.mem_univ x⟩
  toFun := fun _ => c
  isRegular := isRegularVia_const _ c

@[simp]
theorem add_toFun (r s : RationalRep Y) (x : Y) (hx : x ∈ (add hY r s).U) :
    (add hY r s).toFun ⟨x, hx⟩ = r.toFun ⟨x, hx.1⟩ + s.toFun ⟨x, hx.2⟩ := rfl

@[simp]
theorem mul_toFun (r s : RationalRep Y) (x : Y) (hx : x ∈ (mul hY r s).U) :
    (mul hY r s).toFun ⟨x, hx⟩ = r.toFun ⟨x, hx.1⟩ * s.toFun ⟨x, hx.2⟩ := rfl

@[simp]
theorem neg_toFun (r : RationalRep Y) (x : Y) (hx : x ∈ r.neg.U) :
    r.neg.toFun ⟨x, hx⟩ = -r.toFun ⟨x, hx⟩ := rfl

@[simp]
theorem const_toFun (c : k) (x : Y) (hx : x ∈ (const hY c).U) :
    (const hY c).toFun ⟨x, hx⟩ = c := rfl

theorem add_congr {r r' s s' : RationalRep Y} (hr : r.Rel r') (hs : s.Rel s') :
    (add hY r s).Rel (add hY r' s') := by
  intro x hx hx'
  rw [add_toFun, add_toFun, hr x hx.1 hx'.1, hs x hx.2 hx'.2]

theorem mul_congr {r r' s s' : RationalRep Y} (hr : r.Rel r') (hs : s.Rel s') :
    (mul hY r s).Rel (mul hY r' s') := by
  intro x hx hx'
  rw [mul_toFun, mul_toFun, hr x hx.1 hx'.1, hs x hx.2 hx'.2]

theorem neg_congr {r r' : RationalRep Y} (hr : r.Rel r') : r.neg.Rel r'.neg := by
  intro x hx hx'
  rw [neg_toFun, neg_toFun, hr x hx hx']

end RationalRep

variable {hY : IsIrreducible Y}

noncomputable instance : Add (FunctionField hY) :=
  ⟨Quotient.map₂ (RationalRep.add hY) fun _ _ hr _ _ hs => RationalRep.add_congr hY hr hs⟩

noncomputable instance : Mul (FunctionField hY) :=
  ⟨Quotient.map₂ (RationalRep.mul hY) fun _ _ hr _ _ hs => RationalRep.mul_congr hY hr hs⟩

noncomputable instance : Neg (FunctionField hY) :=
  ⟨Quotient.map RationalRep.neg fun _ _ hr => RationalRep.neg_congr hr⟩

noncomputable instance : Zero (FunctionField hY) := ⟨Quotient.mk _ (RationalRep.const hY 0)⟩

noncomputable instance : One (FunctionField hY) := ⟨Quotient.mk _ (RationalRep.const hY 1)⟩

/-- Every ring axiom on `K(Y)` reduces to the same identity in `k`, checked at a
point of the common domain, which is nonempty by irreducibility. -/
private theorem mk_eq_mk {r s : RationalRep Y}
    (h : ∀ (x : Y) (hr : x ∈ r.U) (hs : x ∈ s.U), r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩) :
    (Quotient.mk (rationalSetoid hY) r : FunctionField hY) = Quotient.mk _ s :=
  Quotient.sound h

/-- `K(Y)` is a commutative ring. -/
noncomputable instance instCommRingFunctionField : CommRing (FunctionField hY) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    refine Quotient.ind fun a => Quotient.ind fun b => Quotient.ind fun c => ?_
    exact mk_eq_mk fun _ _ _ => by simp [add_assoc]
  zero_add := by
    refine Quotient.ind fun a => ?_
    exact mk_eq_mk fun _ _ _ => by simp
  add_zero := by
    refine Quotient.ind fun a => ?_
    exact mk_eq_mk fun _ _ _ => by simp
  add_comm := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact mk_eq_mk fun _ _ _ => by simp [add_comm]
  neg_add_cancel := by
    refine Quotient.ind fun a => ?_
    exact mk_eq_mk fun _ _ _ => by simp
  mul_assoc := by
    refine Quotient.ind fun a => Quotient.ind fun b => Quotient.ind fun c => ?_
    exact mk_eq_mk fun _ _ _ => by simp [mul_assoc]
  mul_comm := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact mk_eq_mk fun _ _ _ => by simp [mul_comm]
  one_mul := by
    refine Quotient.ind fun a => ?_
    exact mk_eq_mk fun _ _ _ => by simp
  mul_one := by
    refine Quotient.ind fun a => ?_
    exact mk_eq_mk fun _ _ _ => by simp
  zero_mul := by
    refine Quotient.ind fun a => ?_
    exact mk_eq_mk fun _ _ _ => by simp
  mul_zero := by
    refine Quotient.ind fun a => ?_
    exact mk_eq_mk fun _ _ _ => by simp
  left_distrib := by
    refine Quotient.ind fun a => Quotient.ind fun b => Quotient.ind fun c => ?_
    exact mk_eq_mk fun _ _ _ => by simp [mul_add]
  right_distrib := by
    refine Quotient.ind fun a => Quotient.ind fun b => Quotient.ind fun c => ?_
    exact mk_eq_mk fun _ _ _ => by simp [add_mul]

/-- The structure map `k → K(Y)`, sending a scalar to the constant function. -/
def constHomFunctionField : k →+* FunctionField hY where
  toFun c := Quotient.mk _ (RationalRep.const hY c)
  map_one' := rfl
  map_mul' _ _ := Quotient.sound fun _ _ _ => rfl
  map_zero' := rfl
  map_add' _ _ := Quotient.sound fun _ _ _ => rfl

noncomputable instance : Algebra k (FunctionField hY) := constHomFunctionField.toAlgebra

end Hartshorne
