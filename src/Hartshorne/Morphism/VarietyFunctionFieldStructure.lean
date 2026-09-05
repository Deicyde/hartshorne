/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyRational

/-!
# `K(X)` is a field, for an arbitrary variety

Hartshorne, *Algebraic Geometry*, I.3, the assertion on p. 16 that `K(Y)` is a
field, for a bundled `Variety`.

The ring structure is the germ one with the base point removed: sums and
products intersect domains, and the intersection is nonempty by irreducibility
rather than because both contain `P`. Every ring axiom is then the corresponding
identity in `k`, checked at a point of the common domain.

Inverting is where the base point mattered, and where dropping it makes the
statement stronger rather than weaker. A germ is invertible when it is nonzero
*at `P`*, which is a strictly stronger condition than being a nonzero germ; a
rational function is invertible as soon as it is nonzero, because "nonzero"
already means "nonzero somewhere", and the locus where it is nonzero is open and
may be taken as the new domain. That is the whole reason `K(X)` is a field and
`𝒪_P` is only local.

## Main results

* `Hartshorne.Variety.instFieldFunctionField`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X : Variety.{u, v} k}

namespace Variety.RationalRep

/-- The sum of two representatives, on the intersection of their domains, which
is nonempty because the variety is irreducible. -/
def add (r s : RationalRep X) : RationalRep X where
  U := r.U ⊓ s.U
  nonempty_U := opens_inter_nonempty r.nonempty_U s.nonempty_U
  toFun := fun x => r.toFun ⟨x.1, x.2.1⟩ + s.toFun ⟨x.1, x.2.2⟩
  regular := Subalgebra.add_mem _ (X.regular_restrict inf_le_left r.regular)
    (X.regular_restrict inf_le_right s.regular)

/-- The product of two representatives. -/
def mul (r s : RationalRep X) : RationalRep X where
  U := r.U ⊓ s.U
  nonempty_U := opens_inter_nonempty r.nonempty_U s.nonempty_U
  toFun := fun x => r.toFun ⟨x.1, x.2.1⟩ * s.toFun ⟨x.1, x.2.2⟩
  regular := Subalgebra.mul_mem _ (X.regular_restrict inf_le_left r.regular)
    (X.regular_restrict inf_le_right s.regular)

/-- The negative of a representative. -/
def neg (r : RationalRep X) : RationalRep X where
  U := r.U
  nonempty_U := r.nonempty_U
  toFun := fun x => -r.toFun x
  regular := Subalgebra.neg_mem _ r.regular

/-- A constant, defined everywhere. -/
def const (X : Variety.{u, v} k) (c : k) : RationalRep X where
  U := ⊤
  nonempty_U := (X.nonempty.elim fun x => ⟨x, trivial⟩ : _)
  toFun := fun _ => c
  regular := Subalgebra.algebraMap_mem _ c

@[simp]
theorem add_toFun (r s : RationalRep X) (x : X.carrier) (hx : x ∈ (r.add s).U) :
    (r.add s).toFun ⟨x, hx⟩ = r.toFun ⟨x, hx.1⟩ + s.toFun ⟨x, hx.2⟩ := rfl

@[simp]
theorem mul_toFun (r s : RationalRep X) (x : X.carrier) (hx : x ∈ (r.mul s).U) :
    (r.mul s).toFun ⟨x, hx⟩ = r.toFun ⟨x, hx.1⟩ * s.toFun ⟨x, hx.2⟩ := rfl

@[simp]
theorem neg_toFun (r : RationalRep X) (x : X.carrier) (hx : x ∈ r.neg.U) :
    r.neg.toFun ⟨x, hx⟩ = -r.toFun ⟨x, hx⟩ := rfl

@[simp]
theorem const_toFun (c : k) (x : X.carrier) (hx : x ∈ (const X c).U) :
    (const X c).toFun ⟨x, hx⟩ = c := rfl

theorem add_congr {r r' s s' : RationalRep X} (hr : r.Rel r') (hs : s.Rel s') :
    (r.add s).Rel (r'.add s') := by
  intro x hx hx'
  rw [add_toFun, add_toFun, hr x hx.1 hx'.1, hs x hx.2 hx'.2]

theorem mul_congr {r r' s s' : RationalRep X} (hr : r.Rel r') (hs : s.Rel s') :
    (r.mul s).Rel (r'.mul s') := by
  intro x hx hx'
  rw [mul_toFun, mul_toFun, hr x hx.1 hx'.1, hs x hx.2 hx'.2]

theorem neg_congr {r r' : RationalRep X} (hr : r.Rel r') : r.neg.Rel r'.neg := by
  intro x hx hx'
  rw [neg_toFun, neg_toFun, hr x hx hx']

/-- The set where a representative is defined and nonzero. -/
def nonvanishingSet (r : RationalRep X) : Set X.carrier :=
  {x | (∀ hx : x ∈ r.U, r.toFun ⟨x, hx⟩ ≠ 0) ∧ x ∈ r.U}

theorem nonvanishingSet_subset (r : RationalRep X) :
    r.nonvanishingSet ⊆ (r.U : Set X.carrier) := fun _ hx => hx.2

theorem nonvanishingSet_eq_image (r : RationalRep X) :
    r.nonvanishingSet = Subtype.val '' {y : r.U | r.toFun y ≠ 0} := by
  ext x
  constructor
  · rintro ⟨hall, hx⟩
    exact ⟨⟨x, hx⟩, hall hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun _ => hy, y.2⟩

/-- The nonvanishing set is open: it is the complement, inside the open `r.U`,
of a zero locus, and zero loci of regular functions are closed. -/
theorem isOpen_nonvanishingSet (r : RationalRep X) : IsOpen r.nonvanishingSet := by
  rw [nonvanishingSet_eq_image]
  refine r.U.isOpen.isOpenMap_subtype_val _ ?_
  simpa [Set.compl_ofPred] using (X.isClosed_zeroLocus r.regular).isOpen_compl

/-- The nonvanishing set, as an open subset. -/
def nonvanishing (r : RationalRep X) : Opens X.carrier :=
  ⟨r.nonvanishingSet, r.isOpen_nonvanishingSet⟩

/-- **A representative not equivalent to zero is nonzero somewhere.**

This is where the function field parts company with the local ring: there is no
point at which the value has to be nonzero, only the negation of "vanishes
identically", and that is exactly what is needed. -/
theorem nonempty_nonvanishing {r : RationalRep X} (h : ¬ r.Rel (const X 0)) :
    ((r.nonvanishing : Opens X.carrier) : Set X.carrier).Nonempty := by
  by_contra hempty
  refine h fun x hx _ => ?_
  by_contra hne
  exact hempty ⟨x, fun _ => hne, hx⟩

/-- The reciprocal, on the open set where the representative is nonzero. -/
noncomputable def inv (r : RationalRep X) (h : ¬ r.Rel (const X 0)) : RationalRep X where
  U := r.nonvanishing
  nonempty_U := nonempty_nonvanishing h
  toFun := fun x => (r.toFun ⟨x.1, x.2.2⟩)⁻¹
  regular := by
    have hle : r.nonvanishing ≤ r.U := r.nonvanishingSet_subset
    have hres : (fun x : r.nonvanishing => r.toFun ⟨x.1, x.2.2⟩) ∈ X.regular r.nonvanishing :=
      X.regular_restrict hle r.regular
    have := X.regular_div (Subalgebra.one_mem (X.regular r.nonvanishing)) hres
      fun x => x.2.1 x.2.2
    simpa [one_div] using this

@[simp]
theorem inv_toFun (r : RationalRep X) (h : ¬ r.Rel (const X 0)) (x : X.carrier)
    (hx : x ∈ (r.inv h).U) : (r.inv h).toFun ⟨x, hx⟩ = (r.toFun ⟨x, hx.2⟩)⁻¹ := rfl

theorem mul_inv_rel_one (r : RationalRep X) (h : ¬ r.Rel (const X 0)) :
    (r.mul (r.inv h)).Rel (const X 1) := by
  intro x hx _
  rw [mul_toFun, inv_toFun, const_toFun]
  exact mul_inv_cancel₀ (hx.2.1 hx.2.2)

end Variety.RationalRep

namespace Variety

noncomputable instance : Add (FunctionField X) :=
  ⟨Quotient.map₂ RationalRep.add fun _ _ hr _ _ hs => RationalRep.add_congr hr hs⟩

noncomputable instance : Mul (FunctionField X) :=
  ⟨Quotient.map₂ RationalRep.mul fun _ _ hr _ _ hs => RationalRep.mul_congr hr hs⟩

noncomputable instance : Neg (FunctionField X) :=
  ⟨Quotient.map RationalRep.neg fun _ _ hr => RationalRep.neg_congr hr⟩

noncomputable instance : Zero (FunctionField X) := ⟨Quotient.mk _ (RationalRep.const X 0)⟩

noncomputable instance : One (FunctionField X) := ⟨Quotient.mk _ (RationalRep.const X 1)⟩

/-- Every ring axiom reduces to the same identity in `k`, checked at a point of
the common domain. -/
private theorem mk_eq_mk {r s : RationalRep X}
    (h : ∀ (x : X.carrier) (hr : x ∈ r.U) (hs : x ∈ s.U),
      r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩) :
    (Quotient.mk (rationalSetoid X) r : FunctionField X) = Quotient.mk _ s :=
  Quotient.sound h

/-- `K(X)` is a commutative ring. -/
noncomputable instance instCommRingFunctionField : CommRing (FunctionField X) where
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

/-- The structure map `k → K(X)`. -/
def constRatHom : k →+* FunctionField X where
  toFun c := Quotient.mk _ (RationalRep.const X c)
  map_one' := rfl
  map_mul' _ _ := Quotient.sound fun _ _ _ => rfl
  map_zero' := rfl
  map_add' _ _ := Quotient.sound fun _ _ _ => rfl

noncomputable instance : Algebra k (FunctionField X) := constRatHom.toAlgebra

theorem zero_ne_one_functionField : (0 : FunctionField X) ≠ 1 := by
  intro h
  obtain ⟨x⟩ := X.nonempty
  exact zero_ne_one (Quotient.exact h x trivial trivial)

instance : Nontrivial (FunctionField X) := ⟨⟨0, 1, zero_ne_one_functionField⟩⟩

/-- **`K(X)` is a field.**

A nonzero class has a representative that does not vanish identically, and
restricting to the open set where it is nonzero makes it invertible. Nothing
here is available for `𝒪_P`, where invertibility is nonvanishing at one
prescribed point. -/
theorem isField_functionField : IsField (FunctionField X) where
  exists_pair_ne := ⟨0, 1, zero_ne_one_functionField⟩
  mul_comm := mul_comm
  mul_inv_cancel {a} ha := by
    refine Quotient.inductionOn a
      (motive := fun a : FunctionField X => a ≠ 0 → ∃ b, a * b = 1) ?_ ha
    intro r hr
    have hrel : ¬ r.Rel (RationalRep.const X 0) := fun h => hr (Quotient.sound h)
    exact ⟨Quotient.mk _ (r.inv hrel), mk_eq_mk (r.mul_inv_rel_one hrel)⟩

noncomputable instance instFieldFunctionField : Field (FunctionField X) :=
  isField_functionField.toField

end Variety

end Hartshorne
