/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyGerm

/-!
# The local ring of an arbitrary variety

Hartshorne, *Algebraic Geometry*, I.3, p. 16, for a bundled `Variety`.

`𝒪_{P,X}` gets its `k`-algebra structure and its `IsLocalRing` instance.

The affine version of this needed two facts proved by hand about polynomials: a
nowhere-zero regular function has a regular reciprocal, and the set where a
regular function is nonzero is open. Over the abstract structure both are
fields — `regular_div` and `isClosed_zeroLocus` — so the argument here is
Hartshorne's one line and nothing else.

## Main definitions

* `Hartshorne.Variety.GermRep.add`, `.mul`, `.neg`, `.const`, `.inv`
* `Hartshorne.Variety.evalAtPoint`

## Main results

* the `CommRing`, `Algebra k` and `IsLocalRing` instances on
  `Hartshorne.Variety.LocalRingAt`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X : Variety.{u, v} k} {P : X.carrier}

namespace Variety.GermRep

/-- The sum of two representatives, on the intersection of their domains. -/
def add (r s : GermRep X P) : GermRep X P where
  U := r.U ⊓ s.U
  mem_U := ⟨r.mem_U, s.mem_U⟩
  toFun := fun x => r.toFun ⟨x.1, x.2.1⟩ + s.toFun ⟨x.1, x.2.2⟩
  regular := Subalgebra.add_mem _ (X.regular_restrict inf_le_left r.regular)
    (X.regular_restrict inf_le_right s.regular)

/-- The product of two representatives. -/
def mul (r s : GermRep X P) : GermRep X P where
  U := r.U ⊓ s.U
  mem_U := ⟨r.mem_U, s.mem_U⟩
  toFun := fun x => r.toFun ⟨x.1, x.2.1⟩ * s.toFun ⟨x.1, x.2.2⟩
  regular := Subalgebra.mul_mem _ (X.regular_restrict inf_le_left r.regular)
    (X.regular_restrict inf_le_right s.regular)

/-- The negative of a representative. -/
def neg (r : GermRep X P) : GermRep X P where
  U := r.U
  mem_U := r.mem_U
  toFun := fun x => -r.toFun x
  regular := Subalgebra.neg_mem _ r.regular

/-- A constant, defined everywhere. -/
def const (P : X.carrier) (c : k) : GermRep X P where
  U := ⊤
  mem_U := trivial
  toFun := fun _ => c
  regular := Subalgebra.algebraMap_mem _ c

@[simp]
theorem add_toFun (r s : GermRep X P) (x : X.carrier) (hx : x ∈ (r.add s).U) :
    (r.add s).toFun ⟨x, hx⟩ = r.toFun ⟨x, hx.1⟩ + s.toFun ⟨x, hx.2⟩ := rfl

@[simp]
theorem mul_toFun (r s : GermRep X P) (x : X.carrier) (hx : x ∈ (r.mul s).U) :
    (r.mul s).toFun ⟨x, hx⟩ = r.toFun ⟨x, hx.1⟩ * s.toFun ⟨x, hx.2⟩ := rfl

@[simp]
theorem neg_toFun (r : GermRep X P) (x : X.carrier) (hx : x ∈ r.neg.U) :
    r.neg.toFun ⟨x, hx⟩ = -r.toFun ⟨x, hx⟩ := rfl

@[simp]
theorem const_toFun (c : k) (x : X.carrier) (hx : x ∈ (const P c).U) :
    (const P c).toFun ⟨x, hx⟩ = c := rfl

theorem add_congr {r r' s s' : GermRep X P} (hr : r.Rel r') (hs : s.Rel s') :
    (r.add s).Rel (r'.add s') := by
  intro x hx hx'
  rw [add_toFun, add_toFun, hr x hx.1 hx'.1, hs x hx.2 hx'.2]

theorem mul_congr {r r' s s' : GermRep X P} (hr : r.Rel r') (hs : s.Rel s') :
    (r.mul s).Rel (r'.mul s') := by
  intro x hx hx'
  rw [mul_toFun, mul_toFun, hr x hx.1 hx'.1, hs x hx.2 hx'.2]

theorem neg_congr {r r' : GermRep X P} (hr : r.Rel r') : r.neg.Rel r'.neg := by
  intro x hx hx'
  rw [neg_toFun, neg_toFun, hr x hx hx']

/-- The value of a representative at `P`. -/
def valueAt (r : GermRep X P) : k := r.toFun ⟨P, r.mem_U⟩

/-- The set where a representative is defined and nonzero. -/
def nonvanishingSet (r : GermRep X P) : Set X.carrier :=
  {x | (∀ hx : x ∈ r.U, r.toFun ⟨x, hx⟩ ≠ 0) ∧ x ∈ r.U}

theorem nonvanishingSet_subset (r : GermRep X P) : r.nonvanishingSet ⊆ (r.U : Set X.carrier) :=
  fun _ hx => hx.2

theorem nonvanishingSet_eq_image (r : GermRep X P) :
    r.nonvanishingSet = Subtype.val '' {y : r.U | r.toFun y ≠ 0} := by
  ext x
  constructor
  · rintro ⟨hall, hx⟩
    exact ⟨⟨x, hx⟩, hall hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun _ => hy, y.2⟩

/-- The nonvanishing set is open: it is the complement, inside the open `r.U`,
of a zero locus, and zero loci of regular functions are closed. -/
theorem isOpen_nonvanishingSet (r : GermRep X P) : IsOpen r.nonvanishingSet := by
  rw [nonvanishingSet_eq_image]
  refine r.U.isOpen.isOpenMap_subtype_val _ ?_
  simpa [Set.compl_ofPred] using (X.isClosed_zeroLocus r.regular).isOpen_compl

/-- The nonvanishing set, as an open subset. -/
def nonvanishing (r : GermRep X P) : Opens X.carrier :=
  ⟨r.nonvanishingSet, r.isOpen_nonvanishingSet⟩

theorem mem_nonvanishing (r : GermRep X P) (h : r.valueAt ≠ 0) : P ∈ r.nonvanishing :=
  ⟨fun _ => h, r.mem_U⟩

/-- The reciprocal of a representative that is nonzero at `P`, on the open set
where it is nonzero. Regularity is closure under division, a field of
`Variety`. -/
noncomputable def inv (r : GermRep X P) (h : r.valueAt ≠ 0) : GermRep X P where
  U := r.nonvanishing
  mem_U := r.mem_nonvanishing h
  toFun := fun x => (r.toFun ⟨x.1, x.2.2⟩)⁻¹
  regular := by
    have hle : r.nonvanishing ≤ r.U := r.nonvanishingSet_subset
    have hres : (fun x : r.nonvanishing => r.toFun ⟨x.1, x.2.2⟩) ∈ X.regular r.nonvanishing :=
      X.regular_restrict hle r.regular
    have := X.regular_div (Subalgebra.one_mem (X.regular r.nonvanishing)) hres
      fun x => x.2.1 x.2.2
    simpa [one_div] using this

@[simp]
theorem inv_toFun (r : GermRep X P) (h : r.valueAt ≠ 0) (x : X.carrier)
    (hx : x ∈ (r.inv h).U) : (r.inv h).toFun ⟨x, hx⟩ = (r.toFun ⟨x, hx.2⟩)⁻¹ :=
  rfl

theorem mul_inv_rel_one (r : GermRep X P) (h : r.valueAt ≠ 0) :
    (r.mul (r.inv h)).Rel (const P 1) := by
  intro x hx _
  rw [mul_toFun, inv_toFun, const_toFun]
  exact mul_inv_cancel₀ (hx.2.1 hx.2.2)

end Variety.GermRep

namespace Variety

noncomputable instance : Add (LocalRingAt X P) :=
  ⟨Quotient.map₂ GermRep.add fun _ _ hr _ _ hs => GermRep.add_congr hr hs⟩

noncomputable instance : Mul (LocalRingAt X P) :=
  ⟨Quotient.map₂ GermRep.mul fun _ _ hr _ _ hs => GermRep.mul_congr hr hs⟩

noncomputable instance : Neg (LocalRingAt X P) :=
  ⟨Quotient.map GermRep.neg fun _ _ hr => GermRep.neg_congr hr⟩

noncomputable instance : Zero (LocalRingAt X P) := ⟨Quotient.mk _ (GermRep.const P 0)⟩

noncomputable instance : One (LocalRingAt X P) := ⟨Quotient.mk _ (GermRep.const P 1)⟩

/-- Every ring axiom reduces to the same identity in `k`, checked at a point of
the common domain. -/
private theorem mk_eq_mk {r s : GermRep X P}
    (h : ∀ (x : X.carrier) (hr : x ∈ r.U) (hs : x ∈ s.U),
      r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩) :
    (Quotient.mk (germSetoid X P) r : LocalRingAt X P) = Quotient.mk _ s :=
  Quotient.sound h

/-- `𝒪_{P,X}` is a commutative ring. -/
noncomputable instance instCommRingLocalRingAt : CommRing (LocalRingAt X P) where
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

/-- The structure map `k → 𝒪_{P,X}`. -/
def constHom : k →+* LocalRingAt X P where
  toFun c := Quotient.mk _ (GermRep.const P c)
  map_one' := rfl
  map_mul' _ _ := Quotient.sound fun _ _ _ => rfl
  map_zero' := rfl
  map_add' _ _ := Quotient.sound fun _ _ _ => rfl

noncomputable instance : Algebra k (LocalRingAt X P) := constHom.toAlgebra

/-- Evaluation at `P`, as a ring homomorphism `𝒪_{P,X} → k`. -/
def evalAtPoint : LocalRingAt X P →+* k where
  toFun := Quotient.lift GermRep.valueAt fun r s h => h P r.mem_U s.mem_U
  map_one' := rfl
  map_zero' := rfl
  map_mul' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    rfl
  map_add' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    rfl

@[simp]
theorem evalAtPoint_mk (r : GermRep X P) :
    evalAtPoint (Quotient.mk (germSetoid X P) r : LocalRingAt X P) = r.valueAt := rfl

/-- **A germ is a unit exactly when it does not vanish at `P`.** -/
theorem isUnit_iff_evalAtPoint_ne_zero (a : LocalRingAt X P) :
    IsUnit a ↔ evalAtPoint a ≠ 0 := by
  refine ⟨fun ha => (ha.map (evalAtPoint (X := X) (P := P))).ne_zero, ?_⟩
  refine Quotient.inductionOn a ?_
  intro r hr
  set b : LocalRingAt X P := Quotient.mk (germSetoid X P) r with hb
  set c : LocalRingAt X P := Quotient.mk (germSetoid X P) (r.inv hr) with hc
  have hmul : b * c = 1 := mk_eq_mk (r.mul_inv_rel_one hr)
  exact ⟨⟨b, c, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

instance : Nontrivial (LocalRingAt X P) :=
  ⟨⟨0, 1, fun h => by simpa using congrArg (evalAtPoint (X := X) (P := P)) h⟩⟩

/-- **`𝒪_{P,X}` is a local ring**, for any variety. -/
instance instIsLocalRingLocalRingAt : IsLocalRing (LocalRingAt X P) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases eq_or_ne (evalAtPoint a) 0 with h | h
  · right
    rw [isUnit_iff_evalAtPoint_ne_zero]
    simp [h]
  · exact Or.inl ((isUnit_iff_evalAtPoint_ne_zero a).2 h)

/-- The maximal ideal is the germs vanishing at `P`. -/
theorem maximalIdeal_eq_ker :
    IsLocalRing.maximalIdeal (LocalRingAt X P) = RingHom.ker (evalAtPoint (X := X) (P := P)) := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_evalAtPoint_ne_zero,
    not_not, RingHom.mem_ker]

end Variety

end Hartshorne
