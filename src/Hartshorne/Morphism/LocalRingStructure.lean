/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.Injections

/-!
# The local ring at a point is a ring, and is local

Hartshorne, *Algebraic Geometry*, I.3, p. 16.

`𝒪_{P,Y}` was built as a quotient of germ representatives; here it gets its
`k`-algebra structure and the `IsLocalRing` instance.

Operations are defined on representatives by intersecting domains, which is
where the shared point `P` earns its keep: the intersection of two
neighbourhoods of `P` is again one, so it is automatically nonempty and the
result is again a germ representative.

## Locality

The unique maximal ideal is the set of germs vanishing at `P`, and the argument
is Hartshorne's one line. If `f(P) ≠ 0` then `f` is nonzero on a whole
neighbourhood of `P` — that set is open because the locus where `f` agrees with
`0` is closed, by Lemma 3.1 — and on that neighbourhood `1/f` is again regular,
with the roles of numerator and denominator swapped. So a germ is a unit exactly
when it does not vanish at `P`, and the non-units are the kernel of evaluation.

Evaluation at `P` is also surjective onto `k`, since constants are regular, so
the residue field is `k`.

## Main definitions

* `Hartshorne.GermRep.add`, `Hartshorne.GermRep.mul`, `Hartshorne.GermRep.neg`,
  `Hartshorne.GermRep.const`, `Hartshorne.GermRep.inv`
* `Hartshorne.evalAtPoint`, `Hartshorne.residueFieldEquiv`

## Main results

* `Hartshorne.isUnit_iff_evalAtPoint_ne_zero`
* the `CommRing`, `Algebra k` and `IsLocalRing` instances on `LocalRingAt`
* `Hartshorne.maximalIdeal_eq_ker`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)} {P : Y}

namespace GermRep

/-- The sum of two representatives, on the intersection of their domains. -/
def add (r s : GermRep Y P) : GermRep Y P where
  U := r.U ∩ s.U
  isOpen_U := r.isOpen_U.inter s.isOpen_U
  mem_U := ⟨r.mem_U, s.mem_U⟩
  toFun := fun x => r.toFun ⟨x.1, x.2.1⟩ + s.toFun ⟨x.1, x.2.2⟩
  isRegular :=
    IsRegularVia.add (isRegularVia_restrict (fun _ hy => hy.1) r.isRegular)
      (isRegularVia_restrict (fun _ hy => hy.2) s.isRegular)

/-- The product of two representatives, on the intersection of their domains. -/
def mul (r s : GermRep Y P) : GermRep Y P where
  U := r.U ∩ s.U
  isOpen_U := r.isOpen_U.inter s.isOpen_U
  mem_U := ⟨r.mem_U, s.mem_U⟩
  toFun := fun x => r.toFun ⟨x.1, x.2.1⟩ * s.toFun ⟨x.1, x.2.2⟩
  isRegular :=
    IsRegularVia.mul (isRegularVia_restrict (fun _ hy => hy.1) r.isRegular)
      (isRegularVia_restrict (fun _ hy => hy.2) s.isRegular)

/-- The negative of a representative, on the same domain. -/
def neg (r : GermRep Y P) : GermRep Y P where
  U := r.U
  isOpen_U := r.isOpen_U
  mem_U := r.mem_U
  toFun := fun x => -r.toFun x
  isRegular := IsRegularVia.neg r.isRegular

/-- A constant, as a representative defined on all of `Y`. -/
def const (P : Y) (c : k) : GermRep Y P where
  U := Set.univ
  isOpen_U := isOpen_univ
  mem_U := Set.mem_univ _
  toFun := fun _ => c
  isRegular := isRegularVia_const _ c

@[simp]
theorem add_toFun (r s : GermRep Y P) (x : Y) (hx : x ∈ (r.add s).U) :
    (r.add s).toFun ⟨x, hx⟩ = r.toFun ⟨x, hx.1⟩ + s.toFun ⟨x, hx.2⟩ := rfl

@[simp]
theorem mul_toFun (r s : GermRep Y P) (x : Y) (hx : x ∈ (r.mul s).U) :
    (r.mul s).toFun ⟨x, hx⟩ = r.toFun ⟨x, hx.1⟩ * s.toFun ⟨x, hx.2⟩ := rfl

@[simp]
theorem neg_toFun (r : GermRep Y P) (x : Y) (hx : x ∈ r.neg.U) :
    r.neg.toFun ⟨x, hx⟩ = -r.toFun ⟨x, hx⟩ := rfl

@[simp]
theorem const_toFun (c : k) (x : Y) (hx : x ∈ (const P c).U) :
    (const P c).toFun ⟨x, hx⟩ = c := rfl

theorem add_congr {r r' s s' : GermRep Y P} (hr : r.Rel r') (hs : s.Rel s') :
    (r.add s).Rel (r'.add s') := by
  intro x hx hx'
  rw [add_toFun, add_toFun, hr x hx.1 hx'.1, hs x hx.2 hx'.2]

theorem mul_congr {r r' s s' : GermRep Y P} (hr : r.Rel r') (hs : s.Rel s') :
    (r.mul s).Rel (r'.mul s') := by
  intro x hx hx'
  rw [mul_toFun, mul_toFun, hr x hx.1 hx'.1, hs x hx.2 hx'.2]

theorem neg_congr {r r' : GermRep Y P} (hr : r.Rel r') : r.neg.Rel r'.neg := by
  intro x hx hx'
  rw [neg_toFun, neg_toFun, hr x hx hx']

/-- The value of a representative at `P`. Germs that are related agree at `P`,
so this descends to `𝒪_{P,Y}`. -/
def valueAt (r : GermRep Y P) : k := r.toFun ⟨P, r.mem_U⟩

/-- The set where a representative is defined and nonzero.

Phrased as "defined, and nonzero for every proof of definedness" rather than as
a dependent pair, so that membership can be projected without choice. -/
def nonvanishing (r : GermRep Y P) : Set Y :=
  {x | (∀ hx : x ∈ r.U, r.toFun ⟨x, hx⟩ ≠ 0) ∧ x ∈ r.U}

theorem nonvanishing_subset (r : GermRep Y P) : r.nonvanishing ⊆ r.U := fun _ hx => hx.2

theorem nonvanishing_eq_image (r : GermRep Y P) :
    r.nonvanishing = Subtype.val '' {y : r.U | r.toFun y ≠ 0} := by
  ext x
  constructor
  · rintro ⟨hall, hx⟩
    exact ⟨⟨x, hx⟩, hall hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨fun _ => hy, y.2⟩

/-- The nonvanishing set is open: it is the complement, inside the open `r.U`,
of the locus where `r` agrees with `0`, which is closed by Lemma 3.1. -/
theorem isOpen_nonvanishing (r : GermRep Y P) : IsOpen r.nonvanishing := by
  rw [nonvanishing_eq_image]
  refine r.isOpen_U.isOpenMap_subtype_val _ ?_
  have hclosed : IsClosed {y : r.U | r.toFun y = 0} := by
    have := isClosed_eqLocusVia (ι := fun x : r.U => (x.1 : σ → k))
      (by fun_prop) r.isRegular (isRegularVia_const (fun x : r.U => (x.1 : σ → k)) 0)
    simpa using this
  simpa [Set.compl_ofPred] using hclosed.isOpen_compl

theorem mem_nonvanishing (r : GermRep Y P) (h : r.valueAt ≠ 0) : P ∈ r.nonvanishing :=
  ⟨fun _ => h, r.mem_U⟩

/-- The inverse of a representative that is nonzero at `P`, defined on the open
set where it is nonzero. -/
def inv (r : GermRep Y P) (h : r.valueAt ≠ 0) : GermRep Y P where
  U := r.nonvanishing
  isOpen_U := r.isOpen_nonvanishing
  mem_U := r.mem_nonvanishing h
  toFun := fun x => (r.toFun ⟨x.1, x.2.2⟩)⁻¹
  isRegular :=
    (isRegularVia_restrict r.nonvanishing_subset r.isRegular).inv
      fun x => x.2.1 (r.nonvanishing_subset x.2)

@[simp]
theorem inv_toFun (r : GermRep Y P) (h : r.valueAt ≠ 0) (x : Y) (hx : x ∈ (r.inv h).U) :
    (r.inv h).toFun ⟨x, hx⟩ = (r.toFun ⟨x, hx.2⟩)⁻¹ := rfl

/-- A representative nonzero at `P` becomes invertible after restricting to the
open set where it is nonzero. -/
theorem mul_inv_rel_one (r : GermRep Y P) (h : r.valueAt ≠ 0) :
    (r.mul (r.inv h)).Rel (const P 1) := by
  intro x hx _
  rw [mul_toFun, inv_toFun, const_toFun]
  exact mul_inv_cancel₀ (hx.2.1 hx.2.2)

end GermRep

variable {hY : IsIrreducible Y}

noncomputable instance : Add (LocalRingAt hY P) :=
  ⟨Quotient.map₂ GermRep.add fun _ _ hr _ _ hs => GermRep.add_congr hr hs⟩

noncomputable instance : Mul (LocalRingAt hY P) :=
  ⟨Quotient.map₂ GermRep.mul fun _ _ hr _ _ hs => GermRep.mul_congr hr hs⟩

noncomputable instance : Neg (LocalRingAt hY P) :=
  ⟨Quotient.map GermRep.neg fun _ _ hr => GermRep.neg_congr hr⟩

noncomputable instance : Zero (LocalRingAt hY P) := ⟨Quotient.mk _ (GermRep.const P 0)⟩

noncomputable instance : One (LocalRingAt hY P) := ⟨Quotient.mk _ (GermRep.const P 1)⟩

/-- Every ring axiom on `𝒪_{P,Y}` reduces to the same identity in `k`, checked
at a point of the common domain of the representatives, so they all have this
shape. -/
private theorem mk_eq_mk {r s : GermRep Y P}
    (h : ∀ (x : Y) (hr : x ∈ r.U) (hs : x ∈ s.U), r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩) :
    (Quotient.mk (germSetoid hY P) r : LocalRingAt hY P) = Quotient.mk _ s :=
  Quotient.sound h

/-- `𝒪_{P,Y}` is a commutative ring.

Addition and multiplication intersect domains, which is legitimate because a
finite intersection of neighbourhoods of `P` is again one. Every axiom is then
the corresponding identity in `k`. -/
noncomputable instance instCommRingLocalRingAt : CommRing (LocalRingAt hY P) where
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

/-- The structure map `k → 𝒪_{P,Y}`, sending a scalar to the constant germ. -/
def constHom : k →+* LocalRingAt hY P where
  toFun c := Quotient.mk _ (GermRep.const P c)
  map_one' := rfl
  map_mul' _ _ := Quotient.sound fun _ _ _ => rfl
  map_zero' := rfl
  map_add' _ _ := Quotient.sound fun _ _ _ => rfl

noncomputable instance : Algebra k (LocalRingAt hY P) := constHom.toAlgebra

/-- Evaluation at `P`, as a ring homomorphism `𝒪_{P,Y} → k`.

Well defined because `P` lies in the domain of every representative, and
related representatives agree wherever both are defined. -/
def evalAtPoint : LocalRingAt hY P →+* k where
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
theorem evalAtPoint_mk (r : GermRep Y P) :
    evalAtPoint (Quotient.mk (germSetoid hY P) r : LocalRingAt hY P) = r.valueAt := rfl

/-- **A germ is a unit exactly when it does not vanish at `P`.**

This is the whole content of locality. One direction is that evaluation is a
ring map into a field. The other is that a germ nonzero at `P` is nonzero on a
whole neighbourhood, where its reciprocal is again regular. -/
theorem isUnit_iff_evalAtPoint_ne_zero (a : LocalRingAt hY P) :
    IsUnit a ↔ evalAtPoint a ≠ 0 := by
  refine ⟨fun ha => (ha.map (evalAtPoint (hY := hY) (P := P))).ne_zero, ?_⟩
  refine Quotient.inductionOn a ?_
  intro r hr
  set a : LocalRingAt hY P := Quotient.mk (germSetoid hY P) r with ha
  set b : LocalRingAt hY P := Quotient.mk (germSetoid hY P) (r.inv hr) with hb
  have hmul : a * b = 1 := mk_eq_mk (r.mul_inv_rel_one hr)
  exact ⟨⟨a, b, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩

instance : Nontrivial (LocalRingAt hY P) :=
  ⟨⟨0, 1, fun h => by simpa using congrArg (evalAtPoint (hY := hY) (P := P)) h⟩⟩

/-- **`𝒪_{P,Y}` is a local ring.**

Given any germ, either it is nonzero at `P`, and so a unit, or it vanishes at
`P`, in which case `1 - a` does not and is a unit instead. -/
instance instIsLocalRingLocalRingAt : IsLocalRing (LocalRingAt hY P) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases eq_or_ne (evalAtPoint a) 0 with h | h
  · right
    rw [isUnit_iff_evalAtPoint_ne_zero]
    simp [h]
  · exact Or.inl ((isUnit_iff_evalAtPoint_ne_zero a).2 h)

/-- Hartshorne's `𝔪`: the maximal ideal is exactly the germs vanishing at
`P`. -/
theorem maximalIdeal_eq_ker :
    IsLocalRing.maximalIdeal (LocalRingAt hY P)
      = RingHom.ker (evalAtPoint (hY := hY) (P := P)) := by
  ext a
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_evalAtPoint_ne_zero,
    not_not, RingHom.mem_ker]

theorem evalAtPoint_surjective :
    Function.Surjective (evalAtPoint (hY := hY) (P := P)) :=
  fun c => ⟨Quotient.mk _ (GermRep.const P c), rfl⟩

/-- **The residue field is `k`**: evaluation at `P` is a surjection onto `k`
whose kernel is the maximal ideal. -/
noncomputable def residueFieldEquiv :
    (LocalRingAt hY P ⧸ IsLocalRing.maximalIdeal (LocalRingAt hY P)) ≃+* k :=
  (Ideal.quotEquivOfEq maximalIdeal_eq_ker).trans
    (RingHom.quotientKerEquivOfSurjective evalAtPoint_surjective)

end Hartshorne
