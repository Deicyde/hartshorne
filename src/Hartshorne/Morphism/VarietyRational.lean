/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyGerm

/-!
# Rational functions on an arbitrary variety

Hartshorne, *Algebraic Geometry*, I.3, the definition of `K(Y)` on p. 16, for a
bundled `Variety`.

The affine case was built from `IsRegularVia`, in coordinates. Theorem 3.4(c) is
about `K(Y)` for a *projective* variety, so the construction has to be redone
over the abstract structure, exactly as the germ construction was.

A rational function is a regular function on a nonempty open set, two being
identified when they agree on the overlap of their domains. Dropping the base
point is the only change from germs, and it costs one thing: the overlap of two
domains is no longer nonempty for free. Irreducibility supplies it, and supplies
it twice, since transitivity needs the triple overlap to be nonempty as well.

## Main definitions

* `Hartshorne.Variety.RationalRep`, `Hartshorne.Variety.RationalRep.Rel`
* `Hartshorne.Variety.FunctionField`

## Main results

* `Hartshorne.Variety.RationalRep.rel_trans`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X : Variety.{u, v} k}

namespace Variety

/-- **Two nonempty open subsets of a variety meet.**

This is irreducibility, and it is what replaces the shared point of the germ
construction. Without it a rational function could be identified with another by
having a disjoint domain, and the relation would not be transitive. -/
theorem opens_inter_nonempty {U V : Opens X.carrier} (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    ((U ⊓ V : Opens X.carrier) : Set X.carrier).Nonempty := by
  have hXu : IsPreirreducible (Set.univ : Set X.carrier) :=
    PreirreducibleSpace.isPreirreducible_univ
  obtain ⟨u, hu⟩ := hU
  obtain ⟨v, hv⟩ := hV
  obtain ⟨z, -, hz⟩ := hXu U V U.isOpen V.isOpen ⟨u, Set.mem_univ u, hu⟩ ⟨v, Set.mem_univ v, hv⟩
  exact ⟨z, hz⟩

/-- **A nonempty open subset of a variety is dense.** The set-level form of the
same fact, which is what a dominance hypothesis is usually stated with. -/
theorem dense_of_isOpen_of_nonempty {W : Set X.carrier} (hW : IsOpen W)
    (hne : W.Nonempty) : Dense W := by
  have hXu : IsPreirreducible (Set.univ : Set X.carrier) :=
    PreirreducibleSpace.isPreirreducible_univ
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨w, hw⟩ := hne
  obtain ⟨z, -, hz⟩ := hXu U W hU hW ⟨u, Set.mem_univ u, hu⟩ ⟨w, Set.mem_univ w, hw⟩
  exact ⟨z, hz⟩

/-- A regular function on a nonempty open subset: a representative of a rational
function. -/
structure RationalRep (X : Variety.{u, v} k) where
  /-- The domain. -/
  U : Opens X.carrier
  /-- It is nonempty. -/
  nonempty_U : (U : Set X.carrier).Nonempty
  /-- The function. -/
  toFun : U → k
  /-- Which is regular. -/
  regular : toFun ∈ X.regular U

/-- Hartshorne's identification: two representatives are equivalent when they
agree on the overlap of their domains. -/
def RationalRep.Rel (r s : RationalRep X) : Prop :=
  ∀ (x : X.carrier) (hr : x ∈ r.U) (hs : x ∈ s.U), r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩

theorem RationalRep.rel_refl (r : RationalRep X) : r.Rel r := fun _ _ _ => rfl

theorem RationalRep.rel_symm {r s : RationalRep X} (h : r.Rel s) : s.Rel r :=
  fun x hs hr => (h x hr hs).symm

/-- **Transitivity of the identification on rational functions.**

The germ argument, with irreducibility in place of the shared point. Both
functions are regular on `U ∩ W` and agree on `U ∩ V ∩ W`; the identity
principle closes the gap, provided the triple overlap is nonempty, which is
`opens_inter_nonempty` applied twice. -/
theorem RationalRep.rel_trans {r s t : RationalRep X} (hrs : r.Rel s) (hst : s.Rel t) :
    r.Rel t := by
  intro x hr ht
  set W : Opens X.carrier := r.U ⊓ t.U with hW
  have hWne : (W : Set X.carrier).Nonempty := opens_inter_nonempty r.nonempty_U t.nonempty_U
  have hfr : (fun y : W => r.toFun ⟨y.1, y.2.1⟩) ∈ X.regular W :=
    X.regular_restrict inf_le_left r.regular
  have hft : (fun y : W => t.toFun ⟨y.1, y.2.2⟩) ∈ X.regular W :=
    X.regular_restrict inf_le_right t.regular
  have hsub : IsOpen {y : W | (y : X.carrier) ∈ s.U} :=
    s.U.isOpen.preimage continuous_subtype_val
  have hne : ({y : W | (y : X.carrier) ∈ s.U}).Nonempty := by
    obtain ⟨z, hzW, hzs⟩ := opens_inter_nonempty (U := W) (V := s.U) hWne s.nonempty_U
    exact ⟨⟨z, hzW⟩, hzs⟩
  have heq : Set.EqOn (fun y : W => r.toFun ⟨y.1, y.2.1⟩)
      (fun y : W => t.toFun ⟨y.1, y.2.2⟩) {y : W | (y : X.carrier) ∈ s.U} := by
    intro y hy
    exact (hrs y.1 y.2.1 hy).trans (hst y.1 hy y.2.2)
  have hall := Variety.eq_of_eqOn hfr hft hsub hne heq
  exact congrFun hall ⟨x, ⟨hr, ht⟩⟩

/-- Rational functions, as a setoid. -/
def rationalSetoid (X : Variety.{u, v} k) : Setoid (RationalRep X) where
  r := RationalRep.Rel
  iseqv := ⟨RationalRep.rel_refl, RationalRep.rel_symm, RationalRep.rel_trans⟩

/-- Hartshorne's function field `K(X)`, for an arbitrary variety. -/
def FunctionField (X : Variety.{u, v} k) : Type _ :=
  Quotient (rationalSetoid X)

/-- Every germ is in particular a rational function, since a neighbourhood of a
point is nonempty. This is the map `𝒪_P → K(X)` on representatives. -/
def GermRep.toRationalRep {P : X.carrier} (r : GermRep X P) : RationalRep X where
  U := r.U
  nonempty_U := ⟨P, r.mem_U⟩
  toFun := r.toFun
  regular := r.regular

end Variety

end Hartshorne
