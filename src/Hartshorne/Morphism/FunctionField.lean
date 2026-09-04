/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.LocalRing

/-!
# Rational functions

Hartshorne, *Algebraic Geometry*, I.3, the definition of `K(Y)` on p. 16.

An element of the function field is a pair `(U, f)` with `U` a *nonempty* open
subset and `f` regular on `U`, two pairs identified when they agree on the
overlap.

Irreducibility of `Y` is doing real work throughout, and Hartshorne says so:
"Since `Y` is irreducible, any two nonempty open sets have a nonempty
intersection." That is what makes addition and multiplication definable at all,
and it is also what replaces the shared point `P` that made the germ relation
transitive. Here there is no distinguished point, so the nonempty overlap has to
come from irreducibility instead.

## Main definitions

* `Hartshorne.RationalRep`, `Hartshorne.RationalRep.Rel`

## Main results

* `Hartshorne.inter_nonempty` : nonempty opens in an irreducible space meet.
* `Hartshorne.RationalRep.rel_trans` : transitivity of the identification.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}

/-- In an irreducible space any two nonempty open sets meet. This is what makes
the operations on rational functions definable, since two representatives can
always be compared on a nonempty common domain. -/
theorem inter_nonempty (hY : IsIrreducible Y) {U V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hUne : U.Nonempty) (hVne : V.Nonempty) :
    (U ∩ V).Nonempty := by
  have : PreirreducibleSpace Y := isPreirreducible_iff_preirreducibleSpace.1 hY.2
  have hYu : IsPreirreducible (Set.univ : Set Y) :=
    PreirreducibleSpace.isPreirreducible_univ
  obtain ⟨u, hu⟩ := hUne
  obtain ⟨v, hv⟩ := hVne
  obtain ⟨z, -, hz⟩ := hYu U V hU hV ⟨u, Set.mem_univ u, hu⟩ ⟨v, Set.mem_univ v, hv⟩
  exact ⟨z, hz⟩

/-- A regular function on a nonempty open subset: a representative of a rational
function. -/
structure RationalRep (Y : Set (σ → k)) where
  /-- The domain. -/
  U : Set Y
  /-- It is open. -/
  isOpen_U : IsOpen U
  /-- And nonempty. -/
  nonempty_U : U.Nonempty
  /-- The function. -/
  toFun : U → k
  /-- Which is regular. -/
  isRegular : IsRegularVia (fun x : U => (x.1 : σ → k)) toFun

/-- Hartshorne's identification: two representatives are equivalent when they
agree on the overlap of their domains. -/
def RationalRep.Rel (r s : RationalRep Y) : Prop :=
  ∀ (x : Y) (hr : x ∈ r.U) (hs : x ∈ s.U), r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩

theorem RationalRep.rel_refl (r : RationalRep Y) : r.Rel r := fun _ _ _ => rfl

theorem RationalRep.rel_symm {r s : RationalRep Y} (h : r.Rel s) : s.Rel r :=
  fun x hs hr => (h x hr hs).symm

/-- **Transitivity of the identification on rational functions.**

The argument is the germ one, except that the germ case got a nonempty overlap
free from the shared point `P`. Here there is no distinguished point, so
irreducibility supplies it: `r.U ∩ t.U` is a nonempty open subset of an
irreducible space, hence irreducible, and `r.U ∩ s.U ∩ t.U` is a nonempty open
subset of *that* on which the two functions agree. The identity principle does
the rest. -/
theorem RationalRep.rel_trans (hY : IsIrreducible Y) {r s t : RationalRep Y}
    (hrs : r.Rel s) (hst : s.Rel t) : r.Rel t := by
  intro x hr ht
  set W : Set Y := r.U ∩ t.U with hWdef
  have hWopen : IsOpen W := r.isOpen_U.inter t.isOpen_U
  have hWne : W.Nonempty :=
    inter_nonempty hY r.isOpen_U t.isOpen_U r.nonempty_U t.nonempty_U
  have hfr : IsRegularVia (fun y : W => (y.1 : σ → k))
      (fun y : W => r.toFun ⟨y.1, y.2.1⟩) :=
    isRegularVia_restrict (fun _ hy => hy.1) r.isRegular
  have hft : IsRegularVia (fun y : W => (y.1 : σ → k))
      (fun y : W => t.toFun ⟨y.1, y.2.2⟩) :=
    isRegularVia_restrict (fun _ hy => hy.2) t.isRegular
  have hWirr : IsPreirreducible (Set.univ : Set W) :=
    preirreducible_univ_of_isOpen hY hWopen hWne
  have hsub : IsOpen {y : W | (y : Y) ∈ s.U} :=
    s.isOpen_U.preimage continuous_subtype_val
  -- Nonemptiness of the triple overlap is again irreducibility, applied twice.
  have hne : ({y : W | (y : Y) ∈ s.U}).Nonempty := by
    obtain ⟨z, hzW, hzs⟩ := inter_nonempty hY hWopen s.isOpen_U hWne s.nonempty_U
    exact ⟨⟨z, hzW⟩, hzs⟩
  have heq : Set.EqOn (fun y : W => r.toFun ⟨y.1, y.2.1⟩)
      (fun y : W => t.toFun ⟨y.1, y.2.2⟩) {y : W | (y : Y) ∈ s.U} := by
    intro y hy
    exact (hrs y.1 y.2.1 hy).trans (hst y.1 hy y.2.2)
  have hall := eq_of_eqOn_isOpen hWirr (by fun_prop) hfr hft hsub hne heq
  exact congrFun hall ⟨x, ⟨hr, ht⟩⟩

/-- Every germ at a point is in particular a rational function, since a
neighbourhood of a point is nonempty. This is the map `𝒪_P → K(Y)`. -/
def GermRep.toRationalRep {P : Y} (r : GermRep Y P) : RationalRep Y where
  U := r.U
  isOpen_U := r.isOpen_U
  nonempty_U := ⟨P, r.mem_U⟩
  toFun := r.toFun
  isRegular := r.isRegular

end Hartshorne
