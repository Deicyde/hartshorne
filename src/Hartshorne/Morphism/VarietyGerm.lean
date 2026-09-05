/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyIdentity

/-!
# Germs on an arbitrary variety

Hartshorne, *Algebraic Geometry*, I.3, the definition of `𝒪_{P,Y}` on p. 16, for
a bundled `Variety`.

The affine case was built from `IsRegularVia`, in coordinates. Theorem 3.4 is
about `𝒪_P` for a *projective* variety, so the construction has to be redone
over the abstract structure — where it is in fact shorter, because everything it
needs is a field of `Variety`.

Hartshorne's parenthetical, "use (3.1.1) to verify that this is an equivalence
relation!", is again the whole content. Transitivity does not hold pointwise: a
point of `U ∩ W` need not lie in `V`, so there is nothing to chain. What is
available is agreement on `U ∩ V ∩ W`, a nonempty open subset of the irreducible
`U ∩ W`, and the identity principle upgrades that to agreement throughout.

## Main definitions

* `Hartshorne.Variety.GermRep`, `Hartshorne.Variety.GermRep.Rel`
* `Hartshorne.Variety.LocalRingAt`

## Main results

* `Hartshorne.Variety.GermRep.rel_trans`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X : Variety.{u, v} k}

namespace Variety

/-- A regular function on an open neighbourhood of `P`: a representative of a
germ. -/
structure GermRep (X : Variety.{u, v} k) (P : X.carrier) where
  /-- The neighbourhood. -/
  U : Opens X.carrier
  /-- It contains `P`. -/
  mem_U : P ∈ U
  /-- The function. -/
  toFun : U → k
  /-- Which is regular. -/
  regular : toFun ∈ X.regular U

variable {P : X.carrier}

/-- Hartshorne's identification: two representatives are equivalent when they
agree on the whole overlap of their domains. -/
def GermRep.Rel (r s : GermRep X P) : Prop :=
  ∀ (x : X.carrier) (hr : x ∈ r.U) (hs : x ∈ s.U), r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩

theorem GermRep.rel_refl (r : GermRep X P) : r.Rel r := fun _ _ _ => rfl

theorem GermRep.rel_symm {r s : GermRep X P} (h : r.Rel s) : s.Rel r :=
  fun x hs hr => (h x hr hs).symm

/-- **Transitivity of the germ relation**, Hartshorne's parenthetical on p. 16.

The hypotheses give agreement on `U ∩ V` and on `V ∩ W`; a point of `U ∩ W` need
not lie in `V`, so there is nothing to chain pointwise. Instead both functions
are regular on `U ∩ W` and agree on the nonempty open `U ∩ V ∩ W`, and the
identity principle closes the gap. -/
theorem GermRep.rel_trans {r s t : GermRep X P} (hrs : r.Rel s) (hst : s.Rel t) :
    r.Rel t := by
  intro x hr ht
  set W : Opens X.carrier := r.U ⊓ t.U with hW
  have hPW : P ∈ W := ⟨r.mem_U, t.mem_U⟩
  have hfr : (fun y : W => r.toFun ⟨y.1, y.2.1⟩) ∈ X.regular W :=
    X.regular_restrict inf_le_left r.regular
  have hft : (fun y : W => t.toFun ⟨y.1, y.2.2⟩) ∈ X.regular W :=
    X.regular_restrict inf_le_right t.regular
  have hsub : IsOpen {y : W | (y : X.carrier) ∈ s.U} :=
    s.U.isOpen.preimage continuous_subtype_val
  have hne : ({y : W | (y : X.carrier) ∈ s.U}).Nonempty := ⟨⟨P, hPW⟩, s.mem_U⟩
  have heq : Set.EqOn (fun y : W => r.toFun ⟨y.1, y.2.1⟩)
      (fun y : W => t.toFun ⟨y.1, y.2.2⟩) {y : W | (y : X.carrier) ∈ s.U} := by
    intro y hy
    exact (hrs y.1 y.2.1 hy).trans (hst y.1 hy y.2.2)
  have hall := Variety.eq_of_eqOn hfr hft hsub hne heq
  exact congrFun hall ⟨x, ⟨hr, ht⟩⟩

/-- Germs at `P`, as a setoid. Transitivity is the identity principle. -/
def germSetoid (X : Variety.{u, v} k) (P : X.carrier) : Setoid (GermRep X P) where
  r := GermRep.Rel
  iseqv := ⟨GermRep.rel_refl, GermRep.rel_symm, GermRep.rel_trans⟩

/-- Hartshorne's local ring `𝒪_{P,X}`, for an arbitrary variety. -/
def LocalRingAt (X : Variety.{u, v} k) (P : X.carrier) : Type _ :=
  Quotient (germSetoid X P)

end Variety

end Hartshorne
