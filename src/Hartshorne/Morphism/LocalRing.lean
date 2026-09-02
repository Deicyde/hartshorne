/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.GlobalRegular

/-!
# Germs of regular functions

Hartshorne, *Algebraic Geometry*, I.3, the definition of `𝒪_{P,Y}` on p. 16.

An element of the local ring at `P` is a pair `(U, f)` with `U` an open
neighbourhood of `P` and `f` regular on `U`, two pairs identified when they
agree on the overlap.

Hartshorne adds a parenthetical: "Use (3.1.1) to verify that this is an
equivalence relation!" That is not decoration. Transitivity genuinely needs the
identity principle: from `f = g` on `U ∩ V` and `g = h` on `V ∩ W` one cannot
conclude `f = h` on `U ∩ W` pointwise, because a point of `U ∩ W` need not lie
in `V` at all. What is available is that `f` and `h` agree on `U ∩ V ∩ W`, a
nonempty open subset of the irreducible `U ∩ W`, and the identity principle
upgrades that to agreement on all of `U ∩ W`.

## A note on elaboration

Restriction lemmas here supply the restricted point **explicitly**, as
`hne ⟨x.1, hUV x.2⟩ hx` rather than `hne _ hx`. With a metavariable Lean cannot
match the two coercions syntactically, falls back on unfolding `eval` over
`MvPolynomial`, and diverges. Naming the point makes the conclusion match by
cheap definitional equality. The two forms are interchangeable mathematically
and differ only in whether the elaborator terminates.

## Main definitions

* `Hartshorne.GermRep`, `Hartshorne.GermRep.Rel`

## Main results

* `Hartshorne.GermRep.rel_trans` : transitivity, via the identity principle.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*}

/-- A regular function on some open neighbourhood of `P`: a representative of a
germ. -/
structure GermRep (Y : Set (σ → k)) (P : Y) where
  /-- The neighbourhood. -/
  U : Set Y
  /-- It is open. -/
  isOpen_U : IsOpen U
  /-- It contains `P`. -/
  mem_U : P ∈ U
  /-- The function. -/
  toFun : U → k
  /-- Which is regular. -/
  isRegular : IsRegularVia (fun x : U => (x.1 : σ → k)) toFun

variable {Y : Set (σ → k)} {P : Y}

/-- Hartshorne's identification: two representatives are equivalent when they
agree on the whole overlap of their domains. -/
def GermRep.Rel (r s : GermRep Y P) : Prop :=
  ∀ (x : Y) (hr : x ∈ r.U) (hs : x ∈ s.U), r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩

theorem GermRep.rel_refl (r : GermRep Y P) : r.Rel r := fun _ _ _ => rfl

theorem GermRep.rel_symm {r s : GermRep Y P} (h : r.Rel s) : s.Rel r :=
  fun x hs hr => (h x hr hs).symm

/-- Restriction of a regular function to a smaller subset stays regular.

The restricted point is supplied explicitly rather than as `_`; see the note
above on why that matters. -/
theorem isRegularVia_restrict {U V : Set Y} (hUV : V ⊆ U) {f : U → k}
    (hf : IsRegularVia (fun x : U => (x.1 : σ → k)) f) :
    IsRegularVia (fun x : V => (x.1 : σ → k)) (fun x : V => f ⟨x.1, hUV x.2⟩) := by
  intro Q
  obtain ⟨W, hW, hQW, g, h, hne, he⟩ := hf ⟨Q.1, hUV Q.2⟩
  exact ⟨(fun x : V => (⟨x.1, hUV x.2⟩ : U)) ⁻¹' W,
    hW.preimage (Continuous.subtype_mk continuous_subtype_val _), hQW, g, h,
    fun x hx => hne ⟨x.1, hUV x.2⟩ hx, fun x hx => he ⟨x.1, hUV x.2⟩ hx⟩

/-- A nonempty open subset of an irreducible space is irreducible as a space.
This is what lets the identity principle be applied on an overlap. -/
theorem preirreducible_univ_of_isOpen (hY : IsIrreducible Y) {W : Set Y}
    (hW : IsOpen W) (hne : W.Nonempty) :
    IsPreirreducible (Set.univ : Set W) := by
  haveI : PreirreducibleSpace Y := isPreirreducible_iff_preirreducibleSpace.1 hY.2
  have hYu : IsPreirreducible (Set.univ : Set Y) :=
    PreirreducibleSpace.isPreirreducible_univ
  have hWpre : IsPreirreducible W := by
    simpa using IsPreirreducible.inter_isOpen hYu hW
  haveI : PreirreducibleSpace W := isPreirreducible_iff_preirreducibleSpace.1 hWpre
  exact PreirreducibleSpace.isPreirreducible_univ

/-- **Transitivity of the germ relation**, Hartshorne's parenthetical on p. 16.

The hypotheses give agreement on `U ∩ V` and on `V ∩ W`; a point of `U ∩ W` need
not lie in `V`, so there is nothing to chain pointwise. Instead both functions
are regular on `U ∩ W`, a nonempty open subset of an irreducible space, and they
agree on the nonempty open `U ∩ V ∩ W`. The identity principle closes the gap. -/
theorem GermRep.rel_trans (hY : IsIrreducible Y) {r s t : GermRep Y P}
    (hrs : r.Rel s) (hst : s.Rel t) : r.Rel t := by
  intro x hr ht
  set W : Set Y := r.U ∩ t.U with hWdef
  have hPW : P ∈ W := ⟨r.mem_U, t.mem_U⟩
  have hWopen : IsOpen W := r.isOpen_U.inter t.isOpen_U
  -- Restrict both functions to the overlap. Done inline: with `r` and `t`
  -- concrete this elaborates, whereas the quantified form does not.
  have hfr : IsRegularVia (fun y : W => (y.1 : σ → k))
      (fun y : W => r.toFun ⟨y.1, y.2.1⟩) :=
    isRegularVia_restrict (fun _ hy => hy.1) r.isRegular
  have hft : IsRegularVia (fun y : W => (y.1 : σ → k))
      (fun y : W => t.toFun ⟨y.1, y.2.2⟩) :=
    isRegularVia_restrict (fun _ hy => hy.2) t.isRegular
  have hWirr : IsPreirreducible (Set.univ : Set W) :=
    preirreducible_univ_of_isOpen hY hWopen ⟨P, hPW⟩
  have hsub : IsOpen {y : W | (y : Y) ∈ s.U} :=
    s.isOpen_U.preimage continuous_subtype_val
  have hne : ({y : W | (y : Y) ∈ s.U}).Nonempty := ⟨⟨P, hPW⟩, s.mem_U⟩
  have heq : Set.EqOn (fun y : W => r.toFun ⟨y.1, y.2.1⟩)
      (fun y : W => t.toFun ⟨y.1, y.2.2⟩) {y : W | (y : Y) ∈ s.U} := by
    intro y hy
    exact (hrs y.1 y.2.1 hy).trans (hst y.1 hy y.2.2)
  have hall := eq_of_eqOn_isOpen hWirr (by fun_prop) hfr hft hsub hne heq
  exact congrFun hall ⟨x, ⟨hr, ht⟩⟩

end Hartshorne
