/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.FunctionField

/-!
# The three rings embed in the function field

Hartshorne, *Algebraic Geometry*, I.3, the injections on p. 16.

Restriction gives maps `𝒪(Y) → 𝒪_{P,Y} → K(Y)`, and all of them are injective,
so the three rings may be treated as subrings of `K(Y)`. Hartshorne does this in
a sentence and then relies on it silently: Theorem 3.2(a) is stated as an
intersection of localisations *inside* `K(Y)`, and the whole of Theorem 3.4
compares subrings of the fraction field of `S(Y)`.

In Lean the identification cannot stay silent. It has to be a named map with a
proved injectivity lemma, or every later statement grows explicit coercions.

## Where the identity principle enters

Injectivity is immediate for Hartshorne's identification, because his relation
is "agree on the whole overlap" rather than "agree near `P`". What the identity
principle buys is that the two relations *coincide*
(`GermRep.rel_iff_eventually`): germs agreeing on some neighbourhood of `P`
already agree on the whole overlap. Without that, the definition would depend on
which relation was chosen.

## Main definitions

* `Hartshorne.germSetoid`, `Hartshorne.LocalRingAt`
* `Hartshorne.rationalSetoid`, `Hartshorne.FunctionField`

## Main results

* `Hartshorne.globalToLocal_injective`, `Hartshorne.localToFunctionField_injective`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*} {Y : Set (σ → k)}

/-- Germs at `P`, as a setoid. Transitivity is the identity principle. -/
def germSetoid (hY : IsIrreducible Y) (P : Y) : Setoid (GermRep Y P) where
  r := GermRep.Rel
  iseqv := ⟨GermRep.rel_refl, GermRep.rel_symm, GermRep.rel_trans hY⟩

/-- Hartshorne's local ring `𝒪_{P,Y}`, as a set. -/
def LocalRingAt (hY : IsIrreducible Y) (P : Y) : Type _ :=
  Quotient (germSetoid hY P)

/-- Rational functions, as a setoid. -/
def rationalSetoid (hY : IsIrreducible Y) : Setoid (RationalRep Y) where
  r := RationalRep.Rel
  iseqv := ⟨RationalRep.rel_refl, RationalRep.rel_symm, RationalRep.rel_trans hY⟩

/-- Hartshorne's function field `K(Y)`, as a set. -/
def FunctionField (hY : IsIrreducible Y) : Type _ :=
  Quotient (rationalSetoid hY)

/-- A global regular function, viewed as a germ at `P`. -/
def globalToGermRep (P : Y) (f : Y → k) (hf : IsRegular f) : GermRep Y P where
  U := Set.univ
  isOpen_U := isOpen_univ
  mem_U := Set.mem_univ _
  toFun := fun x => f x.1
  isRegular := by
    intro Q
    obtain ⟨W, hW, hQW, g, h, hne, he⟩ := hf Q.1
    exact ⟨(fun x : (Set.univ : Set Y) => x.1) ⁻¹' W,
      hW.preimage continuous_subtype_val, hQW, g, h,
      fun x hx => hne x.1 hx, fun x hx => he x.1 hx⟩

/-- The map `𝒪(Y) → 𝒪_{P,Y}`. -/
def globalToLocal (hY : IsIrreducible Y) (P : Y) (f : globalRegular Y) :
    LocalRingAt hY P :=
  Quotient.mk _ (globalToGermRep P f.1 f.2)

/-- The map `𝒪_{P,Y} → K(Y)`. -/
def localToFunctionField (hY : IsIrreducible Y) (P : Y) :
    LocalRingAt hY P → FunctionField hY :=
  Quotient.lift (fun r => Quotient.mk _ r.toRationalRep)
    (fun _ _ h => Quotient.sound h)

/-- `𝒪(Y) → 𝒪_{P,Y}` is injective.

With Hartshorne's identification this is immediate: two global functions have
the same germ exactly when they agree on the overlap of their domains, which is
all of `Y`. -/
theorem globalToLocal_injective (hY : IsIrreducible Y) (P : Y) :
    Function.Injective (globalToLocal hY P) := by
  intro f g h
  have hrel : (globalToGermRep P f.1 f.2).Rel (globalToGermRep P g.1 g.2) :=
    Quotient.exact h
  apply Subtype.ext
  funext x
  exact hrel x (Set.mem_univ x) (Set.mem_univ x)

/-- `𝒪_{P,Y} → K(Y)` is injective: the two identifications are the same
condition, agreement on the overlap. -/
theorem localToFunctionField_injective (hY : IsIrreducible Y) (P : Y) :
    Function.Injective (localToFunctionField hY P) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro r s h
  have hrel : RationalRep.Rel r.toRationalRep s.toRationalRep := Quotient.exact h
  exact Quotient.sound (fun x hr hs => hrel x hr hs)

/-- The two candidate germ relations coincide: agreeing on some neighbourhood of
`P` is the same as agreeing on the whole overlap.

This is what the identity principle buys. Without it Hartshorne's definition and
the usual "agree near `P`" definition of a germ would be different notions. -/
theorem GermRep.rel_iff_eventually (hY : IsIrreducible Y) {P : Y} (r s : GermRep Y P) :
    r.Rel s ↔ ∃ W : Set Y, IsOpen W ∧ P ∈ W ∧ ∀ (x : Y) (hx : x ∈ W)
      (hr : x ∈ r.U) (hs : x ∈ s.U), r.toFun ⟨x, hr⟩ = s.toFun ⟨x, hs⟩ := by
  refine ⟨fun h => ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun x _ hr hs => h x hr hs⟩, ?_⟩
  rintro ⟨W, hW, hPW, hagree⟩
  -- Both are regular on `r.U ∩ s.U`, and agree on the nonempty open piece
  -- inside `W`, so the identity principle gives agreement throughout.
  intro x hr hs
  set V : Set Y := r.U ∩ s.U with hVdef
  have hVopen : IsOpen V := r.isOpen_U.inter s.isOpen_U
  have hPV : P ∈ V := ⟨r.mem_U, s.mem_U⟩
  have hfr : IsRegularVia (fun y : V => (y.1 : σ → k))
      (fun y : V => r.toFun ⟨y.1, y.2.1⟩) :=
    isRegularVia_restrict (fun _ hy => hy.1) r.isRegular
  have hfs : IsRegularVia (fun y : V => (y.1 : σ → k))
      (fun y : V => s.toFun ⟨y.1, y.2.2⟩) :=
    isRegularVia_restrict (fun _ hy => hy.2) s.isRegular
  have hVirr : IsPreirreducible (Set.univ : Set V) :=
    preirreducible_univ_of_isOpen hY hVopen ⟨P, hPV⟩
  have hsub : IsOpen {y : V | (y : Y) ∈ W} := hW.preimage continuous_subtype_val
  have hne : ({y : V | (y : Y) ∈ W}).Nonempty := ⟨⟨P, hPV⟩, hPW⟩
  have heq : Set.EqOn (fun y : V => r.toFun ⟨y.1, y.2.1⟩)
      (fun y : V => s.toFun ⟨y.1, y.2.2⟩) {y : V | (y : Y) ∈ W} :=
    fun y hy => hagree y.1 hy y.2.1 y.2.2
  have hall := eq_of_eqOn_isOpen hVirr (by fun_prop) hfr hfs hsub hne heq
  exact congrFun hall ⟨x, ⟨hr, hs⟩⟩

end Hartshorne
