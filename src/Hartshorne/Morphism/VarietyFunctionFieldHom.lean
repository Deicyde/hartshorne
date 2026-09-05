/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyFunctionFieldStructure
import Hartshorne.Morphism.Hom

/-!
# The function field is functorial for dominant morphisms

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(c).

A rational function cannot be pulled back along an arbitrary morphism: the
preimage of a nonempty open set can be empty, and then there is no
representative. It can be pulled back along a *dominant* one, and dominance is
exactly what makes the preimage nonempty.

That covers the two cases Theorem 3.4(c) needs at once. An isomorphism is
surjective, so its range is dense; and the inclusion of a nonempty open subset
of an irreducible space is dense for the same reason the identity principle
works. So `K(Y) ≅ K(X)` along an isomorphism, and `K(Y) ≅ K(Z)` for `Z` open in
`Y`, come from one construction.

Compared with the germ version this is easier, not harder. There is no base
point, so nothing is indexed by a point, and the transport along `ψ(φ(P)) = P`
that forced the germ statement to be phrased as bijectivity never arises.

## Main definitions

* `Hartshorne.VarietyHom.ratPullback`, `Hartshorne.VarietyHom.functionFieldHom`

## Main results

* `Hartshorne.VarietyHom.bijective_functionFieldHom_of_isIso`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X Y Z : Variety.{u, v} k}

namespace VarietyHom

/-- A morphism with dense range pulls a rational function back to one. -/
noncomputable def ratPullback (f : VarietyHom X Y) (hd : Dense (Set.range f.toFun))
    (r : Variety.RationalRep Y) : Variety.RationalRep X where
  U := Opens.comap ⟨f.toFun, f.continuous_toFun⟩ r.U
  nonempty_U := by
    obtain ⟨y, hy, x, hx⟩ := hd.inter_open_nonempty _ r.U.isOpen r.nonempty_U
    exact ⟨x, show f x ∈ r.U by rw [hx]; exact hy⟩
  toFun := fun x => r.toFun ⟨f x.1, x.2⟩
  regular := f.regular_comp r.U r.toFun r.regular

theorem ratPullback_congr (f : VarietyHom X Y) (hd : Dense (Set.range f.toFun))
    {r s : Variety.RationalRep Y} (h : r.Rel s) :
    (f.ratPullback hd r).Rel (f.ratPullback hd s) :=
  fun x hr hs => h (f x) hr hs

/-- The induced map `K(Y) → K(X)`. -/
noncomputable def functionFieldHom (f : VarietyHom X Y) (hd : Dense (Set.range f.toFun)) :
    Variety.FunctionField Y →+* Variety.FunctionField X where
  toFun := Quotient.map (f.ratPullback hd) fun _ _ h => f.ratPullback_congr hd h
  map_one' := Quotient.sound fun _ _ _ => rfl
  map_zero' := Quotient.sound fun _ _ _ => rfl
  map_mul' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl
  map_add' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl

@[simp]
theorem functionFieldHom_mk (f : VarietyHom X Y) (hd : Dense (Set.range f.toFun))
    (r : Variety.RationalRep Y) :
    f.functionFieldHom hd (Quotient.mk (Variety.rationalSetoid Y) r)
      = Quotient.mk (Variety.rationalSetoid X) (f.ratPullback hd r) :=
  rfl

/-- A surjective morphism has dense range. -/
theorem dense_range_of_surjective {f : VarietyHom X Y} (hf : Function.Surjective f.toFun) :
    Dense (Set.range f.toFun) := by
  rw [hf.range_eq]
  exact dense_univ

/-- **An isomorphism of varieties induces an isomorphism of function fields.**

Both halves are the germ argument with the base point deleted. Injectivity uses
that `f` is surjective on points; surjectivity pulls back along the inverse
morphism, which is legitimate because it too has dense range. -/
theorem bijective_functionFieldHom_of_isIso {f : VarietyHom X Y} (hf : f.IsIso)
    (hd : Dense (Set.range f.toFun)) : Function.Bijective (f.functionFieldHom hd) := by
  obtain ⟨g, hgf, hfg⟩ := hf
  have hgfx : ∀ x : X.carrier, g (f x) = x := congrFun (congrArg VarietyHom.toFun hgf)
  have hfgy : ∀ y : Y.carrier, f (g y) = y := congrFun (congrArg VarietyHom.toFun hfg)
  have hgd : Dense (Set.range g.toFun) :=
    dense_range_of_surjective fun x => ⟨f x, hgfx x⟩
  constructor
  · refine Quotient.ind fun r => Quotient.ind fun s => fun hrs => ?_
    have hrel := Quotient.exact hrs
    refine Quotient.sound fun y hr hs => ?_
    have hy : f (g y) = y := hfgy y
    have h := hrel (g y) (show f (g y) ∈ r.U by rw [hy]; exact hr)
      (show f (g y) ∈ s.U by rw [hy]; exact hs)
    simpa [ratPullback, hy] using h
  · refine Quotient.ind fun t => ?_
    refine ⟨Quotient.mk _ (g.ratPullback hgd t), Quotient.sound fun x hr hs => ?_⟩
    have hx : g (f x) = x := hgfx x
    show t.toFun ⟨g (f x), _⟩ = t.toFun ⟨x, hs⟩
    simp [hx]

end VarietyHom

end Hartshorne
