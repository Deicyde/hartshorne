/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.VarietyFunctionFieldHom
import Hartshorne.Morphism.AffineRationalCompare
import Hartshorne.Morphism.GlobalRegularTop
import Hartshorne.Morphism.FunctionFieldFractions

/-!
# Global regular functions inside the function field

Toward Hartshorne, *Algebraic Geometry*, I.3, Theorem 3.4(a).

`𝒪(X) → K(X)` for an arbitrary variety, injectively, together with the fact that
it commutes with pullback along a dominant morphism.

A global regular function is a rational function whose domain happens to be
everything, so the map is nothing but forgetting that. Injectivity is likewise
free: two global functions with the same class agree on the overlap of their
domains, and that overlap is the whole variety. The affine version of this is
part of [the injections node](../../blueprint/roadmap/morphisms/function-field-injections.md);
what is new here is only that it holds over the abstract structure.

The reason Theorem 3.4(a) needs it is that its argument compares a global
regular function with the graded pieces of `S(Y)`, and those two things have no
common home until both are inside `K(Y)`. Parts (b) and (c) never needed this:
they worked one chart at a time, and a single chart supplies its own ambient
ring.

## Main definitions

* `Hartshorne.Variety.globalToFunctionField`
* `Hartshorne.VarietyHom.globalPullback`

## Main results

* `Hartshorne.Variety.globalToFunctionField_injective`
* `Hartshorne.VarietyHom.functionFieldHom_globalToFunctionField`
* `Hartshorne.coordToRational_eq_globalToFunctionField`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k] {X Y : Variety.{u, v} k}

namespace Variety

/-- A global regular function, as a representative of a rational function. -/
def globalRationalRep (X : Variety.{u, v} k) (f : X.globalRegular) : RationalRep X where
  U := ⊤
  nonempty_U := X.nonempty.elim fun x => ⟨x, trivial⟩
  toFun := f.1
  regular := f.2

/-- **`𝒪(X) → K(X)`.** A global regular function is a rational function defined
everywhere. -/
def globalToFunctionField (X : Variety.{u, v} k) : X.globalRegular →+* X.FunctionField where
  toFun f := Quotient.mk _ (X.globalRationalRep f)
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := Quotient.sound fun _ _ _ => rfl
  map_add' _ _ := Quotient.sound fun _ _ _ => rfl

@[simp]
theorem globalToFunctionField_apply (X : Variety.{u, v} k) (f : X.globalRegular) :
    X.globalToFunctionField f = Quotient.mk (rationalSetoid X) (X.globalRationalRep f) :=
  rfl

/-- The map is injective: the overlap of two everywhere-defined domains is
everything, so agreeing there is agreeing. -/
theorem globalToFunctionField_injective (X : Variety.{u, v} k) :
    Function.Injective X.globalToFunctionField := by
  intro f g hfg
  have h := Quotient.exact hfg
  exact Subtype.ext (funext fun x => h x.1 trivial trivial)

end Variety

namespace VarietyHom

/-- Pullback of global regular functions along a morphism. -/
def globalPullback (f : VarietyHom X Y) (g : Y.globalRegular) : X.globalRegular :=
  ⟨fun x => g.1 ⟨f x.1, trivial⟩, f.regular_comp ⊤ g.1 g.2⟩

@[simp]
theorem globalPullback_id (X : Variety.{u, v} k) (g : X.globalRegular) :
    (VarietyHom.id X).globalPullback g = g := rfl

/-- Pullback of global functions is contravariantly functorial. -/
theorem globalPullback_comp {Z : Variety.{u, v} k} (g : VarietyHom Y Z)
    (f : VarietyHom X Y) (h : Z.globalRegular) :
    (g.comp f).globalPullback h = f.globalPullback (g.globalPullback h) := rfl

/-- **Pullback commutes with the inclusion into the function field.**

Both sides are the class of the same function, since a global function has the
same values however it is regarded; the domains differ only in how `⊤` is
written. -/
theorem functionFieldHom_globalToFunctionField (f : VarietyHom X Y)
    (hd : Dense (Set.range f.toFun)) (g : Y.globalRegular) :
    f.functionFieldHom hd (Y.globalToFunctionField g)
      = X.globalToFunctionField (f.globalPullback g) :=
  Quotient.sound fun _ _ _ => rfl

end VarietyHom

section Affine

open MvPolynomial

variable {σ : Type*} [IsAlgClosed k] [Finite σ] {Z : Set (σ → k)}

/-- **The two routes from `A(Y)` into `K(Y)` agree.**

One goes through Theorem 3.2(a), reading a polynomial class as a global regular
function and then as a rational function; the other reads it as a rational
function directly. Both are the class of the same representative, since both
evaluate the polynomial at the point.

Theorem 3.4(a) needs this because it starts with a global regular function and
has to land in `S(Y)`, and `A(Yᵢ)` is the only bridge between the two. -/
theorem coordToRational_eq_globalToFunctionField (hZ : IsAffineVariety Z)
    (a : coordinateRing Z) :
    coordToRational hZ.isIrreducible a
      = functionFieldEquivAffine hZ.isQuasiAffineVariety
        (Variety.globalToFunctionField _ (coordinateRingEquivRegularTop hZ a)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact Quotient.sound fun _ _ _ => rfl

end Affine

end Hartshorne
