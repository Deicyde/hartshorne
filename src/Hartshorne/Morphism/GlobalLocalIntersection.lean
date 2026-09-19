/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.GlobalRegularFunctionField
import Hartshorne.Morphism.VarietyLocalRing

/-!
# Global regular functions as an intersection of local rings

Hartshorne, *Algebraic Geometry*, I.3, p. 16.

For every point `P` of a variety `X`, restriction and forgetting the base point
give injective `k`-algebra homomorphisms

`𝒪(X) → 𝒪_{P,X} → K(X)`.

Inside `K(X)`, the image of `𝒪(X)` is the intersection of the images of all the
local rings. For the difficult inclusion, choose a germ representing the given
rational function at each point. Their values glue because any two chosen
germs have the same image in the function field, and `regular_of_locally` then
makes the glued function globally regular.

## Main definitions

* `Hartshorne.Variety.globalToLocalAlgHom`
* `Hartshorne.Variety.localToFunctionFieldAlgHom`
* `Hartshorne.Variety.globalToFunctionFieldAlgHom`

## Main result

* `Hartshorne.Variety.globalRegularRange_eq_iInf_localRingRange`
-/

namespace Hartshorne

open TopologicalSpace

universe u v

variable {k : Type u} [Field k]

namespace Variety

/-- A global regular function, regarded as a germ at `P`. -/
def globalGermRep (X : Variety.{u, v} k) (P : X.carrier)
    (f : X.globalRegular) : GermRep X P where
  U := ⊤
  mem_U := trivial
  toFun := f.1
  regular := f.2

/-- Restriction of global regular functions to germs at `P`. -/
noncomputable def globalToLocalAlgHom (X : Variety.{u, v} k) (P : X.carrier) :
    X.globalRegular →ₐ[k] X.LocalRingAt P where
  toFun f := Quotient.mk _ (X.globalGermRep P f)
  map_one' := rfl
  map_mul' _ _ := Quotient.sound fun _ _ _ => rfl
  map_zero' := rfl
  map_add' _ _ := Quotient.sound fun _ _ _ => rfl
  commutes' _ := rfl

/-- Forgetting the base point embeds the local ring at `P` in the function
field. -/
noncomputable def localToFunctionFieldAlgHom (X : Variety.{u, v} k)
    (P : X.carrier) : X.LocalRingAt P →ₐ[k] X.FunctionField where
  toFun := Quotient.map GermRep.toRationalRep fun _ _ h => h
  map_one' := rfl
  map_mul' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl
  map_zero' := rfl
  map_add' := by
    refine Quotient.ind fun a => Quotient.ind fun b => ?_
    exact Quotient.sound fun _ _ _ => rfl
  commutes' _ := Quotient.sound fun _ _ _ => rfl

/-- The existing global-to-function-field ring homomorphism, upgraded to a
`k`-algebra homomorphism. -/
noncomputable def globalToFunctionFieldAlgHom (X : Variety.{u, v} k) :
    X.globalRegular →ₐ[k] X.FunctionField where
  __ := X.globalToFunctionField
  commutes' _ := Quotient.sound fun _ _ _ => rfl

/-- Restriction from global functions to the local ring is injective. -/
theorem globalToLocalAlgHom_injective (X : Variety.{u, v} k) (P : X.carrier) :
    Function.Injective (X.globalToLocalAlgHom P) := by
  intro f g hfg
  have h := Quotient.exact hfg
  exact Subtype.ext (funext fun x => h x.1 trivial trivial)

/-- Forgetting the base point of a germ is injective. -/
theorem localToFunctionFieldAlgHom_injective (X : Variety.{u, v} k)
    (P : X.carrier) : Function.Injective (X.localToFunctionFieldAlgHom P) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro r s h
  change (Quotient.mk (rationalSetoid X) r.toRationalRep : X.FunctionField) =
    Quotient.mk (rationalSetoid X) s.toRationalRep at h
  have hrel : RationalRep.Rel r.toRationalRep s.toRationalRep := Quotient.exact h
  exact Quotient.sound (show GermRep.Rel r s from hrel)

/-- The composite `𝒪(X) → 𝒪_{P,X} → K(X)` is the canonical inclusion of
global regular functions into the function field. -/
@[simp]
theorem localToFunctionFieldAlgHom_globalToLocalAlgHom
    (X : Variety.{u, v} k) (P : X.carrier) (f : X.globalRegular) :
    X.localToFunctionFieldAlgHom P (X.globalToLocalAlgHom P f) =
      X.globalToFunctionFieldAlgHom f :=
  Quotient.sound fun _ _ _ => rfl

/-- The copy of `𝒪(X)` inside `K(X)`. -/
noncomputable def globalRegularRange (X : Variety.{u, v} k) :
    Subalgebra k X.FunctionField :=
  X.globalToFunctionFieldAlgHom.range

/-- The copy of `𝒪_{P,X}` inside `K(X)`. -/
noncomputable def localRingRange (X : Variety.{u, v} k) (P : X.carrier) :
    Subalgebra k X.FunctionField :=
  (X.localToFunctionFieldAlgHom P).range

/-- **Global regular functions are the intersection of the local rings inside
the function field.** -/
theorem globalRegularRange_eq_iInf_localRingRange (X : Variety.{u, v} k) :
    X.globalRegularRange = ⨅ P : X.carrier, X.localRingRange P := by
  apply le_antisymm
  · refine le_iInf fun P => ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨X.globalToLocalAlgHom P f,
      X.localToFunctionFieldAlgHom_globalToLocalAlgHom P f⟩
  · intro q hq
    have hqP (P : X.carrier) : q ∈ X.localRingRange P :=
      (iInf_le (fun P : X.carrier => X.localRingRange P) P) hq
    have hex (P : X.carrier) :
        ∃ a : X.LocalRingAt P, X.localToFunctionFieldAlgHom P a = q := hqP P
    choose a ha using hex
    let s : ∀ P : X.carrier, GermRep X P := fun P => Quotient.out (a P)
    have hs_mk (P : X.carrier) :
        (Quotient.mk (germSetoid X P) (s P) : X.LocalRingAt P) = a P :=
      Quotient.out_eq (a P)
    have hs_image (P : X.carrier) :
        (Quotient.mk (rationalSetoid X) (s P).toRationalRep : X.FunctionField) = q := by
      change X.localToFunctionFieldAlgHom P
        (Quotient.mk (germSetoid X P) (s P) : X.LocalRingAt P) = q
      rw [hs_mk P]
      exact ha P
    let f : (⊤ : Opens X.carrier) → k := fun x => (s x.1).valueAt
    have hvalue (P : X.carrier) (y : (s P).U) :
        f ⟨y.1, trivial⟩ = (s P).toFun y := by
      have heq :
          (Quotient.mk (rationalSetoid X) (s y.1).toRationalRep : X.FunctionField) =
            Quotient.mk (rationalSetoid X) (s P).toRationalRep :=
        (hs_image y.1).trans (hs_image P).symm
      have hrel : RationalRep.Rel (s y.1).toRationalRep (s P).toRationalRep :=
        Quotient.exact heq
      exact hrel y.1 (s y.1).mem_U y.2
    have hf : f ∈ X.regular ⊤ := by
      apply X.regular_of_locally
      intro x
      refine ⟨(s x.1).U, le_top, (s x.1).mem_U, ?_⟩
      convert (s x.1).regular using 1
      funext y
      exact hvalue x.1 y
    let g : X.globalRegular := ⟨f, hf⟩
    obtain ⟨P⟩ := X.nonempty
    have hgerm : X.globalToLocalAlgHom P g = a P := by
      rw [← hs_mk P]
      apply Quotient.sound
      intro x _ hx
      exact hvalue P ⟨x, hx⟩
    refine ⟨g, ?_⟩
    calc
      X.globalToFunctionFieldAlgHom g =
          X.localToFunctionFieldAlgHom P (X.globalToLocalAlgHom P g) :=
        (X.localToFunctionFieldAlgHom_globalToLocalAlgHom P g).symm
      _ = X.localToFunctionFieldAlgHom P (a P) :=
        congrArg (fun z => X.localToFunctionFieldAlgHom P z) hgerm
      _ = q := ha P

end Variety

end Hartshorne
