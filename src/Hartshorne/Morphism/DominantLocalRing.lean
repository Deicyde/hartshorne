/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.LocalRingFunctionField

/-!
# Dominant morphisms and local rings

Hartshorne, *Algebraic Geometry*, I.3, Exercise 3.3(c) (p. 21).

A dominant morphism of varieties induces an injective map on every local ring.
The proof compares the local-ring map with the induced map of function fields:
both local rings embed in their function fields, and a homomorphism between
fields is injective.
-/

namespace Hartshorne

universe u v

variable {k : Type u} [Field k] {X Y : Variety.{u, v} k}

namespace VarietyHom

/-- **Hartshorne I.3, Exercise 3.3(c).** A morphism with dense range induces an
injective map `𝒪_{φ(P),Y} → 𝒪_{P,X}` on local rings. -/
theorem injective_localRingHom_of_denseRange (f : VarietyHom X Y)
    (hd : DenseRange f.toFun) (P : X.carrier) :
    Function.Injective (f.localRingHom P) := by
  change Dense (Set.range f.toFun) at hd
  intro a b hab
  apply Y.localToFunctionFieldAlgHom_injective (f P)
  apply (f.functionFieldHom hd).injective
  rw [functionFieldHom_localToFunctionFieldAlgHom,
    functionFieldHom_localToFunctionFieldAlgHom, hab]

end VarietyHom

end Hartshorne
