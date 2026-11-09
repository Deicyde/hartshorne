/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CartierClassPicardIntegral
import Hartshorne.Scheme.Differentials.CanonicalSheaf

/-!
# The canonical divisor class

Project bridge from Hartshorne, *Algebraic Geometry*, II.8 (the canonical sheaf) and II.6,
Proposition 6.15 (`CaCl X ≃ Pic X` on an integral scheme).

On an integral scheme `X` over a field `k` whose canonical sheaf `ω_X` is invertible (for instance
a nonsingular variety, `Hartshorne.canonicalSheaf_isInvertible`), the canonical divisor class
`Hartshorne.canonicalDivisorClass` is the Cartier divisor class corresponding to `[ω_X] ∈ Pic X`.
It is characterized by: the class of a Cartier divisor `D` is the canonical class if and only if
`𝒪_X(D) ≅ ω_X` (`Hartshorne.cartierDivisorClassHom_eq_canonicalDivisorClass_iff`). It is a class
modulo linear equivalence; no preferred divisor representative is chosen.
-/

universe u

open CategoryTheory AlgebraicGeometry
open Hartshorne.Ringed

namespace Hartshorne

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
  (hω : (canonicalSheaf f).IsInvertible)

/-- **The canonical divisor class.** On an integral scheme `X` over `k` with invertible canonical
sheaf `ω_X` (for instance a nonsingular variety), the Cartier divisor class whose associated
invertible sheaf is isomorphic to `ω_X`: the preimage of `[ω_X]` under `CaCl X ≃ Pic X`. -/
noncomputable def canonicalDivisorClass : X.CartierClassGroup :=
  X.cartierClassEquivPicard.symm
    (Additive.ofMul (Ringed.Pic.mk (R := X.sheaf) (canonicalSheaf f)
      ((Scheme.Modules.isInvertible_iff_ringed _).1 hω)))

/-- The class of a Cartier divisor `D` is the canonical divisor class if and only if
`𝒪_X(D) ≅ ω_X`. -/
theorem cartierDivisorClassHom_eq_canonicalDivisorClass_iff (D : X.CartierDivisor) :
    X.cartierDivisorClassHom D = canonicalDivisorClass f hω ↔
      Nonempty (D.sheaf ≅ canonicalSheaf f) := by
  rw [canonicalDivisorClass, AddEquiv.eq_symm_apply, Scheme.cartierClassEquivPicard_apply,
    Scheme.cartierClassToPicard_apply]
  exact Additive.ofMul.injective.eq_iff.trans (Ringed.Pic.mk_eq_mk_iff _ _)

/-- The canonical divisor class is the class of some Cartier divisor `K` with `𝒪_X(K) ≅ ω_X`. -/
theorem exists_cartierDivisor_canonicalDivisorClass :
    ∃ K : X.CartierDivisor, X.cartierDivisorClassHom K = canonicalDivisorClass f hω ∧
      Nonempty (K.sheaf ≅ canonicalSheaf f) := by
  obtain ⟨K, hK⟩ := QuotientAddGroup.mk'_surjective X.principalCartierDivisorSubgroup
    (canonicalDivisorClass f hω)
  exact ⟨K, hK, (cartierDivisorClassHom_eq_canonicalDivisorClass_iff f hω K).1 hK⟩

end Hartshorne
