/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CartierLinearEquivalenceSheaf

/-!
# Cartier classes inject into the Picard group

Hartshorne, *Algebraic Geometry*, II.6, Corollary 6.14 (p. 144).

For every scheme `X`, the assignment `D ↦ O_X(D)` descends to an injective group homomorphism
`CaCl X → Pic X` (`cartierClassToPicard`, `cartierClassToPicard_injective`). Since `CaCl X` is
written additively and `Pic X` multiplicatively, the homomorphism is recorded as an additive
homomorphism into `Additive (Pic X)`.

* `O_X(D) ⊗ O_X(D') ≅ O_X(D + D')` (Proposition 6.13(b)) makes `D ↦ [O_X(D)]` a homomorphism
  `Div X → Pic X`.
* `D₁ ∼ D₂` if and only if `O_X(D₁) ≅ O_X(D₂)` (Proposition 6.13(c)): the forward direction says
  this homomorphism kills the principal divisors, so it descends to `CaCl X`, and the converse
  says the descended map is injective.
-/

open CategoryTheory Hartshorne Hartshorne.Ringed

namespace AlgebraicGeometry

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Scheme

variable (X : Scheme.{u})

/-- The homomorphism `Div X → Pic X`, `D ↦ [O_X(D)]`, written additively. -/
def cartierDivisorToPicard : X.CartierDivisor →+ Additive (Pic X.sheaf) :=
  AddMonoidHom.mk'
    (fun D ↦ Additive.ofMul (Pic.mk (R := X.sheaf) D.sheaf
      ((Modules.isInvertible_iff_ringed _).1 D.isInvertible_sheaf)))
    (fun D D' ↦ congrArg Additive.ofMul ((Pic.mk_eq_mk_iff _ _).2
      ⟨(CartierDivisor.tensorIso D D').symm⟩))

/-- **Hartshorne II.6, Corollary 6.14.** For every scheme `X`, the assignment `D ↦ O_X(D)`
descends to a group homomorphism `CaCl X → Pic X` (written additively). -/
def cartierClassToPicard : X.CartierClassGroup →+ Additive (Pic X.sheaf) :=
  QuotientAddGroup.lift X.principalCartierDivisorSubgroup X.cartierDivisorToPicard
    (fun D hD ↦ by
      have h : D.LinearEquivalent 0 := by
        change D - 0 ∈ X.principalCartierDivisorSubgroup
        rwa [sub_zero]
      obtain ⟨e⟩ := (CartierDivisor.linearEquivalent_iff_nonempty_iso D 0).1 h
      have he : X.cartierDivisorToPicard D = X.cartierDivisorToPicard 0 :=
        congrArg Additive.ofMul ((Pic.mk_eq_mk_iff _ _).2 ⟨e⟩)
      exact AddMonoidHom.mem_ker.2 (he.trans (map_zero _)))

variable {X}

/-- The homomorphism `CaCl X → Pic X` sends the class of `D` to the class of `O_X(D)`. -/
theorem cartierClassToPicard_apply (D : X.CartierDivisor) :
    X.cartierClassToPicard (X.cartierDivisorClassHom D) =
      Additive.ofMul (Pic.mk (R := X.sheaf) D.sheaf
        ((Modules.isInvertible_iff_ringed _).1 D.isInvertible_sheaf)) :=
  rfl

variable (X)

/-- **Hartshorne II.6, Corollary 6.14.** The homomorphism `CaCl X → Pic X`, `[D] ↦ [O_X(D)]`, is
injective. -/
theorem cartierClassToPicard_injective : Function.Injective X.cartierClassToPicard := by
  intro c c' h
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk'_surjective X.principalCartierDivisorSubgroup c
  obtain ⟨D', rfl⟩ := QuotientAddGroup.mk'_surjective X.principalCartierDivisorSubgroup c'
  refine (cartierDivisorClass_eq_iff D D').2
    ((CartierDivisor.linearEquivalent_iff_nonempty_iso D D').2 ?_)
  exact (Pic.mk_eq_mk_iff _ _).1 (Additive.ofMul.injective h)

end Scheme

end

end AlgebraicGeometry
