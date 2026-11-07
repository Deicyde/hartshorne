/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LocallyFactorialWeilCartier
import Hartshorne.Scheme.CartierClassPicardIntegral

/-!
# Weil classes and the Picard group on a locally factorial scheme

Hartshorne, *Algebraic Geometry*, II.6, Corollary 6.16 (p. 145).

Let `X` be an integral separated Noetherian locally factorial scheme. The identification of Weil
and Cartier divisors (Proposition 6.11, `weilCartierEquiv`) matches the principal subgroups, so it
descends to an isomorphism `Cl X ≃ CaCl X` (`weilClassCartierClassEquiv`). Composing with the
isomorphism `CaCl X ≃ Pic X` of Proposition 6.15 (`cartierClassEquivPicard`) gives the isomorphism
`Cl X ≃ Pic X` (`weilClassEquivPicard`), written additively. It is natural in the sense that the
class of a Weil divisor `D` goes to the class of `O_X(D)`, where `D` is viewed as a Cartier divisor
(`weilClassEquivPicard_weilDivisorClassHom`).
-/

open CategoryTheory Hartshorne Hartshorne.Ringed

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [X.IsSeparated]

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- On an integral separated Noetherian locally factorial scheme, the identification of Weil and
Cartier divisors descends to an isomorphism of class groups `Cl X ≃ CaCl X`. -/
def weilClassCartierClassEquiv (hlf : X.IsLocallyFactorial) :
    X.WeilClassGroup (satisfiesConditionStar_of_isLocallyFactorial hlf) ≃+ X.CartierClassGroup :=
  QuotientAddGroup.congr _ _ (weilCartierEquiv hlf) (map_principalDivisorSubgroup_weilCartierEquiv hlf)

/-- The isomorphism `Cl X ≃ CaCl X` sends the class of a Weil divisor to the class of the
corresponding Cartier divisor. -/
theorem weilClassCartierClassEquiv_weilDivisorClassHom (hlf : X.IsLocallyFactorial)
    (D : X.WeilDivisor) :
    weilClassCartierClassEquiv hlf
        (X.weilDivisorClassHom (satisfiesConditionStar_of_isLocallyFactorial hlf) D) =
      X.cartierDivisorClassHom (weilCartierEquiv hlf D) :=
  rfl

/-- **Hartshorne II.6, Corollary 6.16.** On an integral separated Noetherian locally factorial
scheme, the identification of Weil and Cartier divisors followed by `D ↦ O_X(D)` induces an
isomorphism `Cl X ≃ Pic X` (written additively). -/
def weilClassEquivPicard (hlf : X.IsLocallyFactorial) :
    X.WeilClassGroup (satisfiesConditionStar_of_isLocallyFactorial hlf) ≃+
      Additive (Pic X.sheaf) :=
  (weilClassCartierClassEquiv hlf).trans X.cartierClassEquivPicard

/-- **Hartshorne II.6, Corollary 6.16 (naturality).** The isomorphism `Cl X ≃ Pic X` sends the
class of a Weil divisor `D` to the class of `O_X(D)`, where `D` is viewed as a Cartier divisor. -/
theorem weilClassEquivPicard_weilDivisorClassHom (hlf : X.IsLocallyFactorial)
    (D : X.WeilDivisor) :
    weilClassEquivPicard hlf
        (X.weilDivisorClassHom (satisfiesConditionStar_of_isLocallyFactorial hlf) D) =
      Additive.ofMul (Pic.mk (R := X.sheaf) (weilCartierEquiv hlf D).sheaf
        ((Modules.isInvertible_iff_ringed _).1 (weilCartierEquiv hlf D).isInvertible_sheaf)) :=
  rfl

/-- The isomorphism `Cl X ≃ Pic X` is the composite of `Cl X ≃ CaCl X` and `CaCl X ≃ Pic X`. -/
theorem weilClassEquivPicard_apply (hlf : X.IsLocallyFactorial)
    (c : X.WeilClassGroup (satisfiesConditionStar_of_isLocallyFactorial hlf)) :
    weilClassEquivPicard hlf c = X.cartierClassEquivPicard (weilClassCartierClassEquiv hlf c) :=
  rfl

end

end AlgebraicGeometry.Scheme
