/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LocallyFactorialClassPicard
import Hartshorne.Scheme.VarietyBasicInstances
import Hartshorne.Scheme.ProjectiveSpaceProper

/-!
# Surfaces and effective curves

Hartshorne, *Algebraic Geometry*, V.1, conventions (p. 357).

Over an algebraically closed field `k`, a *surface* (in Chapter V) is an integral regular scheme
of dimension two, projective over `k`. A *curve on the surface* is an effective (Weil) divisor; it
may be singular, reducible, nonreduced, or have repeated components. An unqualified *point* of
the surface is a closed point.

A surface is regular, hence locally factorial, so Weil and Cartier divisors are identified
(Proposition II.6.11) and divisor classes are identified with `Pic X` (Corollary II.6.16).

## Main definitions and results

* `Hartshorne.Surface`: a Chapter V surface over `k`.
* `Hartshorne.Surface.Curve`, `Hartshorne.Surface.Point`: curves and points on a surface.
* `Hartshorne.Surface.weilCartierEquiv`: Weil divisors are Cartier divisors.
* `Hartshorne.Surface.classGroupEquivPicard`: `Cl X ≅ Pic X`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits Hartshorne.Ringed

namespace Hartshorne

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- **A surface** in Hartshorne's Chapter V: over an algebraically closed field `k`, an integral
regular scheme `X` of dimension two together with a projective structure morphism
`X ⟶ Spec k`. -/
structure Surface (k : Type u) [Field k] [IsAlgClosed k] where
  /-- The underlying scheme. -/
  X : Scheme.{u}
  /-- The structure morphism to `Spec k`. -/
  hom : X ⟶ Spec (.of k)
  [isIntegral : IsIntegral X]
  /-- The surface is nonsingular: every local ring is a regular local ring. -/
  isRegular : X.IsRegular
  /-- The surface is projective over `k`. -/
  projective : Projective hom
  /-- The surface has dimension two. -/
  dim_eq : topologicalKrullDim X = 2

namespace Surface

attribute [instance] Surface.isIntegral

variable {k : Type u} [Field k] [IsAlgClosed k] (S : Surface k)

instance isProper : IsProper S.hom := S.projective.isProper

/-- A surface is of finite type over `k`. -/
theorem finiteType : FiniteType S.hom := ⟨inferInstance, inferInstance⟩

instance isNoetherian : IsNoetherian S.X := isNoetherian_of_finiteType S.hom S.finiteType

instance isSeparated : S.X.IsSeparated := isSeparated_of_isSeparated_spec S.hom

/-- A surface is locally factorial. -/
theorem isLocallyFactorial : S.X.IsLocallyFactorial := isLocallyFactorial_of_isRegular S.isRegular

/-- **A curve on a surface** is an effective (Weil) divisor; it may be singular, reducible,
nonreduced, or have repeated components. -/
abbrev Curve : Type u := {D : S.X.WeilDivisor // Scheme.WeilDivisor.IsEffective D}

/-- An unqualified **point** of a surface is a closed point. -/
abbrev Point : Type u := {x : S.X // IsClosed ({x} : Set S.X)}

/-- On a surface, Weil divisors and Cartier divisors are identified (Proposition II.6.11, using
that the surface is regular, hence locally factorial). -/
def weilCartierEquiv : S.X.WeilDivisor ≃+ S.X.CartierDivisor :=
  Scheme.weilCartierEquiv S.isLocallyFactorial

/-- On a surface, the divisor class group is identified with `Pic X` (Corollary II.6.16), the
class of a divisor `D` going to the class of `O_X(D)`. -/
def classGroupEquivPicard :
    S.X.WeilClassGroup (Scheme.satisfiesConditionStar_of_isLocallyFactorial S.isLocallyFactorial) ≃+
      Additive (Pic S.X.sheaf) :=
  Scheme.weilClassEquivPicard S.isLocallyFactorial

/-- The identification `Cl X ≅ Pic X` sends the class of a divisor `D` to the class of `O_X(D)`.
-/
theorem classGroupEquivPicard_weilDivisorClassHom (D : S.X.WeilDivisor) :
    S.classGroupEquivPicard
        (S.X.weilDivisorClassHom
          (Scheme.satisfiesConditionStar_of_isLocallyFactorial S.isLocallyFactorial) D) =
      S.X.cartierDivisorToPicard (S.weilCartierEquiv D) :=
  Scheme.weilClassEquivPicard_weilDivisorClassHom _ D

end Surface

end

end Hartshorne
