/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.TensorPowerSectionRing
import Hartshorne.Scheme.Differentials.CanonicalSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The canonical section ring

Hartshorne, *Algebraic Geometry*, V.6, definition of the canonical ring (p. 421).

For a scheme `X` over a field `k` with canonical sheaf `ω_X`, the canonical section ring is the
graded ring `R(X, K) = ⨁_{n ≥ 0} H⁰(X, ω_X^{⊗ n})`, with multiplication induced by the tensor
product of sections. It is defined through `ω_X`, without choosing a canonical divisor.
Hartshorne defines `R(X, K) = ⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` for a canonical divisor `K`; here it is
defined through `ω_X`, and `Hartshorne.canonicalSectionRingEquivOfDivisor` compares the two.

When `ω_X` is invertible, for instance when `X` is regular, irreducible and of finite type over
an algebraically closed field, the ring is commutative (`canonicalSectionRingCommRing`). When `X`
is integral and universally closed (for instance proper) over an algebraically closed field, its
degree-zero part is `k` (`canonicalSectionRing_degreeZero_bijective`), because `H⁰(X, 𝒪_X) = k`.
-/

open CategoryTheory Opposite
open scoped DirectSum

namespace Hartshorne

open AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The degree-`n` part `H⁰(X, ω_X^{⊗ n})` of the canonical section ring. -/
abbrev CanonicalSectionRing.Component (n : ℕ) : Type u :=
  TensorPowerSectionRing.Component (R := X.sheaf) (canonicalSheaf f) (op ⊤) n

/-- **The canonical section ring** `R(X, K) = ⨁_{n ≥ 0} H⁰(X, ω_X^{⊗ n})`, a graded ring with
multiplication induced by the tensor product of sections. -/
abbrev CanonicalSectionRing : Type u :=
  ⨁ n, CanonicalSectionRing.Component f n

/-- The graded ring structure on `n ↦ H⁰(X, ω_X^{⊗ n})`. -/
noncomputable instance CanonicalSectionRing.gRing :
    DirectSum.GRing (CanonicalSectionRing.Component f) :=
  TensorPowerSectionRing.gRing (R := X.sheaf) (canonicalSheaf f) (op ⊤)

/-- The ring structure of the canonical section ring. -/
noncomputable example : Ring (CanonicalSectionRing f) := inferInstance

/-- **The canonical section ring is commutative** when `X` is regular, irreducible, of finite
type and of dimension `n` over an algebraically closed field, since then `ω_X` is invertible. -/
@[instance_reducible]
noncomputable def canonicalSectionRingCommRing [IsAlgClosed k] [IrreducibleSpace X]
    (hf : FiniteType f) (hX : X.IsRegular) (n : ℕ) (hn : topologicalKrullDim X = n) :
    CommRing (CanonicalSectionRing f) :=
  TensorPowerSectionRing.commRing (R := X.sheaf) (canonicalSheaf f) (op ⊤)
    ((Scheme.Modules.isInvertible_iff_ringed _).1 (canonicalSheaf_isInvertible f hf hX n hn))

/-- **The degree-zero part of the canonical section ring is `k`.** For `X` integral and
universally closed (for instance proper) over an algebraically closed field `k`, the map
`k → H⁰(X, ω_X^{⊗ 0})`, `c ↦ c · 1`, is bijective, because `H⁰(X, 𝒪_X) = k`: it is integral over
`k`. -/
theorem canonicalSectionRing_degreeZero_bijective [IsAlgClosed k] [IsIntegral X]
    [UniversallyClosed f] :
    Function.Bijective (fun c : k =>
      (show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤) from
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c) •
        TensorPowerSectionRing.oneSec (R := X.sheaf) (canonicalSheaf f) (op ⊤)) := by
  have hint : ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.IsIntegral := by
    rw [CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
      (isIntegral_appTop_of_universallyClosed f)
  have h₁ := IsAlgClosed.ringHom_bijective_of_isIntegral (K := Γ(X, ⊤)) _ hint
  have h₂ := TensorPowerSectionRing.smul_oneSec_bijective (R := X.sheaf) (canonicalSheaf f) ⊤
  exact h₂.comp h₁

end Hartshorne
