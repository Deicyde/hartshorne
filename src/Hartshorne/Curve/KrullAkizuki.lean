/-
Copyright (c) 2026 Hartshorne formalization contributors and Dokying Yang.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.KrullAkizukiQuotient

/-!
# The Krull--Akizuki theorem

This file proves the final Noetherian and dimension conclusions of the
Krull--Akizuki theorem.  If `A` is a one-dimensional Noetherian domain with
fraction field `K`, `L/K` is finite, and `B` is an arbitrary intermediate ring
`A ⊆ B ⊆ L`, then `B` is Noetherian and has Krull dimension at most one.

Both dimension interfaces used by the pinned Mathlib checkout are exposed:
`Ring.KrullDimLE 1 B` and the legacy `Ring.DimensionLEOne B`.  The proof uses
finite length of nonzero ideal quotients from
`Hartshorne.Curve.KrullAkizukiQuotient`; it assumes neither that `B` is finite
over `A` nor that `B` is integral over `A`.

The argument follows Stacks Project, Tag 00PG, and the implementation strategy
of Mathlib PR #41755.
-/

namespace Hartshorne

universe u v w x

variable
  (A : Type u) [CommRing A] [IsDomain A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L]
  (B : Type x) [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra B L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [NoZeroSMulDivisors B L]
  [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

include A K L

/-- **Krull--Akizuki theorem (Noetherian part).**  An arbitrary intermediate
ring `A ⊆ B ⊆ L` is Noetherian. -/
theorem krullAkizuki_isNoetherianRing :
    IsNoetherianRing B := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro J
  obtain rfl | hJ := eq_or_ne J ⊥
  · exact Submodule.fg_bot
  obtain ⟨b, hbJ, hb_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  let I : Ideal B := Ideal.span {b}
  have h_quotient_noetherian : IsNoetherian B (B ⧸ I) :=
    isNoetherian_of_tower A
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (krullAkizuki_quotientIdeal_isFiniteLength A K L B I
          (mt Ideal.span_singleton_eq_bot.mp hb_ne))).1
  exact Submodule.fg_of_fg_map_of_fg_inf_ker I.mkQ
    (IsNoetherian.noetherian _)
    ⟨{b}, by
      rw [Finset.coe_singleton, Submodule.ker_mkQ,
        inf_of_le_right (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbJ))]⟩

/-- Every nonzero prime ideal of an arbitrary intermediate ring `A ⊆ B ⊆ L`
is maximal. -/
private theorem krullAkizuki_isMaximal_of_isPrime
    {p : Ideal B} (hp_ne : p ≠ ⊥) (hp_prime : p.IsPrime) :
    p.IsMaximal := by
  let quotient_domain : IsDomain (B ⧸ p) := Ideal.Quotient.isDomain p
  have quotient_artinian : IsArtinianRing (B ⧸ p) :=
    isArtinian_of_tower B <| isArtinian_of_tower A <|
      (isFiniteLength_iff_isNoetherian_isArtinian.mp
        (krullAkizuki_quotientIdeal_isFiniteLength A K L B p hp_ne)).2
  exact Ideal.Quotient.maximal_of_isField p
    (IsArtinianRing.isField_of_isDomain (B ⧸ p))

/-- **Krull--Akizuki theorem (Krull-dimension part).**  An arbitrary
intermediate ring `A ⊆ B ⊆ L` has Krull dimension at most one. -/
theorem krullAkizuki_krullDimLE_one :
    Ring.KrullDimLE 1 B :=
  Ring.KrullDimLE.mk₁' fun {p} hp_ne hp_prime =>
    krullAkizuki_isMaximal_of_isPrime A K L B (p := p) hp_ne hp_prime

/-- **Krull--Akizuki theorem (legacy dimension interface).**  The same
dimension bound expressed using the interface required by the pinned
`IsDedekindDomain` API. -/
theorem krullAkizuki_dimensionLEOne :
    Ring.DimensionLEOne B where
  maximalOfPrime := fun {p} hp_ne hp_prime =>
    krullAkizuki_isMaximal_of_isPrime A K L B (p := p) hp_ne hp_prime

/-- **Krull--Akizuki theorem.**  An arbitrary intermediate ring in a finite
extension of the fraction field of a one-dimensional Noetherian domain is
Noetherian and has dimension at most one, in both pinned dimension interfaces. -/
theorem krull_akizuki :
    IsNoetherianRing B ∧ Ring.KrullDimLE 1 B ∧ Ring.DimensionLEOne B :=
  ⟨krullAkizuki_isNoetherianRing A K L B,
    krullAkizuki_krullDimLE_one A K L B,
    krullAkizuki_dimensionLEOne A K L B⟩

end Hartshorne
