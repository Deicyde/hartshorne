/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Graded localization

Hartshorne, *Algebraic Geometry*, I.3, the definition of `S_(𝔭)` and `S_(f)` on
p. 18.

For a graded ring `S` and a homogeneous prime `𝔭`, invert the homogeneous
elements outside `𝔭`. The result is graded by `deg(f/g) = deg f - deg g`, and
`S_(𝔭)` is its degree-zero part. It is a local ring, and when `S` is a domain
and `𝔭 = (0)` it is a field. Likewise `S_(f)` is the degree-zero part of `S_f`.

Mathlib has this construction, developed for `Proj`: `HomogeneousLocalization`
is the degree-zero part directly rather than a graded ring cut down afterwards,
which is the same object and avoids the negative degrees Hartshorne's phrasing
needs. This file fixes Mathlib's names as the project's `S_(𝔭)` and `S_(f)`, in
the same way the dimension node fixes `ringKrullDim`.

The one claim Hartshorne makes that Mathlib does not have is that `S_((0))` is a
field for a domain. Theorem 3.4(c) is about exactly that ring, so it is supplied
here.

## Main definitions

* `Hartshorne.gradedLocalization`, `Hartshorne.gradedLocalizationAway`

## Main results

* `Hartshorne.isField_gradedLocalization_bot`
-/

namespace Hartshorne

open HomogeneousLocalization

variable {ι σ A : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- Hartshorne's `S_(𝔭)`: the degree-zero part of the localization of `S` at the
homogeneous elements outside `𝔭`. -/
abbrev gradedLocalization (𝔭 : Ideal A) [𝔭.IsPrime] := HomogeneousLocalization.AtPrime 𝒜 𝔭

/-- Hartshorne's `S_(f)`: the degree-zero part of `S_f`. -/
abbrev gradedLocalizationAway (f : A) := HomogeneousLocalization.Away 𝒜 f

/-- **`S_((0))` is a field** when `S` is a domain.

An element is `a/b` with `a` and `b` homogeneous of the same degree and `b ≠ 0`;
it is nonzero exactly when `a ≠ 0`, and then `b/a` is its inverse. The proof
below runs that argument through `val`: for `𝔭 = (0)` in a domain the ambient
localization is the fraction field, where nonzero already means invertible, and
`HomogeneousLocalization.isUnit_iff_isUnit_val` transports invertibility back to
the degree-zero part. -/
theorem isField_gradedLocalization_bot [IsDomain A] :
    IsField (gradedLocalization 𝒜 (⊥ : Ideal A)) := by
  refine ⟨exists_pair_ne _, mul_comm, fun {a} ha => ?_⟩
  have hfr : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  let _ : Field (Localization.AtPrime (⊥ : Ideal A)) := IsFractionRing.toField A
  have hval : a.val ≠ 0 := fun h => ha (val_injective _ (by simpa using h))
  obtain ⟨u, hu⟩ := (isUnit_iff_isUnit_val 𝒜 ⊥ a).1 (isUnit_iff_ne_zero.2 hval)
  exact ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv⟩

end Hartshorne
