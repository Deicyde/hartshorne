/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.AffineConeIdeal

/-!
# Irreducibility of the affine cone

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.10(b) (p. 12).

For a nonempty projective algebraic set `Y`, its affine cone is irreducible if
and only if `Y` is irreducible. Consequently, the cone over a projective
variety is an affine variety.

## Main results

* `Hartshorne.isIrreducible_affineCone_iff`
* `Hartshorne.IsProjVariety.isAffineVariety_affineCone`
-/

namespace Hartshorne

variable {k : Type*} [Field k] {σ : Type*}

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- **Exercise 2.10(b)**: the affine cone over a nonempty projective algebraic
set is irreducible if and only if the projective algebraic set is irreducible. -/
theorem isIrreducible_affineCone_iff {Y : Set (ProjectiveSpace k σ)}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) :
    IsIrreducible (affineCone Y) ↔ IsIrreducible Y := by
  rw [isIrreducible_iff_isPrime (isAlgebraicSet_affineCone hY hne),
    vanishingIdeal_affineCone hY hne,
    isIrreducible_iff_isPrime_homogeneousVanishingIdeal hY]

/-- The affine cone over a projective variety is an affine variety. -/
theorem IsProjVariety.isAffineVariety_affineCone {Y : Set (ProjectiveSpace k σ)}
    (hY : IsProjVariety Y) : IsAffineVariety (affineCone Y) := by
  refine ⟨(isIrreducible_affineCone_iff hY.isProjAlgebraicSet hY.1.nonempty).2 hY.1, ?_⟩
  exact isClosed_iff_isAlgebraicSet.2
    (isAlgebraicSet_affineCone hY.isProjAlgebraicSet hY.1.nonempty)

end AlgClosed

end Hartshorne
