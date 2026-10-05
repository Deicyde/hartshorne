/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Associated points of a scheme

Hartshorne, *Algebraic Geometry*, III.9 (p. 257).

A point of a scheme is associated when the maximal ideal of its local ring is
an associated prime.  For a locally Noetherian scheme, this is equivalent to
every element of that maximal ideal being a zero-divisor.
-/

open AlgebraicGeometry

namespace Hartshorne

universe u

/-- **Hartshorne III.9, p. 257.** The associated points of a scheme are the points whose local
ring has its maximal ideal as an associated prime. -/
def associatedPoints (X : Scheme.{u}) : Set X :=
  {x | IsAssociatedPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)}

/-- On a locally Noetherian scheme, a point is associated if and only if every element of the
maximal ideal of its local ring is a zero-divisor. -/
theorem mem_associatedPoints_iff_maximalIdeal_subset_zeroDivisors
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    x ∈ associatedPoints X ↔
      ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        r ∉ nonZeroDivisors (X.presheaf.stalk x) := by
  let R := X.presheaf.stalk x
  let m : Ideal R := IsLocalRing.maximalIdeal R
  change IsAssociatedPrime m R ↔ ∀ r ∈ m, r ∉ nonZeroDivisors R
  have havoid :
      ((m : Set R) ⊆ ⋃ I ∈ associatedPrimes R R, (I : Set R)) ↔
        m ∈ associatedPrimes R R :=
    Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (associatedPrimes.finite R R) m m
      (fun I hI _ _ ↦ (AssociatedPrimes.mem_iff.mp hI).isPrime)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  rw [← AssociatedPrimes.mem_iff]
  refine havoid.symm.trans ?_
  rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors R]
  rfl

end Hartshorne
