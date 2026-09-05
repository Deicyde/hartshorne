/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Correspondence
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Projective space is irreducible

Hartshorne, *Algebraic Geometry*, I.2, the projective form of Example 1.4.1.

`ℙⁿ` is an irreducible topological space, hence a projective variety. The affine
statement is proved by computing `I(𝔸ⁿ) = 0`; this is the same computation with
one extra step, since a polynomial is not a function on `ℙⁿ` and the vanishing
condition is stated at chosen representatives.

The extra step is small. A homogeneous `f` vanishing at every point vanishes at
every *nonzero* vector, because the criterion for vanishing at a point may be
tested at any representative. It then vanishes at `0` as well, since
`0 = 0 • w` for a nonzero `w` and homogeneity turns that into `0ⁿ · f(w)`,
uniformly in `n`, including `n = 0`. So `f` vanishes identically and, over an
infinite field, is zero.

This is needed to view `ℙⁿ` itself as a variety, which Proposition 3.3 does when
it calls the standard charts isomorphisms of varieties.

## Main results

* `Hartshorne.homogeneousVanishingIdeal_univ`
* `Hartshorne.isProjVariety_univ`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- Only the zero polynomial is homogeneous and vanishes on all of `ℙⁿ`, so
`J(ℙⁿ) = 0`. -/
theorem homogeneousVanishingIdeal_univ [Nonempty σ] [Infinite k] :
    homogeneousVanishingIdeal (Set.univ : Set (ProjectiveSpace k σ)) = ⊥ := by
  rw [homogeneousVanishingIdeal, Ideal.span_eq_bot]
  rintro f ⟨⟨n, hf⟩, hvan⟩
  -- A nonzero vector to test against.
  obtain ⟨i⟩ := ‹Nonempty σ›
  have hw : (fun _ => (1 : k)) ≠ (0 : σ → k) := fun hc => one_ne_zero (congrFun hc i)
  refine MvPolynomial.funext fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · -- At the origin: `0 = 0 • w`, and homogeneity gives `0ⁿ · f(w)`.
    have hw0 := hvan (Projectivization.mk k _ hw) (Set.mem_univ _)
    rw [homogeneousVanish_iff_of_isHomogeneous hf hw] at hw0
    have hz : (0 : σ → k) = (0 : k) • fun _ => (1 : k) := by simp
    rw [hz, hf.eval_smul, hw0, mul_zero, map_zero]
  · have hv0 := hvan (Projectivization.mk k v hv) (Set.mem_univ _)
    rw [homogeneousVanish_iff_of_isHomogeneous hf hv] at hv0
    simpa using hv0

/-- **Projective space is irreducible.**

`J(ℙⁿ) = 0` is prime because the polynomial ring is a domain, and Exercise 2.4
turns that into irreducibility. -/
theorem isIrreducible_univ_projectiveSpace [Nonempty σ] [IsAlgClosed k] [Finite σ] :
    IsIrreducible (Set.univ : Set (ProjectiveSpace k σ)) := by
  rw [isIrreducible_iff_isPrime_homogeneousVanishingIdeal isProjAlgebraicSet_univ,
    homogeneousVanishingIdeal_univ]
  exact Ideal.isPrime_bot

/-- `ℙⁿ` is a projective variety. -/
theorem isProjVariety_univ [Nonempty σ] [IsAlgClosed k] [Finite σ] :
    IsProjVariety (Set.univ : Set (ProjectiveSpace k σ)) :=
  ⟨isIrreducible_univ_projectiveSpace, isClosed_univ⟩

end Hartshorne
