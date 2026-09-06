/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Dimension.FgDomain
import Hartshorne.Dimension.HeightCoheight

/-!
# The dimension formula, reduced to transcendence degrees

Hartshorne, *Algebraic Geometry*, I.1, Theorem 1.8A(b) (p. 6).

Theorem 1.8A(b) says `height 𝔭 + dim B/𝔭 = dim B` for a prime of a finitely
generated domain over a field. Part (a) computes both dimensions as
transcendence degrees, so the formula is equivalent to

`trdeg_k K(B) = trdeg_k K(B/𝔭) + height 𝔭`,

and this file records that reduction. It does not prove the formula; it isolates
what is left of it.

The reduction is worth having because the two sides are not the same kind of
statement. `height 𝔭 + dim B/𝔭 = dim B` is about the poset of primes and is what
makes a ring catenary; `trdeg K(B) = trdeg K(B/𝔭) + height 𝔭` is a statement
about field extensions, and it is the form in which the standard proofs — by
Noether normalisation adapted to `𝔭` — actually establish it.

The quotient side needs no new work: `B/𝔭` is again a finitely generated domain
over `k`, so part (a) applies to it verbatim.

## Main results

* `Hartshorne.exists_ringKrullDim_quotient_eq_trdeg`
* `Hartshorne.height_add_ringKrullDim_quotient_eq_of_trdeg`
-/

namespace Hartshorne

open Ideal

universe u

variable (k R K : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [Algebra.FiniteType k R] [Field K] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
  [IsFractionRing R K]

omit [IsDomain R] in
/-- **Part (a), applied to a quotient.** A quotient of a finitely generated
domain by a prime is again one, so its dimension is the transcendence degree of
its fraction field. -/
theorem exists_ringKrullDim_quotient_eq_trdeg (𝔭 : Ideal R) [𝔭.IsPrime] :
    ∃ s : ℕ, ringKrullDim (R ⧸ 𝔭) = s ∧
      Algebra.trdeg k (FractionRing (R ⧸ 𝔭)) = s :=
  exists_ringKrullDim_eq_trdeg k (R ⧸ 𝔭) (FractionRing (R ⧸ 𝔭))

/-- **The dimension formula follows from the transcendence-degree drop.**

This is all that is left of Theorem 1.8A(b): the hypothesis is the statement
that passing to `B/𝔭` costs exactly `height 𝔭` in transcendence degree. -/
theorem height_add_ringKrullDim_quotient_eq_of_trdeg (𝔭 : Ideal R) [𝔭.IsPrime]
    (h : ℕ)
    (hkey : ∀ d e : ℕ, Algebra.trdeg k K = d →
      Algebra.trdeg k (FractionRing (R ⧸ 𝔭)) = e → d = e + h) :
    (h : WithBot ℕ∞) + ringKrullDim (R ⧸ 𝔭) = ringKrullDim R := by
  obtain ⟨d, hd, htd⟩ := exists_ringKrullDim_eq_trdeg k R K
  obtain ⟨e, he, hte⟩ := exists_ringKrullDim_quotient_eq_trdeg k R 𝔭
  rw [hd, he, ← Nat.cast_add, hkey d e htd hte, Nat.add_comm]

end Hartshorne
