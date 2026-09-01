/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.Variety
import Mathlib.RingTheory.FiniteType

/-!
# The affine coordinate ring

Hartshorne, *Algebraic Geometry*, I.1, the definition on p. 4 and Remark 1.4.6.

For an affine algebraic set `Y`, the *affine coordinate ring* is
`A(Y) = k[x₁,…,xₙ]/I(Y)`. When `Y` is a variety, `I(Y)` is prime, so `A(Y)` is a
finitely generated `k`-algebra that is an integral domain.

The converse — that every finitely generated `k`-algebra domain arises this way
— is `Hartshorne.exists_isAffineVariety_coordinateRing_equiv` and is what
supplies essential surjectivity in Corollary 3.8.

## Main definitions

* `Hartshorne.coordinateRing`

## Main results

* `Hartshorne.isDomain_coordinateRing` : `A(Y)` is a domain for `Y` a variety.
* `Hartshorne.exists_isAffineVariety_coordinateRing_equiv` : Remark 1.4.6.
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- The *affine coordinate ring* `A(Y) = k[x₁,…,xₙ]/I(Y)` of an algebraic set.

This is an `abbrev` so that the `CommRing` and `Algebra k` structures on the
quotient are found by instance search rather than restated. -/
abbrev coordinateRing (Y : Set (σ → k)) : Type _ :=
  MvPolynomial σ k ⧸ vanishingIdeal k Y

/-- `A(Y)` is a finitely generated `k`-algebra: it is a quotient of a polynomial
ring in finitely many variables. -/
instance finiteType_coordinateRing [Finite σ] (Y : Set (σ → k)) :
    Algebra.FiniteType k (coordinateRing Y) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ k (vanishingIdeal k Y)) Ideal.Quotient.mk_surjective

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- Remark 1.4.6, first half: the coordinate ring of an affine variety is an
integral domain, because the vanishing ideal of an irreducible set is prime. -/
theorem isDomain_coordinateRing {Y : Set (σ → k)} (hY : IsAffineVariety Y) :
    IsDomain (coordinateRing Y) := by
  have : (vanishingIdeal k Y).IsPrime :=
    (isIrreducible_iff_isPrime hY.isAlgebraicSet).1 hY.1
  exact Ideal.Quotient.isDomain _

/-- The coordinate ring of the zero locus of a prime ideal is the quotient by
that ideal: the Nullstellensatz recovers `𝔭` exactly, not merely its radical. -/
theorem vanishingIdeal_zeroLocus_of_isPrime {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsPrime) : vanishingIdeal k (zeroLocus k I) = I :=
  vanishingIdeal_zeroLocus_of_isRadical hI.isRadical

/-- The zero locus of a prime ideal is an affine variety. -/
theorem isAffineVariety_zeroLocus_of_isPrime {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsPrime) : IsAffineVariety (zeroLocus k I) := by
  refine ⟨?_, isClosed_zeroLocus I⟩
  have halg : IsAlgebraicSet (zeroLocus k I) := isAlgebraicSet_iff_exists_ideal.2 ⟨I, rfl⟩
  refine (isIrreducible_iff_isPrime halg).2 ?_
  rwa [vanishingIdeal_zeroLocus_of_isPrime hI]

end AlgClosed

/-- **Hartshorne, Remark 1.4.6**, second half: every finitely generated
`k`-algebra that is an integral domain is the coordinate ring of an affine
variety.

Present `B` as `k[x₁,…,xₙ]/𝔞`. Because `B` is a domain, `𝔞 = ker f` is prime,
so `Z(𝔞)` is a variety; and because `𝔞` is prime it is radical, so the
Nullstellensatz gives `I(Z(𝔞)) = 𝔞` on the nose rather than `√𝔞`. Both steps
fail without the domain hypothesis, which is why it appears in Corollary 3.8.

This supplies essential surjectivity for the equivalence of categories. -/
theorem exists_isAffineVariety_coordinateRing_equiv [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] :
    ∃ (n : ℕ) (Y : Set (Fin n → k)), IsAffineVariety Y ∧
      Nonempty (coordinateRing Y ≃ₐ[k] B) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹_›
  have hker : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  refine ⟨n, zeroLocus k (RingHom.ker f), isAffineVariety_zeroLocus_of_isPrime hker, ⟨?_⟩⟩
  -- The two ideals are equal, but the ring structure on the quotient depends on
  -- the ideal, so transport along an equivalence rather than rewriting.
  exact (Ideal.quotientEquivAlgOfEq k (vanishingIdeal_zeroLocus_of_isPrime hker)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hf)

end Hartshorne
