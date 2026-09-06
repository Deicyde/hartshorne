/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.QuasiAffineChain
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Morphism.PointsMaximal
import Hartshorne.Dimension.QuotientHeight
import Hartshorne.Dimension.DimFormula
import Hartshorne.Morphism.LocalRingDimension

/-!
# From primes of `A(Ȳ)` to irreducible closed subsets through a point

Toward Hartshorne, *Algebraic Geometry*, I.1, Proposition 1.10 (p. 6).

A prime of `A(Ȳ)` becomes an irreducible closed subset of the ambient space by
taking the zero set of its preimage. This file records the three things a chain
of such primes needs in order to be carried into `Ȳ`, and then into `Y`:

* the zero set lies inside `Ȳ`, because the preimage contains `I(Ȳ)`;
* it contains `P` whenever the prime lies below `𝔪_P`;
* and the assignment reverses strict inclusions.

Those three, together with the restriction map of
[the previous file](QuasiAffineChain.lean), close the reverse inequality of
Proposition 1.10 and hence the proposition itself: a maximal chain of primes
below `𝔪_P` has length `dim Ȳ` because every maximal ideal of a finitely
generated domain has full height, and restricting to `Y` keeps the length.

## Main results

* `Hartshorne.zeroLocusOfPrime`
* `Hartshorne.zeroLocusOfPrime_subset_closure`
* `Hartshorne.mem_zeroLocusOfPrime`
* `Hartshorne.zeroLocusOfPrime_lt`
* `Hartshorne.dim_closure_le_dim`
* `Hartshorne.dim_eq_dim_closure`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {σ : Type} [Finite σ]
  {W : Set (σ → k)} (hW : IsAlgebraicSet W)

/-- The irreducible closed subset attached to a prime of `A(W)`. -/
def zeroLocusOfPrime (p : PrimeSpectrum (coordinateRing W)) :
    IrreducibleCloseds (σ → k) where
  carrier := zeroLocus k (Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k W)) p.asIdeal)
  isIrreducible' :=
    (isAffineVariety_zeroLocus_of_isPrime (Ideal.comap_isPrime _ _)).1
  isClosed' := isClosed_zeroLocus _

include hW in
/-- It lies inside `W`, the preimage containing `I(W)`. -/
theorem zeroLocusOfPrime_subset_closure (p : PrimeSpectrum (coordinateRing W)) :
    (zeroLocusOfPrime p : Set (σ → k)) ⊆ W := by
  refine (zeroLocus_anti_mono ?_).trans_eq hW.zeroLocus_vanishingIdeal
  intro x hx
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  exact Ideal.zero_mem _

/-- It contains `P` as soon as the prime sits below the maximal ideal at `P`. -/
theorem mem_zeroLocusOfPrime {P : W} {p : PrimeSpectrum (coordinateRing W)}
    (hle : p.asIdeal ≤ maximalIdealAt W P) :
    (P : σ → k) ∈ (zeroLocusOfPrime p : Set (σ → k)) := by
  intro f hf
  have hmem : f ∈ Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k W))
      (maximalIdealAt W P) := Ideal.comap_mono hle hf
  rw [comap_maximalIdealAt, mem_vanishingIdeal_singleton_iff] at hmem
  exact hmem

/-- And the assignment reverses strict inclusions. -/
theorem zeroLocusOfPrime_lt {p q : PrimeSpectrum (coordinateRing W)} (h : p < q) :
    zeroLocusOfPrime q < zeroLocusOfPrime p := by
  have hcomap : Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k W)) p.asIdeal
      < Ideal.comap (Ideal.Quotient.mk (vanishingIdeal k W)) q.asIdeal :=
    comap_lt_comap_quotient h
  have hZ := (irreducibleClosedsOrderIso (k := k) (σ := σ)).symm.strictMono
    (show (OrderDual.toDual (⟨_, Ideal.comap_isPrime _ q.asIdeal⟩ :
        PrimeSpectrum (MvPolynomial σ k)))
      < OrderDual.toDual (⟨_, Ideal.comap_isPrime _ p.asIdeal⟩ :
        PrimeSpectrum (MvPolynomial σ k)) from hcomap)
  exact hZ

set_option maxHeartbeats 600000 in
/-- **Proposition 1.10**, the reverse inequality: a quasi-affine variety has at
least the dimension of its closure.

A maximal chain of primes below `𝔪_P` in `A(Ȳ)` has length `dim Ȳ`, because
every maximal ideal of a finitely generated domain has full height. Reading it
as irreducible closed subsets of `Ȳ`, all of them through `P`, and restricting
each to `Y`, gives a chain of the same length inside `Y`. -/
theorem dim_closure_le_dim {Y : Set (σ → k)} (hY : IsQuasiAffineVariety Y) :
    dim (closure Y) ≤ dim Y := by
  classical
  obtain ⟨hne, V₀, U, hV₀aff, hU, hYeq⟩ := hY
  obtain ⟨P, hP⟩ := hne
  have hYq : IsQuasiAffineVariety Y := ⟨⟨P, hP⟩, V₀, U, hV₀aff, hU, hYeq⟩
  have hcl : IsAffineVariety (closure Y) := hYq.isAffineVariety_closure
  have hV₀cl : IsClosed V₀ := isClosed_iff_isAlgebraicSet.2 hV₀aff.isAlgebraicSet
  have : IsDomain (coordinateRing (closure Y)) := isDomain_coordinateRing hcl
  have : FiniteRingKrullDim (coordinateRing (closure Y)) :=
    finiteRingKrullDim_of_finiteType k _
  set Pc : ↥(closure Y) := ⟨P, subset_closure hP⟩ with hPcdef
  have hmax : (maximalIdealAt (closure Y) Pc).IsMaximal := maximalIdealAt_isMaximal Pc
  have : (maximalIdealAt (closure Y) Pc).IsPrime := hmax.isPrime
  rw [dim_eq_ringKrullDim_coordinateRing hcl.isAlgebraicSet,
    ← height_eq_ringKrullDim_of_isMaximal k (coordinateRing (closure Y))
      (maximalIdealAt (closure Y) Pc)]
  obtain ⟨l, hlast, hlen⟩ :=
    (maximalIdealAt (closure Y) Pc).exists_ltSeries_length_eq_height
  have hbelow : ∀ i, (l i).asIdeal ≤ maximalIdealAt (closure Y) Pc := by
    intro i
    have hle : l i ≤ l.last := l.monotone (Fin.le_last i)
    rw [hlast] at hle
    exact hle
  -- The chain, read on `Y`.
  let Zs : Fin (l.length + 1) → IrreducibleCloseds Y := fun i =>
    restrictToY hYeq hV₀cl hU hP
      ⟨zeroLocusOfPrime (l i.rev), mem_zeroLocusOfPrime (hbelow i.rev),
        zeroLocusOfPrime_subset_closure hcl.isAlgebraicSet _⟩
  have hstep : ∀ i : Fin l.length, Zs i.castSucc < Zs i.succ := by
    intro i
    refine strictMono_restrictToY hYeq hV₀cl hU hP ?_
    refine Subtype.mk_lt_mk.2 (zeroLocusOfPrime_lt (l.strictMono ?_))
    exact Fin.rev_lt_rev.2 Fin.castSucc_lt_succ
  have hle := Order.LTSeries.length_le_krullDim
    (⟨l.length, Zs, hstep⟩ : LTSeries (IrreducibleCloseds Y))
  rw [← hlen]
  calc ((l.length : ℕ∞) : WithBot ℕ∞) = (l.length : WithBot ℕ∞) := by norm_cast
    _ ≤ Order.krullDim (IrreducibleCloseds Y) := hle
    _ = dim Y := rfl

/-- **Proposition 1.10**: a quasi-affine variety and its closure have the same
dimension. -/
theorem dim_eq_dim_closure {Y : Set (σ → k)} (hY : IsQuasiAffineVariety Y) :
    dim Y = dim (closure Y) :=
  le_antisymm (dim_le_dim_closure Y) (dim_closure_le_dim hY)

end Hartshorne
