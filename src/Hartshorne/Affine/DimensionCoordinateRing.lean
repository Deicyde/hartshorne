/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.CoordinateRing
import Hartshorne.Affine.Dimension
import Hartshorne.Topology.Subspace
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Dimension is the dimension of the coordinate ring

Hartshorne, *Algebraic Geometry*, I.1, Proposition 1.7 (p. 6).

Hartshorne's proof is a chain of order isomorphisms rather than a computation:
closed irreducible subsets of `Y` correspond to primes of `k[x₁,…,xₙ]`
containing `I(Y)`, which correspond to primes of `A(Y)`. Every step reverses or
preserves inclusion uniformly, so chains match chains and the suprema agree.

Spelling that out needs three links. Corollary 1.4 becomes an order
*anti*-isomorphism here; the passage between a closed subspace and its ambient
space is `IrreducibleCloseds.subtypeOrderIso`; and the quotient step is
Mathlib's `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`.

## Main results

* `Hartshorne.irreducibleClosedsOrderIso` : Corollary 1.4 as an order
  isomorphism onto the order dual of the prime spectrum.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ]

/-- **Corollary 1.4 as an order isomorphism.** Irreducible closed subsets of
affine space correspond to prime ideals of the polynomial ring, and the
correspondence reverses inclusion, so it lands in the order dual.

This is the form Proposition 1.7 needs: the bijection of Corollary 1.4 records
only that the two collections match, whereas computing a Krull dimension needs
chains to be carried to chains. -/
def irreducibleClosedsOrderIso :
    IrreducibleCloseds (σ → k) ≃o (PrimeSpectrum (MvPolynomial σ k))ᵒᵈ where
  toFun Z :=
    ⟨vanishingIdeal k (Z : Set (σ → k)),
      (isIrreducible_iff_isPrime (isClosed_iff_isAlgebraicSet.1 Z.isClosed)).1
        Z.isIrreducible⟩
  invFun p :=
    ⟨zeroLocus k p.asIdeal,
      (isAffineVariety_zeroLocus_of_isPrime p.isPrime).1,
      isClosed_zeroLocus _⟩
  left_inv Z := by
    apply IrreducibleCloseds.ext
    exact (isClosed_iff_isAlgebraicSet.1 Z.isClosed).zeroLocus_vanishingIdeal
  right_inv p := by
    apply PrimeSpectrum.ext
    exact vanishingIdeal_zeroLocus_of_isPrime p.isPrime
  map_rel_iff' := by
    intro Z W
    constructor
    · -- `I(W) ≤ I(Z)` forces `Z ⊆ W`, by applying `Z(-)` and using that both
      -- sets are algebraic.
      intro h
      have hZ := (isClosed_iff_isAlgebraicSet.1 Z.isClosed).zeroLocus_vanishingIdeal
      have hW := (isClosed_iff_isAlgebraicSet.1 W.isClosed).zeroLocus_vanishingIdeal
      calc (Z : Set (σ → k)) = zeroLocus k (vanishingIdeal k (Z : Set (σ → k))) := hZ.symm
        _ ⊆ zeroLocus k (vanishingIdeal k (W : Set (σ → k))) := zeroLocus_anti_mono h
        _ = (W : Set (σ → k)) := hW
    · exact fun h => vanishingIdeal_anti_mono h

/-- The order isomorphism of Corollary 1.4 restricted to what sits inside a
fixed algebraic set `Y`: irreducible closed subsets of `Y` correspond to primes
containing `I(Y)`. -/
noncomputable def subtypeIrreducibleClosedsOrderIso {Y : Set (σ → k)}
    (hY : IsAlgebraicSet Y) :
    {Z : IrreducibleCloseds (σ → k) // (Z : Set (σ → k)) ⊆ Y} ≃o
      ({p : PrimeSpectrum (MvPolynomial σ k) //
        p ∈ PrimeSpectrum.zeroLocus (vanishingIdeal k Y : Set (MvPolynomial σ k))})ᵒᵈ where
  toFun Z := OrderDual.toDual
    ⟨OrderDual.ofDual (irreducibleClosedsOrderIso Z.1), by
      rw [PrimeSpectrum.mem_zeroLocus]
      exact SetLike.coe_subset_coe.2 (vanishingIdeal_anti_mono Z.2)⟩
  invFun p :=
    ⟨irreducibleClosedsOrderIso.symm (OrderDual.toDual (OrderDual.ofDual p).1), by
      have hle : vanishingIdeal k Y ≤ ((OrderDual.ofDual p).1).asIdeal :=
        SetLike.coe_subset_coe.1
          ((PrimeSpectrum.mem_zeroLocus _ _).1 (OrderDual.ofDual p).2)
      calc zeroLocus k ((OrderDual.ofDual p).1).asIdeal
            ⊆ zeroLocus k (vanishingIdeal k Y) := zeroLocus_anti_mono hle
        _ = Y := hY.zeroLocus_vanishingIdeal⟩
  left_inv Z := by
    apply Subtype.ext
    exact irreducibleClosedsOrderIso.left_inv Z.1
  right_inv p := by
    apply Subtype.ext
    exact irreducibleClosedsOrderIso.right_inv _
  map_rel_iff' := by
    intro Z W
    exact irreducibleClosedsOrderIso.map_rel_iff

/-- **Hartshorne 1.7**: the dimension of an affine algebraic set equals the
Krull dimension of its affine coordinate ring.

This is the bridge that lets every dimension statement about varieties be
answered by commutative algebra, and every later dimension result in the
chapter routes through it. -/
theorem dim_eq_ringKrullDim_coordinateRing {Y : Set (σ → k)} (hY : IsAlgebraicSet Y) :
    dim Y = ringKrullDim (coordinateRing Y) := by
  rw [dim_def, topologicalKrullDim_subtype_eq (isClosed_iff_isAlgebraicSet.2 hY),
    ringKrullDim, Order.krullDim_eq_of_orderIso (subtypeIrreducibleClosedsOrderIso hY),
    Order.krullDim_orderDual,
    Order.krullDim_eq_of_orderIso
      (Ideal.primeSpectrumQuotientOrderIsoZeroLocus (vanishingIdeal k Y))]

omit [Finite σ] in
/-- Only the zero polynomial vanishes identically on affine space. An
algebraically closed field is infinite, which is exactly what this needs; the
number of variables is irrelevant. -/
theorem vanishingIdeal_univ :
    vanishingIdeal k (Set.univ : Set (σ → k)) = ⊥ := by
  ext f
  simp only [mem_vanishingIdeal_iff, Set.mem_univ, forall_const, Ideal.mem_bot]
  refine ⟨fun h => MvPolynomial.funext fun x => ?_, fun h => by simp [h]⟩
  simpa using h x

/-- **Hartshorne 1.9**: `dim 𝔸ⁿ = n`.

By Proposition 1.7 this is the assertion that `k[x₁,…,xₙ]` has Krull dimension
`n`. Hartshorne deduces that from Theorem 1.8A, but it does not need the full
strength of 1.8A: Mathlib computes the dimension of a polynomial ring over a
Noetherian base directly. -/
theorem dimAffineSpace_eq : dimAffineSpace k σ = Nat.card σ := by
  rw [← dim_univ, dim_eq_ringKrullDim_coordinateRing isAlgebraicSet_univ]
  have hbot : ringKrullDim (coordinateRing (Set.univ : Set (σ → k)))
      = ringKrullDim (MvPolynomial σ k) := by
    exact RingEquiv.ringKrullDim
      ((Ideal.quotEquivOfEq vanishingIdeal_univ).trans
        (RingEquiv.quotientBot (MvPolynomial σ k)))
  rw [hbot, MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, zero_add]

end Hartshorne
