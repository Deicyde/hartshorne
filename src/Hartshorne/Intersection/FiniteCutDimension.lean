/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Affine.DimensionCoordinateRing
import Hartshorne.Dimension.DimFormula
import Hartshorne.Intersection.AffineComponents
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Dimension of a component cut out by finitely many equations

Hartshorne, *Algebraic Geometry*, I.7, proof of Proposition 7.1 (p. 48).

If an irreducible component `W` of an affine variety `X` is cut out by a
finite family `T`, Krull's height theorem bounds its codimension by the number
of equations.  The dimension formula converts that height bound into
`dim X ≤ dim W + T.ncard`.

## Main result

* `Hartshorne.dim_component_inter_zeroLocus_add_ncard`
-/

namespace Hartshorne

open MvPolynomial

noncomputable section

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {σ : Type} [Finite σ]

/-- Quotienting `A(X)` by the relative ideal of `W` recovers `A(W)`. -/
def coordinateRingQuotientComponentIdealEquiv
    {X W : Set (σ → k)} (hWX : W ⊆ X) :
    (coordinateRing X ⧸ componentIdeal X W) ≃ₐ[k] coordinateRing W :=
  DoubleQuot.quotQuotEquivQuotOfLEₐ k (vanishingIdeal_anti_mono hWX)

/-- **Hartshorne I.7, repeated principal-section bound.** An irreducible
component cut out by `T` has codimension at most the number of equations. -/
theorem dim_component_inter_zeroLocus_add_ncard
    {X W : Set (σ → k)} (hX : IsAffineVariety X)
    (T : Set (MvPolynomial σ k)) (hT : T.Finite)
    (hW : Maximal
      (fun V : Set (σ → k) ↦
        IsAffineVariety V ∧ V ⊆ X ∩ zeroSet T) W) :
    dim X ≤ dim W + T.ncard := by
  classical
  let S : Set (coordinateRing X) :=
    Ideal.Quotient.mk (vanishingIdeal k X) '' T
  have hWfin : Maximal
      (fun V : Set (σ → k) ↦
        IsAffineVariety V ∧
          V ⊆ X ∩ zeroSet (hT.toFinset : Set (MvPolynomial σ k))) W := by
    simpa only [hT.coe_toFinset] using hW
  have hpmin : componentIdeal X W ∈ (Ideal.span S).minimalPrimes := by
    simpa only [S, hT.coe_toFinset] using
      componentIdeal_mem_minimalPrimes hX hT.toFinset hWfin
  have : (componentIdeal X W).IsPrime := hpmin.1.1
  have hcard : S.ncard ≤ T.ncard := by
    dsimp only [S]
    exact Set.ncard_image_le hT
  have hheight : (componentIdeal X W).height ≤ T.ncard :=
    (Ideal.height_le_card_of_mem_minimalPrimes_span (hT.image _) hpmin).trans
      (by exact_mod_cast hcard)
  have hheight_ne : (componentIdeal X W).height ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hheight
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (componentIdeal X W).height = h :=
    ENat.ne_top_iff_exists.mp hheight_ne |>.imp fun _ e ↦ e.symm
  have hhT : h ≤ T.ncard := by
    rw [hh] at hheight
    exact_mod_cast hheight
  have hhT' : (h : WithBot ℕ∞) ≤ (T.ncard : WithBot ℕ∞) := by
    exact_mod_cast hhT
  have hWX : W ⊆ X := fun _ hx ↦ (hW.1.2 hx).1
  have hquot : ringKrullDim (coordinateRing X ⧸ componentIdeal X W) = dim W := by
    calc
      ringKrullDim (coordinateRing X ⧸ componentIdeal X W) =
          ringKrullDim (coordinateRing W) :=
        RingEquiv.ringKrullDim (coordinateRingQuotientComponentIdealEquiv hWX).toRingEquiv
      _ = dim W := (dim_eq_ringKrullDim_coordinateRing hW.1.1.isAlgebraicSet).symm
  have : IsDomain (coordinateRing X) := isDomain_coordinateRing hX
  have hform := height_add_ringKrullDim_quotient_eq k (coordinateRing X)
    (componentIdeal X W) h hh
  rw [hquot, ← dim_eq_ringKrullDim_coordinateRing hX.isAlgebraicSet] at hform
  calc
    dim X = (h : WithBot ℕ∞) + dim W := hform.symm
    _ = dim W + (h : WithBot ℕ∞) := add_comm _ _
    _ ≤ dim W + (T.ncard : WithBot ℕ∞) := by
      exact add_le_add_right hhT' _

end

end Hartshorne
