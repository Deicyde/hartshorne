/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.Correspondence

/-!
# The affine cone and its ideal

Hartshorne, *Algebraic Geometry*, I.2, Exercise 2.10(a) (p. 12).

For a nonempty projective algebraic set `Y`, its affine cone consists of the
origin and all nonzero representatives of points of `Y`. Its affine vanishing
ideal is the homogeneous vanishing ideal of `Y`.

## Main definitions

* `Hartshorne.affineCone`

## Main results

* `Hartshorne.vanishingIdeal_affineCone`
-/

namespace Hartshorne

open MvPolynomial

variable {k : Type*} [Field k] {σ : Type*}

/-- The affine cone over a subset of projective space: the origin together
with the nonzero representatives of its points. -/
def affineCone (Y : Set (ProjectiveSpace k σ)) : Set (σ → k) :=
  {v | v = 0 ∨ ∃ hv : v ≠ 0, Projectivization.mk k v hv ∈ Y}

/-- For a nonempty projective algebraic set, the geometric affine cone is the
affine zero set of its homogeneous vanishing ideal. -/
theorem affineCone_eq_zeroSet {Y : Set (ProjectiveSpace k σ)}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) :
    affineCone Y = zeroSet
      ((homogeneousVanishingIdeal Y : Ideal (MvPolynomial σ k)) : Set (MvPolynomial σ k)) := by
  ext v
  constructor
  · rintro (rfl | ⟨hv, hvY⟩)
    · obtain ⟨P, hPY⟩ := hne
      have hrep : P.rep ∈ zeroSet
          ((homogeneousVanishingIdeal Y : Ideal (MvPolynomial σ k)) :
            Set (MvPolynomial σ k)) :=
        fun f hf => eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal hf hPY
      have hzero := zeroSet_smul_of_isHomogeneousIdeal
        (isHomogeneousIdeal_homogeneousVanishingIdeal Y) (a := (0 : k)) hrep
      simpa using hzero
    · let P := Projectivization.mk k v hv
      have hrep : P.rep ∈ zeroSet
          ((homogeneousVanishingIdeal Y : Ideal (MvPolynomial σ k)) :
            Set (MvPolynomial σ k)) :=
        fun f hf => eval_rep_eq_zero_of_mem_homogeneousVanishingIdeal hf hvY
      obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
      have hscaled := zeroSet_smul_of_isHomogeneousIdeal
        (isHomogeneousIdeal_homogeneousVanishingIdeal Y)
        (a := ((a⁻¹ : kˣ) : k)) hrep
      rw [← ha, Units.smul_def] at hscaled
      simpa [smul_smul] using hscaled
  · intro hvzero
    by_cases hv : v = 0
    · exact Or.inl hv
    · refine Or.inr ⟨hv, ?_⟩
      let P := Projectivization.mk k v hv
      have hrep : P.rep ∈ zeroSet
          ((homogeneousVanishingIdeal Y : Ideal (MvPolynomial σ k)) :
            Set (MvPolynomial σ k)) := by
        obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
        rw [← ha, Units.smul_def]
        exact zeroSet_smul_of_isHomogeneousIdeal
          (isHomogeneousIdeal_homogeneousVanishingIdeal Y) hvzero
      have hP : P ∈ projZeroSet
          ((homogeneousVanishingIdeal Y : Ideal (MvPolynomial σ k)) :
            Set (MvPolynomial σ k)) :=
        fun f hf => hrep f hf
      have hclosed : IsClosed Y := isClosed_iff_isProjAlgebraicSet.2 hY
      rwa [projZeroSet_homogeneousVanishingIdeal_eq_closure, hclosed.closure_eq] at hP

/-- The affine cone over a nonempty projective algebraic set is affine
algebraic. -/
theorem isAlgebraicSet_affineCone {Y : Set (ProjectiveSpace k σ)}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) : IsAlgebraicSet (affineCone Y) := by
  rw [affineCone_eq_zeroSet hY hne]
  exact isAlgebraicSet_iff_exists_ideal.2 ⟨homogeneousVanishingIdeal Y, rfl⟩

section AlgClosed

variable [IsAlgClosed k] [Finite σ]

/-- **Exercise 2.10(a)**: the affine vanishing ideal of the affine cone over a
nonempty projective algebraic set is its homogeneous vanishing ideal. -/
theorem vanishingIdeal_affineCone {Y : Set (ProjectiveSpace k σ)}
    (hY : IsProjAlgebraicSet Y) (hne : Y.Nonempty) :
    vanishingIdeal k (affineCone Y) = homogeneousVanishingIdeal Y := by
  rw [affineCone_eq_zeroSet hY hne, vanishingIdeal_zeroSet_eq_radical,
    (isRadical_homogeneousVanishingIdeal hY hne).radical]

end AlgClosed

end Hartshorne
