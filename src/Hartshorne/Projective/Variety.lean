/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.VanishingIdeal
import Hartshorne.Affine.Decomposition
import Hartshorne.Affine.Dimension
import Mathlib.Topology.NoetherianSpace

/-!
# Projective varieties, and `ℙⁿ` is Noetherian

Hartshorne, *Algebraic Geometry*, I.2, the definitions on p. 10 and
Exercise 2.5 (p. 11).

A *projective variety* is an irreducible algebraic set in `ℙⁿ`; a
*quasi-projective variety* is a nonempty open subset of one. The definitions are
verbatim the affine ones, so this file is short.

Exercise 2.5, that `ℙⁿ` is a Noetherian space, is proved the same way as its
affine counterpart: an open set is sent to the homogeneous ideal of its
complement, giving a strictly monotone map into the ideals of `S`. Doing it this
way rather than through the affine charts keeps §2 independent of Proposition
2.2, which is not yet available.

## Main definitions

* `Hartshorne.IsProjVariety`, `Hartshorne.IsQuasiProjVariety`
* `Hartshorne.projDim`

## Main results

* `Hartshorne.instNoetherianSpaceProjectiveSpace` : Exercise 2.5.
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] {σ : Type*}

/-- A *projective variety* is an irreducible closed subset of `ℙⁿ`. -/
def IsProjVariety (Y : Set (ProjectiveSpace k σ)) : Prop :=
  IsIrreducible Y ∧ IsClosed Y

/-- A *quasi-projective variety* is a nonempty open subset of a projective
variety. -/
def IsQuasiProjVariety (Y : Set (ProjectiveSpace k σ)) : Prop :=
  Y.Nonempty ∧ ∃ V U : Set (ProjectiveSpace k σ),
    IsProjVariety V ∧ IsOpen U ∧ Y = V ∩ U

theorem IsProjVariety.isProjAlgebraicSet {Y : Set (ProjectiveSpace k σ)}
    (h : IsProjVariety Y) : IsProjAlgebraicSet Y :=
  isClosed_iff_isProjAlgebraicSet.1 h.2

theorem IsProjVariety.isQuasiProjVariety {Y : Set (ProjectiveSpace k σ)}
    (h : IsProjVariety Y) : IsQuasiProjVariety Y :=
  ⟨h.1.nonempty, Y, Set.univ, h, isOpen_univ, (Set.inter_univ Y).symm⟩

/-- A quasi-projective variety is irreducible, by the same argument as in the
affine case. -/
theorem IsQuasiProjVariety.isIrreducible {Y : Set (ProjectiveSpace k σ)}
    (h : IsQuasiProjVariety Y) : IsIrreducible Y := by
  obtain ⟨hne, V, U, hV, hU, rfl⟩ := h
  exact ⟨hne, IsPreirreducible.inter_isOpen hV.1.2 hU⟩

/-- The dimension of a subset of projective space. -/
noncomputable def projDim (Y : Set (ProjectiveSpace k σ)) : WithBot ℕ∞ :=
  topologicalKrullDim Y

theorem projDim_def (Y : Set (ProjectiveSpace k σ)) :
    projDim Y = topologicalKrullDim Y := rfl

/-- An algebraic set is recovered as the zero set of its homogeneous ideal. -/
theorem IsProjAlgebraicSet.projZeroSet_homogeneousVanishingIdeal_eq
    {Y : Set (ProjectiveSpace k σ)} (h : IsProjAlgebraicSet Y) :
    projZeroSet (homogeneousVanishingIdeal Y : Set (MvPolynomial σ k)) = Y := by
  rw [_root_.Hartshorne.projZeroSet_homogeneousVanishingIdeal]
  exact h.projZeroSet_homogeneousVanishingSet

/-- Sending an open set of `ℙⁿ` to the homogeneous ideal of its complement is
strictly monotone, which is what makes `ℙⁿ` Noetherian. -/
theorem strictMono_homogeneousVanishingIdeal_compl :
    StrictMono (fun U : Opens (ProjectiveSpace k σ) =>
      homogeneousVanishingIdeal ((U : Set (ProjectiveSpace k σ))ᶜ)) := by
  refine Monotone.strictMono_of_injective (fun U V h => ?_) (fun U V h => ?_)
  · exact homogeneousVanishingIdeal_anti_mono (Set.compl_subset_compl.2 h)
  · have hU : IsProjAlgebraicSet ((U : Set (ProjectiveSpace k σ))ᶜ) :=
      isClosed_iff_isProjAlgebraicSet.1 U.isOpen.isClosed_compl
    have hV : IsProjAlgebraicSet ((V : Set (ProjectiveSpace k σ))ᶜ) :=
      isClosed_iff_isProjAlgebraicSet.1 V.isOpen.isClosed_compl
    have hc : (U : Set (ProjectiveSpace k σ))ᶜ = (V : Set (ProjectiveSpace k σ))ᶜ := by
      rw [← hU.projZeroSet_homogeneousVanishingIdeal_eq,
        ← hV.projZeroSet_homogeneousVanishingIdeal_eq, h]
    exact Opens.ext (compl_injective hc)

/-- **Exercise 2.5**: projective space is a Noetherian topological space, so
every algebraic set in it decomposes uniquely into irreducible components. -/
instance instNoetherianSpaceProjectiveSpace [Finite σ] :
    NoetherianSpace (ProjectiveSpace k σ) :=
  strictMono_homogeneousVanishingIdeal_compl.wellFoundedGT

/-- Exercise 2.5, decomposition form: every algebraic set in `ℙⁿ` is uniquely a
finite irredundant union of projective varieties. -/
theorem IsProjAlgebraicSet.exists_unique_decomposition [Finite σ]
    {Y : Set (ProjectiveSpace k σ)} (hY : IsProjAlgebraicSet Y) :
    ∃! S : Finset (Set (ProjectiveSpace k σ)), (∀ t ∈ S, IsProjVariety t) ∧
      Y = ⋃ t ∈ S, t ∧ ∀ t ∈ S, ∀ u ∈ S, t ⊆ u → t = u := by
  obtain ⟨S, ⟨hSc, hSi, hSu, hSa⟩, huniq⟩ :=
    exists_unique_irredundant_decomposition (isClosed_iff_isProjAlgebraicSet.2 hY)
  refine ⟨S, ⟨fun t ht => ⟨hSi t ht, hSc t ht⟩, hSu, hSa⟩, ?_⟩
  rintro T ⟨hTv, hTu, hTa⟩
  exact huniq T ⟨fun t ht => (hTv t ht).2, fun t ht => (hTv t ht).1, hTu, hTa⟩

end Hartshorne
