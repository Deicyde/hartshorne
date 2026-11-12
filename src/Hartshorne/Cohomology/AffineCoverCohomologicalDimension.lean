/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AffineCoverComparison
import Hartshorne.Cohomology.CohomologicalDimension

/-!
# Cohomological dimension from an affine cover

Hartshorne, *Algebraic Geometry*, III, Exercise 4.8(c) (p. 224): if a Noetherian separated scheme
`X` can be covered by `r + 1` open affine subsets, then `cd(X) ≤ r`.

Following the book, the proof combines two facts.

* The ordered Čech complex of a cover indexed by a finite linearly ordered set with at most `p`
  elements has no strictly increasing `(p + 1)`-tuples of indices, so its degree-`p` cochains vanish
  (`Hartshorne.OrderedCechIndex.isEmpty_of_card_le`,
  `Hartshorne.orderedCechCohomology_isZero_of_card_le`).
* For an open affine cover of a Noetherian separated scheme, Čech cohomology of a quasi-coherent
  sheaf computes its sheaf cohomology (Hartshorne III, Theorem 4.5,
  `Hartshorne.cechCohomologyIsoOfIsQuasicoherent`).

The main results are `Hartshorne.isCohomologicalDimensionBound_of_affine_cover` and
`Hartshorne.cohomologicalDimension_le_of_affine_cover`. The cover may be indexed by any type with
`r + 1` elements, in any universe; a linear order on the index set, needed to form ordered Čech
cochains, is chosen in the proof.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u v

namespace Hartshorne

/-- A finite linearly ordered set with at most `p` elements has no strictly increasing
`(p + 1)`-tuples. -/
theorem OrderedCechIndex.isEmpty_of_card_le {ι : Type u} [LinearOrder ι] [Finite ι] {p : ℕ}
    (hp : Nat.card ι ≤ p) : IsEmpty (OrderedCechIndex ι p) := by
  refine ⟨fun a ↦ ?_⟩
  have h := Nat.card_le_card_of_injective a.1 a.2.injective
  rw [Nat.card_fin] at h
  omega

/-- The ordered Čech cohomology of a cover indexed by a finite linearly ordered set with at most `p`
elements vanishes in degree `p`: there are no degree-`p` cochains. -/
theorem orderedCechCohomology_isZero_of_card_le {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]
    [Finite ι] (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) {p : ℕ} (hp : Nat.card ι ≤ p) :
    IsZero (orderedCechCohomology U F p) := by
  have := OrderedCechIndex.isEmpty_of_card_le hp
  have : Subsingleton (orderedCechCochains U F p) :=
    ⟨fun s t ↦ funext fun (a : OrderedCechIndex ι p) ↦ isEmptyElim a⟩
  have hX : IsZero ((orderedCechComplex U F).X p) :=
    AddCommGrpCat.isZero_of_subsingleton (orderedCechCochains U F p)
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ hX

/-- **Hartshorne III, Exercise 4.8(c)**, as a cohomology bound. If a Noetherian separated scheme
`X` is covered by `r + 1` open affine subsets, then `H^i(X, F) = 0` for every quasi-coherent
`𝒪_X`-module `F` and every `i > r`. -/
theorem isCohomologicalDimensionBound_of_affine_cover {X : Scheme.{u}} [IsNoetherian X]
    [X.IsSeparated] {ι : Type v} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) {r : ℕ} (hr : Nat.card ι = r + 1) :
    IsCohomologicalDimensionBound X r := by
  have : Finite ι := Nat.finite_of_card_ne_zero (by omega)
  let e : ι ≃ Fin (r + 1) := Finite.equivFinOfCardEq hr
  let U' : ULift.{u} (Fin (r + 1)) → X.Opens := fun j ↦ U (e.symm j.down)
  have hU' : IsOpenCover U' := by
    refine top_le_iff.mp (hU.iSup_eq_top ▸ iSup_le fun i ↦ ?_)
    exact le_iSup_of_le (ULift.up (e i)) (by simp [U'])
  have hUa' : ∀ j, IsAffineOpen (U' j) := fun j ↦ hUa _
  intro F hF i hi
  have := hF
  have hi' : r < i := WithTop.coe_lt_coe.1 hi
  refine IsZero.of_iso ?_ (cechCohomologyIsoOfIsQuasicoherent U' hU' hUa' i F).symm
  exact orderedCechCohomology_isZero_of_card_le U' _ (by simp; omega)

/-- **Hartshorne III, Exercise 4.8(c).** If a Noetherian separated scheme `X` is covered by `r + 1`
open affine subsets, then `cd(X) ≤ r`. -/
theorem cohomologicalDimension_le_of_affine_cover {X : Scheme.{u}} [IsNoetherian X]
    [X.IsSeparated] {ι : Type v} (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i)) {r : ℕ} (hr : Nat.card ι = r + 1) :
    cohomologicalDimension X ≤ r :=
  (cohomologicalDimension_le_iff X r).2 (isCohomologicalDimensionBound_of_affine_cover U hU hUa hr)

end Hartshorne
