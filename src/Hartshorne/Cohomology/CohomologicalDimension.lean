/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SheafCohomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Data.ENat.Lattice

/-!
# Cohomological dimension

Hartshorne, *Algebraic Geometry*, III, Exercise 4.8 (p. 224), with the project's extended-value
convention.

A value `n : WithTop ℕ` bounds the cohomology of a scheme `X`
(`Hartshorne.IsCohomologicalDimensionBound X n`) if `H^i(X, F) = 0` for every quasi-coherent
`𝒪_X`-module `F` and every `i > n`; the cohomology of an `𝒪_X`-module is that of its underlying
abelian sheaf. The cohomological dimension `Hartshorne.cohomologicalDimension X` is the infimum
of all bounds. Since `⊤` is always a bound, the infimum is itself a bound
(`Hartshorne.isCohomologicalDimensionBound_cohomologicalDimension`); it is `⊤` exactly when no
finite bound exists (`Hartshorne.cohomologicalDimension_eq_top_iff`), and otherwise it is the least
natural-number bound, which is Hartshorne's definition
(`Hartshorne.cohomologicalDimension_eq_coe_iff`).

Hartshorne states the definition for Noetherian separated schemes; the Lean definition makes
sense, and agrees with it, for every scheme.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Hartshorne

/-- `n : WithTop ℕ` bounds the cohomology of `X`: `H^i(X, F) = 0` for every quasi-coherent
`𝒪_X`-module `F` and every natural number `i > n`. -/
def IsCohomologicalDimensionBound (X : Scheme.{u}) (n : WithTop ℕ) : Prop :=
  ∀ F : X.Modules, F.IsQuasicoherent → ∀ i : ℕ, n < i →
    IsZero ((sheafCohomology X.toTopCat i).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F))

/-- **Cohomological dimension** (Hartshorne III, Exercise 4.8). The cohomological dimension
`cd(X) ∈ ℕ ∪ {∞}` of a scheme `X` is the infimum of the `n ∈ ℕ ∪ {∞}` such that
`H^i(X, F) = 0` for every quasi-coherent sheaf `F` and every `i > n`. -/
noncomputable def cohomologicalDimension (X : Scheme.{u}) : WithTop ℕ :=
  sInf {n | IsCohomologicalDimensionBound X n}

theorem isCohomologicalDimensionBound_top (X : Scheme.{u}) :
    IsCohomologicalDimensionBound X ⊤ :=
  fun _ _ _ hi ↦ absurd hi (not_lt.2 le_top)

theorem IsCohomologicalDimensionBound.mono {X : Scheme.{u}} {m n : WithTop ℕ}
    (hm : IsCohomologicalDimensionBound X m) (hmn : m ≤ n) : IsCohomologicalDimensionBound X n :=
  fun F hF i hi ↦ hm F hF i (lt_of_le_of_lt hmn hi)

/-- The cohomological dimension is itself a bound. -/
theorem isCohomologicalDimensionBound_cohomologicalDimension (X : Scheme.{u}) :
    IsCohomologicalDimensionBound X (cohomologicalDimension X) :=
  csInf_mem (s := {n | IsCohomologicalDimensionBound X n}) ⟨⊤, isCohomologicalDimensionBound_top X⟩

theorem cohomologicalDimension_le_iff (X : Scheme.{u}) (n : WithTop ℕ) :
    cohomologicalDimension X ≤ n ↔ IsCohomologicalDimensionBound X n :=
  ⟨(isCohomologicalDimensionBound_cohomologicalDimension X).mono, fun h ↦ csInf_le' h⟩

/-- The cohomological dimension is `∞` exactly when no finite bound exists. -/
theorem cohomologicalDimension_eq_top_iff (X : Scheme.{u}) :
    cohomologicalDimension X = ⊤ ↔ ∀ n : ℕ, ¬ IsCohomologicalDimensionBound X n := by
  constructor
  · intro h n hn
    have := (cohomologicalDimension_le_iff X n).2 hn
    rw [h] at this
    exact WithTop.coe_ne_top (top_le_iff.1 this)
  · intro h
    by_contra hne
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 hne
    have := isCohomologicalDimensionBound_cohomologicalDimension X
    rw [← hn] at this
    exact h n this

/-- When it is finite, the cohomological dimension is the least natural-number bound, as in
Hartshorne's definition. -/
theorem cohomologicalDimension_eq_coe_iff (X : Scheme.{u}) (n : ℕ) :
    cohomologicalDimension X = n ↔
      IsCohomologicalDimensionBound X n ∧ ∀ m : ℕ, IsCohomologicalDimensionBound X m → n ≤ m := by
  constructor
  · intro h
    refine ⟨h ▸ isCohomologicalDimensionBound_cohomologicalDimension X, fun m hm ↦ ?_⟩
    have := (cohomologicalDimension_le_iff X m).2 hm
    rw [h] at this
    exact WithTop.coe_le_coe.1 this
  · rintro ⟨hn, hmin⟩
    refine le_antisymm ((cohomologicalDimension_le_iff X n).2 hn) ?_
    induction h : cohomologicalDimension X using WithTop.recTopCoe with
    | top => exact le_top
    | coe m =>
      have := isCohomologicalDimensionBound_cohomologicalDimension X
      rw [h] at this
      exact WithTop.coe_le_coe.2 (hmin m this)

end Hartshorne
