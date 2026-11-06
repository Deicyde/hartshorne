/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Length
import Hartshorne.Intersection.CodimensionCycles

/-!
# The fundamental cycle of a closed subscheme

Hartshorne, *Algebraic Geometry*, Appendix A.1 (p. 425).

A closed subscheme of `X` is a closed immersion `f : Z ⟶ X`. The irreducible components of `Z`
are recorded by their generic points, the set `genericPoints Z`. For `r : ℕ`, the codimension-`r`
fundamental cycle of `Z` has coefficient, at the image `f z` of the generic point `z` of an
irreducible component whose closure in `X` has codimension exactly `r`, the length of the local
ring `𝒪_{Z,z}` as a module over itself; every other point of `X` has coefficient zero. In
particular, components of any other codimension do not contribute.

When `Z` has codimension `r` in `X`, this is the cycle `[Z]_r` of Hartshorne. The definition does
not use the codimension of `Z`, so it is stated for every `r`.

On a Noetherian scheme `X` (the setting of varieties) `Z` has finitely many irreducible
components, so the cycle has finite support, and each such local ring is Artinian, so its length
is finite (`closedSubschemeFundamentalCycle_apply_generic` records the coefficient as the genuine
length). The length is a value in `ℕ∞`; the coefficient is its natural-number value, which is the
length itself because the length is finite.
-/

universe u

namespace Hartshorne

open AlgebraicGeometry Topology TopologicalSpace

variable {X Z : Scheme.{u}} (f : Z ⟶ X)

/-- The generic point of an irreducible component of a locally Noetherian scheme has an
Artinian local ring. -/
theorem isArtinianRing_stalk_of_mem_genericPoints [IsLocallyNoetherian Z] {z : Z}
    (hz : z ∈ genericPoints Z) : IsArtinianRing (Z.presheaf.stalk z) := by
  have hmax : IsMax z := by
    intro w hzw
    -- `z ≤ w` means that `w` specializes to `z`, i.e. `z ∈ closure {w}`.
    have hspec : w ⤳ z := hzw
    have hsub : closure {z} ⊆ closure ({w} : Set Z) := hspec.closure_subset
    have hwz : z ⤳ w := by
      rw [specializes_iff_mem_closure]
      exact hz.2 isIrreducible_singleton.closure hsub (subset_closure rfl)
    exact hwz
  have hdim : Ring.KrullDimLE 0 (Z.presheaf.stalk z) :=
    krullDimLE_of_coheight_le (Order.coheight_eq_zero.mpr hmax).le
  exact isArtinianRing_iff_krullDimLE_zero.mpr hdim

/-- The length of the local ring of a locally Noetherian scheme at the generic point of an
irreducible component is finite. -/
theorem length_stalk_ne_top_of_mem_genericPoints [IsLocallyNoetherian Z] {z : Z}
    (hz : z ∈ genericPoints Z) :
    Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z) ≠ ⊤ := by
  have := isArtinianRing_stalk_of_mem_genericPoints hz
  exact Module.length_ne_top

open Classical in
/-- The coefficient function of the codimension-`r` fundamental cycle of the closed subscheme
`f : Z ⟶ X`: at the image of the generic point `z` of an irreducible component of `Z` whose
closure in `X` has codimension `r`, it is the length of the local ring of `Z` at `z`; elsewhere it
is zero. -/
noncomputable def closedSubschemeFundamentalCycleCoeff (r : ℕ) (x : X) : ℤ :=
  if h : ∃ z ∈ genericPoints Z, f.base z = x ∧ codim (closure {x}) = r then
    ((Module.length (Z.presheaf.stalk h.choose) (Z.presheaf.stalk h.choose)).toNat : ℤ)
  else 0

theorem closedSubschemeFundamentalCycleCoeff_apply_generic [IsClosedImmersion f] (r : ℕ)
    {z : Z} (hz : z ∈ genericPoints Z) (hr : codim (closure {f.base z}) = r) :
    closedSubschemeFundamentalCycleCoeff f r (f.base z) =
      ((Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z)).toNat : ℤ) := by
  have h : ∃ w ∈ genericPoints Z, f.base w = f.base z ∧ codim (closure {f.base z}) = r :=
    ⟨z, hz, rfl, hr⟩
  have hw : h.choose = z := f.isClosedEmbedding.injective h.choose_spec.2.1
  rw [closedSubschemeFundamentalCycleCoeff, dif_pos h, hw]

theorem closedSubschemeFundamentalCycleCoeff_eq_zero (r : ℕ) {x : X}
    (hx : ¬ ∃ z ∈ genericPoints Z, f.base z = x ∧ codim (closure {x}) = r) :
    closedSubschemeFundamentalCycleCoeff f r x = 0 := by
  rw [closedSubschemeFundamentalCycleCoeff, dif_neg hx]

theorem support_closedSubschemeFundamentalCycleCoeff_subset (r : ℕ) :
    Function.support (closedSubschemeFundamentalCycleCoeff f r) ⊆
      {x | ∃ z ∈ genericPoints Z, f.base z = x ∧ codim (closure {x}) = r} := by
  intro x hx
  by_contra h
  exact hx (closedSubschemeFundamentalCycleCoeff_eq_zero f r h)

/-- **The fundamental cycle of a closed subscheme** (Hartshorne, Appendix A.1, p. 425).
For a closed subscheme `f : Z ⟶ X` of a Noetherian scheme and `r : ℕ`, this is the
codimension-`r` cycle `∑ᵢ nᵢ [Yᵢ]`, where `Yᵢ` runs over the irreducible components of `Z` of
codimension exactly `r` in `X` and `nᵢ` is the length of the local ring of `Z` at the generic point
of `Yᵢ`. Components of other codimension do not contribute. -/
noncomputable def closedSubschemeFundamentalCycle [IsClosedImmersion f] [IsNoetherian X]
    (r : ℕ) : codimensionCycles X r := by
  have hfin : (Function.support (closedSubschemeFundamentalCycleCoeff f r)).Finite := by
    have : NoetherianSpace Z := f.isClosedEmbedding.isInducing.noetherianSpace
    have hgen : (genericPoints Z).Finite :=
      genericPoints.finite (NoetherianSpace.finite_irreducibleComponents)
    refine ((hgen.image f.base).subset ?_).subset
      (support_closedSubschemeFundamentalCycleCoeff_subset f r)
    rintro x ⟨z, hz, rfl, -⟩
    exact ⟨z, hz, rfl⟩
  refine ⟨⟨closedSubschemeFundamentalCycleCoeff f r, by simp, fun x _ ↦ ?_⟩, hfin, ?_⟩
  · exact ⟨Set.univ, Filter.univ_mem, hfin.subset Set.inter_subset_right⟩
  · intro x hx
    obtain ⟨-, -, -, hr⟩ := support_closedSubschemeFundamentalCycleCoeff_subset f r hx
    exact hr

/-- The coefficient of the fundamental cycle at the generic point of an irreducible component of
codimension `r` is the length of the local ring there; this length is finite. -/
theorem closedSubschemeFundamentalCycle_apply_generic [IsClosedImmersion f] [IsNoetherian X]
    (r : ℕ) {z : Z} (hz : z ∈ genericPoints Z) (hr : codim (closure {f.base z}) = r) :
    ∃ n : ℕ, ((closedSubschemeFundamentalCycle f r : AlgebraicCycle X ℤ) (f.base z) = n) ∧
      (n : ℕ∞) = Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  refine ⟨(Module.length (Z.presheaf.stalk z) (Z.presheaf.stalk z)).toNat,
    closedSubschemeFundamentalCycleCoeff_apply_generic f r hz hr, ?_⟩
  exact ENat.natCast_toNat (length_stalk_ne_top_of_mem_genericPoints hz)

/-- Points of `X` other than images of generic points of irreducible components of `Z` of
codimension `r` have coefficient zero; in particular components of larger codimension do not
contribute. -/
theorem closedSubschemeFundamentalCycle_apply_eq_zero [IsClosedImmersion f] [IsNoetherian X]
    (r : ℕ) {x : X}
    (hx : ¬ ∃ z ∈ genericPoints Z, f.base z = x ∧ codim (closure {x}) = r) :
    (closedSubschemeFundamentalCycle f r : AlgebraicCycle X ℤ) x = 0 :=
  closedSubschemeFundamentalCycleCoeff_eq_zero f r hx

end Hartshorne
