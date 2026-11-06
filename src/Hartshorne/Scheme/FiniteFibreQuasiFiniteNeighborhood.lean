/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceProper
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# A zero-dimensional fibre has a quasi-finite neighbourhood

Hartshorne, *Algebraic Geometry*, V.5, the neighbourhood step in the proof of
Theorem 5.2.

A zero-dimensional fibre of a finite-type morphism is discrete, so the morphism
is quasi-finite at each of its points. The quasi-finite locus is open, and a
closed morphism carries its closed complement to a closed set missing the base
point; the complement of that image is the required neighbourhood.
-/

noncomputable section

open CategoryTheory

namespace Hartshorne

open AlgebraicGeometry Topology

universe u

/-- A proper morphism whose fibre over `P` has Krull dimension at most zero is
locally quasi-finite over some open neighbourhood of `P`. No Noetherian
hypothesis is needed. -/
theorem exists_mem_locallyQuasiFinite_morphismRestrict_of_isProper
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsProper f] (P : X)
    (hP : topologicalKrullDim (f.fiber P) ≤ 0) :
    ∃ U : X.Opens, P ∈ U ∧ LocallyQuasiFinite (f ∣_ U) := by
  have hfib : ∀ x : Z, f x = P → f.QuasiFiniteAt x := by
    rintro x rfl
    have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
      inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))
    have : IsLocallyNoetherian (f.fiber (f x)) :=
      LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
    have : IsLocallyArtinian (f.fiber (f x)) := .of_topologicalKrullDim_le_zero hP
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
    exact isOpen_discrete _
  let C : Set X := f '' (f.quasiFiniteLocus : Set Z)ᶜ
  have hC : IsClosed C := f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl
  have hPC : P ∉ C := by
    rintro ⟨x, hx, hxP⟩
    exact hx (hfib x hxP)
  let U : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  refine ⟨U, hPC, ?_⟩
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  rintro x -
  rw [Scheme.Hom.mem_quasiFiniteLocus, ← Scheme.Hom.quasiFiniteAt_comp_iff (g := U.ι),
    morphismRestrict_ι, Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion]
  by_contra h
  exact x.2 ⟨_, h, rfl⟩

/-- Hartshorne V.5, neighbourhood step in Theorem 5.2: if a projective
finite-type morphism of Noetherian schemes has a zero-dimensional fibre over
`P`, then it is quasi-finite over some open neighbourhood of `P`. -/
theorem Projective.exists_mem_locallyQuasiFinite_morphismRestrict
    {Z X : Scheme.{u}} [IsNoetherian Z] [IsNoetherian X]
    {f : Z ⟶ X} (hf : Projective f) [LocallyOfFiniteType f] (P : X)
    (hP : topologicalKrullDim (f.fiber P) = 0) :
    ∃ U : X.Opens, P ∈ U ∧ LocallyQuasiFinite (f ∣_ U) := by
  have : IsProper f := Projective.isProper hf
  exact exists_mem_locallyQuasiFinite_morphismRestrict_of_isProper f P hP.le

end Hartshorne
