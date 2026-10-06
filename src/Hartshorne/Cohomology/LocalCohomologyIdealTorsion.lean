/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.LocalCohomologyDerivedTorsion

/-!
# Local cohomology is ideal-power torsion

Hartshorne, *Algebraic Geometry*, III, Exercise 3.3(c), p. 217.

Every element of algebraic local cohomology is annihilated by some power of
the supporting ideal. This follows by computing the derived functor on an
injective resolution: the terms are ideal-power torsion, and this property is
preserved by taking submodules and quotients.
-/

noncomputable section

open CategoryTheory

universe u

namespace Hartshorne

private lemma primaryComponent_eq_top_of_injective
    {A M N : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (a : Ideal A) (f : M →ₗ[A] N) (hf : Function.Injective f)
    (hN : Ideal.primaryComponent N a = ⊤) :
    Ideal.primaryComponent M a = ⊤ := by
  rw [eq_top_iff]
  intro x _
  apply (Ideal.primaryComponent_mem M a x).mpr
  have hfx : f x ∈ Ideal.primaryComponent N a := by
    rw [hN]
    trivial
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem N a (f x)).mp hfx
  refine ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff] at hn ⊢
  intro r
  apply hf
  simpa only [map_smul, map_zero] using hn r

private lemma primaryComponent_eq_top_of_surjective
    {A M N : Type u} [CommRing A]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (a : Ideal A) (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hM : Ideal.primaryComponent M a = ⊤) :
    Ideal.primaryComponent N a = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  simpa using Ideal.primaryComponent_map_mem a f
    ⟨x, by rw [hM]; trivial⟩

private lemma primaryComponent_primaryComponent_eq_top
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (a : Ideal A) :
    Ideal.primaryComponent (Ideal.primaryComponent M a) a = ⊤ := by
  rw [eq_top_iff]
  intro x _
  apply (Ideal.primaryComponent_mem (Ideal.primaryComponent M a) a x).mpr
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M a x.1).mp x.2
  refine ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff] at hn ⊢
  intro r
  apply Subtype.ext
  exact hn r

/-- Every algebraic local cohomology module is ideal-power torsion. -/
theorem localCohomology_primaryComponent_eq_top
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (a : Ideal A) (i : ℕ) (M : ModuleCat.{u} A) :
    Ideal.primaryComponent (localCohomologyObject A a i M) a = ⊤ := by
  let F := idealPowerTorsionFunctor A a
  let P := injectiveResolution M
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.cocomplex
  let e : (F.rightDerived i).obj M ≅ K.homology i :=
    P.isoRightDerivedObj F i
  have hKX : Ideal.primaryComponent (K.X i) a = ⊤ := by
    change Ideal.primaryComponent
      (Ideal.primaryComponent (P.cocomplex.X i) a) a = ⊤
    exact primaryComponent_primaryComponent_eq_top a
  have hcycles : Ideal.primaryComponent (K.cycles i) a = ⊤ :=
    primaryComponent_eq_top_of_injective a (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance) hKX
  have hhomology : Ideal.primaryComponent (K.homology i) a = ⊤ :=
    primaryComponent_eq_top_of_surjective a (K.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance) hcycles
  change Ideal.primaryComponent ((F.rightDerived i).obj M) a = ⊤
  exact primaryComponent_eq_top_of_surjective a e.inv.hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) hhomology

/-- Elementwise form: every local cohomology class is annihilated by some
power of the supporting ideal. -/
theorem localCohomology_mem_primaryComponent
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (a : Ideal A) (i : ℕ) (M : ModuleCat.{u} A)
    (x : localCohomologyObject A a i M) :
    x ∈ Ideal.primaryComponent (localCohomologyObject A a i M) a := by
  rw [localCohomology_primaryComponent_eq_top]
  trivial

end Hartshorne
