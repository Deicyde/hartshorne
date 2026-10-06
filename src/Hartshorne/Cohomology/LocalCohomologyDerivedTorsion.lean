/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Algebraic local cohomology as derived ideal-power torsion

Hartshorne, *Algebraic Geometry*, III, Exercise 3.3(a), p. 217.

For an ideal `a` of a commutative ring `A`, `idealPowerTorsionFunctor A a`
sends an `A`-module `M` to the submodule of elements annihilated by some
power of `a`. This functor is left exact. For a Noetherian ring, its right
derived functors define algebraic local cohomology.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Hartshorne

/-- The ideal-power torsion functor `M ↦ Γ_a(M)` on `A`-modules. -/
def idealPowerTorsionFunctor (A : Type u) [CommRing A] (a : Ideal A) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A where
  obj M := ModuleCat.of A (Ideal.primaryComponent M a)
  map f := ModuleCat.ofHom (Ideal.primaryComponent.map a f.hom)
  map_id M := by
    ext x
    rfl
  map_comp f g := by
    ext x
    rfl

instance idealPowerTorsionFunctor_additive (A : Type u) [CommRing A] (a : Ideal A) :
    (idealPowerTorsionFunctor A a).Additive where
  map_add := by
    intro M N f g
    ext x
    rfl

private lemma idealPowerTorsion_exact_kernel
    (A : Type u) [CommRing A] (a : Ideal A)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    Function.Exact
      (Ideal.primaryComponent.map a f.hom.ker.subtype)
      (Ideal.primaryComponent.map a f.hom) := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    have hx' : x.1 ∈
        (Ideal.primaryComponent.map a f.hom).ker.map
          (Ideal.primaryComponent M a).subtype :=
      ⟨x, hx, rfl⟩
    rw [Ideal.primaryComponent.map_ker_eq a f.hom] at hx'
    rcases hx' with ⟨y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact y.1.2

private lemma idealPowerTorsion_preservesKernel
    (A : Type u) [CommRing A] (a : Ideal A)
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (idealPowerTorsionFunctor A a) := by
  apply preservesLimit_of_preserves_limit_cone (ModuleCat.kernelIsLimit f)
  apply (KernelFork.isLimitMapConeEquiv _ (idealPowerTorsionFunctor A a)).2
  exact ModuleCat.isLimitKernelFork _ _
    (idealPowerTorsion_exact_kernel A a f)
    (by
      intro x y h
      change Ideal.primaryComponent.map a f.hom.ker.subtype x =
        Ideal.primaryComponent.map a f.hom.ker.subtype y at h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      change f.hom.ker.subtype x.1 = f.hom.ker.subtype y.1 at h'
      exact f.hom.ker.subtype_injective h')

/-- Ideal-power torsion is left exact. -/
noncomputable instance idealPowerTorsionFunctor_preservesFiniteLimits
    (A : Type u) [CommRing A] (a : Ideal A) :
    PreservesFiniteLimits (idealPowerTorsionFunctor A a) := by
  letI : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (idealPowerTorsionFunctor A a) :=
    fun {_ _} f ↦ idealPowerTorsion_preservesKernel A a f
  exact Functor.preservesFiniteLimits_of_preservesKernels
    (idealPowerTorsionFunctor A a)

/-- The `i`-th algebraic local cohomology functor with support in `a`, defined
as the `i`-th right derived functor of ideal-power torsion. -/
noncomputable def localCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (a : Ideal A) (i : ℕ) : ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  (idealPowerTorsionFunctor A a).rightDerived i

/-- The `i`-th algebraic local cohomology module of `M` with support in `a`. -/
noncomputable abbrev localCohomologyObject
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (a : Ideal A) (i : ℕ) (M : ModuleCat.{u} A) : ModuleCat.{u} A :=
  (localCohomology A a i).obj M

/-- Degree-zero local cohomology is ideal-power torsion. -/
noncomputable def localCohomologyZeroIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) :
    localCohomology A a 0 ≅ idealPowerTorsionFunctor A a :=
  Functor.rightDerivedZeroIsoSelf _

end Hartshorne
