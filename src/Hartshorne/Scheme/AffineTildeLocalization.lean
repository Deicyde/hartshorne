/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Localization formulas for the affine tilde sheaf

For an `R`-module `M`, Mathlib's `AlgebraicGeometry.tilde M` is the
associated sheaf on `Spec R`.  This file records the three localization
isomorphisms of Hartshorne, Proposition II.5.1, with stable project names.
-/

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry PrimeSpectrum

universe u

/-- Sections of `M̃` over the principal open `D(f)` are the localization of
`M` away from `f`. -/
noncomputable def affineTildeBasicOpenIso
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    LocalizedModule.Away f M ≃ₗ[R]
      (modulesSpecToSheaf.obj (tilde M)).presheaf.obj
        (.op (basicOpen f)) :=
  IsLocalizedModule.iso (.powers f)
    (tilde.toOpen M (basicOpen f)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalk of `M̃` at a prime `p` is the localization of `M` at the
complement of `p`. -/
noncomputable def affineTildeStalkIso
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (p : PrimeSpectrum R) :
    LocalizedModule p.asIdeal.primeCompl M ≃ₗ[R]
      (tilde M).presheaf.stalk p :=
  IsLocalizedModule.iso p.asIdeal.primeCompl
    (tilde.toStalk M p).hom

/-- Global sections of `M̃` on `Spec R` recover `M`. -/
noncomputable def affineTildeGlobalSectionsIso
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    M ≅ (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (.op ⊤) :=
  tilde.isoTop M

/-- Localization preserves injectivity, so tilde preserves monomorphisms. -/
theorem affineTilde_map_mono
    {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] :
    Mono (tilde.map f) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t h
  apply Subtype.ext
  funext p
  let q : PrimeSpectrum R := p.1
  let : q.asIdeal.IsPrime := q.isPrime
  apply IsLocalizedModule.map_injective q.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap q.asIdeal.primeCompl N) f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
  exact congrArg (fun z => z.val p) h

/-- Tilde preserves finite limits, since it preserves monos and is right exact. -/
theorem affineTilde_preservesFiniteLimits (R : CommRingCat.{u}) :
    Limits.PreservesFiniteLimits (tilde.functor R) := by
  apply (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (tilde.functor R)).mpr
  intro S hS
  let : Mono S.f := hS.mono_f
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel (tilde.functor R)
    hS.epi_g (inferInstance), ?_⟩
  exact affineTilde_map_mono S.f

/-- The tilde functor preserves exact and short exact sequences, as well as finite limits
and colimits, hence kernels, images, and cokernels (Hartshorne II.5.2(a)). -/
theorem affineTilde_exact (R : CommRingCat.{u}) :
    (∀ S : ShortComplex (ModuleCat.{u} R),
      S.Exact → (S.map (tilde.functor R)).Exact) ∧
    (∀ S : ShortComplex (ModuleCat.{u} R),
      S.ShortExact → (S.map (tilde.functor R)).ShortExact) ∧
    Limits.PreservesFiniteLimits (tilde.functor R) ∧
    Limits.PreservesFiniteColimits (tilde.functor R) := by
  have h : Limits.PreservesFiniteLimits (tilde.functor R) ∧
      Limits.PreservesFiniteColimits (tilde.functor R) :=
    ⟨affineTilde_preservesFiniteLimits R, inferInstance⟩
  exact ⟨((Functor.exact_tfae (tilde.functor R)).out 3 1).mp h,
    ((Functor.exact_tfae (tilde.functor R)).out 3 0).mp h, h⟩

end Hartshorne
