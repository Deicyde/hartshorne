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

end Hartshorne
