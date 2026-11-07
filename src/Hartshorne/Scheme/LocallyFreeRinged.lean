/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.LocallyFree
import Hartshorne.Scheme.LocallyFreeInvertible

/-!
# Locally free modules on a scheme, as on a ringed space

For a scheme `X`, an `𝒪_X`-module `F : X.Modules` is also a module over the ringed space
`(X, 𝒪_X)`, with `R := X.sheaf`. Its restriction to an open `U` is either the module
`F.restrict U.ι` on the open subscheme `U` (the phrasing of `Scheme.Modules.IsLocallyFree`) or
the module `F.over U` on the opens contained in `U` (the phrasing of
`Hartshorne.Ringed.IsLocallyFree`). Mathlib's equivalence `Scheme.Modules.overEquiv U`
identifies the two (`Scheme.Modules.overFunctorEquiv`) and preserves free modules, so the scheme
and ringed-space notions of locally free, locally free of rank `r` and invertible agree. On a
scheme, locally free of finite rank means locally free with finite rank at every point.
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The equivalence `Scheme.Modules.overEquiv U` takes free modules to free modules. -/
noncomputable def overEquivFreeIso (U : X.Opens) (I : Type u) :
    (SheafOfModules.free I : (U : Scheme.{u}).Modules) ≅
      (overEquiv U).functor.obj (SheafOfModules.free I) :=
  let G : SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤
      SheafOfModules.{u} (U : Scheme.{u}).ringCatSheaf :=
    (overEquiv U).functor
  have : PreservesColimitsOfShape (Discrete I) G :=
    (overEquiv U).toAdjunction.leftAdjoint_preservesColimits.{u, u}.preservesColimitsOfShape
  SheafOfModules.mapFreeIso G I (Iso.refl _)

/-- The restriction of `F` to the open subscheme `U` is free on `I` exactly when its
restriction to the opens contained in `U` is. -/
theorem nonempty_restrict_iso_free_iff (F : X.Modules) (U : X.Opens) (I : Type u) :
    Nonempty (F.restrict U.ι ≅ SheafOfModules.free I) ↔
      Nonempty (F.over U ≅ SheafOfModules.free I) := by
  let e := overEquiv U
  let c : e.functor.obj (F.over U) ≅ F.restrict U.ι := (overFunctorEquiv U).app F
  constructor
  · rintro ⟨α⟩
    exact ⟨e.fullyFaithfulFunctor.preimageIso (c ≪≫ α ≪≫ overEquivFreeIso U I)⟩
  · rintro ⟨β⟩
    exact ⟨c.symm ≪≫ e.functor.mapIso β ≪≫ (overEquivFreeIso U I).symm⟩

/-- On a scheme, locally free in the ringed-space sense agrees with locally free in the scheme
sense. -/
theorem isLocallyFree_iff_ringed (F : X.Modules) :
    F.IsLocallyFree ↔ Hartshorne.Ringed.IsLocallyFree (R := X.sheaf) F := by
  refine forall_congr' fun x => exists_congr fun U => and_congr_right fun _ => ?_
  exact exists_congr fun I => nonempty_restrict_iso_free_iff F U I

/-- On a scheme, locally free of rank `r` in the ringed-space sense agrees with the scheme
notion. -/
theorem isLocallyFreeOfRank_iff_ringed (F : X.Modules) (r : ℕ) :
    F.IsLocallyFreeOfRank r ↔ Hartshorne.Ringed.IsLocallyFreeOfRank (R := X.sheaf) F r := by
  refine forall_congr' fun x => exists_congr fun U => and_congr_right fun _ => ?_
  exact nonempty_restrict_iso_free_iff F U _

/-- On a scheme, invertible in the ringed-space sense agrees with the scheme notion. -/
theorem isInvertible_iff_ringed (F : X.Modules) :
    F.IsInvertible ↔ Hartshorne.Ringed.IsInvertible (R := X.sheaf) F :=
  isLocallyFreeOfRank_iff_ringed F 1

/-- On a scheme, a module is locally free of finite rank exactly when it is locally free with
finite rank at every point. -/
theorem isFiniteLocallyFree_iff (F : X.Modules) :
    Hartshorne.Ringed.IsFiniteLocallyFree (R := X.sheaf) F ↔
      F.IsLocallyFree ∧ ∀ x : X, F.rankAt x < Cardinal.aleph0 := by
  constructor
  · intro hF
    refine ⟨(isLocallyFree_iff_ringed F).mpr hF.isLocallyFree, fun x => ?_⟩
    obtain ⟨U, hxU, r, hU⟩ := hF x
    obtain ⟨α⟩ := (nonempty_restrict_iso_free_iff F U _).mpr hU
    rw [F.rankAt_eq α hxU]
    exact Cardinal.lt_aleph0_of_finite _
  · rintro ⟨hF, hfin⟩ x
    obtain ⟨U, hxU, I, ⟨α⟩⟩ := hF x
    have hI : Finite I := by
      have := hfin x
      rw [F.rankAt_eq α hxU] at this
      exact Cardinal.lt_aleph0_iff_finite.mp this
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
    refine ⟨U, hxU, n, (nonempty_restrict_iso_free_iff F U _).mp
      ⟨α ≪≫ SheafOfModules.freeFunctor.mapIso (e.trans Equiv.ulift.symm).toIso⟩⟩

end AlgebraicGeometry.Scheme.Modules
