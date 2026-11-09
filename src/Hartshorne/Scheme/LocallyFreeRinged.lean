/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.LocallyFree
import Hartshorne.RingedSpace.LocallyFreeRank
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

The stalks of the structure sheaf of a scheme are local rings, hence nonzero, so the rank of a
module at a point (`Scheme.Modules.rankAt`) agrees with its rank as a module on the ringed space
(`Hartshorne.Ringed.rankAt`; `rankAt_eq_ringed`), and the ringed-space theorems on the rank
apply to schemes.

The comparisons used by the rank theorems (`nonempty_restrict_iso_free_iff`,
`isLocallyFree_iff_ringed`, `rankAt_eq_ringed`) live in `Hartshorne.Scheme.LocallyFreeInvertible`,
where the scheme rank theorems are derived from the ringed-space ones; this file adds the rest.
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

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
