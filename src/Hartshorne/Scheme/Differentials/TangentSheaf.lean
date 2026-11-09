/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.PicardGroup
import Hartshorne.Scheme.LocallyFreeRinged
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular

/-!
# The tangent sheaf

Hartshorne, *Algebraic Geometry*, II.8, definition of the tangent sheaf (p. 180).

For a scheme `X` over a field `k`, the tangent sheaf is the dual
`T_X = ℋom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` of the sheaf of relative differentials. On a nonsingular variety
of dimension `n`, `Ω_{X/k}` is locally free of rank `n` (Hartshorne II.8.15), hence so is its
dual.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

/-- The dual of a module locally free of rank `r` on a ringed space is locally free of rank `r`:
the dual frame of a local frame is a local frame. -/
theorem Ringed.IsLocallyFreeOfRank.moduleSheafDual {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    {F : SheafOfModules.{u} (ringCatSheafOf R)} {r : ℕ} (hF : Ringed.IsLocallyFreeOfRank F r) :
    Ringed.IsLocallyFreeOfRank (Ringed.moduleSheafDual F) r := by
  classical
  intro x
  obtain ⟨U, hx, ⟨α⟩⟩ := hF x
  exact ⟨U, hx, Ringed.nonempty_over_iso_free_of_isLocalFrame
    (Ringed.isLocalFrame_of_over_iso α).dual⟩

/-- **Hartshorne II.8 (p. 180).** The tangent sheaf `T_X = ℋom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` of a scheme
`X` over a field `k`. Hartshorne defines it for a nonsingular variety; the definition makes sense
for any `X` over `k`. -/
noncomputable def tangentSheaf {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : X.Modules :=
  Ringed.moduleSheafDual (R := X.sheaf) (Scheme.relativeDifferentials f)

/-- If `Ω_{X/k}` is locally free of rank `n`, then so is the tangent sheaf. -/
theorem tangentSheaf_isLocallyFreeOfRank_of_relativeDifferentials {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ}
    (h : (Scheme.relativeDifferentials f).IsLocallyFreeOfRank n) :
    (tangentSheaf f).IsLocallyFreeOfRank n := by
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at h ⊢
  exact Ringed.IsLocallyFreeOfRank.moduleSheafDual h

/-- **Hartshorne II.8 (p. 180).** On a nonsingular variety `X` of dimension `n` over an
algebraically closed field `k`, the tangent sheaf is locally free of rank `n`. Here `X` is an
irreducible regular scheme of finite type over `k`; separatedness is not used. -/
theorem tangentSheaf_isLocallyFreeOfRank {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IrreducibleSpace X] (hf : FiniteType f)
    (hX : X.IsRegular) (n : ℕ) (hn : topologicalKrullDim X = n) :
    (tangentSheaf f).IsLocallyFreeOfRank n :=
  tangentSheaf_isLocallyFreeOfRank_of_relativeDifferentials f
    ((isRegular_iff_relativeDifferentials_isLocallyFreeOfRank f hf n hn).mp hX)

end Hartshorne
