/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.PicardGroup
import Hartshorne.Scheme.ExteriorPerfectPairing
import Hartshorne.Scheme.LocallyFreeRinged
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular

/-!
# The canonical sheaf

Hartshorne, *Algebraic Geometry*, II.8, definition of the canonical sheaf (pp. 180–181).

For a scheme `X` over a field `k` and `n = dim X`, the canonical sheaf is the top exterior power
`ω_X = ⋀^n Ω_{X/k}` of the sheaf of relative differentials. On a nonsingular variety of dimension
`n`, `Ω_{X/k}` is locally free of rank `n` (Hartshorne II.8.15), so `ω_X` is invertible: the
exterior products of a local frame of a locally free module of rank `n` form a local frame of its
`r`-th exterior power, of size `n choose r`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

/-- The `r`-th exterior power of a module locally free of rank `n` on a ringed space is locally free
of rank `n choose r`. -/
theorem Ringed.IsLocallyFreeOfRank.moduleSheafExteriorPower {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
    {F : SheafOfModules.{u} (ringCatSheafOf R)} {n : ℕ} (hF : Ringed.IsLocallyFreeOfRank F n)
    (r : ℕ) : Ringed.IsLocallyFreeOfRank (moduleSheafExteriorPower r F) (n.choose r) := by
  classical
  intro x
  obtain ⟨U, hxU, ⟨α⟩⟩ := hF x
  have he := ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame F
    (Ringed.isLocalFrame_of_over_iso α) r
  have hcard : Fintype.card (ULift.{u} (Fin (n.choose r))) =
      Fintype.card (Set.powersetCard (ULift.{u} (Fin n)) r) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Set.powersetCard.card]
    simp
  exact ⟨U, hxU,
    Ringed.nonempty_over_iso_free_of_isLocalFrame (he.reindex (Fintype.equivOfCardEq hcard))⟩

/-- **Hartshorne II.8 (pp. 180–181).** The canonical sheaf `ω_X = ⋀^n Ω_{X/k}` of a scheme `X` over
a field `k`, for `n = dim X` (the dimension is a parameter here; the invertibility theorem
`Hartshorne.canonicalSheaf_isInvertible` takes `n = dim X` as a hypothesis). Hartshorne defines it
for a nonsingular variety; the definition makes sense for any `X` over `k`. -/
noncomputable def canonicalSheaf {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) : X.Modules :=
  moduleSheafExteriorPower (R := X.sheaf) n (Scheme.relativeDifferentials f)

/-- If `Ω_{X/k}` is locally free of rank `n`, then `⋀^n Ω_{X/k}` is invertible. -/
theorem canonicalSheaf_isInvertible_of_relativeDifferentials {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {n : ℕ}
    (h : (Scheme.relativeDifferentials f).IsLocallyFreeOfRank n) :
    (canonicalSheaf f n).IsInvertible := by
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at h
  rw [Scheme.Modules.isInvertible_iff_ringed]
  have := h.moduleSheafExteriorPower n
  rwa [Nat.choose_self] at this

/-- **Hartshorne II.8 (pp. 180–181).** On a nonsingular variety `X` of dimension `n` over an
algebraically closed field `k`, the canonical sheaf `ω_X = ⋀^n Ω_{X/k}` is invertible. Here `X` is
an irreducible regular scheme of finite type over `k`; separatedness is not used. -/
theorem canonicalSheaf_isInvertible {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IrreducibleSpace X] (hf : FiniteType f)
    (hX : X.IsRegular) (n : ℕ) (hn : topologicalKrullDim X = n) :
    (canonicalSheaf f n).IsInvertible :=
  canonicalSheaf_isInvertible_of_relativeDifferentials f
    ((isRegular_iff_relativeDifferentials_isLocallyFreeOfRank f hf n hn).mp hX)

end Hartshorne
