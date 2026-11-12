/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleSheafDualExact
import Hartshorne.Scheme.Differentials.NormalConormalSheaves

/-!
# The tangent-normal exact sequence

Hartshorne, *Algebraic Geometry*, II.8, the exact sequence of tangent and normal sheaves (p. 182).

For a nonsingular closed subvariety `Y` of a nonsingular variety `X`, dualizing the conormal
sequence `0 ⟶ J/J² ⟶ Ω_X ⊗ 𝒪_Y ⟶ Ω_Y ⟶ 0` (Theorem II.8.17) gives a short exact sequence
`0 ⟶ T_Y ⟶ T_X|_Y ⟶ N_{Y/X} ⟶ 0`.

* `Hartshorne.tangentNormal_shortExact`: the tangent-normal sequence
  `0 ⟶ T_Y ⟶ (i^* Ω_X)^∨ ⟶ N_{Y/X} ⟶ 0`. The conormal sequence is short exact by
  Theorem II.8.17 and `Ω_Y` is locally free of finite rank by Theorem II.8.15, so its dual is short
  exact (`Hartshorne.Ringed.dualShortComplex_shortExact`).

The middle term is the dual `(i^* Ω_{X/k})^∨` of `Ω_{X/k} ⊗ 𝒪_Y = i^* Ω_{X/k}`. Hartshorne writes
it `T_X|_Y = i^* T_X`; the two agree because pullback commutes with duals of finite locally free
modules, which is not formalized here.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Hartshorne

section TangentNormal

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (i : Y ⟶ X) [IsClosedImmersion i]

/-- The map `T_Y ⟶ (i^* Ω_{X/k})^∨` dual to the map `i^* Ω_{X/k} ⟶ Ω_{Y/k}` of the conormal
sequence. -/
noncomputable def tangentToPullbackDual :
    tangentSheaf (i ≫ p) ⟶
      Ringed.moduleSheafDual (R := Y.sheaf) ((Scheme.Modules.pullback i).obj
        (Scheme.relativeDifferentials p)) :=
  (Ringed.moduleSheafHomPrecomp (R := Y.sheaf) (Scheme.pullbackRelativeDifferentialsToComp i p)).app
    (Ringed.structureModule Y.sheaf)

/-- The map `(i^* Ω_{X/k})^∨ ⟶ N_{Y/X}` dual to the map `N^*_{Y/X} ⟶ i^* Ω_{X/k}` of the
conormal sequence, with `N^*_{Y/X}` identified with `i^* J`
(`Hartshorne.immersionConormalSheafIso`). -/
noncomputable def pullbackDualToNormal :
    Ringed.moduleSheafDual (R := Y.sheaf) ((Scheme.Modules.pullback i).obj
        (Scheme.relativeDifferentials p)) ⟶ normalSheaf i :=
  (Ringed.moduleSheafHomPrecomp (R := Y.sheaf) (ClosedConormal.conormalToPullback i p)).app
      (Ringed.structureModule Y.sheaf) ≫
    (Ringed.moduleSheafHomPrecomp (R := Y.sheaf) (immersionConormalSheafIso i).hom).app
      (Ringed.structureModule Y.sheaf)

lemma tangentToPullbackDual_comp_pullbackDualToNormal :
    tangentToPullbackDual p i ≫ pullbackDualToNormal p i = 0 := by
  have h := Ringed.moduleSheafHomPrecomp_g_comp_f (R := Y.sheaf)
    (S := ShortComplex.mk (ClosedConormal.conormalToPullback i p)
      (Scheme.pullbackRelativeDifferentialsToComp i p)
      (ClosedConormal.conormalToPullback_comp i p)) (Ringed.structureModule Y.sheaf)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h).trans zero_comp)

/-- The codimension of a nonempty closed subscheme of an integral scheme of finite type over a
field is finite. -/
private theorem exists_codim_range_eq (hp : FiniteType p) [IsIntegral X] [Nonempty Y] :
    ∃ r : ℕ, codim (Set.range i.base) = r := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  have := hp.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have hcod := codim_eq_iInf_ringKrullDim_stalk p hp
    (Set.range_nonempty_iff_nonempty.mpr ⟨y⟩) i.isClosedEmbedding.isClosed_range
  have hle : (codim (Set.range i.base) : WithBot ℕ∞) ≤
      ringKrullDim (X.presheaf.stalk (i.base y)) :=
    hcod ▸ iInf_le (fun P : Set.range i.base ↦ ringKrullDim (X.presheaf.stalk P.1))
      ⟨i.base y, y, rfl⟩
  have hne : codim (Set.range i.base) ≠ ⊤ := by
    intro htop
    rw [htop, WithBot.coe_top] at hle
    exact (lt_of_le_of_lt hle ringKrullDim_lt_top).false
  exact ⟨(codim (Set.range i.base)).toNat, (ENat.natCast_toNat hne).symm⟩

/-- **Hartshorne II.8 (p. 182), the tangent-normal sequence.** Let `X` be a nonsingular variety
over an algebraically closed field `k` and `i : Y ⟶ X` a nonsingular irreducible closed
subscheme. Dualizing the conormal sequence `0 ⟶ N^*_{Y/X} ⟶ i^* Ω_{X/k} ⟶ Ω_{Y/k} ⟶ 0`
(Theorem II.8.17) gives the short exact sequence `0 ⟶ T_Y ⟶ (i^* Ω_{X/k})^∨ ⟶ N_{Y/X} ⟶ 0`,
whose middle term is Hartshorne's `T_X|_Y`. As in the formalization of Theorem II.8.17, `X` is
irreducible, regular and of finite type over `k`, and `Y` is irreducible and regular;
separatedness is not used. -/
theorem tangentNormal_shortExact [IsAlgClosed k] (hp : FiniteType p) [IrreducibleSpace X]
    (hX : X.IsRegular) [IrreducibleSpace Y] (hY : Y.IsRegular) :
    (ShortComplex.mk (tangentToPullbackDual p i) (pullbackDualToNormal p i)
      (tangentToPullbackDual_comp_pullbackDualToNormal p i)).ShortExact := by
  have : IsIntegral X := isIntegral_of_isRegular hX
  have : IsIntegral Y := isIntegral_of_isRegular hY
  have := hp.1
  have := hp.2
  have hp' : FiniteType (i ≫ p) := ⟨inferInstance, inferInstance⟩
  obtain ⟨r, hr⟩ := exists_codim_range_eq p i hp
  obtain ⟨n, hn, -⟩ := exists_topologicalKrullDim_eq_trdeg (i ≫ p) hp'
  -- the conormal sequence is short exact (Theorem II.8.17)
  have hS := (NonsingularConormal.nonsingular_closedImmersion_conormal p i hp hX hY r hr).1
  -- `Ω_{Y/k}` is locally free of rank `dim Y` (Theorem II.8.15)
  have hΩ := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank (i ≫ p) hp' n hn).mp hY
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at hΩ
  have hdual := Ringed.dualShortComplex_shortExact hS hΩ.isFiniteLocallyFree
  refine ShortComplex.shortExact_of_iso ?_ hdual
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (((Ringed.moduleSheafHomBifunctor Y.sheaf).mapIso (immersionConormalSheafIso i).op).app
      (Ringed.structureModule Y.sheaf))
    (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
    (by exact Category.id_comp _)

end TangentNormal

end Hartshorne
