/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.ImmersionConormalIndependence
import Hartshorne.Scheme.Differentials.NonsingularClosedImmersionConormal
import Hartshorne.Scheme.Differentials.TangentSheaf

/-!
# Normal and conormal sheaves

Hartshorne, *Algebraic Geometry*, II.8, definitions of the conormal and normal sheaves (p. 182).

Let `Y` be a nonsingular closed subvariety of a nonsingular variety `X`, with ideal sheaf `J`.
The conormal sheaf is `N^*_{Y/X} = J/J²`, and the normal sheaf `N_{Y/X}` is its dual
`ℋom_{𝒪_Y}(N^*_{Y/X}, 𝒪_Y)`. The normal sheaf is locally free of rank `codim (Y, X)`.

As a sheaf on `Y`, the conormal sheaf of an immersion is `immersionConormalSheaf`. For a closed
immersion `i : Y ⟶ X` with ideal sheaf `J`, it is identified with `i^* J`
(`Hartshorne.immersionConormalSheafIso`), and its pushforward with `J/J²`
(`Hartshorne.immersionConormalSheafPushforwardIso`). The normal sheaf is the dual
`Hartshorne.normalSheaf`.

When `X` and `Y` are nonsingular, Theorem II.8.17 makes `i^* J`, hence the conormal sheaf, locally
free of rank `r = codim (Y, X)` (`Hartshorne.immersionConormalSheaf_isLocallyFreeOfRank`). The
dual of a sheaf locally free of rank `r` is locally free of rank `r`, so the normal sheaf is too
(`Hartshorne.normalSheaf_isLocallyFreeOfRank`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Hartshorne

section Immersion

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [IsImmersion f]

/-- For an immersion `f : Z ⟶ X`, the conormal sheaf `N^*_f`, defined through the closed immersion
`f.liftCoborder` into the open subscheme `f.coborderRange`, is `f^* I_f`, for the ideal sheaf
`I_f` of `f` itself. -/
noncomputable def immersionConormalSheafIso :
    immersionConormalSheaf f ≅
      (Scheme.Modules.pullback f).obj (closedImmersionIdealSheaf f) :=
  ConormalIndependence.conormalRestrictIso f.liftCoborder f.coborderRange.ι ≪≫
    eqToIso (congrArg ConormalIndependence.conormalOf f.liftCoborder_ι)

/-- **Hartshorne II.8 (p. 182).** The normal sheaf `N_f = ℋom_{𝒪_Z}(N^*_f, 𝒪_Z)` of an immersion
`f : Z ⟶ X`: the dual of the conormal sheaf `N^*_f`. Hartshorne defines it for a nonsingular
closed subvariety of a nonsingular variety; the definition makes sense for any immersion. -/
noncomputable def normalSheaf : Z.Modules :=
  Ringed.moduleSheafDual (R := Z.sheaf) (immersionConormalSheaf f)

end Immersion

section ClosedImmersion

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- **Hartshorne II.8 (p. 182).** For a closed immersion `i : Y ⟶ X` with ideal sheaf `J`, the
conormal sheaf is `J/J²`: the pushforward `i_* N^*_{Y/X}` is isomorphic to `J/J²`. Hartshorne
defines it for a nonsingular closed subvariety; this holds for any closed immersion. -/
noncomputable def immersionConormalSheafPushforwardIso :
    (Scheme.Modules.pushforward i).obj (immersionConormalSheaf i) ≅ idealSheafSqQuotient i :=
  (Scheme.Modules.pushforward i).mapIso (immersionConormalSheafIso i) ≪≫
    (@asIso _ _ _ _ (idealSheafSqQuotientToPushforward i)
      (isIso_idealSheafSqQuotientToPushforward i)).symm

variable {k : Type u} [Field k] [IsAlgClosed k] (p : X ⟶ Spec (.of k))

/-- Let `X` be a nonsingular variety over an algebraically closed field `k` and `i : Y ⟶ X` a
nonsingular irreducible closed subscheme with `r = codim (Y, X)`. Then the conormal sheaf
`N^*_{Y/X}` is locally free of rank `r` (Hartshorne II, Theorem 8.17). As in the formalization of
that theorem, `X` is irreducible, regular and of finite type over `k`, and `Y` is irreducible and
regular. -/
theorem immersionConormalSheaf_isLocallyFreeOfRank (hp : FiniteType p) [IrreducibleSpace X]
    (hX : X.IsRegular) [IrreducibleSpace Y] (hY : Y.IsRegular) (r : ℕ)
    (hr : codim (Set.range i.base) = r) :
    (immersionConormalSheaf i).IsLocallyFreeOfRank r := by
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ :=
    (NonsingularConormal.nonsingular_closedImmersion_conormal p i hp hX hY r hr).2.1 y
  exact ⟨U, hy, ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso (immersionConormalSheafIso i) ≪≫ e⟩⟩

/-- **Hartshorne II.8 (p. 182).** Let `X` be a nonsingular variety over an algebraically closed
field `k` and `i : Y ⟶ X` a nonsingular irreducible closed subscheme with `r = codim (Y, X)`. Then
the normal sheaf `N_{Y/X}` is locally free of rank `r`. Here `X` is irreducible, regular and of
finite type over `k`, and `Y` is irreducible and regular; separatedness is not used. -/
theorem normalSheaf_isLocallyFreeOfRank (hp : FiniteType p) [IrreducibleSpace X]
    (hX : X.IsRegular) [IrreducibleSpace Y] (hY : Y.IsRegular) (r : ℕ)
    (hr : codim (Set.range i.base) = r) :
    (normalSheaf i).IsLocallyFreeOfRank r := by
  have h := immersionConormalSheaf_isLocallyFreeOfRank i p hp hX hY r hr
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at h ⊢
  exact Ringed.IsLocallyFreeOfRank.moduleSheafDual h

end ClosedImmersion

end Hartshorne
