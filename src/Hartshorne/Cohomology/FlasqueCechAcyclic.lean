/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AcyclicResolutionComparison
import Hartshorne.Cohomology.CechDerivedComparison
import Hartshorne.Cohomology.SheafCohomologyFlasque

/-!
# Flasque sheaves are Čech-acyclic

Hartshorne, *Algebraic Geometry*, III, Proposition 4.3 (p. 221).

If `F` is a flasque abelian sheaf on `X`, then `Ȟ^p(U, F) = 0` for every open cover `U` of `X`
and every `p > 0` (`Hartshorne.orderedCechCohomology_isZero_of_isFlasque`).

## Proof

The terms `𝒞^p(U, F)` of the sheafified Čech resolution have sections
`∏_a F(V ∩ U_a)` over `V`, with componentwise restriction maps; these are surjective when `F` is
flasque, so every `𝒞^p(U, F)` is flasque
(`Hartshorne.SheafifiedCech.isFlasque_cochainSheaf`). Flasque sheaves are acyclic, so the
resolution `F → 𝒞^•(U, F)` computes `H^p(X, F)` after taking global sections, which give the
ordered Čech complex `C^•(U, F)`. Hence `Ȟ^p(U, F) ≅ H^p(X, F)`
(`Hartshorne.flasqueCechIso`), and the right side vanishes for `p > 0`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Hartshorne

universe u

variable {X : TopCat.{u}} {ι : Type u} [LinearOrder ι]

namespace SheafifiedCech

/-- If `F` is flasque, then every term `𝒞^p(U, F)` of the sheafified Čech complex is flasque:
its restriction maps are products of restriction maps of `F`. -/
instance isFlasque_cochainSheaf (U : ι → Opens X) (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFlasque]
    (p : ℕ) : (cochainSheaf U F p).IsFlasque where
  epi {V W} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    have hsurj : ∀ a : OrderedCechIndex ι p, Function.Surjective
        (F.presheaf.map (homOfLE (intersection_mono
          (fun j ↦ inf_le_inf_right (U j) i.unop.le) a)).op) := fun a ↦
      (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
    exact ⟨fun a ↦ (hsurj a (t a)).choose, funext fun a ↦ (hsurj a (t a)).choose_spec⟩

end SheafifiedCech

/-- For a flasque abelian sheaf `F` and an open cover `U`, ordered Čech cohomology computes sheaf
cohomology: `H^p(X, F) ≅ Ȟ^p(U, F)`, via the sheafified Čech resolution, which is a flasque
resolution. -/
def flasqueCechIso (U : ι → Opens X) (hU : IsOpenCover U) (F : X.Sheaf AddCommGrpCat.{u})
    [F.IsFlasque] (p : ℕ) :
    (sheafCohomology X p).obj F ≅ orderedCechCohomology U F p :=
  haveI := SheafifiedCech.quasiIso_augmentationHom U hU F
  acyclicResolutionIso (sheafSectionsOver (X := X) ⊤) (SheafifiedCech.augmentationHom U F)
      (fun i ↦ isRightAcyclic_sheafSectionsOver_top_of_isFlasque
        (SheafifiedCech.cochainSheaf U F i)) p ≪≫
    HomologicalComplex.homologyMapIso (CechDerivedComparison.globalSectionsIso U F) p

/-- **Flasque sheaves are Čech-acyclic** (Hartshorne III, Proposition 4.3). If `F` is a flasque
abelian sheaf on `X`, then `Ȟ^p(U, F) = 0` for every open cover `U` of `X` and every `p > 0`. -/
theorem orderedCechCohomology_isZero_of_isFlasque (U : ι → Opens X) (hU : IsOpenCover U)
    (F : X.Sheaf AddCommGrpCat.{u}) [F.IsFlasque] (p : ℕ) (hp : 0 < p) :
    IsZero (orderedCechCohomology U F p) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  exact (sheafCohomology_isZero_of_isFlasque F n).of_iso (flasqueCechIso U hU F (n + 1)).symm

end Hartshorne
