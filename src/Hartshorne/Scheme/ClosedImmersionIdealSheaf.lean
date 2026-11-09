/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.QcqsPushforwardQuasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Hartshorne.Scheme.CoherentPushforwardCounterexample
import Hartshorne.Cohomology.QuasicoherentCoherentSubobjects

/-!
# Ideal sheaves of closed immersions

Hartshorne, *Algebraic Geometry*, II, Proposition 5.9 (pp. 115–116), forward direction.

For a closed immersion `i : Y ⟶ X`, the ideal sheaf `I_Y` is the kernel of the morphism
`𝒪_X ⟶ i_* 𝒪_Y` of `𝒪_X`-modules (`Hartshorne.closedImmersionIdealSheaf`), a subsheaf of `𝒪_X`
through `Hartshorne.closedImmersionIdealSheafι`. It is quasi-coherent
(`Hartshorne.isQuasicoherent_closedImmersionIdealSheaf`): `i` is quasi-compact and separated, so
`i_* 𝒪_Y` is quasi-coherent (Proposition 5.8(c)), and kernels of morphisms of quasi-coherent
modules are quasi-coherent (Proposition 5.7). If `X` is Noetherian it is coherent
(`Hartshorne.isCoherent_closedImmersionIdealSheaf`): on an affine open `Spec A` it is the sheaf
associated to an ideal of the Noetherian ring `A`, a finitely generated `A`-module.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace Hartshorne

variable {X Y : Scheme.{u}}

namespace ClosedImmersionIdeal

open QuasicoherentAbelianAux

/-- The structure sheaf is quasi-coherent. -/
lemma isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := by
  refine (isQuasicoherent_iff_forall_essImage _).mpr fun U ↦ ?_
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  exact ⟨ModuleCat.of Γ(X, (U : X.Opens)) Γ(X, (U : X.Opens)),
    ⟨tildeSelf ≪≫ (Scheme.Modules.restrictUnitIso U.2.fromSpec).symm⟩⟩

end ClosedImmersionIdeal

open ClosedImmersionIdeal

/-- The morphism `𝒪_X ⟶ i_* 𝒪_Y` of `𝒪_X`-modules given by `i^# : 𝒪_X → i_* 𝒪_Y`. -/
noncomputable def structureSheafToPushforward (i : Y ⟶ X) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

/-- **The ideal sheaf of a closed immersion** `i : Y ⟶ X` (Hartshorne II.5, p. 115):
`I_Y = ker (𝒪_X ⟶ i_* 𝒪_Y)`. -/
noncomputable def closedImmersionIdealSheaf (i : Y ⟶ X) : X.Modules :=
  kernel (structureSheafToPushforward i)

/-- The inclusion of the ideal sheaf `I_Y` into `𝒪_X`, a monomorphism of `𝒪_X`-modules. -/
noncomputable def closedImmersionIdealSheafι (i : Y ⟶ X) :
    closedImmersionIdealSheaf i ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  kernel.ι (structureSheafToPushforward i)

instance (i : Y ⟶ X) : Mono (closedImmersionIdealSheafι i) := by
  unfold closedImmersionIdealSheafι
  exact equalizer.ι_mono

/-- **Hartshorne II, Proposition 5.9 (forward direction).** The ideal sheaf of a closed immersion
is quasi-coherent. -/
theorem isQuasicoherent_closedImmersionIdealSheaf (i : Y ⟶ X) [IsClosedImmersion i] :
    (closedImmersionIdealSheaf i).IsQuasicoherent := by
  have := isQuasicoherent_unit X
  have := isQuasicoherent_unit Y
  have : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward i (Or.inr ⟨inferInstance, inferInstance⟩) _
  exact isQuasicoherent_kernel _

/-- **Hartshorne II, Proposition 5.9 (forward direction).** If `X` is Noetherian, the ideal sheaf
of a closed immersion into `X` is coherent. -/
theorem isCoherent_closedImmersionIdealSheaf (i : Y ⟶ X) [IsClosedImmersion i]
    [IsNoetherian X] : IsCoherent (closedImmersionIdealSheaf i) := by
  have := isQuasicoherent_unit Y
  have : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Y.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward i (Or.inr ⟨inferInstance, inferInstance⟩) _
  exact isCoherent_kernel_of_isQuasicoherent _ (isCoherent_structureSheafModule X)

end Hartshorne
