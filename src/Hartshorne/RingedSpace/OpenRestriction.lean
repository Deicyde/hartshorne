/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ModuleSheafTensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-!
# Restriction of module sheaves to an open is pullback along the inclusion

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`, and let `U` be an open subset. The restriction `F|_U` of an `𝒪_X`-module is the
module sheaf `F.over U` on the opens contained in `U` (Mathlib's `SheafOfModules.overFunctor`).
Its right adjoint is the pushforward along the inclusion (`Hartshorne.Ringed.openPushforward`),
whose sections over an open `W` of `X` are the sections over `W ∩ U` (computed as the product
`U ⨯ W`); the adjunction is Mathlib's `SheafOfModules.overPushforwardOverAdj`
(`Hartshorne.Ringed.restrictionAdjunction`). Consequently restriction agrees with the
module-sheaf pullback along the inclusion (`Hartshorne.Ringed.overFunctorIsoPullback`).

We also record when the unit `F ⟶ j_*(F|_U)` is an isomorphism: exactly when the restriction
maps `F(W) → F(W ∩ U)` are bijective, i.e. when `F` is already determined by its sections inside
`U` (`Hartshorne.Ringed.isIso_restrictionAdjunction_unit_app`). This holds for example for the
pushforward of a module sheaf on an open contained in the preimage of `U`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The pushforward `j_*` along the inclusion of an open `U`, from module sheaves on the opens
contained in `U` to `𝒪_X`-modules: its sections over `W` are the sections over `U ⨯ W`. -/
noncomputable abbrev openPushforward (U : Opens X) :
    SheafOfModules.{u} ((ringCatSheafOf R).over U) ⥤ SheafOfModules.{u} (ringCatSheafOf R) :=
  SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := ringCatSheafOf R) U)

/-- **Restriction to an open is left adjoint to pushforward along the inclusion.** -/
noncomputable def restrictionAdjunction (U : Opens X) :
    SheafOfModules.overFunctor (ringCatSheafOf R) U ⊣ openPushforward (R := R) U :=
  SheafOfModules.overPushforwardOverAdj U

/-- The unit `F ⟶ j_*(F|_U)` is restriction from `W` to `U ⨯ W`, along the projection. -/
lemma restrictionAdjunction_unit_app_app (U : Opens X)
    (F : SheafOfModules.{u} (ringCatSheafOf R)) (W : (Opens X)ᵒᵖ) (x : F.val.presheaf.obj W) :
    ((PresheafOfModules.toPresheaf _).map ((restrictionAdjunction U).unit.app F).val).app W x =
      F.val.presheaf.map ((Over.forgetAdjStar U).counit.app W.unop).op x :=
  rfl

instance (U : Opens X) : (openPushforward (R := R) U).IsRightAdjoint :=
  (restrictionAdjunction U).isRightAdjoint

/-- **Restriction to an open is the pullback along the inclusion.** -/
noncomputable def overFunctorIsoPullback (U : Opens X) :
    SheafOfModules.overFunctor (ringCatSheafOf R) U ≅
      SheafOfModules.pullback (SheafOfModules.pushforwardOver (R := ringCatSheafOf R) U) :=
  (restrictionAdjunction U).leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction _)

/-- The unit `F ⟶ j_*(F|_U)` is an isomorphism when all restriction maps `F(W) → F(U ⨯ W)` are
bijective. -/
lemma isIso_restrictionAdjunction_unit_app (U : Opens X)
    (F : SheafOfModules.{u} (ringCatSheafOf R))
    (h : ∀ W : Opens X,
      Function.Bijective (F.val.presheaf.map ((Over.forgetAdjStar U).counit.app W).op)) :
    IsIso ((restrictionAdjunction U).unit.app F) := by
  have hS : ∀ S : Sheaf (Opens.grothendieckTopology X) RingCat.{u},
      (SheafOfModules.forget.{u} S).ReflectsIsomorphisms :=
    fun S => (SheafOfModules.fullyFaithfulForget S).reflectsIsomorphisms
  have := hS (ringCatSheafOf R)
  have : (SheafOfModules.forget (ringCatSheafOf R) ⋙
      PresheafOfModules.toPresheaf (ringCatSheafOf R).obj).ReflectsIsomorphisms :=
    reflectsIsomorphisms_comp _ _
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget (ringCatSheafOf R) ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro W
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (h W.unop)

end Ringed

end Hartshorne
