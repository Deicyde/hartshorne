/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Tilde under affine change of rings

Hartshorne, *Algebraic Geometry*, Proposition II.5.2(d,e).

Let `φ : R ⟶ S` be a morphism of commutative rings and `f = Spec.map φ : Spec S ⟶ Spec R`.

* `tildePushforwardIso φ` is the natural isomorphism `f_* Ñ ≅ (N_R)~` for `S`-modules `N`,
  where `N_R` is `N` viewed as an `R`-module by restriction of scalars.
* `tildePullbackIso φ` is the natural isomorphism `f^* M̃ ≅ (S ⊗_R M)~` for `R`-modules `M`.

Both rest on `pushforwardSpecΓIso φ`, the natural `R`-linear identification of the global
sections of `f_* F` with the global sections of `F` viewed as an `R`-module, valid for every
`𝒪_{Spec S}`-module `F`. For (d), the pushforward of `Ñ` is again of the form `Γ(-)~` (Mathlib's
`isIso_fromTildeΓ_pushforward`, which is the check on principal opens); for (e), both sides are left
adjoints of the two sides of `pushforwardSpecΓIso φ`, so they are isomorphic by uniqueness of
adjoints.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- For `φ : R ⟶ S` and an `𝒪_{Spec S}`-module `F`, the global sections of the pushforward
`(Spec.map φ)_* F`, as an `R`-module, are the global sections of `F` with `R` acting through `φ`;
natural in `F`. -/
noncomputable def pushforwardSpecΓIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤))

/-- **Hartshorne, Proposition II.5.2(d).** For `φ : R ⟶ S` and `f = Spec.map φ`, the natural
isomorphism `f_* Ñ ≅ (N_R)~` of `𝒪_{Spec R}`-modules, for `S`-modules `N`, where `N_R` is the
restriction of scalars of `N` along `φ`. -/
noncomputable def tildePushforwardIso :
    tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ) ≅
      ModuleCat.restrictScalars.{u} φ.hom ⋙ tilde.functor R :=
  haveI : IsIso (Functor.whiskerLeft (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ))
      (Scheme.Modules.fromTildeΓNatTrans (R := R))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro N
    exact isIso_fromTildeΓ_pushforward φ (tilde N)
  (asIso (Functor.whiskerLeft (tilde.functor S ⋙ Scheme.Modules.pushforward (Spec.map φ))
      (Scheme.Modules.fromTildeΓNatTrans (R := R)))).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (pushforwardSpecΓIso φ) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (tilde.toTildeΓNatIso (R := S)).symm _ ≪≫ Functor.leftUnitor _)
      (tilde.functor R)

/-- **Hartshorne, Proposition II.5.2(e).** For `φ : R ⟶ S` and `f = Spec.map φ`, the natural
isomorphism `f^* M̃ ≅ (S ⊗_R M)~` of `𝒪_{Spec S}`-modules, for `R`-modules `M`, where
`S ⊗_R M` is the extension of scalars of `M` along `φ`. -/
noncomputable def tildePullbackIso :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars.{u} φ.hom ⋙ tilde.functor S :=
  (conjugateIsoEquiv ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction)
    (tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)))).symm
    (pushforwardSpecΓIso φ).symm

end Hartshorne
