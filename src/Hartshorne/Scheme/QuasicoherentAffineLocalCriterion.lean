/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The affine-local criterion for quasi-coherence

An `𝒪_X`-module is quasi-coherent exactly when it is associated to a module on an
affine open cover, and exactly when this holds canonically on every affine open.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

private abbrev affineSpecRestriction {X : Scheme.{u}} (F : X.Modules)
    (U : X.affineOpens) : (Spec Γ(X, (U : X.Opens))).Modules :=
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  F.restrict U.2.fromSpec

/-- An `𝒪_X`-module is associated to a module on the members of some affine open cover. -/
def HasAffineTildeCover {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∃ (ι : Type u) (U : ι → X.affineOpens),
    (⨆ i, (U i : X.Opens)) = ⊤ ∧
      ∀ i, (tilde.functor Γ(X, (U i : X.Opens))).essImage
        (affineSpecRestriction F (U i))

/-- On every affine open, the canonical map from the tilde of global sections to the
restriction of `F` is an isomorphism. -/
def IsTildeOnEveryAffineOpen {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ U : X.affineOpens, IsIso (affineSpecRestriction F U).fromTildeΓ

private noncomputable def presentationOfEssImage
    {X : Scheme.{u}} (F : X.Modules) (U : X.affineOpens)
    (h : (tilde.functor Γ(X, (U : X.Opens))).essImage
      (affineSpecRestriction F U)) :
    (affineSpecRestriction F U).Presentation := by
  let M := h.choose
  let e := h.choose_spec.some
  refine @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    e.hom e.isIso_hom ?_
  exact presentationTilde M .univ (by simp) _ (Submodule.span_eq _)

private noncomputable def presentationRestrictAffineOpen
    {X : Scheme.{u}} (F : X.Modules) (U : X.affineOpens)
    (h : (tilde.functor Γ(X, (U : X.Opens))).essImage
      (affineSpecRestriction F U)) :
    (F.restrict (U : X.Opens).ι).Presentation := by
  letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let P := presentationOfEssImage F U h
  let Q := Scheme.Modules.presentationRestrict U.2.isoSpec.hom P
  let e : (affineSpecRestriction F U).restrict U.2.isoSpec.hom ≅
      F.restrict (U : X.Opens).ι :=
    ((Scheme.Modules.restrictFunctorComp U.2.isoSpec.hom U.2.fromSpec).app F).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr U.2.isoSpec_hom_fromSpec).app F
  exact @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    e.hom e.isIso_hom Q

private noncomputable def presentationOverOfEssImage
    {X : Scheme.{u}} (F : X.Modules) (U : X.affineOpens)
    (h : (tilde.functor Γ(X, (U : X.Opens))).essImage
      (affineSpecRestriction F U)) :
    (F.over (U : X.Opens)).Presentation := by
  let P := presentationRestrictAffineOpen F U h
  let Q := @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ P
    (Scheme.Modules.overEquiv (U : X.Opens)).inverse
    ((Scheme.Modules.overEquiv (U : X.Opens)).symm.toAdjunction.leftAdjoint_preservesColimits)
    ((U : X.Opens).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm
  let e : F.over (U : X.Opens) ≅
      (Scheme.Modules.overEquiv (U : X.Opens)).inverse.obj
        (F.restrict (U : X.Opens).ι) :=
    (Scheme.Modules.overEquiv (U : X.Opens)).unitIso.app
      (F.over (U : X.Opens)) ≪≫
      (Scheme.Modules.overEquiv (U : X.Opens)).inverse.mapIso
        ((Scheme.Modules.overFunctorEquiv (U : X.Opens)).app F)
  letI : IsIso e.inv := e.isIso_inv
  exact SheafOfModules.Presentation.ofIsIso e.inv Q

/-- **Hartshorne II.5, Proposition 5.4.** For an `𝒪_X`-module, quasi-coherence,
being associated to modules on an affine open cover, and being canonically associated
to its sections on every affine open are equivalent. -/
theorem quasicoherent_affine_local_tfae
    {X : Scheme.{u}} (F : X.Modules) :
    List.TFAE
      [F.IsQuasicoherent,
        HasAffineTildeCover F,
        IsTildeOnEveryAffineOpen F] := by
  tfae_have 1 → 3 := by
    intro h
    change ∀ U : X.affineOpens, IsIso (affineSpecRestriction F U).fromTildeΓ
    intro U
    letI : F.IsQuasicoherent := h
    letI : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    exact (isQuasicoherent_iff_isIso_fromTildeΓ _).mp inferInstance
  tfae_have 3 → 2 := by
    intro h
    change ∀ U : X.affineOpens, IsIso (affineSpecRestriction F U).fromTildeΓ at h
    refine ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, ?_⟩
    intro U
    exact isIso_fromTildeΓ_iff.mp (h U)
  tfae_have 2 → 1 := by
    rintro ⟨ι, U, hU, h⟩
    have hU' : (Opens.grothendieckTopology X).CoversTop
        (fun i ↦ (U i : X.Opens)) := by
      rw [Opens.coversTop_iff, IsOpenCover]
      exact hU
    letI (i : ι) : (F.over (U i : X.Opens)).IsQuasicoherent :=
      (presentationOverOfEssImage F (U i) (h i)).isQuasicoherent
    exact SheafOfModules.IsQuasicoherent.of_coversTop F
      (fun i ↦ (U i : X.Opens)) hU'
  tfae_finish

end

end Hartshorne
