/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeSpecModuleGluing
import Hartshorne.Cohomology.ChevalleyGenericFrame
import Hartshorne.Cohomology.Semicontinuity.CoherentFiberDimension

/-!
# Generic coherent pushforward approximation

Hartshorne, *Algebraic Geometry*, III, Exercise 4.2(b) (p. 223).

Let `f : X ⟶ Y` be a finite morphism of Noetherian schemes with `Y` integral, `M` a coherent
`𝒪_X`-module and `α : 𝒪_Y^r ⟶ f_* M` a morphism which is an isomorphism at the generic point `η`
of `Y`. For every coherent `𝒪_Y`-module `F` there are a coherent `𝒪_X`-module `G` and a morphism
`f_* G ⟶ F^r` which is an isomorphism at `η`.

## Construction

The module `G` corresponds to the sheaf `ℋom(f_* M, F)` with its `f_* 𝒪_X`-module structure. Over
an affine open `U ⊆ Y`, with `A = Γ(U, 𝒪_Y)` and `B = Γ(f⁻¹ U, 𝒪_X)`, it is the sheaf on
`f⁻¹ U = Spec B` associated to the `B`-module `Hom_A(M(f⁻¹ U), F(U))`, on which `b ∈ B` acts by
precomposition with multiplication by `b`. For a basic open `D(r) ⊆ U` restriction of
homomorphisms identifies `Hom_{A_r}(M(f⁻¹ U)_r, F(U)_r)` with the localization of
`Hom_A(M(f⁻¹ U), F(U))` at `r`, since `M(f⁻¹ U)` is finitely presented over the Noetherian ring
`A`. These modules glue over the relative spectrum `Spec_Y (f_* 𝒪_X) ≅ X`
(`Hartshorne.RelSpecModuleData`).

The global sections `mᵢ` of `f_* M` defining `α` give, over each affine `U`, the evaluation maps
`h ↦ h(mᵢ|_U) : Hom_A(M(f⁻¹ U), F(U)) ⟶ F(U)`; they glue to morphisms `f_* G ⟶ F`, whence
`f_* G ⟶ F^r`. Near `η` the `mᵢ` form a basis of `M(f⁻¹ U)`, so the map is bijective on sections
over small affine neighbourhoods of `η`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

noncomputable section

namespace Hartshorne

namespace ChevalleyApprox

/-! ### Sections of a quasi-coherent module over basic opens -/

section BasicOpen

variable {Y : Scheme.{u}} (P : Y.Modules) {U : Y.Opens}

/-- The restriction `Γ(U, P) → Γ(W, P)` to an open `W ⊆ U`, as a `Γ(Y, U)`-linear map, where
`Γ(Y, U)` acts on `Γ(W, P)` through the restriction of functions. -/
def resₗ {W : Y.Opens} (h : W ≤ U) :
    letI := Module.compHom Γ(P, W) (Y.presheaf.map (homOfLE h).op).hom
    Γ(P, U) →ₗ[Γ(Y, U)] Γ(P, W) :=
  letI := Module.compHom Γ(P, W) (Y.presheaf.map (homOfLE h).op).hom
  { toFun := P.presheaf.map (homOfLE h).op
    map_add' := map_add _
    map_smul' := fun a x => P.val.map_smul (homOfLE h).op a x }

theorem resₗ_apply {W : Y.Opens} (h : W ≤ U) (x : Γ(P, U)) :
    resₗ P h x = P.presheaf.map (homOfLE h).op x := rfl

/-- **Sections over basic opens are localizations**: for a quasi-coherent module `P`, an affine
open `U` and `r ∈ Γ(U, 𝒪_Y)`, the restriction `Γ(U, P) → Γ(D(r), P)` is the localization at the
powers of `r`. -/
theorem isLocalizedModule_resₗ (hU : IsAffineOpen U) [IsIso (P.restrict hU.fromSpec).fromTildeΓ]
    (r : Γ(Y, U)) {W : Y.Opens} (h : W ≤ U) (hW : Y.basicOpen r = W) :
    letI := Module.compHom Γ(P, W) (Y.presheaf.map (homOfLE h).op).hom
    IsLocalizedModule (Submonoid.powers r) (resₗ P h) := by
  subst hW
  let := Module.compHom Γ(P, Y.basicOpen r) (Y.presheaf.map (homOfLE h).op).hom
  let e := CoherentAux.sectionsEquiv P hU
  let ρ : Γ(P.restrict hU.fromSpec, ⊤) →ₗ[Γ(Y, U)] Γ(P.restrict hU.fromSpec, CoherentAux.D r) :=
    ((modulesSpecToSheaf.obj (P.restrict hU.fromSpec)).obj.map (CoherentAux.D r).leTop.op).hom
  have hρ : IsLocalizedModule (Submonoid.powers r) ρ :=
    (isIso_fromTildeΓ_iff_isLocalizing (P.restrict hU.fromSpec)).mp inferInstance r
  have himg : hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen r = Y.basicOpen r :=
    hU.fromSpec_image_basicOpen r
  let e3 : Γ(P.restrict hU.fromSpec, CoherentAux.D r) ≃ₗ[Γ(Y, U)] Γ(P, Y.basicOpen r) :=
    { toFun := fun t => P.presheaf.map (eqToHom himg.symm).op t
      invFun := fun t => P.presheaf.map (eqToHom himg).op t
      left_inv := fun t => CoherentAux.map_eqToHom_map_eqToHom P himg.symm t
      right_inv := fun t => CoherentAux.map_eqToHom_map_eqToHom P himg t
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun a t => by
        rw [Scheme.Modules.smul_Spec_def]
        change P.presheaf.map (eqToHom himg.symm).op
            ((((Spec Γ(Y, U)).presheaf.map (CoherentAux.D r).leTop.op ≫
              (hU.fromSpec.appIso (PrimeSpectrum.basicOpen r)).inv)
              ((Scheme.ΓSpecIso Γ(Y, U)).inv a)) •
              (show Γ(P, hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen r) from t)) = _
        have hc := ConcreteCategory.congr_hom (FiberDimAux.ring_compat_basicOpen hU r) a
        rw [← Category.assoc] at hc
        erw [← ConcreteCategory.comp_apply, hc]
        refine (P.val.map_smul (eqToHom himg.symm).op _ t).trans ?_
        congr 1
        change (Y.presheaf.map (homOfLE (FiberDimAux.fromSpec_image_basicOpen_le hU r)).op ≫
          Y.presheaf.map (eqToHom himg.symm).op) a = Y.presheaf.map (homOfLE h).op a
        rw [← Functor.map_comp]
        rfl }
  have heq : resₗ P h = e3.toLinearMap ∘ₗ ρ ∘ₗ e.toLinearMap := by
    ext x
    change P.presheaf.map (homOfLE h).op x = P.presheaf.map (eqToHom himg.symm).op
      (P.presheaf.map _ (P.presheaf.map _ x))
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  rw [heq]
  exact IsLocalizedModule.of_linearEquiv _ _ _

end BasicOpen

end ChevalleyApprox

end Hartshorne
