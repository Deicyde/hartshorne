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

/-! ### The modules of homomorphisms over affine opens -/

section HomModule

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (F : Y.Modules)

/-- Multiplication by a section `b` of `𝒪_X` over `f⁻¹ U` on `Γ(U, f_* M)`, which is
`Γ(U, 𝒪_Y)`-linear. -/
def mulB (U : Y.Opens) (b : Γ(X, f ⁻¹ᵁ U)) :
    Γ((Scheme.Modules.pushforward f).obj M, U) →ₗ[Γ(Y, U)]
      Γ((Scheme.Modules.pushforward f).obj M, U) where
  toFun m := (b • (show Γ(M, f ⁻¹ᵁ U) from m) : Γ(M, f ⁻¹ᵁ U))
  map_add' x y := smul_add b (show Γ(M, f ⁻¹ᵁ U) from x) y
  map_smul' a m := by
    change b • (f.app U a • (show Γ(M, f ⁻¹ᵁ U) from m)) =
      f.app U a • (b • (show Γ(M, f ⁻¹ᵁ U) from m))
    rw [smul_smul, smul_smul, mul_comm]

theorem mulB_app (U : Y.Opens) (a : Γ(Y, U)) (m : Γ((Scheme.Modules.pushforward f).obj M, U)) :
    mulB f M U (f.app U a) m = a • m := rfl

/-- The `Γ(f⁻¹ U, 𝒪_X)`-module structure on `Hom_{Γ(U, 𝒪_Y)}(Γ(U, f_* M), Γ(U, F))`, by
precomposition with multiplication. -/
@[reducible] def homModule (U : Y.Opens) :
    Module Γ(X, f ⁻¹ᵁ U) (Γ((Scheme.Modules.pushforward f).obj M, U) →ₗ[Γ(Y, U)] Γ(F, U)) where
  smul b h := h ∘ₗ mulB f M U b
  one_smul h := LinearMap.ext fun m => congrArg h (one_smul _ (show Γ(M, f ⁻¹ᵁ U) from m))
  mul_smul b b' h := LinearMap.ext fun m => congrArg h (by
    change (b * b') • (show Γ(M, f ⁻¹ᵁ U) from m) = b' • b • (show Γ(M, f ⁻¹ᵁ U) from m)
    rw [mul_comm, mul_smul])
  smul_zero b := LinearMap.zero_comp _
  smul_add b h h' := LinearMap.add_comp _ _ _
  add_smul b b' h := LinearMap.ext fun m => by
    change h ((b + b') • (show Γ(M, f ⁻¹ᵁ U) from m)) =
      h (b • (show Γ(M, f ⁻¹ᵁ U) from m)) + h (b' • (show Γ(M, f ⁻¹ᵁ U) from m))
    rw [add_smul]
    exact map_add h _ _
  zero_smul h := LinearMap.ext fun m => by
    change h ((0 : Γ(X, f ⁻¹ᵁ U)) • (show Γ(M, f ⁻¹ᵁ U) from m)) = 0
    rw [zero_smul]
    exact map_zero h

/-- The module `Hom_{Γ(U, 𝒪_Y)}(Γ(U, f_* M), Γ(U, F))` over `Γ(f⁻¹ U, 𝒪_X)`. -/
def homSec (U : Y.Opens) : ModuleCat.{u} Γ(X, f ⁻¹ᵁ U) :=
  letI := homModule f M F U
  ModuleCat.of Γ(X, f ⁻¹ᵁ U) (Γ((Scheme.Modules.pushforward f).obj M, U) →ₗ[Γ(Y, U)] Γ(F, U))

/-- An element of `homSec` as a linear map. -/
def homSec.lin {U : Y.Opens} (h : homSec f M F U) :
    Γ((Scheme.Modules.pushforward f).obj M, U) →ₗ[Γ(Y, U)] Γ(F, U) := h

theorem homSec.smul_lin {U : Y.Opens} (b : Γ(X, f ⁻¹ᵁ U)) (h : homSec f M F U)
    (m : Γ((Scheme.Modules.pushforward f).obj M, U)) :
    homSec.lin f M F (b • h) m = homSec.lin f M F h (mulB f M U b m) := rfl

theorem homSec.lin_add {U : Y.Opens} (h h' : homSec f M F U) :
    homSec.lin f M F (h + h') = homSec.lin f M F h + homSec.lin f M F h' := rfl

/-- On `homSec`, sections of `𝒪_Y` act through `f` as they act on the values. -/
theorem homSec.app_smul {U : Y.Opens} (a : Γ(Y, U)) (h : homSec f M F U) :
    homSec.lin f M F (f.app U a • h) = a • homSec.lin f M F h :=
  LinearMap.ext fun m => (homSec.smul_lin f M F _ h m).trans ((homSec.lin f M F h).map_smul a m)

end HomModule

/-! ### Restriction of homomorphisms to basic opens -/

section Restriction

open RelSpecModuleData

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) (F : Y.Modules)

theorem le_of_hom {U V : Y.AffineZariskiSite} (i : U ⟶ V) : U.1 ≤ V.1 :=
  Scheme.AffineZariskiSite.toOpens_mono (leOfHom i)

/-- The restriction `Γ(V, 𝒪_Y) → Γ(U, 𝒪_Y)` as an algebra. -/
abbrev transAlgebra {U V : Y.AffineZariskiSite} (i : U ⟶ V) : Algebra Γ(Y, V.1) Γ(Y, U.1) :=
  (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom.toAlgebra

theorem transIsLocalization {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    letI := transAlgebra i
    IsLocalization.Away (transElt i) Γ(Y, U.1) := by
  have hr := basicOpen_transElt i
  revert hr
  generalize transElt i = r
  intro hr
  obtain rfl : U = V.basicOpen r := Subtype.ext hr.symm
  exact V.2.isLocalization_basicOpen r

variable [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent] [F.IsQuasicoherent]

/-- **Restriction of homomorphisms**: for a basic open `U = D(r) ⊆ V`, a homomorphism
`Γ(V, f_* M) → Γ(V, F)` induces `Γ(U, f_* M) = Γ(V, f_* M)_r → Γ(V, F)_r = Γ(U, F)`. -/
def homRes {U V : Y.AffineZariskiSite} (i : U ⟶ V)
    (h : Γ((Scheme.Modules.pushforward f).obj M, V.1) →ₗ[Γ(Y, V.1)] Γ(F, V.1)) :
    Γ((Scheme.Modules.pushforward f).obj M, U.1) →ₗ[Γ(Y, U.1)] Γ(F, U.1) :=
  letI := transAlgebra i
  letI := Module.compHom Γ((Scheme.Modules.pushforward f).obj M, U.1)
    (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom
  letI := Module.compHom Γ(F, U.1) (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom
  haveI : IsScalarTower Γ(Y, V.1) Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1) :=
    IsScalarTower.of_compHom _ _ _
  haveI : IsScalarTower Γ(Y, V.1) Γ(Y, U.1) Γ(F, U.1) := IsScalarTower.of_compHom _ _ _
  haveI := transIsLocalization i
  haveI := isLocalizedModule_resₗ ((Scheme.Modules.pushforward f).obj M) V.2 (transElt i)
    (le_of_hom i) (basicOpen_transElt i)
  haveI := isLocalizedModule_resₗ F V.2 (transElt i) (le_of_hom i) (basicOpen_transElt i)
  IsLocalizedModule.mapExtendScalars (Submonoid.powers (transElt i))
    (resₗ ((Scheme.Modules.pushforward f).obj M) (le_of_hom i)) (resₗ F (le_of_hom i))
    Γ(Y, U.1) h

theorem homRes_res {U V : Y.AffineZariskiSite} (i : U ⟶ V)
    (h : Γ((Scheme.Modules.pushforward f).obj M, V.1) →ₗ[Γ(Y, V.1)] Γ(F, V.1))
    (m : Γ((Scheme.Modules.pushforward f).obj M, V.1)) :
    homRes f M F i h (((Scheme.Modules.pushforward f).obj M).presheaf.map
      (homOfLE (le_of_hom i)).op m) = F.presheaf.map (homOfLE (le_of_hom i)).op (h m) := by
  letI := transAlgebra i
  letI := Module.compHom Γ((Scheme.Modules.pushforward f).obj M, U.1)
    (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom
  letI := Module.compHom Γ(F, U.1) (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom
  haveI : IsScalarTower Γ(Y, V.1) Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1) :=
    IsScalarTower.of_compHom _ _ _
  haveI : IsScalarTower Γ(Y, V.1) Γ(Y, U.1) Γ(F, U.1) := IsScalarTower.of_compHom _ _ _
  haveI := transIsLocalization i
  haveI := isLocalizedModule_resₗ ((Scheme.Modules.pushforward f).obj M) V.2 (transElt i)
    (le_of_hom i) (basicOpen_transElt i)
  haveI := isLocalizedModule_resₗ F V.2 (transElt i) (le_of_hom i) (basicOpen_transElt i)
  exact IsLocalizedModule.map_apply (Submonoid.powers (transElt i))
    (resₗ ((Scheme.Modules.pushforward f).obj M) (le_of_hom i)) (resₗ F (le_of_hom i)) h m

/-- Homomorphisms over a basic open are determined by their values on restricted sections. -/
theorem homRes_ext {U V : Y.AffineZariskiSite} (i : U ⟶ V)
    {g g' : Γ((Scheme.Modules.pushforward f).obj M, U.1) →ₗ[Γ(Y, U.1)] Γ(F, U.1)}
    (H : ∀ m : Γ((Scheme.Modules.pushforward f).obj M, V.1),
      g (((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE (le_of_hom i)).op m) =
        g' (((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE (le_of_hom i)).op m)) :
    g = g' := by
  letI := transAlgebra i
  letI := Module.compHom Γ((Scheme.Modules.pushforward f).obj M, U.1)
    (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom
  letI := Module.compHom Γ(F, U.1) (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom
  haveI : IsScalarTower Γ(Y, V.1) Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1) :=
    IsScalarTower.of_compHom _ _ _
  haveI : IsScalarTower Γ(Y, V.1) Γ(Y, U.1) Γ(F, U.1) := IsScalarTower.of_compHom _ _ _
  haveI := isLocalizedModule_resₗ ((Scheme.Modules.pushforward f).obj M) V.2 (transElt i)
    (le_of_hom i) (basicOpen_transElt i)
  haveI := isLocalizedModule_resₗ F V.2 (transElt i) (le_of_hom i) (basicOpen_transElt i)
  have := IsLocalizedModule.ext (Submonoid.powers (transElt i))
    (resₗ ((Scheme.Modules.pushforward f).obj M) (le_of_hom i))
    (IsLocalizedModule.map_units (resₗ F (le_of_hom i)))
    (j := g.restrictScalars Γ(Y, V.1)) (k := g'.restrictScalars Γ(Y, V.1))
    (LinearMap.ext H)
  exact LinearMap.ext fun m => LinearMap.congr_fun this m

theorem homRes_add {U V : Y.AffineZariskiSite} (i : U ⟶ V)
    (h h' : Γ((Scheme.Modules.pushforward f).obj M, V.1) →ₗ[Γ(Y, V.1)] Γ(F, V.1)) :
    homRes f M F i (h + h') = homRes f M F i h + homRes f M F i h' :=
  homRes_ext f M F i fun m => by
    rw [LinearMap.add_apply, homRes_res, homRes_res, homRes_res, LinearMap.add_apply, map_add]

theorem homRes_comp {U V W : Y.AffineZariskiSite} (i : U ⟶ V) (j : V ⟶ W)
    (h : Γ((Scheme.Modules.pushforward f).obj M, W.1) →ₗ[Γ(Y, W.1)] Γ(F, W.1)) :
    homRes f M F (i ≫ j) h = homRes f M F i (homRes f M F j h) :=
  homRes_ext f M F (i ≫ j) fun m => by
    have e1 : ((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE (le_of_hom (i ≫ j))).op m =
        ((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE (le_of_hom i)).op
          (((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE (le_of_hom j)).op m) :=
      (DirectedModuleGluing.pmap_map _ _ _ _ m).symm
    have e2 : F.presheaf.map (homOfLE (le_of_hom (i ≫ j))).op (h m) =
        F.presheaf.map (homOfLE (le_of_hom i)).op (F.presheaf.map (homOfLE (le_of_hom j)).op (h m)) :=
      (DirectedModuleGluing.pmap_map _ _ _ _ _).symm
    rw [homRes_res, e1, homRes_res, homRes_res, e2]

theorem mulB_res {U V : Y.Opens} (hUV : U ≤ V) (b : Γ(X, f ⁻¹ᵁ V))
    (m : Γ((Scheme.Modules.pushforward f).obj M, V)) :
    mulB f M U (X.presheaf.map (homOfLE (f.preimage_mono hUV)).op b)
        (((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE hUV).op m) =
      ((Scheme.Modules.pushforward f).obj M).presheaf.map (homOfLE hUV).op (mulB f M V b m) :=
  (M.val.map_smul (homOfLE (f.preimage_mono hUV)).op b (show Γ(M, f ⁻¹ᵁ V) from m)).symm

theorem homRes_smul {U V : Y.AffineZariskiSite} (i : U ⟶ V) (b : Γ(X, f ⁻¹ᵁ V.1))
    (h : homSec f M F V.1) :
    homRes f M F i (homSec.lin f M F (b • h)) = homSec.lin f M F
      ((X.presheaf.map (homOfLE (f.preimage_mono (le_of_hom i))).op b) •
        (show homSec f M F U.1 from homRes f M F i (homSec.lin f M F h))) :=
  homRes_ext f M F i fun m => by
    rw [homRes_res, homSec.smul_lin, homSec.smul_lin, mulB_res]
    exact (homRes_res f M F i _ _).symm

/-- The restriction of homomorphisms as a semilinear map `homSec V ⟶ homSec U`. -/
def homResHom {U V : Y.AffineZariskiSite} (i : U ⟶ V) :
    homSec f M F V.1 ⟶ (ModuleCat.restrictScalars
      (X.presheaf.map (homOfLE (f.preimage_mono (le_of_hom i))).op).hom).obj
        (homSec f M F U.1) :=
  ModuleCat.semilinearMapAddEquiv _ _ _
    { toFun := fun h => homRes f M F i (homSec.lin f M F h)
      map_add' := fun h h' => homRes_add f M F i h h'
      map_smul' := fun b h => homRes_smul f M F i b h }

theorem homResHom_apply {U V : Y.AffineZariskiSite} (i : U ⟶ V)
    (h : homSec f M F V.1) :
    homSec.lin f M F ((homResHom f M F i).hom h) = homRes f M F i (homSec.lin f M F h) := rfl

/-- **Localization of homomorphisms**: since `Γ(V, f_* M)` is finitely presented, restriction of
homomorphisms to `U = D(r) ⊆ V` is the localization at the powers of `r`. -/
theorem isLocalizedModule_homResHom {U V : Y.AffineZariskiSite} (i : U ⟶ V)
    [Module.FinitePresentation Γ(Y, V.1) Γ((Scheme.Modules.pushforward f).obj M, V.1)] :
    IsLocalizedModule (Submonoid.powers (f.app V.1 (transElt i))) (homResHom f M F i).hom := by
  letI := transAlgebra i
  letI := Module.compHom Γ((Scheme.Modules.pushforward f).obj M, U.1)
    (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom
  letI := Module.compHom Γ(F, U.1) (Y.presheaf.map (homOfLE (le_of_hom i)).op).hom
  haveI : IsScalarTower Γ(Y, V.1) Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1) :=
    IsScalarTower.of_compHom _ _ _
  haveI : IsScalarTower Γ(Y, V.1) Γ(Y, U.1) Γ(F, U.1) := IsScalarTower.of_compHom _ _ _
  haveI := transIsLocalization i
  haveI := isLocalizedModule_resₗ ((Scheme.Modules.pushforward f).obj M) V.2 (transElt i)
    (le_of_hom i) (basicOpen_transElt i)
  haveI := isLocalizedModule_resₗ F V.2 (transElt i) (le_of_hom i) (basicOpen_transElt i)
  have hR : IsLocalizedModule (Submonoid.powers (transElt i))
      (IsLocalizedModule.mapExtendScalars (Submonoid.powers (transElt i))
        (resₗ ((Scheme.Modules.pushforward f).obj M) (le_of_hom i)) (resₗ F (le_of_hom i))
        Γ(Y, U.1)) := inferInstance
  let r := transElt i
  -- the action of `f^# r` on `homSec U` agrees with the action of `r`
  have hactU : ∀ (n : ℕ) (h : homSec f M F U.1),
      homSec.lin f M F ((X.presheaf.map (homOfLE (f.preimage_mono (le_of_hom i))).op
        (f.app V.1 r ^ n)) • h) = r ^ n • homSec.lin f M F h := by
    intro n h
    have hnat : X.presheaf.map (homOfLE (f.preimage_mono (le_of_hom i))).op (f.app V.1 r ^ n) =
        f.app U.1 (Y.presheaf.map (homOfLE (le_of_hom i)).op (r ^ n)) := by
      rw [map_pow, map_pow, map_pow]
      congr 1
      exact (ConcreteCategory.congr_hom (f.naturality (homOfLE (le_of_hom i)).op) r).symm
    rw [hnat, homSec.app_smul]
    rfl
  have hactV : ∀ (n : ℕ) (h : homSec f M F V.1),
      homSec.lin f M F ((f.app V.1 r ^ n) • h) = r ^ n • homSec.lin f M F h := by
    intro n h
    rw [← map_pow, homSec.app_smul]
  refine ⟨fun s => ?_, fun h' => ?_, fun {h₁ h₂} e => ?_⟩
  · obtain ⟨_, n, rfl⟩ := s
    have hu := hR.map_units ⟨r ^ n, n, rfl⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    have key : (⇑(algebraMap Γ(X, f ⁻¹ᵁ V.1) (Module.End Γ(X, f ⁻¹ᵁ V.1)
        ((ModuleCat.restrictScalars (X.presheaf.map (homOfLE (f.preimage_mono
          (le_of_hom i))).op).hom).obj (homSec f M F U.1))) (f.app V.1 r ^ n))) =
        ⇑(algebraMap Γ(Y, V.1) (Module.End Γ(Y, V.1) (Γ((Scheme.Modules.pushforward f).obj M,
          U.1) →ₗ[Γ(Y, U.1)] Γ(F, U.1))) (r ^ n)) :=
      funext fun h => hactU n h
    rw [key]
    exact hu
  · obtain ⟨⟨h, ⟨_, n, rfl⟩⟩, e⟩ := hR.surj (homSec.lin f M F h')
    refine ⟨⟨h, ⟨_, n, rfl⟩⟩, ?_⟩
    simp only [Submonoid.smul_def] at e ⊢
    exact (hactU n h').trans (e.trans (homResHom_apply f M F i h).symm)
  · obtain ⟨⟨_, n, rfl⟩, e'⟩ := hR.exists_of_eq (S := Submonoid.powers r)
      (x₁ := homSec.lin f M F h₁) (x₂ := homSec.lin f M F h₂)
      ((homResHom_apply f M F i h₁).symm.trans (e.trans (homResHom_apply f M F i h₂)))
    refine ⟨⟨_, n, rfl⟩, ?_⟩
    simp only [Submonoid.smul_def] at e' ⊢
    exact (hactV n h₁).trans (e'.trans (hactV n h₂).symm)

end Restriction

/-- Over a Noetherian ring, homomorphisms between finite modules form a finite module. -/
theorem finite_linearMap_of_isNoetherianRing {R P Q : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Module.Finite R P]
    [Module.Finite R Q] : Module.Finite R (P →ₗ[R] Q) := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := P)
  let Φ : (P →ₗ[R] Q) →ₗ[R] (Fin n → Q) := LinearMap.pi fun j => LinearMap.applyₗ (v j)
  have hΦ : Function.Injective Φ := fun h h' e =>
    LinearMap.ext_on_range hv fun j => congrFun e j
  haveI : IsNoetherian R (P →ₗ[R] Q) := isNoetherian_of_injective Φ hΦ
  infer_instance

/-! ### The glued module -/

section Glue

open RelSpecModuleData QuasiCoherentAlgebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (M : X.Modules) (F : Y.Modules)
  [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent] [F.IsQuasicoherent]
  [hfp : ∀ V : Y.AffineZariskiSite,
    Module.FinitePresentation Γ(Y, V.1) Γ((Scheme.Modules.pushforward f).obj M, V.1)]

/-- The modules `Hom_{Γ(U, 𝒪_Y)}(Γ(U, f_* M), Γ(U, F))` with their restriction maps, as a
quasi-coherent module over `f_* 𝒪_X`. -/
def homData : RelSpecModuleData (QuasiCoherentAlgebra.ofHom f) where
  N U := homSec f M F U.1
  ρ i := homResHom f M F i
  ρ_comp i j h := homRes_comp f M F i j (homSec.lin f M F h)
  isLocalizedModule i := isLocalizedModule_homResHom f M F i

/-- **The approximating module** `G` on `X`: the module glued from the sheaves associated to the
`Γ(f⁻¹ U, 𝒪_X)`-modules `Hom_{Γ(U, 𝒪_Y)}(Γ(U, f_* M), Γ(U, F))`, transported along
`Spec_Y (f_* 𝒪_X) ≅ X`. -/
def approx : X.Modules := (homData f M F).glue.restrict (relSpecOfHomIso f).inv

theorem fromSpec_relSpecOfHomIso_inv (U : Y.AffineZariskiSite) :
    (U.2.preimage f).fromSpec ≫ (relSpecOfHomIso f).inv = (QuasiCoherentAlgebra.ofHom f).ι U := by
  have h := ι_relSpecOfHomHom f U
  have h2 : relSpecOfHomHom f ≫ (relSpecOfHomIso f).inv = 𝟙 _ := (relSpecOfHomIso f).hom_inv_id
  erw [← h, Category.assoc, h2, Category.comp_id]

/-- The restriction of `G` to the affine open `f⁻¹ U` is the sheaf associated to `homSec U`. -/
def approxRestrictIso (U : Y.AffineZariskiSite) :
    (approx f M F).restrict (U.2.preimage f).fromSpec ≅ tilde (homSec f M F U.1) :=
  ((Scheme.Modules.restrictFunctorComp (U.2.preimage f).fromSpec (relSpecOfHomIso f).inv).app
      (homData f M F).glue).symm ≪≫
    (@Scheme.Modules.restrictFunctorCongr _ _ _ _ (fromSpec_relSpecOfHomIso_inv f U) inferInstance
      (QuasiCoherentAlgebra.isOpenImmersion_ι (ofHom f) U)).app _ ≪≫
    (homData f M F).ψ U

/-- `homSec U` is a finite `Γ(f⁻¹ U, 𝒪_X)`-module when `Γ(U, f_* M)` and `Γ(U, F)` are finite over
the Noetherian ring `Γ(U, 𝒪_Y)`. -/
theorem finite_homSec (U : Y.AffineZariskiSite) [IsNoetherianRing Γ(Y, U.1)]
    [Module.Finite Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1)]
    [Module.Finite Γ(Y, U.1) Γ(F, U.1)] :
    Module.Finite Γ(X, f ⁻¹ᵁ U.1) (homSec f M F U.1) := by
  letI : Algebra Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1) := (f.app U.1).hom.toAlgebra
  letI := homModule f M F U.1
  haveI : Module.Finite Γ(Y, U.1)
      (Γ((Scheme.Modules.pushforward f).obj M, U.1) →ₗ[Γ(Y, U.1)] Γ(F, U.1)) :=
    finite_linearMap_of_isNoetherianRing
  haveI : IsScalarTower Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
      (Γ((Scheme.Modules.pushforward f).obj M, U.1) →ₗ[Γ(Y, U.1)] Γ(F, U.1)) := by
    refine ⟨fun a b h => LinearMap.ext fun m => ?_⟩
    change h (mulB f M U.1 (f.app U.1 a * b) m) = a • h (mulB f M U.1 b m)
    rw [← map_smul]
    congr 1
    change (f.app U.1 a * b) • (show Γ(M, f ⁻¹ᵁ U.1) from m) =
      f.app U.1 a • b • (show Γ(M, f ⁻¹ᵁ U.1) from m)
    rw [mul_smul]
  exact Module.Finite.of_restrictScalars_finite Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)
    (Γ((Scheme.Modules.pushforward f).obj M, U.1) →ₗ[Γ(Y, U.1)] Γ(F, U.1))

theorem iSup_preimage_eq_top :
    (⨆ U : Y.AffineZariskiSite, f ⁻¹ᵁ U.1) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hxV⟩

/-- **`G` is coherent.** -/
theorem isCoherent_approx [IsLocallyNoetherian Y]
    [∀ U : Y.AffineZariskiSite,
      Module.Finite Γ(Y, U.1) Γ((Scheme.Modules.pushforward f).obj M, U.1)]
    [∀ U : Y.AffineZariskiSite, Module.Finite Γ(Y, U.1) Γ(F, U.1)] :
    IsCoherent (approx f M F) := by
  refine ⟨Y.AffineZariskiSite, fun U => ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩, iSup_preimage_eq_top f,
    fun U => ⟨homSec f M F U.1, ?_, ⟨(approxRestrictIso f M F U).symm⟩⟩⟩
  haveI : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  exact finite_homSec f M F U

end Glue

end ChevalleyApprox

end Hartshorne
