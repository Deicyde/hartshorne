/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleSkyscraper

/-!
# Stalks of the pullback of a module sheaf

Let `h : X' ⟶ X` be a morphism of schemes, `F` an `𝒪_X`-module and `x' : X'`. The stalk of the
module pullback `h^*F` at `x'` is `𝒪_{X',x'} ⊗_{𝒪_{X,h(x')}} F_{h(x')}`, as an
`𝒪_{X',x'}`-module (`pullbackStalkLinearEquiv`).

## Proof

Both functors `F ↦ (h^*F)_{x'}` and `F ↦ 𝒪_{X',x'} ⊗ F_{h(x')}` are left adjoint to the same
functor. Indeed the stalk functor is left adjoint to the skyscraper functor
(`Hartshorne.Ringed.moduleStalkSkyscraperAdjunction`), so the first is left adjoint to
`N ↦ h_*(x'_* N)`, and the second is left adjoint to `N ↦ h(x')_* N`, with `N` viewed as an
`𝒪_{X,h(x')}`-module through the stalk map. These agree: the pushforward of the skyscraper sheaf
at `x'` is the skyscraper sheaf at `h(x')` (`pushforwardSkyscraperIso`), since `x' ∈ h⁻¹(U)`
exactly when `h(x') ∈ U`. Uniqueness of left adjoints gives the natural isomorphism
`pullbackStalkIso`.
-/

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace Hartshorne

open AlgebraicGeometry Ringed

noncomputable section

variable {X' X : Scheme.{u}} (h : X' ⟶ X) (x' : X')

/-- Pushing forward the skyscraper sheaf at `x'` along `h` (componentwise identity). -/
def pushforwardSkyscraperHom (N : ModuleCat.{u} (X'.presheaf.stalk x')) :
    (Scheme.Modules.pushforward h).obj ((moduleSkyscraper (R := X'.sheaf) x').obj N) ⟶
      (moduleSkyscraper (R := X.sheaf) (h x')).obj
        ((ModuleCat.restrictScalars (h.stalkMap x').hom).obj N) where
  val := PresheafOfModules.homMk
    { app _ := AddCommGrpCat.ofHom (AddMonoidHom.id _)
      naturality _ _ _ := rfl }
    (fun U r f => funext fun p => by
      change X'.presheaf.germ (h ⁻¹ᵁ U.unop) x' p.down (h.app U.unop r) • f p =
        h.stalkMap x' (X.presheaf.germ U.unop (h x') p.down r) • f p
      exact congrArg (· • f p) (Scheme.Hom.germ_stalkMap_apply h U.unop x' p.down r).symm)

/-- The inverse of `pushforwardSkyscraperHom` (componentwise identity). -/
def pushforwardSkyscraperInv (N : ModuleCat.{u} (X'.presheaf.stalk x')) :
    (moduleSkyscraper (R := X.sheaf) (h x')).obj
        ((ModuleCat.restrictScalars (h.stalkMap x').hom).obj N) ⟶
      (Scheme.Modules.pushforward h).obj ((moduleSkyscraper (R := X'.sheaf) x').obj N) where
  val := PresheafOfModules.homMk
    { app _ := AddCommGrpCat.ofHom (AddMonoidHom.id _)
      naturality _ _ _ := rfl }
    (fun U r f => funext fun p => by
      change h.stalkMap x' (X.presheaf.germ U.unop (h x') p.down r) • f p =
        X'.presheaf.germ (h ⁻¹ᵁ U.unop) x' p.down (h.app U.unop r) • f p
      exact congrArg (· • f p) (Scheme.Hom.germ_stalkMap_apply h U.unop x' p.down r))

/-- **The pushforward of a skyscraper sheaf.** Pushing forward the skyscraper sheaf at `x'` with
value `N` along `h` gives the skyscraper sheaf at `h(x')` with value `N`, viewed as an
`𝒪_{X,h(x')}`-module through the stalk map. -/
def pushforwardSkyscraperIso :
    moduleSkyscraper (R := X'.sheaf) x' ⋙ Scheme.Modules.pushforward h ≅
      ModuleCat.restrictScalars (h.stalkMap x').hom ⋙ moduleSkyscraper (R := X.sheaf) (h x') :=
  NatIso.ofComponents
    (fun N =>
      { hom := pushforwardSkyscraperHom h x' N
        inv := pushforwardSkyscraperInv h x' N
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

/-- The adjunction `(h^* -)_{x'} ⊣ h_*(x'_* -)`. -/
def pullbackStalkAdjunction :
    Scheme.Modules.pullback h ⋙ moduleStalkFunctor (R := X'.sheaf) x' ⊣
      moduleSkyscraper (R := X'.sheaf) x' ⋙ Scheme.Modules.pushforward h :=
  (Scheme.Modules.pullbackPushforwardAdjunction h).comp
    (moduleStalkSkyscraperAdjunction (R := X'.sheaf) x')

/-- The adjunction `𝒪_{X',x'} ⊗ (-)_{h(x')} ⊣ h_*(x'_* -)`. -/
def stalkExtendScalarsAdjunction :
    moduleStalkFunctor (R := X.sheaf) (h x') ⋙ ModuleCat.extendScalars (h.stalkMap x').hom ⊣
      moduleSkyscraper (R := X'.sheaf) x' ⋙ Scheme.Modules.pushforward h :=
  ((moduleStalkSkyscraperAdjunction (R := X.sheaf) (h x')).comp
    (ModuleCat.extendRestrictScalarsAdj (h.stalkMap x').hom)).ofNatIsoRight
      (pushforwardSkyscraperIso h x').symm

/-- **Stalks of the module pullback**, as a natural isomorphism: for `𝒪_X`-modules `F`,
`(h^*F)_{x'} ≅ 𝒪_{X',x'} ⊗_{𝒪_{X,h(x')}} F_{h(x')}`. -/
def pullbackStalkIso :
    Scheme.Modules.pullback h ⋙ moduleStalkFunctor (R := X'.sheaf) x' ≅
      moduleStalkFunctor (R := X.sheaf) (h x') ⋙ ModuleCat.extendScalars (h.stalkMap x').hom :=
  (pullbackStalkAdjunction h x').leftAdjointUniq (stalkExtendScalarsAdjunction h x')

/-- **Stalks of the module pullback.** For a morphism of schemes `h : X' ⟶ X`, an `𝒪_X`-module
`F` and `x' : X'`, the stalk of `h^*F` at `x'` is `𝒪_{X',x'} ⊗_{𝒪_{X,h(x')}} F_{h(x')}`, as
`𝒪_{X',x'}`-modules. -/
def pullbackStalkLinearEquiv (F : X.Modules) :
    letI : Module (ringSheafStalk X'.sheaf x') ((ModuleCat.extendScalars (h.stalkMap x').hom).obj
        ((moduleStalkFunctor (R := X.sheaf) (h x')).obj F)) := ModuleCat.isModule _
    (moduleStalkFunctor (R := X'.sheaf) x').obj ((Scheme.Modules.pullback h).obj F) ≃ₗ[
      ringSheafStalk X'.sheaf x']
      (ModuleCat.extendScalars (h.stalkMap x').hom).obj
        ((moduleStalkFunctor (R := X.sheaf) (h x')).obj F) :=
  ((pullbackStalkIso h x').app F).toLinearEquiv

end

end Hartshorne
