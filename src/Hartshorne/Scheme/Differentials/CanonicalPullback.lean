/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.CanonicalSheaf
import Hartshorne.Scheme.Differentials.RelativeDifferentialsTransitivity
import Hartshorne.Scheme.TensorPowerSectionRingMap
import Hartshorne.Scheme.LocallyFreeRinged
import Hartshorne.Scheme.SheafAlgebraOperations
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.Intersection.RationalEquivalenceLocalization
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Pullback of canonical sections

Hartshorne, *Algebraic Geometry*, II.8, proof of Theorem 8.19 (p. 181).

Let `X` and `X'` be nonsingular varieties of the same dimension `n` over an algebraically closed
field `k`, and let `f : V ⟶ X'` be a `k`-morphism on a dense open `V ⊆ X` representing a
birational map. Pullback of differentials gives an injective map `Γ(X', ω_{X'}) → Γ(V, ω_V)`
(`Hartshorne.canonicalPullback_injective`).

* `Hartshorne.exteriorPowerPullback`: for `f : V ⟶ Y` and `p : Y ⟶ Spec k`, the morphism
  `⋀^n Ω_{Y/k} ⟶ f_*(⋀^n Ω_{V/k})`, `ω_1 ∧ ⋯ ∧ ω_n ↦ f^*ω_1 ∧ ⋯ ∧ f^*ω_n`, built from the
  universal property of the exterior power and the pushforward of the universal alternating map
  (`Hartshorne.ModuleSheafMultilinear.pushforward`).
* Compatibility with open immersions: if `j : W ⟶ V` and `j ≫ f` is an open immersion, the
  derivation `a ↦ d_{Y/k}(((j ≫ f)^♯)⁻¹ (j^♯ a))` gives `Ω_{V/k} ⟶ j_*(Ω_{Y/k}|_W)`
  (`Hartshorne.openImmersionDifferentialsMap`), and on exterior powers
  `⋀^n Ω_{V/k} ⟶ j_*((⋀^n Ω_{Y/k})|_W)` (`Hartshorne.openImmersionExteriorPowerMap`). Composed
  with the pullback, it is the restriction of `⋀^n Ω_{Y/k}` to `W`
  (`Hartshorne.exteriorPowerPullback_comp_openImmersionExteriorPowerMap`).
* `AlgebraicGeometry.Scheme.Modules.presheaf_map_injective_of_isInvertible`: on an integral
  scheme, restriction of sections of an invertible sheaf to a nonempty open is injective. Hence
  the pullback is injective on global sections when `Y` is integral and `⋀^n Ω_{Y/k}` is
  invertible (`Hartshorne.exteriorPowerPullback_app_top_injective`).
-/
universe u

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

namespace Hartshorne

namespace ModuleSheafMultilinear

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {r : ℕ} {F H : X.Modules}

/-- The pushforward of a multilinear morphism of `𝒪_X`-modules along `f : X ⟶ Y`: on an open
`U ⊆ Y` it is the multilinear map over `f⁻¹ U`, viewed as `𝒪_Y(U)`-multilinear through `f^♯`. -/
def pushforward (β : ModuleSheafMultilinear (R := X.sheaf) r F H) :
    ModuleSheafMultilinear (R := Y.sheaf) r ((Scheme.Modules.pushforward f).obj F)
      ((Scheme.Modules.pushforward f).obj H) where
  app U :=
    { toFun := fun m => β.app (op (f ⁻¹ᵁ U.unop)) m
      map_update_add' := fun m i x y => (β.app (op (f ⁻¹ᵁ U.unop))).map_update_add m i x y
      map_update_smul' := fun m i c x =>
        (β.app (op (f ⁻¹ᵁ U.unop))).map_update_smul m i (f.app U.unop c) x }
  naturality _ m := β.naturality _ m

theorem pushforward_app (β : ModuleSheafMultilinear (R := X.sheaf) r F H) (U : Y.Opensᵒᵖ)
    (m : Fin r → ((Scheme.Modules.pushforward f).obj F).val.obj U) :
    (β.pushforward f).app U m = β.app (op (f ⁻¹ᵁ U.unop)) m :=
  rfl

theorem IsAlternating.pushforward {β : ModuleSheafMultilinear (R := X.sheaf) r F H}
    (hβ : β.IsAlternating) : (β.pushforward f).IsAlternating :=
  fun _ m i j hij hne => hβ _ m i j hij hne

variable {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
  {A B C : SheafOfModules.{u} (siteRingCatSheaf R)}

theorem IsAlternating.precompHom {β : ModuleSheafMultilinear r B C} (hβ : β.IsAlternating)
    (α : A ⟶ B) : (β.precompHom α).IsAlternating :=
  fun U _ i j hij hne => hβ U _ i j (congrArg _ hij) hne

end ModuleSheafMultilinear

variable {k : Type u} [Field k] {V Y : Scheme.{u}} (f : V ⟶ Y) (p : Y ⟶ Spec (.of k))

/-- **Pullback of top differential forms.** The morphism
`⋀^n Ω_{Y/k} ⟶ f_*(⋀^n Ω_{V/k})`, `ω_1 ∧ ⋯ ∧ ω_n ↦ f^*ω_1 ∧ ⋯ ∧ f^*ω_n`. -/
def exteriorPowerPullback (n : ℕ) :
    moduleSheafExteriorPower (R := Y.sheaf) n (Scheme.relativeDifferentials p) ⟶
      (Scheme.Modules.pushforward f).obj
        (moduleSheafExteriorPower (R := V.sheaf) n (Scheme.relativeDifferentials (f ≫ p))) :=
  (moduleSheafExteriorPowerHomEquiv n _ _).symm
    ⟨((moduleSheafExteriorPowerMultilinear n _).pushforward f).precompHom
        (Scheme.relativeDifferentialsToPushforwardComp f p),
      ((moduleSheafExteriorPowerMultilinear_isAlternating).pushforward f).precompHom _⟩

/-- **Sections of an invertible sheaf on an integral scheme are determined on a nonempty open.**
Locally `L` has a one-element frame, and restriction of functions to a nonempty open is injective
on an integral scheme. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.presheaf_map_injective_of_isInvertible
    {X : Scheme.{u}} [IsIntegral X]
    {L : X.Modules} (hL : L.IsInvertible) {U U' : X.Opens} (h : U ≤ U') [hU : Nonempty U] :
    Function.Injective (L.val.map (homOfLE h).op) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hL' := (Scheme.Modules.isInvertible_iff_ringed L).1 hL
  refine SheafAlgebraOperations.sheaf_section_ext (R := X.sheaf) L s 0 fun x hx => ?_
  obtain ⟨Ux, hxUx, ⟨α⟩⟩ := hL' x
  let e : ULift.{u} (Fin 1) → L.val.presheaf.obj (op Ux) := fun i =>
    α.inv.val.app (op (Over.mk (𝟙 Ux))) (Ringed.freeVec Ux i)
  have hfr : Ringed.IsLocalFrame L Ux e := Ringed.isLocalFrame_of_over_iso α
  refine ⟨Ux ⊓ U', ⟨hxUx, hx⟩, homOfLE inf_le_right, ?_⟩
  obtain ⟨a, ha⟩ := (hfr (Ux ⊓ U') inf_le_left).2 (L.val.map (homOfLE inf_le_right).op s)
  have hne : ((Ux ⊓ U' : X.Opens) ⊓ U : Set X).Nonempty :=
    nonempty_preirreducible_inter (Ux ⊓ U').isOpen U.isOpen ⟨x, hxUx, hx⟩
      (Set.nonempty_coe_sort.1 hU)
  have : Nonempty ↥((Ux ⊓ U' ⊓ U : X.Opens) : Set X) := ⟨⟨hne.some, hne.some_mem⟩⟩
  have hres := Ringed.localFrameMap_restrict L e (inf_le_left : Ux ⊓ U' ≤ Ux)
    (inf_le_left : (Ux ⊓ U') ⊓ U ≤ Ux ⊓ U') a
  rw [ha] at hres
  have h0 : L.val.map (homOfLE (inf_le_left : (Ux ⊓ U') ⊓ U ≤ Ux ⊓ U')).op
      (L.val.map (homOfLE inf_le_right).op s) = 0 := by
    rw [← PresheafOfModules.map_comp_apply,
      Subsingleton.elim ((homOfLE (inf_le_right : Ux ⊓ U' ≤ U')).op ≫
          (homOfLE (inf_le_left : (Ux ⊓ U') ⊓ U ≤ Ux ⊓ U')).op)
        ((homOfLE h).op ≫ (homOfLE (inf_le_right : (Ux ⊓ U') ⊓ U ≤ U)).op),
      PresheafOfModules.map_comp_apply, hs]
    exact map_zero _
  have ha0 : a = 0 := by
    funext i
    apply map_injective_of_isIntegral (X := X)
      (homOfLE (inf_le_left : (Ux ⊓ U') ⊓ U ≤ Ux ⊓ U')) (H := this)
    have h1 : Ringed.localFrameMap L e (inf_le_left.trans inf_le_left)
        (fun i => X.sheaf.obj.map (homOfLE (inf_le_left : (Ux ⊓ U') ⊓ U ≤ Ux ⊓ U')).op (a i)) =
        Ringed.localFrameMap L e (inf_le_left.trans inf_le_left) 0 := by
      rw [map_zero]
      exact hres.symm.trans h0
    have := congrFun ((hfr _ (inf_le_left.trans inf_le_left)).1 h1) i
    exact this.trans (map_zero _).symm
  exact ha.symm.trans ((congrArg _ ha0).trans ((map_zero _).trans (map_zero _).symm))

/-- A morphism out of an invertible sheaf on an integral scheme is injective on global sections as
soon as it is injective on sections over one nonempty open. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.injective_app_top_of_isInvertible
    {X : Scheme.{u}} [IsIntegral X]
    {L M : X.Modules} (hL : L.IsInvertible) (φ : L ⟶ M) {U : X.Opens} [Nonempty U]
    (hU : Function.Injective (φ.val.app (op U))) : Function.Injective (φ.val.app (op ⊤)) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h1 : φ.val.app (op U) (L.val.map (homOfLE le_top).op s) = 0 := by
    rw [PresheafOfModules.naturality_apply, hs]
    exact map_zero _
  have h2 : L.val.map (homOfLE (le_top : U ≤ ⊤)).op s = 0 :=
    hU (h1.trans (map_zero _).symm)
  exact Scheme.Modules.presheaf_map_injective_of_isInvertible hL le_top
    (h2.trans (map_zero _).symm)

section OpenImmersion

open AlgebraicGeometry.Scheme

variable {W S : Scheme.{u}}

/-- For an open immersion `g : W ⟶ Y` and `p : Y ⟶ S`, the derivation
`𝒪_W ⟶ Ω_{Y/S}|_W`, `a ↦ d_{Y/S}((g^♯)⁻¹ a)`, relative to `(g ≫ p)^♯`. -/
noncomputable def openImmersionDerivation {Y : Scheme.{u}} (g : W ⟶ Y) [IsOpenImmersion g]
    (p : Y ⟶ S) :
    ((relativeDifferentials p).restrict g).val.Derivation
      (F := TopologicalSpace.Opens.map (g ≫ p).base) (g ≫ p).c where
  d {U} := ((relativeDifferentialsDerivation p).d (X := op (g ''ᵁ U.unop))).comp
    (g.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul {U} a b := by
    change (relativeDifferentialsDerivation p).d ((g.appIso U.unop).inv (a * b)) = _
    refine (congrArg (relativeDifferentialsDerivation p).d
      (map_mul (g.appIso U.unop).inv.hom a b)).trans ?_
    exact (relativeDifferentialsDerivation p).d_mul _ _
  d_map {U V} i a := by
    change (relativeDifferentialsDerivation p).d ((g.appIso V.unop).inv (W.presheaf.map i a)) = _
    refine (congrArg (relativeDifferentialsDerivation p).d
      (ConcreteCategory.congr_hom (Scheme.Hom.appIso_inv_naturality g i) a)).trans ?_
    exact (relativeDifferentialsDerivation p).d_map _ _
  d_app {T} t := by
    change (relativeDifferentialsDerivation p).d ((g.appIso (g ⁻¹ᵁ (p ⁻¹ᵁ T.unop))).inv
      (g.app (p ⁻¹ᵁ T.unop) (p.app T.unop t))) = 0
    refine (congrArg (relativeDifferentialsDerivation p).d
      (ConcreteCategory.congr_hom (Scheme.Hom.app_appIso_inv g (p ⁻¹ᵁ T.unop))
        (p.app T.unop t))).trans ?_
    refine ((relativeDifferentialsDerivation p).d_map _ _).trans ?_
    refine (congrArg _
      ((derivationOfInverseImage p (relativeDifferentialsDerivation p)).d_app t)).trans ?_
    exact map_zero _

/-- For `f : V ⟶ Y`, `j : W ⟶ V` with `j ≫ f` an open immersion, and `p : Y ⟶ S`, the derivation
`𝒪_V ⟶ j_*(Ω_{Y/S}|_W)`, `a ↦ d_{Y/S}(((j ≫ f)^♯)⁻¹ (j^♯ a))`, relative to `(f ≫ p)^♯`. -/
noncomputable def openImmersionPushforwardDerivation {V Y : Scheme.{u}} (f : V ⟶ Y)
    (j : W ⟶ V) [IsOpenImmersion (j ≫ f)] (p : Y ⟶ S) :
    ((Modules.pushforward j).obj ((relativeDifferentials p).restrict (j ≫ f))).val.Derivation
      (F := TopologicalSpace.Opens.map (f ≫ p).base) (f ≫ p).c where
  d {U} := ((openImmersionDerivation (j ≫ f) p).d (X := op (j ⁻¹ᵁ U.unop))).comp
    (j.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change (openImmersionDerivation (j ≫ f) p).d (j.app U.unop (a * b)) = _
    refine (congrArg (openImmersionDerivation (j ≫ f) p).d
      (map_mul (j.app U.unop).hom a b)).trans ?_
    exact (openImmersionDerivation (j ≫ f) p).d_mul _ _
  d_map {U U'} i a := by
    change (openImmersionDerivation (j ≫ f) p).d (j.c.app U' (V.presheaf.map i a)) = _
    refine (congrArg (openImmersionDerivation (j ≫ f) p).d
      (NatTrans.naturality_apply j.c i a)).trans ?_
    exact (openImmersionDerivation (j ≫ f) p).d_map _ _
  d_app {T} t := (openImmersionDerivation (j ≫ f) p).d_app (X := T) t

/-- The morphism `Ω_{V/S} ⟶ j_*(Ω_{Y/S}|_W)` attached to `openImmersionPushforwardDerivation`. -/
noncomputable def openImmersionDifferentialsMap {V Y : Scheme.{u}} (f : V ⟶ Y) (j : W ⟶ V)
    [IsOpenImmersion (j ≫ f)] (p : Y ⟶ S) :
    relativeDifferentials (f ≫ p) ⟶
      (Modules.pushforward j).obj ((relativeDifferentials p).restrict (j ≫ f)) :=
  (relativeDifferentialsHomEquiv (f ≫ p) _).symm
    (derivationToInverseImage (f ≫ p) (openImmersionPushforwardDerivation f j p))

variable {V Y : Scheme.{u}} (f : V ⟶ Y) (j : W ⟶ V) [IsOpenImmersion (j ≫ f)] (p : Y ⟶ S)

/-- `openImmersionDifferentialsMap` sends `d_{V/S} a` to `d_{Y/S}(((j ≫ f)^♯)⁻¹ (j^♯ a))`. -/
theorem openImmersionDifferentialsMap_d (U : V.Opensᵒᵖ) (a : V.presheaf.obj U) :
    (openImmersionDifferentialsMap f j p).val.app U
      ((relativeDifferentialsDerivation (f ≫ p)).d a) =
        (openImmersionPushforwardDerivation f j p).d a := by
  have h : (relativeDifferentialsDerivation (f ≫ p)).postcomp
      (openImmersionDifferentialsMap f j p).val =
        derivationToInverseImage (f ≫ p) (openImmersionPushforwardDerivation f j p) := by
    rw [← relativeDifferentialsHomEquiv_apply]
    exact Equiv.apply_symm_apply _ _
  exact PresheafOfModules.Derivation.congr_d h a

/-- Pulling back `Ω_{Y/S}` to `V` and then mapping to `j_*(Ω_{Y/S}|_W)` is the restriction of
`Ω_{Y/S}` to the open subscheme `W`. -/
theorem relativeDifferentialsToPushforwardComp_comp_openImmersionDifferentialsMap :
    relativeDifferentialsToPushforwardComp f p ≫
        (Modules.pushforward f).map (openImmersionDifferentialsMap f j p) =
      (Modules.restrictAdjunction (j ≫ f)).unit.app (relativeDifferentials p) ≫
        (Modules.pushforwardComp j f).inv.app _ := by
  apply (relativeDifferentialsHomEquiv p _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext U b
  change (openImmersionDifferentialsMap f j p).val.app (op (f ⁻¹ᵁ U.unop))
      ((relativeDifferentialsToPushforwardComp f p).val.app U
        ((relativeDifferentialsDerivation p).d b)) =
    (relativeDifferentials p).val.map (homOfLE ((j ≫ f).image_preimage_le U.unop)).op
      ((relativeDifferentialsDerivation p).d b)
  refine (congrArg ((openImmersionDifferentialsMap f j p).val.app (op (f ⁻¹ᵁ U.unop)))
    (relativeDifferentialsToPushforwardComp_d f p U b)).trans ?_
  refine (openImmersionDifferentialsMap_d f j p _ _).trans ?_
  change (relativeDifferentialsDerivation p).d (((j ≫ f).appIso ((j ≫ f) ⁻¹ᵁ U.unop)).inv
    ((j ≫ f).app U.unop b)) = _
  refine (congrArg (relativeDifferentialsDerivation p).d
    (ConcreteCategory.congr_hom (Scheme.Hom.app_appIso_inv (j ≫ f) U.unop) b)).trans ?_
  exact (relativeDifferentialsDerivation p).d_map _ _

end OpenImmersion

namespace ModuleSheafMultilinear

variable {X Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] {r : ℕ} {F H : Y.Modules}

/-- The restriction of a multilinear morphism of `𝒪_Y`-modules along an open immersion
`g : X ⟶ Y`: on an open `U ⊆ X` it is the multilinear map over `g(U)`. -/
def restrict (β : ModuleSheafMultilinear (R := Y.sheaf) r F H) :
    ModuleSheafMultilinear (R := X.sheaf) r (F.restrict g) (H.restrict g) where
  app U :=
    { toFun := fun m => β.app (op (g ''ᵁ U.unop)) m
      map_update_add' := fun m i x y => (β.app (op (g ''ᵁ U.unop))).map_update_add m i x y
      map_update_smul' := fun m i c x =>
        (β.app (op (g ''ᵁ U.unop))).map_update_smul m i ((g.appIso U.unop).inv c) x }
  naturality i m := β.naturality (g.opensFunctor.op.map i) m

theorem restrict_app (β : ModuleSheafMultilinear (R := Y.sheaf) r F H) (U : X.Opensᵒᵖ)
    (m : Fin r → (F.restrict g).val.obj U) :
    (β.restrict g).app U m = β.app (op (g ''ᵁ U.unop)) m :=
  rfl

theorem IsAlternating.restrict {β : ModuleSheafMultilinear (R := Y.sheaf) r F H}
    (hβ : β.IsAlternating) : (β.restrict g).IsAlternating :=
  fun _ m i j hij hne => hβ _ m i j hij hne

end ModuleSheafMultilinear

section ExteriorPower

variable {X : Scheme.{u}} {r : ℕ} {F H : X.Modules}

/-- The morphism `⋀^r F ⟶ H` attached to an alternating multilinear morphism `β` sends
`f₁ ∧ ⋯ ∧ fᵣ` to `β(f₁, …, fᵣ)`. -/
theorem moduleSheafExteriorPowerHomEquiv_symm_app
    (β : ModuleSheafMultilinear (R := X.sheaf) r F H) (hβ : β.IsAlternating) (U : X.Opensᵒᵖ)
    (m : Fin r → F.val.obj U) :
    ((moduleSheafExteriorPowerHomEquiv r F H).symm ⟨β, hβ⟩).val.app U
      ((moduleSheafExteriorPowerMultilinear r F).app U m) = β.app U m := by
  have h := congrArg Subtype.val
    (Equiv.apply_symm_apply (moduleSheafExteriorPowerHomEquiv r F H) ⟨β, hβ⟩)
  exact congrArg (fun γ : ModuleSheafMultilinear r F H => γ.app U m)
    ((moduleSheafExteriorPowerHomEquiv_apply _).symm.trans h)

/-- Morphisms out of `⋀^r F` agreeing on all local wedges `f₁ ∧ ⋯ ∧ fᵣ` are equal. -/
theorem moduleSheafExteriorPower_hom_ext
    {φ ψ : moduleSheafExteriorPower (R := X.sheaf) r F ⟶ H}
    (h : ∀ (U : X.Opensᵒᵖ) (m : Fin r → F.val.obj U),
      φ.val.app U ((moduleSheafExteriorPowerMultilinear r F).app U m) =
        ψ.val.app U ((moduleSheafExteriorPowerMultilinear r F).app U m)) : φ = ψ := by
  apply (moduleSheafExteriorPowerHomEquiv r F H).injective
  apply Subtype.ext
  refine (moduleSheafExteriorPowerHomEquiv_apply φ).trans
    (Eq.trans ?_ (moduleSheafExteriorPowerHomEquiv_apply ψ).symm)
  ext U m
  exact h U m

end ExteriorPower

section OpenImmersionExteriorPower

open AlgebraicGeometry.Scheme

variable {W V Y : Scheme.{u}} (f : V ⟶ Y) (j : W ⟶ V) [IsOpenImmersion (j ≫ f)]
  (p : Y ⟶ Spec (.of k))

/-- The morphism `⋀^n Ω_{V/k} ⟶ j_*((⋀^n Ω_{Y/k})|_W)`,
`ω₁ ∧ ⋯ ∧ ωₙ ↦ ψ ω₁ ∧ ⋯ ∧ ψ ωₙ`, where `ψ = openImmersionDifferentialsMap f j p`. -/
def openImmersionExteriorPowerMap (n : ℕ) :
    moduleSheafExteriorPower (R := V.sheaf) n (relativeDifferentials (f ≫ p)) ⟶
      (Modules.pushforward j).obj
        (Modules.restrict (moduleSheafExteriorPower (R := Y.sheaf) n (relativeDifferentials p))
          (j ≫ f)) :=
  (moduleSheafExteriorPowerHomEquiv n _ _).symm
    ⟨(((moduleSheafExteriorPowerMultilinear n _).restrict (j ≫ f)).pushforward j).precompHom
        (openImmersionDifferentialsMap f j p),
      (((moduleSheafExteriorPowerMultilinear_isAlternating).restrict (j ≫ f)).pushforward
        j).precompHom _⟩

/-- `exteriorPowerPullback` sends `ω₁ ∧ ⋯ ∧ ωₙ` to `f^*ω₁ ∧ ⋯ ∧ f^*ωₙ`. -/
theorem exteriorPowerPullback_app_wedge (n : ℕ) (U : Y.Opensᵒᵖ)
    (m : Fin n → (relativeDifferentials p).val.obj U) :
    (exteriorPowerPullback f p n).val.app U
        ((moduleSheafExteriorPowerMultilinear n _).app U m) =
      (moduleSheafExteriorPowerMultilinear n _).app (op (f ⁻¹ᵁ U.unop))
        (fun i => (relativeDifferentialsToPushforwardComp f p).val.app U (m i)) :=
  moduleSheafExteriorPowerHomEquiv_symm_app _ _ U m

/-- `openImmersionExteriorPowerMap` sends `ω₁ ∧ ⋯ ∧ ωₙ` to `ψ ω₁ ∧ ⋯ ∧ ψ ωₙ`. -/
theorem openImmersionExteriorPowerMap_app_wedge (n : ℕ) (U : V.Opensᵒᵖ)
    (m : Fin n → (relativeDifferentials (f ≫ p)).val.obj U) :
    (openImmersionExteriorPowerMap f j p n).val.app U
        ((moduleSheafExteriorPowerMultilinear n _).app U m) =
      (moduleSheafExteriorPowerMultilinear n _).app (op ((j ≫ f) ''ᵁ (j ⁻¹ᵁ U.unop)))
        (fun i => (openImmersionDifferentialsMap f j p).val.app U (m i)) :=
  moduleSheafExteriorPowerHomEquiv_symm_app _ _ U m

/-- Pulling back `⋀^n Ω_{Y/k}` to `V` and then mapping to `j_*((⋀^n Ω_{Y/k})|_W)` is the
restriction of `⋀^n Ω_{Y/k}` to the open subscheme `W`. -/
theorem exteriorPowerPullback_comp_openImmersionExteriorPowerMap (n : ℕ) :
    exteriorPowerPullback f p n ≫
        (Modules.pushforward f).map (openImmersionExteriorPowerMap f j p n) =
      (Modules.restrictAdjunction (j ≫ f)).unit.app
          (moduleSheafExteriorPower (R := Y.sheaf) n (relativeDifferentials p)) ≫
        (Modules.pushforwardComp j f).inv.app _ := by
  apply moduleSheafExteriorPower_hom_ext
  intro U m
  have hψ : ∀ x : (relativeDifferentials p).val.obj U,
      (openImmersionDifferentialsMap f j p).val.app (op (f ⁻¹ᵁ U.unop))
        ((relativeDifferentialsToPushforwardComp f p).val.app U x) =
      (relativeDifferentials p).val.map (homOfLE ((j ≫ f).image_preimage_le U.unop)).op x :=
    fun x => congrArg (fun φ => φ.val.app U x)
      (relativeDifferentialsToPushforwardComp_comp_openImmersionDifferentialsMap f j p)
  change (openImmersionExteriorPowerMap f j p n).val.app (op (f ⁻¹ᵁ U.unop))
      ((exteriorPowerPullback f p n).val.app U
        ((moduleSheafExteriorPowerMultilinear n _).app U m)) =
    (moduleSheafExteriorPower (R := Y.sheaf) n (relativeDifferentials p)).val.map
      (homOfLE ((j ≫ f).image_preimage_le U.unop)).op
      ((moduleSheafExteriorPowerMultilinear n _).app U m)
  rw [exteriorPowerPullback_app_wedge]
  refine (openImmersionExteriorPowerMap_app_wedge f j p n _ _).trans ?_
  refine Eq.trans ?_ ((moduleSheafExteriorPowerMultilinear n _).naturality _ m).symm
  exact congrArg _ (funext fun i => hψ (m i))

include j in
/-- **Pullback of top forms along a map that is an open immersion on a nonempty open is injective
on global sections**, when `Y` is integral and `⋀^n Ω_{Y/k}` is invertible. -/
theorem exteriorPowerPullback_app_top_injective [IsIntegral Y] [Nonempty W] (n : ℕ)
    (hL : Modules.IsInvertible
      (moduleSheafExteriorPower (R := Y.sheaf) n (relativeDifferentials p))) :
    Function.Injective ((exteriorPowerPullback f p n).val.app (op ⊤)) := by
  let g := j ≫ f
  have : Nonempty ↥((g ''ᵁ (g ⁻¹ᵁ (⊤ : Y.Opens)) : Y.Opens) : Set Y) :=
    ⟨⟨g (Classical.arbitrary W), Classical.arbitrary W, trivial, rfl⟩⟩
  have hinj := Scheme.Modules.presheaf_map_injective_of_isInvertible hL
    (g.image_preimage_le (⊤ : Y.Opens)) (hU := this)
  have h : ∀ x, (openImmersionExteriorPowerMap f j p n).val.app (op (f ⁻¹ᵁ ⊤))
      ((exteriorPowerPullback f p n).val.app (op ⊤) x) =
      (moduleSheafExteriorPower (R := Y.sheaf) n (relativeDifferentials p)).val.map
        (homOfLE (g.image_preimage_le (⊤ : Y.Opens))).op x :=
    fun x => congrArg (fun φ => φ.val.app (op ⊤) x)
      (exteriorPowerPullback_comp_openImmersionExteriorPowerMap f j p n)
  intro x y hxy
  exact hinj ((h x).symm.trans ((congrArg _ hxy).trans (h y)))

end OpenImmersionExteriorPower

section CanonicalPullback

open AlgebraicGeometry.Scheme

/-- Conjugating a morphism of module sheaves by transports `eqToHom` does not change injectivity
on sections. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.injective_app_eqToHom_comp_comp_eqToHom
    {X : Scheme.{u}} {A A' B B' : X.Modules} (hA : A = A') (hB : B = B') (φ : A' ⟶ B)
    (U : X.Opensᵒᵖ) (h : Function.Injective (φ.val.app U)) :
    Function.Injective ((eqToHom hA ≫ φ ≫ eqToHom hB).val.app U) := by
  subst hA hB
  exact fun _ _ hxy => h hxy

variable {X X' : Scheme.{u}} (pX : X ⟶ Spec (.of k)) (pX' : X' ⟶ Spec (.of k))

/-- The domain of a partial map out of an `n`-dimensional variety has dimension `n`. -/
theorem _root_.AlgebraicGeometry.Scheme.PartialMap.topologicalKrullDim_domain [IsIntegral X]
    (hpX : FiniteType pX) {n : ℕ} (hnX : topologicalKrullDim X = n) (φ : X.PartialMap X') :
    topologicalKrullDim φ.domain = n := by
  have : Nonempty φ.domain := φ.dense_domain.nonempty.to_subtype
  have : IsIntegral φ.domain := isIntegral_of_isOpenImmersion φ.domain.ι
  exact topologicalKrullDim_opens_eq pX hpX hnX φ.domain

/-- **Pullback of canonical sections.** For an open `V ⊆ X` and a `k`-morphism `f : V ⟶ X'`,
where `V` and `X'` have dimension `n`, pullback of differentials
`Γ(X', ω_{X'}) → Γ(V, ω_V)`, `ω_1 ∧ ⋯ ∧ ω_n ↦ f^*ω_1 ∧ ⋯ ∧ f^*ω_n`, as a morphism
`ω_{X'} ⟶ f_*ω_V`; its component at `X'` is the map on global sections. -/
def canonicalPullback {V : X.Opens} (f : (V : Scheme) ⟶ X') (hf : f ≫ pX' = V.ι ≫ pX) {n : ℕ}
    (hX' : topologicalKrullDim X' = n) (hV : topologicalKrullDim V = n) :
    canonicalSheaf pX' ⟶ (Modules.pushforward f).obj (canonicalSheaf (V.ι ≫ pX)) :=
  eqToHom (canonicalSheaf_eq pX' hX') ≫ exteriorPowerPullback f pX' n ≫
    eqToHom (congrArg (Modules.pushforward f).obj
      ((canonicalSheaf_eq (f ≫ pX') hV).symm.trans (congrArg canonicalSheaf hf)))

/-- `canonicalPullback` is injective on global sections as soon as `exteriorPowerPullback` is. -/
theorem canonicalPullback_app_top_injective {V : X.Opens} (f : (V : Scheme) ⟶ X')
    (hf : f ≫ pX' = V.ι ≫ pX) {n : ℕ} (hX' : topologicalKrullDim X' = n)
    (hV : topologicalKrullDim V = n)
    (h1 : Function.Injective ((exteriorPowerPullback f pX' n).val.app (op ⊤))) :
    Function.Injective ((canonicalPullback pX pX' f hf hX' hV).val.app (op ⊤)) :=
  Modules.injective_app_eqToHom_comp_comp_eqToHom _ _ _ _ h1

/-- If a partial map `φ` agrees on a dense open with a partial isomorphism, then `φ` is an open
immersion on a nonempty open of its domain. -/
theorem _root_.AlgebraicGeometry.Scheme.PartialMap.exists_isOpenImmersion [Nonempty X]
    (φ : X.PartialMap X') (e : X.PartialIso X') (he : e.toRationalMap = φ.toRationalMap) :
    ∃ (W : X.Opens) (hW : W ≤ φ.domain), Nonempty W ∧
      IsOpenImmersion (X.homOfLE hW ≫ φ.hom) := by
  obtain ⟨W, hW, hWl, hWr, heq⟩ := PartialMap.toRationalMap_eq_iff.mp he.symm
  refine ⟨W, hWl, hW.nonempty.to_subtype, ?_⟩
  have h : X.homOfLE hWl ≫ φ.hom =
      X.homOfLE (show W ≤ e.source from hWr) ≫ e.iso.hom ≫ e.target.ι := heq
  rw [h]
  infer_instance

/-- **Hartshorne II.8, proof of Theorem 8.19 (p. 181): pullback injects canonical sections.**
Let `X` and `X'` be nonsingular varieties of the same dimension `n` over an algebraically closed
field `k`, and let `φ` be a `k`-morphism `f : V ⟶ X'` on a dense open `V ⊆ X` representing a
birational map, i.e. agreeing on a dense open with a partial isomorphism `X ⤏ X'` over `k`. Then
pullback of differentials `Γ(X', ω_{X'}) → Γ(V, ω_V)` is injective. It is linear, being the
component at `X'` of the morphism of `𝒪_{X'}`-modules `canonicalPullback`. Of the hypotheses on
`X`, only integrality, finite type and dimension are used. -/
theorem canonicalPullback_injective [IsAlgClosed k] [IsIntegral X] [IsIntegral X']
    (hpX : FiniteType pX) (hpX' : FiniteType pX') (hX' : X'.IsRegular) {n : ℕ}
    (hnX : topologicalKrullDim X = n) (hnX' : topologicalKrullDim X' = n) (φ : X.PartialMap X')
    (hφ : φ.hom ≫ pX' = φ.domain.ι ≫ pX)
    (hbir : ∃ e : X.PartialIso X', e.IsOver pX pX' ∧ e.toRationalMap = φ.toRationalMap) :
    Function.Injective ((canonicalPullback pX pX' φ.hom hφ hnX'
      (φ.topologicalKrullDim_domain pX hpX hnX)).val.app (op ⊤)) := by
  obtain ⟨e, -, he⟩ := hbir
  obtain ⟨W, hWl, hW, hj⟩ := φ.exists_isOpenImmersion e he
  have hL := canonicalSheaf_isInvertible pX' hpX' hX' n hnX'
  rw [canonicalSheaf_eq pX' hnX'] at hL
  exact canonicalPullback_app_top_injective pX pX' φ.hom hφ hnX' _
    (exteriorPowerPullback_app_top_injective φ.hom (X.homOfLE hWl) pX' n hL)

end CanonicalPullback

end Hartshorne
