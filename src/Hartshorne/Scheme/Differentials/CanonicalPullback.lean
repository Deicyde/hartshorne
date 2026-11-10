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

/-!
# Pullback of canonical sections (work in progress)

Hartshorne, *Algebraic Geometry*, II.8, proof of Theorem 8.19 (p. 181).

* `Hartshorne.exteriorPowerPullback`: for a morphism `f : V ⟶ Y` and `p : Y ⟶ Spec k`, pullback
  of differentials induces `⋀^n Ω_{Y/k} ⟶ f_*(⋀^n Ω_{V/k})`,
  `ω_1 ∧ ⋯ ∧ ω_n ↦ f^*ω_1 ∧ ⋯ ∧ f^*ω_n`. It is built from the universal property of the
  exterior power, using the pushforward of the universal alternating map of `Ω_{V/k}`
  (`Hartshorne.ModuleSheafMultilinear.pushforward`).
* `AlgebraicGeometry.Scheme.Modules.presheaf_map_injective_of_isInvertible`: on an integral
  scheme, restriction of sections of an invertible sheaf to a nonempty open is injective.
* `AlgebraicGeometry.Scheme.Modules.injective_app_top_of_isInvertible`: a morphism out of an
  invertible sheaf on an integral scheme is injective on global sections if it is injective on
  sections over one nonempty open.

The injectivity of `Γ(Y, ω_Y) → Γ(V, ω_V)` for a birational `f` is not yet proved; it needs the
compatibility of relative differentials with open immersions (see the implementation note of the
article `canonical-pullback-injective`).
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

end Hartshorne
