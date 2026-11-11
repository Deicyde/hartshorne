/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.Flatness.ModuleSheafFlatBaseChange
import Hartshorne.Scheme.CoherentFreeLocus
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat morphisms are stable under base change

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.2(b) (p. 254).

Proposition 9.2(b) is stated for an `𝒪_X`-module `F` flat over `Y`; a morphism `f : X → Y` is
flat when `F = 𝒪_X` is flat over `Y`. This file derives the morphism form from the module form
`AlgebraicGeometry.Scheme.Modules.FlatOver.baseChange` with `F = 𝒪_X`:

* the stalk of `𝒪_X`, regarded as an `𝒪_X`-module, is `𝒪_{X,x}` (`unitStalkLinearEquiv`), so
  `𝒪_X` is flat over `Y` exactly when every stalk map `𝒪_{Y,f(x)} → 𝒪_{X,x}` is flat, that is,
  when `f` is flat (`unit_flatOver_iff_flat`);
* the module pullback of `𝒪_X` along the projection `X ×_Y Y' → X` is `𝒪_{X ×_Y Y'}`
  (Mathlib's `SheafOfModules.pullbackObjUnitToUnit`), and flatness over a base is invariant
  under isomorphism of modules (`Scheme.Modules.FlatOver.of_iso`).
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}}

/-- The preimage functor on opens of a morphism of schemes is final: every comma category has
the terminal object `⊤`. -/
private theorem opensMap_final' (f : X ⟶ Y) : (Opens.map f.base).Final := by
  constructor
  intro U
  refine isConnected_of_isTerminal _
    (x := StructuredArrow.mk (homOfLE le_top : U ⟶ (Opens.map f.base).obj ⊤)) ?_
  refine IsTerminal.ofUniqueHom
    (fun A ↦ StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)) ?_
  intro A m
  ext
  exact Subsingleton.elim _ _

attribute [local instance] opensMap_final'

/-- The structure sheaf `𝒪_X`, regarded as an `𝒪_X`-module. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

section StalkEquiv

open FreeLocusAux

variable (x : X)

/-- The germ maps `Γ(U, 𝒪_X) → 𝒪_{X,x}`, as a cocone over the neighbourhoods of `x` in the
abelian presheaf underlying `𝒪_X` regarded as an `𝒪_X`-module. -/
def unitStalkCocone : Cocone ((OpenNhds.inclusion x).op ⋙ (unitModule X).presheaf) where
  pt := AddCommGrpCat.of (X.presheaf.stalk x)
  ι :=
    { app := fun U ↦ AddCommGrpCat.ofHom (X.presheaf.germ U.unop.1 x U.unop.2).hom.toAddMonoidHom
      naturality := fun U V i ↦ by
        ext s
        exact X.presheaf.germ_res_apply ((OpenNhds.inclusion x).map i.unop) x V.unop.2 s }

/-- The stalk of `𝒪_X`, regarded as an `𝒪_X`-module, maps to the local ring `𝒪_{X,x}` by sending
the germ of a section to its germ. -/
def unitStalkToStalk : (unitModule X).presheaf.stalk x →+ X.presheaf.stalk x :=
  (colimit.desc _ (unitStalkCocone x)).hom

theorem unitStalkToStalk_germ (U : X.Opens) (hx : x ∈ U) (s : Γ(unitModule X, U)) :
    unitStalkToStalk x ((unitModule X).presheaf.germ U x hx s) = X.presheaf.germ U x hx s :=
  colimit.ι_desc_apply (C := AddCommGrpCat.{u}) (unitStalkCocone x) (op (⟨U, hx⟩ : OpenNhds x)) s

theorem unitStalkToStalk_bijective : Function.Bijective (unitStalkToStalk x) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun m hm ↦ ?_, fun r ↦ ?_⟩
  · obtain ⟨U, hx, s, rfl⟩ := (unitModule X).presheaf.exists_germ_eq m
    rw [unitStalkToStalk_germ, ← map_zero (X.presheaf.germ U x hx).hom] at hm
    obtain ⟨W, hxW, iU, iU', h⟩ := X.presheaf.germ_eq x hx hx s 0 hm
    rw [← (unitModule X).presheaf.germ_res_apply iU x hxW s]
    change (unitModule X).presheaf.germ W x hxW (X.presheaf.map iU.op s) = 0
    rw [h, map_zero]
    exact map_zero ((unitModule X).presheaf.germ W x hxW).hom
  · obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq r
    exact ⟨(unitModule X).presheaf.germ U x hx s, unitStalkToStalk_germ x U hx s⟩

theorem unitStalkToStalk_smul (r : X.presheaf.stalk x)
    (m : (unitModule X).presheaf.stalk x) :
    unitStalkToStalk x (r • m) = r * unitStalkToStalk x m := by
  induction r, m using stalk_smul_induction x with
  | h U hx t s =>
    rw [← schemeModules_germ_smul, unitStalkToStalk_germ, unitStalkToStalk_germ]
    exact map_mul (X.presheaf.germ U x hx).hom t s

/-- The stalk of `𝒪_X`, regarded as an `𝒪_X`-module, is the local ring `𝒪_{X,x}`. -/
def unitStalkLinearEquiv :
    (unitModule X).presheaf.stalk x ≃ₗ[
      X.presheaf.stalk x] X.presheaf.stalk x :=
  LinearEquiv.ofBijective
    { toFun := unitStalkToStalk x
      map_add' := map_add _
      map_smul' := unitStalkToStalk_smul x }
    (unitStalkToStalk_bijective x)

/-- The stalk map `F_x → G_x` of a morphism of `𝒪_X`-modules. -/
def stalkHom {F G : X.Modules} (φ : F ⟶ G) : F.presheaf.stalk x ⟶ G.presheaf.stalk x :=
  (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ

theorem stalkHom_germ {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) (hx : x ∈ U) (s : Γ(F, U)) :
    stalkHom x φ (F.presheaf.germ U x hx s) = G.presheaf.germ U x hx (φ.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hx φ.mapPresheaf s

theorem stalkHom_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) :
    stalkHom x φ ≫ stalkHom x ψ = stalkHom x (φ ≫ ψ) :=
  ((Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
    φ ψ).symm

theorem stalkHom_id (F : X.Modules) : stalkHom x (𝟙 F) = 𝟙 _ :=
  (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_id F

/-- The stalk map of a morphism of `𝒪_X`-modules is `𝒪_{X,x}`-linear. -/
theorem stalkHom_smul {F G : X.Modules} (φ : F ⟶ G) (r : X.presheaf.stalk x)
    (m : F.presheaf.stalk x) : stalkHom x φ (r • m) = r • stalkHom x φ m := by
  induction r, m using stalk_smul_induction x with
  | h U hx t s =>
    rw [← schemeModules_germ_smul, stalkHom_germ, stalkHom_germ, ← schemeModules_germ_smul,
      Scheme.Modules.Hom.app_smul]

/-- An isomorphism of `𝒪_X`-modules induces an `𝒪_{X,x}`-linear isomorphism of stalks. -/
def stalkLinearEquivOfIso {F G : X.Modules} (e : F ≅ G) :
    F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] G.presheaf.stalk x where
  toFun := stalkHom x e.hom
  invFun := stalkHom x e.inv
  left_inv m := by
    change (stalkHom x e.hom ≫ stalkHom x e.inv) m = m
    rw [stalkHom_comp, e.hom_inv_id, stalkHom_id]
    rfl
  right_inv m := by
    change (stalkHom x e.inv ≫ stalkHom x e.hom) m = m
    rw [stalkHom_comp, e.inv_hom_id, stalkHom_id]
    rfl
  map_add' := map_add _
  map_smul' := stalkHom_smul x e.hom

end StalkEquiv

/-- Flatness over `Y` at `x` can be computed on any `𝒪_{X,x}`-module isomorphic to the stalk. -/
theorem flatOverAt_iff_of_linearEquiv (f : X ⟶ Y) (F : X.Modules) (x : X) {N : Type u}
    [AddCommGroup N] [Module (X.presheaf.stalk x) N]
    (e : F.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N) :
    F.FlatOverAt f x ↔
      letI : Module (Y.presheaf.stalk (f x)) N := Module.compHom N (f.stalkMap x).hom
      Module.Flat (Y.presheaf.stalk (f x)) N := by
  let : Module (Y.presheaf.stalk (f x)) N := Module.compHom N (f.stalkMap x).hom
  let : Module (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let e' : F.presheaf.stalk x ≃ₗ[Y.presheaf.stalk (f x)] N :=
    { e.toAddEquiv with map_smul' := fun r m ↦ e.map_smul ((f.stalkMap x).hom r) m }
  change Module.Flat (Y.presheaf.stalk (f x)) (F.presheaf.stalk x) ↔ _
  exact ⟨fun _ ↦ Module.Flat.of_linearEquiv e'.symm, fun _ ↦ Module.Flat.of_linearEquiv e'⟩

/-- Flatness over a base is invariant under isomorphism of modules. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.FlatOver.of_iso {f : X ⟶ Y} {F G : X.Modules}
    (hF : F.FlatOver f) (e : F ≅ G) : G.FlatOver f := fun x ↦
  (flatOverAt_iff_of_linearEquiv f G x (stalkLinearEquivOfIso x e.symm)).2 (hF x)

/-- `𝒪_X`, regarded as an `𝒪_X`-module, is flat over `Y` exactly when `f` is flat. -/
theorem unit_flatOver_iff_flat (f : X ⟶ Y) :
    (unitModule X).FlatOver f ↔ Flat f := by
  rw [Flat.iff_flat_stalkMap]
  refine forall_congr' fun x ↦ ?_
  rw [flatOverAt_iff_of_linearEquiv f _ x (unitStalkLinearEquiv x)]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The module pullback of `𝒪_Y` along a morphism `f : X ⟶ Y` is `𝒪_X`. -/
def pullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (unitModule Y) ≅ unitModule X := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  exact asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

/-- **Hartshorne III.9, Proposition 9.2(b), for morphisms.** If `f : X → Y` is flat, then for any
`g : Y' → Y` the projection `X ×_Y Y' → Y'` is flat. This is the module form
`Scheme.Modules.FlatOver.baseChange` with `F = 𝒪_X`. -/
theorem flat_pullback_snd {Y' : Scheme.{u}} (f : X ⟶ Y) [Flat f] (g : Y' ⟶ Y) :
    Flat (pullback.snd f g) := by
  have hX : (unitModule X).FlatOver f :=
    (unit_flatOver_iff_flat f).2 inferInstance
  exact (unit_flatOver_iff_flat _).1
    ((Scheme.Modules.FlatOver.baseChange hX g).of_iso (pullbackUnitIso (pullback.fst f g)))

/-- **Hartshorne III.9, Proposition 9.2(b), for morphisms.** Flat morphisms are stable under base
change: in a cartesian square of schemes, a pullback of a flat morphism is flat. -/
theorem flat_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@Flat : MorphismProperty Scheme.{u}) :=
  haveI : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.mk _
      (fun e f hf ↦ MorphismProperty.comp_mem _ _ _ (inferInstance : Flat e.hom) hf)
      (fun e f hf ↦ MorphismProperty.comp_mem _ _ _ hf (inferInstance : Flat e.hom))
  MorphismProperty.IsStableUnderBaseChange.mk' fun X Y S f g _ hg ↦ by
    have := hg
    rw [← pullbackSymmetry_hom_comp_snd]
    exact MorphismProperty.comp_mem _ _ _ (inferInstance : Flat (pullbackSymmetry f g).hom)
      (flat_pullback_snd g f)

end

end Hartshorne
