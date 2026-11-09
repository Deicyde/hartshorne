/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleGluing
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Gluing sheaves of modules along a locally directed open cover

WIP.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace CompatibleFamilies

open ModuleGluing

variable {T : TopCat.{u}} (S : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
  {ι A : Type u} (P : ι → SheafOfModules.{u} S) (src tgt : A → ι)
  (α : ∀ a, P (src a) ⟶ P (tgt a))

/-- The product of the `P i`, as a presheaf of modules. -/
noncomputable def piP : PresheafOfModules.{u} S.obj where
  obj V := ModuleCat.of (S.obj.obj V) (∀ i, (P i).val.obj V)
  map {V V'} f := ModuleCat.semilinearMapAddEquiv (S.obj.map f).hom _ _
    { toFun s i := (P i).val.map f (s i)
      map_add' x y := by funext i; exact map_add _ (x i) (y i)
      map_smul' r x := by funext i; exact (P i).val.map_smul f r (x i) }
  map_id V := by
    ext s
    funext i
    exact congrArg (fun g => g (s i)) (congrArg (fun g => ConcreteCategory.hom g)
      ((P i).val.map_id V))
  map_comp f g := by
    ext s
    funext i
    exact (P i).val.map_comp_apply f g (s i)

/-- The families `(s i)` with `α a (s (src a)) = s (tgt a)` for all `a`. -/
noncomputable def N : (piP S P).Submodule where
  obj V :=
    { carrier := {s | ∀ a, (α a).val.app V (s (src a)) = s (tgt a)}
      add_mem' {x y} hx hy a := by
        change (α a).val.app V (x (src a) + y (src a)) = x (tgt a) + y (tgt a)
        rw [map_add, hx a, hy a]
      zero_mem' a := by
        change (α a).val.app V 0 = 0
        rw [map_zero]
      smul_mem' r x hx a := by
        change (α a).val.app V (r • x (src a)) = r • x (tgt a)
        rw [map_smul, hx a] }
  map {V V'} f s hs a := by
    change (α a).val.app V' ((P (src a)).val.map f (s (src a))) =
      (P (tgt a)).val.map f (s (tgt a))
    rw [PresheafOfModules.naturality_apply, hs a]

/-- The presheaf of compatible families. -/
noncomputable abbrev Fpre : PresheafOfModules.{u} S.obj := (N S P src tgt α).toPresheafOfModules

lemma isSheaf_Fpre : Presheaf.IsSheaf (Opens.grothendieckTopology T) (Fpre S P src tgt α).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := T) _).2 ?_
  intro κ W sf hsf
  have hc : ∀ i k l, (P i).val.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op
      ((sf k).1 i) = (P i).val.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op
      ((sf l).1 i) := fun i k l =>
    congrArg (fun t : (Fpre S P src tgt α).obj _ => t.1 i) (hsf k l)
  choose g hg using fun i => sheaf_glue S (P i) W (fun k => le_iSup W k) le_rfl
    (fun k => (sf k).1 i) (hc i)
  have hmem : (g : (piP S P).obj (op (iSup W))) ∈ (N S P src tgt α).obj (op (iSup W)) := by
    intro a
    refine sheaf_ext S (P (tgt a)) W (fun k => le_iSup W k) le_rfl _ _ fun k => ?_
    rw [← PresheafOfModules.naturality_apply, hg, hg]
    exact (sf k).2 a
  refine ⟨⟨g, hmem⟩, fun k => ?_, fun t ht => ?_⟩
  · exact Subtype.ext (funext fun i => hg i k)
  · refine Subtype.ext (funext fun i => ?_)
    refine sheaf_ext S (P i) W (fun k => le_iSup W k) le_rfl _ _ fun k => ?_
    rw [hg]
    exact congrArg (fun t : (Fpre S P src tgt α).obj _ => t.1 i) (ht k)

/-- The sheaf of compatible families. -/
noncomputable def sheaf : SheafOfModules.{u} S := ⟨Fpre S P src tgt α, isSheaf_Fpre S P src tgt α⟩

/-- The projection to the `i`-th component. -/
noncomputable def π (i : ι) : sheaf S P src tgt α ⟶ P i where
  val :=
    { app V := ModuleCat.ofHom (X := (sheaf S P src tgt α).val.obj V) (Y := (P i).val.obj V)
        { toFun s := (s : ↥((N S P src tgt α).obj V)).1 i
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      naturality _ := rfl }

lemma π_apply (i : ι) (V : Opens T) (s : ↥((N S P src tgt α).obj (op V))) :
    (π S P src tgt α i).val.app (op V) s = s.1 i := rfl

end CompatibleFamilies

namespace DirectedModuleGluing

open AlgebraicGeometry Scheme.Modules

variable {Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y) [Category.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]
  [𝒰.LocallyDirected]

instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (𝒰.trans f) := 𝒰.property_trans f

lemma pmap_map {Z : Scheme.{u}} (M : Z.Modules) {a b c : Z.Opensᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (h : a ⟶ c) (x : M.presheaf.obj a) :
    M.presheaf.map g (M.presheaf.map f x) = M.presheaf.map h x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun k => M.presheaf.map k x) (Subsingleton.elim _ _)

lemma pmap_self {Z : Scheme.{u}} (M : Z.Modules) {a : Z.Opensᵒᵖ} (f : a ⟶ a)
    (x : M.presheaf.obj a) : M.presheaf.map f x = x := by
  rw [Subsingleton.elim f (𝟙 a), CategoryTheory.Functor.map_id]; rfl

omit [Quiver.IsThin 𝒰.I₀] in
lemma image_preimage_trans_le {i j : 𝒰.I₀} (f : i ⟶ j) (O : Y.Opens) :
    𝒰.trans f ''ᵁ (𝒰.f i ⁻¹ᵁ O) ≤ 𝒰.f j ⁻¹ᵁ O := by
  rintro _ ⟨x, hx, rfl⟩
  change (𝒰.f j) ((𝒰.trans f) x) ∈ O
  rw [← Scheme.Hom.comp_apply, 𝒰.trans_map]
  exact hx

/-- Descent data for modules along a locally directed open cover `𝒰` of `Y` (with a thin index
category): a module `M i` on each `𝒰.X i`, and isomorphisms `θ f : (M j)|_{𝒰.X i} ≅ M i` along the
transition maps `𝒰.X i ⟶ 𝒰.X j`, satisfying the cocycle condition. -/
structure Data where
  /-- The module on each piece. -/
  M : ∀ i, (𝒰.X i).Modules
  /-- The transition isomorphisms. -/
  θ : ∀ {i j : 𝒰.I₀} (f : i ⟶ j), (M j).restrict (𝒰.trans f) ≅ M i
  /-- The cocycle condition. -/
  θ_comp : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
    (θ (f ≫ g)).hom = (restrictFunctorCongr (𝒰.trans_comp f g)).hom.app (M k) ≫
      (restrictFunctorComp (𝒰.trans f) (𝒰.trans g)).hom.app (M k) ≫
      (restrictFunctor (𝒰.trans f)).map (θ g).hom ≫ (θ f).hom

namespace Data

variable {𝒰} (D : Data 𝒰)

/-- The arrows of the index category. -/
abbrev Arr : Type u := Σ (i j : 𝒰.I₀), (i ⟶ j)

/-- `M i` pushed forward to `Y`. -/
noncomputable abbrev P (i : 𝒰.I₀) : Y.Modules := (pushforward (𝒰.f i)).obj (D.M i)

/-- Restriction along `𝒰.X i ⟶ 𝒰.X j` followed by `θ f`, pushed forward to `Y`. -/
noncomputable def α (a : Arr (𝒰 := 𝒰)) : D.P a.2.1 ⟶ D.P a.1 :=
  (pushforward (𝒰.f a.2.1)).map ((restrictAdjunction (𝒰.trans a.2.2)).unit.app (D.M a.2.1)) ≫
    (pushforwardComp (𝒰.trans a.2.2) (𝒰.f a.2.1)).hom.app _ ≫
    (pushforwardCongr (𝒰.trans_map a.2.2)).hom.app _ ≫
    (pushforward (𝒰.f a.1)).map (D.θ a.2.2).hom

/-- The glued module: compatible families of sections of the `M i`. -/
noncomputable def glue : Y.Modules :=
  CompatibleFamilies.sheaf Y.ringCatSheaf D.P (fun a : Arr (𝒰 := 𝒰) => a.2.1) (fun a => a.1) D.α

/-- The projection `glue ⟶ (𝒰.f k)_* M k`. -/
noncomputable def πk (k : 𝒰.I₀) : D.glue ⟶ D.P k :=
  CompatibleFamilies.π Y.ringCatSheaf D.P (fun a : Arr (𝒰 := 𝒰) => a.2.1) (fun a => a.1) D.α k

/-- The comparison `glue|_{𝒰.X k} ⟶ M k`. -/
noncomputable def ψHom (k : 𝒰.I₀) : D.glue.restrict (𝒰.f k) ⟶ D.M k :=
  ((restrictAdjunction (𝒰.f k)).homEquiv _ _).symm (D.πk k)

lemma α_apply (a : Arr (𝒰 := 𝒰)) (O : Y.Opens) (x : Γ(D.M a.2.1, 𝒰.f a.2.1 ⁻¹ᵁ O)) :
    (D.α a).app O x = (D.θ a.2.2).hom.app (𝒰.f a.1 ⁻¹ᵁ O)
      ((D.M a.2.1).presheaf.map (homOfLE (image_preimage_trans_le 𝒰 a.2.2 O)).op x) := by
  simp only [α, Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app,
    pushforwardComp_hom_app_app, pushforwardCongr_hom_app_app]
  change (D.θ a.2.2).hom.app _ ((D.M a.2.1).presheaf.map _ ((D.M a.2.1).presheaf.map _ x)) = _
  congr 1
  exact pmap_map (D.M a.2.1) _ _ _ x

end Data

end DirectedModuleGluing

end Hartshorne
