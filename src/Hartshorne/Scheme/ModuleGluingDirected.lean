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

omit [Quiver.IsThin 𝒰.I₀] in
lemma comp_image_le {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k) (W : (𝒰.X i).Opens) :
    𝒰.trans g ''ᵁ (𝒰.trans f ''ᵁ W) ≤ 𝒰.trans (f ≫ g) ''ᵁ W := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨x, hx, ?_⟩
  change (𝒰.trans (f ≫ g)) x = (𝒰.trans g) ((𝒰.trans f) x)
  rw [𝒰.trans_comp, Scheme.Hom.comp_apply]

omit [Quiver.IsThin 𝒰.I₀] in
lemma comp_image_ge {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k) (W : (𝒰.X i).Opens) :
    𝒰.trans (f ≫ g) ''ᵁ W ≤ 𝒰.trans g ''ᵁ (𝒰.trans f ''ᵁ W) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
  change (𝒰.trans g) ((𝒰.trans f) x) = (𝒰.trans (f ≫ g)) x
  rw [𝒰.trans_comp, Scheme.Hom.comp_apply]

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

/-- The sections of the glued module over `O`: compatible families. -/
abbrev Sec (O : Y.Opens) : Type u :=
  ↥((CompatibleFamilies.N Y.ringCatSheaf D.P (fun a : Arr (𝒰 := 𝒰) => a.2.1) (fun a => a.1)
    D.α).obj (op O))

lemma sec_compat {O : Y.Opens} (s : D.Sec O) {i j : 𝒰.I₀} (f : i ⟶ j) :
    (D.θ f).hom.app (𝒰.f i ⁻¹ᵁ O)
      ((D.M j).presheaf.map (homOfLE (image_preimage_trans_le 𝒰 f O)).op (s.1 j)) = s.1 i :=
  (D.α_apply ⟨i, j, f⟩ O (s.1 j)).symm.trans (s.2 ⟨i, j, f⟩)

lemma θ_nat {i j : 𝒰.I₀} (f : i ⟶ j) {W W' : (𝒰.X i).Opens} (h : 𝒰.trans f ''ᵁ W' ≤ 𝒰.trans f ''ᵁ W)
    (h' : W' ≤ W) (x : Γ(D.M j, 𝒰.trans f ''ᵁ W)) :
    (D.θ f).hom.app W' ((D.M j).presheaf.map (homOfLE h).op x) =
      (D.M i).presheaf.map (homOfLE h').op ((D.θ f).hom.app W x) := by
  have := ConcreteCategory.congr_hom ((D.θ f).hom.mapPresheaf.naturality (homOfLE h').op) x
  refine (Eq.trans ?_ this).trans ?_
  · rfl
  · rfl

lemma θ_hom_inv {i j : 𝒰.I₀} (f : i ⟶ j) (W : (𝒰.X i).Opens) (x : Γ(D.M j, 𝒰.trans f ''ᵁ W)) :
    (D.θ f).inv.app W ((D.θ f).hom.app W x) = x :=
  congrArg (fun e => Hom.app e W x) (D.θ f).hom_inv_id

lemma θ_inv_hom {i j : 𝒰.I₀} (f : i ⟶ j) (W : (𝒰.X i).Opens) (x : Γ(D.M i, W)) :
    (D.θ f).hom.app W ((D.θ f).inv.app W x) = x :=
  congrArg (fun e => Hom.app e W x) (D.θ f).inv_hom_id

lemma θ_injective {i j : 𝒰.I₀} (f : i ⟶ j) (W : (𝒰.X i).Opens) :
    Function.Injective ((D.θ f).hom.app W) := fun x y hxy => by
  rw [← D.θ_hom_inv f W x, ← D.θ_hom_inv f W y, hxy]

lemma θ_comp_apply {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k) (W : (𝒰.X i).Opens)
    (x : Γ(D.M k, 𝒰.trans (f ≫ g) ''ᵁ W)) :
    (D.θ (f ≫ g)).hom.app W x = (D.θ f).hom.app W ((D.θ g).hom.app (𝒰.trans f ''ᵁ W)
      ((D.M k).presheaf.map (homOfLE (comp_image_le 𝒰 f g W)).op x)) := by
  rw [D.θ_comp f g]
  simp only [Hom.comp_app, restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app]
  change (D.θ f).hom.app W ((D.θ g).hom.app _ ((D.M k).presheaf.map _
    ((D.M k).presheaf.map _ x))) = _
  rw [pmap_map (D.M k) _ _ (homOfLE (comp_image_le 𝒰 f g W)).op x]

section pieces

variable {k : 𝒰.I₀} {O : Y.Opens}

omit [Quiver.IsThin 𝒰.I₀] in
variable (𝒰) in
lemma le_iSup_pieces (hO : O ≤ (𝒰.f k).opensRange) (i : 𝒰.I₀) :
    𝒰.f i ⁻¹ᵁ O ≤ iSup (fun p : Σ (l : 𝒰.I₀), (l ⟶ i) × (l ⟶ k) =>
      𝒰.trans p.2.1 ''ᵁ (𝒰.f p.1 ⁻¹ᵁ O)) := by
  intro x hx
  obtain ⟨y, hy⟩ := hO hx
  obtain ⟨l, a, b, xl, h1, h2⟩ := 𝒰.exists_of_f_eq_f x y hy.symm
  refine Opens.mem_iSup.2 ⟨⟨l, a, b⟩, xl, ?_, h1⟩
  change (𝒰.f l) xl ∈ O
  rw [← 𝒰.trans_map a, Scheme.Hom.comp_apply, h1]
  exact hx

variable (O) in
/-- The section of `M i` over the piece `𝒰.trans a '' (𝒰.f l)⁻¹ O` determined by a section `m`
of `M k`. -/
noncomputable def σ (m : Γ(D.M k, 𝒰.f k ⁻¹ᵁ O)) {l i : 𝒰.I₀} (a : l ⟶ i) (b : l ⟶ k) :
    Γ(D.M i, 𝒰.trans a ''ᵁ (𝒰.f l ⁻¹ᵁ O)) :=
  (D.θ a).inv.app (𝒰.f l ⁻¹ᵁ O) ((D.θ b).hom.app (𝒰.f l ⁻¹ᵁ O)
    ((D.M k).presheaf.map (homOfLE (image_preimage_trans_le 𝒰 b O)).op m))

lemma θ_σ (m : Γ(D.M k, 𝒰.f k ⁻¹ᵁ O)) {l i : 𝒰.I₀} (a : l ⟶ i) (b : l ⟶ k) :
    (D.θ a).hom.app (𝒰.f l ⁻¹ᵁ O) (D.σ O m a b) = (D.θ b).hom.app (𝒰.f l ⁻¹ᵁ O)
      ((D.M k).presheaf.map (homOfLE (image_preimage_trans_le 𝒰 b O)).op m) :=
  D.θ_inv_hom a _ _

lemma sec_piece (s : D.Sec O) {l i : 𝒰.I₀} (a : l ⟶ i) (b : l ⟶ k) :
    (D.M i).presheaf.map (homOfLE (image_preimage_trans_le 𝒰 a O)).op (s.1 i) =
      D.σ O (s.1 k) a b := by
  refine D.θ_injective a (𝒰.f l ⁻¹ᵁ O) ?_
  exact (D.sec_compat s a).trans ((D.sec_compat s b).symm.trans (D.θ_σ _ a b).symm)

lemma sec_ext (hO : O ≤ (𝒰.f k).opensRange) (s s' : D.Sec O) (h : s.1 k = s'.1 k) : s = s' := by
  refine Subtype.ext (funext fun i => ?_)
  have key : (s.1 i : Γ(D.M i, 𝒰.f i ⁻¹ᵁ O)) = s'.1 i := by
    refine ModuleGluing.sheaf_ext (𝒰.X i).ringCatSheaf (D.M i)
      (fun p : Σ (l : 𝒰.I₀), (l ⟶ i) × (l ⟶ k) => 𝒰.trans p.2.1 ''ᵁ (𝒰.f p.1 ⁻¹ᵁ O))
      (fun p => image_preimage_trans_le 𝒰 p.2.1 O) (le_iSup_pieces 𝒰 hO i) (s.1 i) (s'.1 i)
      fun p => ?_
    exact (D.sec_piece s p.2.1 p.2.2).trans ((congrArg (fun x => D.σ O x p.2.1 p.2.2) h).trans
    (D.sec_piece s' p.2.1 p.2.2).symm)
  exact key

lemma σ_restrict (m : Γ(D.M k, 𝒰.f k ⁻¹ᵁ O)) {l l' i : 𝒰.I₀} (a : l ⟶ i) (b : l ⟶ k)
    (c : l' ⟶ l) (h : 𝒰.trans (c ≫ a) ''ᵁ (𝒰.f l' ⁻¹ᵁ O) ≤ 𝒰.trans a ''ᵁ (𝒰.f l ⁻¹ᵁ O)) :
    (D.M i).presheaf.map (homOfLE h).op (D.σ O m a b) = D.σ O m (c ≫ a) (c ≫ b) := by
  have hc := image_preimage_trans_le 𝒰 c O
  refine D.θ_injective (c ≫ a) (𝒰.f l' ⁻¹ᵁ O) ?_
  rw [D.θ_σ, D.θ_comp_apply c a, D.θ_comp_apply c b]
  refine congrArg ((D.θ c).hom.app _) ?_
  rw [pmap_map (D.M i) _ _ (homOfLE (Scheme.Hom.image_mono _ hc)).op,
    D.θ_nat a (Scheme.Hom.image_mono _ hc) hc, D.θ_σ,
    ← D.θ_nat b (Scheme.Hom.image_mono _ hc) hc,
    pmap_map (D.M k) _ _ (homOfLE ((Scheme.Hom.image_mono _ hc).trans
      (image_preimage_trans_le 𝒰 b O))).op m,
    pmap_map (D.M k) _ _ (homOfLE ((Scheme.Hom.image_mono _ hc).trans
      (image_preimage_trans_le 𝒰 b O))).op m]

end pieces

end Data

end DirectedModuleGluing

end Hartshorne
