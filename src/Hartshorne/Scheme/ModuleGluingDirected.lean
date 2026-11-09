/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleGluing
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Gluing sheaves of modules along a locally directed open cover

Let `𝒰` be a locally directed open cover of a scheme `Y` whose index category is thin (for
example the cover of a relative `Proj` by the affine pieces `Proj S(U)`, indexed by the affine
opens `U` of the base). Suppose given a module `M i` on each piece `𝒰.X i` and isomorphisms
`θ f : (M j)|_{𝒰.X i} ≅ M i` along the transition maps `𝒰.X i ⟶ 𝒰.X j`, satisfying the cocycle
condition. Then the `M i` glue to an `𝒪_Y`-module `M` with isomorphisms
`ψ i : M|_{𝒰.X i} ≅ M i` compatible with the `θ f`.

This is the form of the gluing of sheaves of modules (Hartshorne II, Exercise 1.22, glues
sheaves; the module form is a supplement) used for the relative twisting sheaf of II.7, where the
descent data are indexed by the inclusions of affine opens rather than by pairwise intersections.

## Construction

`Hartshorne.CompatibleFamilies.sheaf` is, for a family of sheaves of modules `P i` on a ringed
space and morphisms `α a : P (src a) ⟶ P (tgt a)`, the sheaf of families `(s i)` with
`α a (s (src a)) = s (tgt a)`. Here `P i = (𝒰.f i)_* M i` and `α f` is restriction along the
transition map followed by `θ f`. Over an open `O` inside the image of `𝒰.X k`, a compatible
family is determined by its `k`-th component, and every section of `M k` extends: the pieces
`𝒰.X l` with `l ⟶ i` and `l ⟶ k` cover `(𝒰.f i)⁻¹ O`, on which the `i`-th component is forced
to be `θ⁻¹ ∘ θ` applied to the `k`-th, and these local sections agree on overlaps by the cocycle
condition. This gives the isomorphisms `ψ k`.

## Main results

* `Hartshorne.DirectedModuleGluing.Data`: the descent data.
* `Hartshorne.DirectedModuleGluing.Data.glue`, `Data.ψ`, `Data.ψ_compat`: the glued module, its
  restrictions to the pieces, and their compatibility with the transition isomorphisms.
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

lemma isSheaf_Fpre :
    Presheaf.IsSheaf (Opens.grothendieckTopology T) (Fpre S P src tgt α).presheaf := by
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

omit [Quiver.IsThin 𝒰.I₀] in
instance isOpenImmersion_trans {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (𝒰.trans f) :=
  𝒰.property_trans f

lemma pmap_map {Z : Scheme.{u}} (M : Z.Modules) {a b c : Z.Opensᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (h : a ⟶ c) (x : M.presheaf.obj a) :
    M.presheaf.map g (M.presheaf.map f x) = M.presheaf.map h x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun k => M.presheaf.map k x) (Subsingleton.elim _ _)

lemma pmap_map_eq {Z : Scheme.{u}} (M : Z.Modules) {a b b' c : Z.Opensᵒᵖ} (f : a ⟶ b)
    (g : b ⟶ c) (f' : a ⟶ b') (g' : b' ⟶ c) (x : M.presheaf.obj a) :
    M.presheaf.map g (M.presheaf.map f x) = M.presheaf.map g' (M.presheaf.map f' x) := by
  rw [pmap_map M f g (f ≫ g), pmap_map M f' g' (f ≫ g)]

lemma pmap_map3_eq {Z : Scheme.{u}} (M : Z.Modules) {a b c d b' : Z.Opensᵒᵖ} (f : a ⟶ b)
    (g : b ⟶ c) (h : c ⟶ d) (f' : a ⟶ b') (g' : b' ⟶ d) (x : M.presheaf.obj a) :
    M.presheaf.map h (M.presheaf.map g (M.presheaf.map f x)) =
      M.presheaf.map g' (M.presheaf.map f' x) := by
  rw [pmap_map M f g (f ≫ g), pmap_map M (f ≫ g) h (f' ≫ g'), pmap_map M f' g' (f' ≫ g')]

lemma pmap_comp_apply {Z : Scheme.{u}} (M : Z.Modules) {a b c : Z.Opensᵒᵖ} (f : a ⟶ b)
    (g : b ⟶ c) (x : M.presheaf.obj a) :
    M.presheaf.map g (M.presheaf.map f x) = M.presheaf.map (f ≫ g) x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]

lemma pmap_self {Z : Scheme.{u}} (M : Z.Modules) {a : Z.Opensᵒᵖ} (f : a ⟶ a)
    (x : M.presheaf.obj a) : M.presheaf.map f x = x := by
  rw [Subsingleton.elim f (𝟙 a), CategoryTheory.Functor.map_id]; rfl

lemma mod_ext {Z : Scheme.{u}} (M : Z.Modules) {V : Z.Opens} {κ : Type u} (W : κ → Z.Opens)
    (hW : ∀ k, W k ≤ V) (hcov : V ≤ iSup W) (s t : Γ(M, V))
    (h : ∀ k, M.presheaf.map (homOfLE (hW k)).op s = M.presheaf.map (homOfLE (hW k)).op t) :
    s = t :=
  ModuleGluing.sheaf_ext Z.ringCatSheaf M W hW hcov s t h

lemma mod_glue {Z : Scheme.{u}} (M : Z.Modules) {V : Z.Opens} {κ : Type u} (W : κ → Z.Opens)
    (hW : ∀ k, W k ≤ V) (hcov : V ≤ iSup W) (sf : ∀ k, Γ(M, W k))
    (hc : ∀ k l, M.presheaf.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op (sf k) =
      M.presheaf.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op (sf l)) :
    ∃ s : Γ(M, V), ∀ k, M.presheaf.map (homOfLE (hW k)).op s = sf k :=
  ModuleGluing.sheaf_glue Z.ringCatSheaf M W hW hcov sf hc

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
  (restrictFunctor (𝒰.f k)).map (D.πk k) ≫ (restrictAdjunction (𝒰.f k)).counit.app (D.M k)

omit [Quiver.IsThin 𝒰.I₀] in
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

omit [Quiver.IsThin 𝒰.I₀] in
lemma sec_compat {O : Y.Opens} (s : D.Sec O) {i j : 𝒰.I₀} (f : i ⟶ j) :
    (D.θ f).hom.app (𝒰.f i ⁻¹ᵁ O)
      ((D.M j).presheaf.map (homOfLE (image_preimage_trans_le 𝒰 f O)).op (s.1 j)) = s.1 i :=
  (D.α_apply ⟨i, j, f⟩ O (s.1 j)).symm.trans (s.2 ⟨i, j, f⟩)

omit [Quiver.IsThin 𝒰.I₀] in
lemma θ_nat {i j : 𝒰.I₀} (f : i ⟶ j) {W W' : (𝒰.X i).Opens} (h : 𝒰.trans f ''ᵁ W' ≤ 𝒰.trans f ''ᵁ W)
    (h' : W' ≤ W) (x : Γ(D.M j, 𝒰.trans f ''ᵁ W)) :
    (D.θ f).hom.app W' ((D.M j).presheaf.map (homOfLE h).op x) =
      (D.M i).presheaf.map (homOfLE h').op ((D.θ f).hom.app W x) := by
  have := ConcreteCategory.congr_hom ((D.θ f).hom.mapPresheaf.naturality (homOfLE h').op) x
  refine (Eq.trans ?_ this).trans ?_
  · rfl
  · rfl

omit [Quiver.IsThin 𝒰.I₀] in
lemma θ_hom_inv {i j : 𝒰.I₀} (f : i ⟶ j) (W : (𝒰.X i).Opens) (x : Γ(D.M j, 𝒰.trans f ''ᵁ W)) :
    (D.θ f).inv.app W ((D.θ f).hom.app W x) = x :=
  congrArg (fun e => Hom.app e W x) (D.θ f).hom_inv_id

omit [Quiver.IsThin 𝒰.I₀] in
lemma θ_inv_hom {i j : 𝒰.I₀} (f : i ⟶ j) (W : (𝒰.X i).Opens) (x : Γ(D.M i, W)) :
    (D.θ f).hom.app W ((D.θ f).inv.app W x) = x :=
  congrArg (fun e => Hom.app e W x) (D.θ f).inv_hom_id

omit [Quiver.IsThin 𝒰.I₀] in
lemma θ_injective {i j : 𝒰.I₀} (f : i ⟶ j) (W : (𝒰.X i).Opens) :
    Function.Injective ((D.θ f).hom.app W) := fun x y hxy => by
  rw [← D.θ_hom_inv f W x, ← D.θ_hom_inv f W y, hxy]

omit [Quiver.IsThin 𝒰.I₀] in
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

omit [Quiver.IsThin 𝒰.I₀] in
lemma θ_σ (m : Γ(D.M k, 𝒰.f k ⁻¹ᵁ O)) {l i : 𝒰.I₀} (a : l ⟶ i) (b : l ⟶ k) :
    (D.θ a).hom.app (𝒰.f l ⁻¹ᵁ O) (D.σ O m a b) = (D.θ b).hom.app (𝒰.f l ⁻¹ᵁ O)
      ((D.M k).presheaf.map (homOfLE (image_preimage_trans_le 𝒰 b O)).op m) :=
  D.θ_inv_hom a _ _

omit [Quiver.IsThin 𝒰.I₀] in
lemma sec_piece (s : D.Sec O) {l i : 𝒰.I₀} (a : l ⟶ i) (b : l ⟶ k) :
    (D.M i).presheaf.map (homOfLE (image_preimage_trans_le 𝒰 a O)).op (s.1 i) =
      D.σ O (s.1 k) a b := by
  refine D.θ_injective a (𝒰.f l ⁻¹ᵁ O) ?_
  exact (D.sec_compat s a).trans ((D.sec_compat s b).symm.trans (D.θ_σ _ a b).symm)

omit [Quiver.IsThin 𝒰.I₀] in
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

omit [Quiver.IsThin 𝒰.I₀] in
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

lemma σ_restrict' (m : Γ(D.M k, 𝒰.f k ⁻¹ᵁ O)) {l l' i : 𝒰.I₀} (a : l ⟶ i) (b : l ⟶ k)
    (e : l' ⟶ i) (e' : l' ⟶ k) (c : l' ⟶ l)
    (h : 𝒰.trans e ''ᵁ (𝒰.f l' ⁻¹ᵁ O) ≤ 𝒰.trans a ''ᵁ (𝒰.f l ⁻¹ᵁ O)) :
    (D.M i).presheaf.map (homOfLE h).op (D.σ O m a b) = D.σ O m e e' := by
  obtain rfl : e = c ≫ a := Subsingleton.elim _ _
  obtain rfl : e' = c ≫ b := Subsingleton.elim _ _
  exact D.σ_restrict m a b c h

omit [Quiver.IsThin 𝒰.I₀] in
lemma piece_mono {l l' i : 𝒰.I₀} (a : l ⟶ i) (c : l' ⟶ l) :
    𝒰.trans (c ≫ a) ''ᵁ (𝒰.f l' ⁻¹ᵁ O) ≤ 𝒰.trans a ''ᵁ (𝒰.f l ⁻¹ᵁ O) :=
  (comp_image_ge 𝒰 c a _).trans (Scheme.Hom.image_mono _ (image_preimage_trans_le 𝒰 c O))

lemma σ_compatible (m : Γ(D.M k, 𝒰.f k ⁻¹ᵁ O)) (i : 𝒰.I₀)
    (p p' : Σ (l : 𝒰.I₀), (l ⟶ i) × (l ⟶ k)) :
    (D.M i).presheaf.map (homOfLE (inf_le_left : 𝒰.trans p.2.1 ''ᵁ (𝒰.f p.1 ⁻¹ᵁ O) ⊓
      𝒰.trans p'.2.1 ''ᵁ (𝒰.f p'.1 ⁻¹ᵁ O) ≤ _)).op (D.σ O m p.2.1 p.2.2) =
    (D.M i).presheaf.map (homOfLE (inf_le_right : 𝒰.trans p.2.1 ''ᵁ (𝒰.f p.1 ⁻¹ᵁ O) ⊓
      𝒰.trans p'.2.1 ''ᵁ (𝒰.f p'.1 ⁻¹ᵁ O) ≤ _)).op (D.σ O m p'.2.1 p'.2.2) := by
  obtain ⟨l, a, b⟩ := p
  obtain ⟨l', a', b'⟩ := p'
  have hle : ∀ q : Σ (l'' : 𝒰.I₀), (l'' ⟶ l) × (l'' ⟶ l'),
      𝒰.trans (q.2.1 ≫ a) ''ᵁ (𝒰.f q.1 ⁻¹ᵁ O) ≤
        𝒰.trans a ''ᵁ (𝒰.f l ⁻¹ᵁ O) ⊓ 𝒰.trans a' ''ᵁ (𝒰.f l' ⁻¹ᵁ O) := fun q =>
    le_inf (piece_mono a q.2.1) (by
      rw [Subsingleton.elim (q.2.1 ≫ a) (q.2.2 ≫ a')]
      exact piece_mono a' q.2.2)
  refine mod_ext (D.M i)
    (fun q : Σ (l'' : 𝒰.I₀), (l'' ⟶ l) × (l'' ⟶ l') => 𝒰.trans (q.2.1 ≫ a) ''ᵁ (𝒰.f q.1 ⁻¹ᵁ O))
    hle ?_ _ _ fun q => ?_
  · rintro x ⟨⟨xl, hxl, rfl⟩, ⟨xl', hxl', hx⟩⟩
    obtain ⟨l'', c, c', x'', h1, h2⟩ := 𝒰.exists_of_trans_eq_trans a a' xl xl' hx.symm
    refine Opens.mem_iSup.2 ⟨⟨l'', c, c'⟩, x'', ?_, ?_⟩
    · change (𝒰.f l'') x'' ∈ O
      rw [← 𝒰.trans_map c, Scheme.Hom.comp_apply, h1]
      exact hxl
    · change (𝒰.trans (c ≫ a)) x'' = (𝒰.trans a) xl
      rw [𝒰.trans_comp, Scheme.Hom.comp_apply, h1]
  · rw [pmap_map (D.M i) _ _ (homOfLE (piece_mono a q.2.1)).op,
      pmap_map (D.M i) _ _ (homOfLE ((hle q).trans inf_le_right)).op,
      D.σ_restrict' m a b (q.2.1 ≫ a) (q.2.1 ≫ b) q.2.1,
      D.σ_restrict' m a' b' (q.2.1 ≫ a) (q.2.1 ≫ b) q.2.2]

lemma exists_sec (hO : O ≤ (𝒰.f k).opensRange) (m : Γ(D.M k, 𝒰.f k ⁻¹ᵁ O)) :
    ∃ s : D.Sec O, s.1 k = m := by
  choose g hg using fun i => mod_glue (D.M i)
    (fun p : Σ (l : 𝒰.I₀), (l ⟶ i) × (l ⟶ k) => 𝒰.trans p.2.1 ''ᵁ (𝒰.f p.1 ⁻¹ᵁ O))
    (fun p => image_preimage_trans_le 𝒰 p.2.1 O) (le_iSup_pieces 𝒰 hO i)
    (fun p => D.σ O m p.2.1 p.2.2) (D.σ_compatible m i)
  have hmem : (g : (CompatibleFamilies.piP Y.ringCatSheaf D.P).obj (op O)) ∈
      (CompatibleFamilies.N Y.ringCatSheaf D.P (fun a : Arr (𝒰 := 𝒰) => a.2.1) (fun a => a.1)
        D.α).obj (op O) := by
    rintro ⟨i, j, f⟩
    change (D.α ⟨i, j, f⟩).app O (g j) = g i
    rw [D.α_apply]
    refine mod_ext (D.M i)
      (fun p : Σ (l : 𝒰.I₀), (l ⟶ i) × (l ⟶ k) => 𝒰.trans p.2.1 ''ᵁ (𝒰.f p.1 ⁻¹ᵁ O))
      (fun p => image_preimage_trans_le 𝒰 p.2.1 O) (le_iSup_pieces 𝒰 hO i) _ _ fun p => ?_
    rw [hg i p]
    obtain ⟨l, a, b⟩ := p
    have ha := image_preimage_trans_le 𝒰 a O
    rw [← D.θ_nat f (Scheme.Hom.image_mono _ ha) ha,
      pmap_map_eq (D.M j) _ _ (homOfLE (image_preimage_trans_le 𝒰 (a ≫ f) O)).op
        (homOfLE (comp_image_le 𝒰 a f _)).op, hg j ⟨l, a ≫ f, b⟩]
    refine D.θ_injective a _ ?_
    rw [D.θ_σ, ← D.θ_comp_apply a f, D.θ_σ]
  refine ⟨⟨g, hmem⟩, ?_⟩
  change g k = m
  refine mod_ext (D.M k)
    (fun p : Σ (l : 𝒰.I₀), (l ⟶ k) × (l ⟶ k) => 𝒰.trans p.2.1 ''ᵁ (𝒰.f p.1 ⁻¹ᵁ O))
    (fun p => image_preimage_trans_le 𝒰 p.2.1 O) (le_iSup_pieces 𝒰 hO k) _ _ fun p => ?_
  rw [hg k p]
  obtain ⟨l, a, b⟩ := p
  obtain rfl : b = a := Subsingleton.elim _ _
  refine D.θ_injective b _ ?_
  rw [D.θ_σ]

end pieces

omit [Quiver.IsThin 𝒰.I₀] in
lemma ψHom_apply (k : 𝒰.I₀) (W : (𝒰.X k).Opens) (s : D.Sec (𝒰.f k ''ᵁ W)) :
    (D.ψHom k).app W s =
      (D.M k).presheaf.map (eqToHom (Scheme.Hom.preimage_image_eq _ W).symm).op (s.1 k) := by
  rfl

lemma ψHom_bijective (k : 𝒰.I₀) (W : (𝒰.X k).Opens) :
    Function.Bijective ((D.ψHom k).app W) := by
  have hO : 𝒰.f k ''ᵁ W ≤ (𝒰.f k).opensRange := Scheme.Hom.image_le_opensRange _ W
  constructor
  · intro (s : D.Sec (𝒰.f k ''ᵁ W)) (s' : D.Sec (𝒰.f k ''ᵁ W)) h
    rw [D.ψHom_apply, D.ψHom_apply] at h
    refine D.sec_ext hO s s' ?_
    have := congrArg ((D.M k).presheaf.map
      (eqToHom (Scheme.Hom.preimage_image_eq (𝒰.f k) W)).op) h
    exact ((pmap_map (D.M k) _ _ (𝟙 _) _).trans (pmap_self _ _ _)).symm.trans
      (this.trans ((pmap_map (D.M k) _ _ (𝟙 _) _).trans (pmap_self _ _ _)))
  · intro m
    obtain ⟨s, hs⟩ := D.exists_sec hO ((D.M k).presheaf.map
      (eqToHom (Scheme.Hom.preimage_image_eq (𝒰.f k) W)).op m)
    refine ⟨s, ?_⟩
    rw [D.ψHom_apply, hs, pmap_map (D.M k) _ _ (𝟙 _), pmap_self]

instance isIso_ψHom (k : 𝒰.I₀) : IsIso (D.ψHom k) :=
  ModuleGluing.isIso_of_bijective _ fun W => D.ψHom_bijective k W.unop

/-- The isomorphisms `glue|_{𝒰.X k} ≅ M k`. -/
noncomputable def ψ (k : 𝒰.I₀) : D.glue.restrict (𝒰.f k) ≅ D.M k := asIso (D.ψHom k)

/-- The isomorphisms `ψ` are compatible with the transition isomorphisms: along `f : i ⟶ j`,
`θ f ∘ (ψ j)|_{𝒰.X i} = ψ i` (up to the canonical identifications of restrictions). -/
theorem ψ_compat {i j : 𝒰.I₀} (f : i ⟶ j) :
    (restrictFunctorCongr (𝒰.trans_map f)).inv.app D.glue ≫
      (restrictFunctorComp (𝒰.trans f) (𝒰.f j)).hom.app D.glue ≫
      (restrictFunctor (𝒰.trans f)).map (D.ψ j).hom ≫ (D.θ f).hom = (D.ψ i).hom := by
  apply Scheme.Modules.hom_ext
  intro W
  ext x
  simp only [Hom.comp_app, restrictFunctorCongr_inv_app_app, restrictFunctorComp_hom_app_app]
  let x' : D.Sec (𝒰.f i ''ᵁ W) := x
  have hW : W ≤ 𝒰.f i ⁻¹ᵁ (𝒰.f i ''ᵁ W) := (Scheme.Hom.preimage_image_eq _ W).ge
  change (D.θ f).hom.app W ((D.M j).presheaf.map _ ((D.M j).presheaf.map _
    ((D.M j).presheaf.map _ (x'.1 j)))) = (D.M i).presheaf.map _ (x'.1 i)
  refine (congrArg ((D.θ f).hom.app W) (pmap_map3_eq (D.M j) _ _ _
    (homOfLE (image_preimage_trans_le 𝒰 f _)).op
    (homOfLE (Scheme.Hom.image_mono _ hW)).op _)).trans ?_
  refine (D.θ_nat f (Scheme.Hom.image_mono _ hW) hW _).trans ?_
  refine (congrArg ((D.M i).presheaf.map (homOfLE hW).op) (D.sec_compat x' f)).trans ?_
  exact congrArg (fun e => (D.M i).presheaf.map e (x'.1 i)) (Subsingleton.elim _ _)

end Data

/-- Descent data as in `Data`, with the transition maps given as separate morphisms `tr f`
(equal to the transition maps `𝒰.trans f` of the cover). This is the form in which descent data
arise in practice, with `tr f` written in terms of the construction of the pieces. -/
structure DataTr where
  /-- The module on each piece. -/
  M : ∀ i, (𝒰.X i).Modules
  /-- The transition maps. -/
  tr : ∀ {i j : 𝒰.I₀} (_ : i ⟶ j), 𝒰.X i ⟶ 𝒰.X j
  [tr_open : ∀ {i j : 𝒰.I₀} (f : i ⟶ j), IsOpenImmersion (tr f)]
  tr_eq : ∀ {i j : 𝒰.I₀} (f : i ⟶ j), tr f = 𝒰.trans f
  tr_comp : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k), tr (f ≫ g) = tr f ≫ tr g
  /-- The transition isomorphisms. -/
  θ : ∀ {i j : 𝒰.I₀} (f : i ⟶ j), (M j).restrict (tr f) ≅ M i
  /-- The cocycle condition. -/
  θ_comp : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
    (θ (f ≫ g)).hom = (restrictFunctorCongr (tr_comp f g)).hom.app (M k) ≫
      (restrictFunctorComp (tr f) (tr g)).hom.app (M k) ≫
      (restrictFunctor (tr f)).map (θ g).hom ≫ (θ f).hom

namespace DataTr

variable {𝒰} (E : DataTr 𝒰)

attribute [instance] DataTr.tr_open

omit [Quiver.IsThin 𝒰.I₀] in
lemma image_tr_eq {i j : 𝒰.I₀} (f : i ⟶ j) (W : (𝒰.X i).Opens) :
    E.tr f ''ᵁ W = 𝒰.trans f ''ᵁ W := by
  ext x
  change x ∈ (E.tr f) '' W ↔ x ∈ (𝒰.trans f) '' W
  rw [E.tr_eq f]

omit [Quiver.IsThin 𝒰.I₀] in
lemma θ_nat {i j : 𝒰.I₀} (f : i ⟶ j) {W W' : (𝒰.X i).Opens} (h : E.tr f ''ᵁ W' ≤ E.tr f ''ᵁ W)
    (h' : W' ≤ W) (x : Γ(E.M j, E.tr f ''ᵁ W)) :
    (E.θ f).hom.app W' ((E.M j).presheaf.map (homOfLE h).op x) =
      (E.M i).presheaf.map (homOfLE h').op ((E.θ f).hom.app W x) := by
  have := ConcreteCategory.congr_hom ((E.θ f).hom.mapPresheaf.naturality (homOfLE h').op) x
  refine (Eq.trans ?_ this).trans ?_
  · rfl
  · rfl

omit [Quiver.IsThin 𝒰.I₀] in
lemma θ_nat' {i j : 𝒰.I₀} (f : i ⟶ j) {W W' : (𝒰.X i).Opens} (e : op W ⟶ op W')
    (h : E.tr f ''ᵁ W' ≤ E.tr f ''ᵁ W) (x : Γ(E.M j, E.tr f ''ᵁ W)) :
    (E.M i).presheaf.map e ((E.θ f).hom.app W x) =
      (E.θ f).hom.app W' ((E.M j).presheaf.map (homOfLE h).op x) := by
  rw [Subsingleton.elim e (homOfLE (leOfHom e.unop)).op]
  exact (E.θ_nat f h (leOfHom e.unop) x).symm

omit [Quiver.IsThin 𝒰.I₀] in
lemma θ_comp_apply {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k) (W : (𝒰.X i).Opens)
    (h : E.tr g ''ᵁ (E.tr f ''ᵁ W) ≤ E.tr (f ≫ g) ''ᵁ W)
    (x : Γ(E.M k, E.tr (f ≫ g) ''ᵁ W)) :
    (E.θ (f ≫ g)).hom.app W x = (E.θ f).hom.app W ((E.θ g).hom.app (E.tr f ''ᵁ W)
      ((E.M k).presheaf.map (homOfLE h).op x)) := by
  rw [E.θ_comp f g]
  simp only [Hom.comp_app, restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app]
  change (E.θ f).hom.app W ((E.θ g).hom.app _ ((E.M k).presheaf.map _
    ((E.M k).presheaf.map _ x))) = _
  rw [pmap_map (E.M k) _ _ (homOfLE h).op x]

/-- The descent data in the form `Data`, transporting `θ f` along `tr f = 𝒰.trans f`. -/
noncomputable def toData : Data 𝒰 where
  M := E.M
  θ f := (restrictFunctorCongr (E.tr_eq f)).symm.app (E.M _) ≪≫ E.θ f
  θ_comp f g := by
    apply Scheme.Modules.hom_ext
    intro W
    ext x
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Hom.comp_app,
      restrictFunctorCongr_inv_app_app, restrictFunctorCongr_hom_app_app,
      restrictFunctorComp_hom_app_app]
    let x' : Γ(E.M _, 𝒰.trans (f ≫ g) ''ᵁ W) := x
    have hle : E.tr f ''ᵁ W ≤ 𝒰.trans f ''ᵁ W := (E.image_tr_eq f W).le
    have hX : E.tr g ''ᵁ (E.tr f ''ᵁ W) ≤ E.tr (f ≫ g) ''ᵁ W := by
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      change (E.tr (f ≫ g)) y = (E.tr g) ((E.tr f) y)
      rw [E.tr_comp, Scheme.Hom.comp_apply]
    change (E.θ (f ≫ g)).hom.app W ((E.M _).presheaf.map _ x') = (E.θ f).hom.app W
      ((E.M _).presheaf.map _ ((E.θ g).hom.app (𝒰.trans f ''ᵁ W) ((E.M _).presheaf.map _
        ((E.M _).presheaf.map _ ((E.M _).presheaf.map _ x')))))
    rw [E.θ_comp_apply f g W hX, E.θ_nat' g _ (Scheme.Hom.image_mono _ hle)]
    simp only [pmap_comp_apply]
    exact congrArg (fun e => (E.θ f).hom.app W ((E.θ g).hom.app _ ((E.M _).presheaf.map e x')))
      (Subsingleton.elim _ _)

/-- The glued module. -/
noncomputable abbrev glue : Y.Modules := E.toData.glue

/-- The isomorphisms `glue|_{𝒰.X k} ≅ M k`. -/
noncomputable abbrev ψ (k : 𝒰.I₀) : E.glue.restrict (𝒰.f k) ≅ E.M k := E.toData.ψ k

/-- The isomorphisms `ψ` are compatible with the transition isomorphisms `θ`. -/
theorem ψ_compat {i j : 𝒰.I₀} (f : i ⟶ j) (h : E.tr f ≫ 𝒰.f j = 𝒰.f i) :
    (restrictFunctorCongr h).inv.app E.glue ≫
      (restrictFunctorComp (E.tr f) (𝒰.f j)).hom.app E.glue ≫
      (restrictFunctor (E.tr f)).map (E.ψ j).hom ≫ (E.θ f).hom = (E.ψ i).hom := by
  apply Scheme.Modules.hom_ext
  intro W
  ext x
  simp only [Hom.comp_app, restrictFunctorCongr_inv_app_app, restrictFunctorComp_hom_app_app]
  let x' : E.toData.Sec (𝒰.f i ''ᵁ W) := x
  have hW : W ≤ 𝒰.f i ⁻¹ᵁ (𝒰.f i ''ᵁ W) := (Scheme.Hom.preimage_image_eq _ W).ge
  have hc := E.toData.sec_compat x' f
  change (E.θ f).hom.app _ ((E.M j).presheaf.map _ ((E.M j).presheaf.map _ (x'.1 j))) =
    x'.1 i at hc
  change (E.θ f).hom.app W ((E.M j).presheaf.map _ ((E.M j).presheaf.map _
    ((E.M j).presheaf.map _ (x'.1 j)))) = (E.M i).presheaf.map _ (x'.1 i)
  simp only [pmap_comp_apply] at hc ⊢
  rw [← hc, E.θ_nat' f _ (Scheme.Hom.image_mono _ hW), pmap_comp_apply]
  exact congrArg ((E.θ f).hom.app W) (pmap_map_eq (E.M j) _ _ _ _ _)

end DataTr

end DirectedModuleGluing

end Hartshorne
