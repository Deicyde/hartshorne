/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# Gluing sheaves of modules on an open cover

WIP.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace Hartshorne

namespace ModuleGluing

variable {X : TopCat.{u}}

lemma opens_hom_ext {V W : Opens X} (f g : V ⟶ W) : f = g := Subsingleton.elim _ _

lemma over_hom_ext {U : Opens X} {A B : Over U} (f g : A ⟶ B) : f = g := by
  ext; exact Subsingleton.elim _ _

lemma overOp_hom_ext {U : Opens X} {A B : (Over U)ᵒᵖ} (f g : A ⟶ B) : f = g :=
  Quiver.Hom.unop_inj (over_hom_ext _ _)

/-- The morphism `A ⟶ B` of `Over U` given by an inclusion of the underlying opens. -/
def ovHom {U : Opens X} {A B : Over U} (h : A.left ≤ B.left) : A ⟶ B :=
  Over.homMk (homOfLE h) (Subsingleton.elim _ _)

/-- The object `U ⨯ V` of `Over U`. -/
noncomputable abbrev st (U V : Opens X) : Over U := (Over.star U).obj V

lemma st_left_le_left (U V : Opens X) : (st U V).left ≤ U := leOfHom (st U V).hom

lemma st_left_le_right (U V : Opens X) : (st U V).left ≤ V :=
  leOfHom ((Over.forgetAdjStar U).counit.app V)

lemma le_st_left {U V W : Opens X} (h₁ : W ≤ U) (h₂ : W ≤ V) : W ≤ (st U V).left :=
  leOfHom (((Over.forgetAdjStar U).homEquiv (Over.mk (homOfLE h₁)) V (homOfLE h₂)).left)

lemma st_left (U V : Opens X) : (st U V).left = U ⊓ V :=
  le_antisymm (le_inf (st_left_le_left U V) (st_left_le_right U V))
    (le_st_left inf_le_left inf_le_right)

section

variable {U : Opens X} {R : (Over U)ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

lemma map_map {a b c : (Over U)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (x : M.obj a) :
    M.map g (M.map f x) = M.map h x := by
  rw [← PresheafOfModules.map_comp_apply, overOp_hom_ext (f ≫ g) h]

lemma map_map_eq {a b b' c : (Over U)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (f' : a ⟶ b') (g' : b' ⟶ c)
    (x : M.obj a) : M.map g (M.map f x) = M.map g' (M.map f' x) := by
  rw [map_map M f g (f ≫ g), map_map M f' g' (f ≫ g)]

lemma map_self {a : (Over U)ᵒᵖ} (f : a ⟶ a) (x : M.obj a) : M.map f x = x := by
  rw [overOp_hom_ext f (𝟙 a), PresheafOfModules.map_id]; rfl

end

/-- Proves inclusions between the opens of the construction from inclusions of the cover. -/
macro "opens_le" : tactic => `(tactic| (
  simp only [Over.map_obj_left, st_left, Over.mk_left, SetLike.le_def, Opens.mem_inf] at *
  intros
  tauto))

section

variable {U : Opens X} {R : (Over U)ᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)

/-- Restriction along an inclusion of opens over `U`. -/
noncomputable abbrev rm {A B : Over U} (h : A.left ≤ B.left) (x : M.obj (op B)) : M.obj (op A) :=
  M.map (ovHom h).op x

lemma rm_rm {A B C : Over U} (h₁ : A.left ≤ B.left) (h₂ : B.left ≤ C.left) (x : M.obj (op C)) :
    rm M h₁ (rm M h₂ x) = rm M (h₁.trans h₂) x :=
  map_map M _ _ _ x

lemma rm_self {A : Over U} (h : A.left ≤ A.left) (x : M.obj (op A)) : rm M h x = x :=
  map_self M _ x

lemma rm_injective {A B : Over U} (h : A.left ≤ B.left) (h' : B.left ≤ A.left) :
    Function.Injective (rm M h) := fun x y hxy => by
  rw [← rm_self M (le_refl B.left) x, ← rm_self M (le_refl B.left) y, ← rm_rm M h' h,
    ← rm_rm M h' h, hxy]

lemma hom_rm {N : PresheafOfModules.{u} R} (f : M ⟶ N) {A B : Over U} (h : A.left ≤ B.left)
    (x : M.obj (op B)) : f.app (op A) (rm M h x) = rm N h (f.app (op B) x) :=
  PresheafOfModules.naturality_apply f _ x

end

variable (S : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Restriction of a module over `𝒪_X|_W` to an open `V ≤ W`. -/
noncomputable abbrev res {V W : Opens X} (h : V ≤ W) :
    SheafOfModules.{u} (S.over W) ⥤ SheafOfModules.{u} (S.over V) :=
  SheafOfModules.overMap S (homOfLE h)

/-- Restricting in two steps is restricting once. -/
noncomputable def resComp {T V W : Opens X} (hTV : T ≤ V) (hVW : V ≤ W) :
    res S hVW ⋙ res S hTV ≅ res S (hTV.trans hVW) :=
  NatIso.ofComponents
    fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso <|
      PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)

lemma opensOp_hom_ext {A B : (Opens X)ᵒᵖ} (f g : A ⟶ B) : f = g :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

lemma ring_map_map {a b c : (Opens X)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (r : S.obj.obj a) :
    S.obj.map g (S.obj.map f r) = S.obj.map h r := by
  rw [← RingCat.comp_apply, ← Functor.map_comp, opensOp_hom_ext (f ≫ g) h]

lemma smul_eq_of_eq {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{u} R)
    {a : Cᵒᵖ} {r r' : R.obj a} (h : r = r') (m : M.obj a) : r • m = r' • m := by rw [h]

lemma ring_over_map {W : Opens X} {a : (Opens X)ᵒᵖ} {b c : (Over W)ᵒᵖ} (f : a ⟶ op b.unop.left)
    (g : b ⟶ c) (h : a ⟶ op c.unop.left) (r : S.obj.obj a) :
    (S.over W).obj.map g (S.obj.map f r) = S.obj.map h r :=
  ring_map_map S f g.unop.left.op h r

/-- Pushforward from `Over W` to `X`: sections over `V` are the sections over `W ⨯ V`. -/
noncomputable abbrev pf (W : Opens X) : SheafOfModules.{u} (S.over W) ⥤ SheafOfModules.{u} S :=
  SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := S) W)

lemma pf_smul (W V : Opens X) (M : SheafOfModules.{u} (S.over W)) (r : S.obj.obj (op V))
    (x : ((pf S W).obj M).val.obj (op V)) :
    r • x = (show (S.over W).obj.obj (op (st W V)) from
      S.obj.map (homOfLE (st_left_le_right W V)).op r) • (show M.val.obj (op (st W V)) from x) :=
  rfl

lemma st_mono {V' W : Opens X} (h : V' ≤ W) (V : Opens X) :
    ((Over.map (homOfLE h)).obj (st V' V)).left ≤ (st W V).left := by
  simp only [Over.map_obj_left, st_left]
  exact inf_le_inf_right _ h

/-- Restriction from `W` to `V' ≤ W`, after pushing forward to `X`. -/
noncomputable def resMor {V' W : Opens X} (h : V' ≤ W) (M : SheafOfModules.{u} (S.over W)) :
    (pf S W).obj M ⟶ (pf S V').obj ((res S h).obj M) where
  val :=
    { app V := ModuleCat.ofHom (X := ((pf S W).obj M).val.obj V)
        (Y := ((pf S V').obj ((res S h).obj M)).val.obj V)
        { toFun x := M.val.map (ovHom (st_mono h V.unop)).op x
          map_add' := fun x y => (M.val.map (ovHom (st_mono h V.unop)).op).hom.map_add x y
          map_smul' := by
            intro r x
            refine (M.val.map_smul (ovHom (st_mono h V.unop)).op
              (S.obj.map (homOfLE (st_left_le_right W V.unop)).op r) x).trans ?_
            refine (smul_eq_of_eq M.val (ring_over_map (W := W) S
              (homOfLE (st_left_le_right W V.unop)).op (ovHom (st_mono h V.unop)).op
              (homOfLE (st_left_le_right V' V.unop)).op r) _).trans ?_
            rfl }
      naturality := by
        intro V₁ V₂ f
        ext x
        exact map_map_eq M.val _ _ _ _ x }

lemma resMor_apply {V' W : Opens X} (h : V' ≤ W) (M : SheafOfModules.{u} (S.over W)) (V : Opens X)
    (x : ((pf S W).obj M).val.obj (op V)) :
    (resMor S h M).val.app (op V) x = M.val.map (ovHom (st_mono h V)).op x := rfl

/-- Sections of a sheaf of modules on `X` that agree locally agree. -/
lemma sheaf_ext (M : SheafOfModules.{u} S) {V : Opens X} {κ : Type u} (W : κ → Opens X)
    (hW : ∀ k, W k ≤ V) (hcov : V ≤ iSup W) (s t : M.val.obj (op V))
    (h : ∀ k, M.val.map (homOfLE (hW k)).op s = M.val.map (homOfLE (hW k)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
    W V (fun k => homOfLE (hW k)) hcov s t h

/-- Compatible local sections of a sheaf of modules on `X` glue. -/
lemma sheaf_glue (M : SheafOfModules.{u} S) {V : Opens X} {κ : Type u} (W : κ → Opens X)
    (hW : ∀ k, W k ≤ V) (hcov : V ≤ iSup W) (sf : ∀ k, M.val.obj (op (W k)))
    (hc : ∀ k l, M.val.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op (sf k) =
      M.val.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op (sf l)) :
    ∃ s : M.val.obj (op V), ∀ k, M.val.map (homOfLE (hW k)).op s = sf k := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (⟨M.val.presheaf, M.isSheaf⟩ :
    TopCat.Sheaf AddCommGrpCat.{u} X) W V (fun k => homOfLE (hW k)) hcov sf
    (by intro k l; exact hc k l)
  exact ⟨s, hs⟩

/-- A morphism of sheaves of modules that is bijective on all sections is an isomorphism. -/
lemma isIso_of_bijective {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (h : ∀ A, Function.Bijective (f.val.app A)) : IsIso f := by
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun A => (LinearEquiv.ofBijective (f.val.app A).hom (h A)).toModuleIso)
    (fun _ _ g => f.val.naturality g)
  have he : e.hom = f.val := by
    ext A x
    rfl
  have : IsIso ((SheafOfModules.forget R).map f) := by
    change IsIso f.val
    rw [← he]
    infer_instance
  exact (SheafOfModules.fullyFaithfulForget R).isIso_of_isIso_map f

lemma ring_over_map_self {W : Opens X} {A : Over W} {b : (Over W)ᵒᵖ}
    (f : op A.left ⟶ op b.unop.left) (g : b ⟶ op A) (r : S.obj.obj (op A.left)) :
    (S.over W).obj.map g (S.obj.map f r) = r := by
  rw [ring_over_map S f g (𝟙 _), S.obj.map_id]; rfl

variable {S}

/-- Restriction to `T ≤ V` of an isomorphism between restrictions to `V`. -/
noncomputable def restrictIso {T V W W' : Opens X} (hT : T ≤ V) {hW : V ≤ W} {hW' : V ≤ W'}
    {G : SheafOfModules.{u} (S.over W)} {G' : SheafOfModules.{u} (S.over W')}
    (α : (res S hW).obj G ≅ (res S hW').obj G') :
    (res S (hT.trans hW)).obj G ≅ (res S (hT.trans hW')).obj G' :=
  ((resComp S hT hW).app G).symm ≪≫ (res S hT).mapIso α ≪≫ (resComp S hT hW').app G'

variable (S X) in
/-- Gluing data for sheaves of modules on a ringed space `(X, S)`: an open cover `U` of `X`, an
`S|_{U i}`-module `F i` for each `i`, and isomorphisms `φ i j` of `S|_{U i ⊓ U j}`-modules on the
double intersections satisfying the identity and cocycle conditions. -/
structure GluingData where
  /-- The index type of the cover. -/
  ι : Type u
  /-- The open cover. -/
  U : ι → Opens X
  /-- The `U i` cover `X`. -/
  iSup_eq_top : iSup U = ⊤
  /-- A module over `S|_{U i}` on each open of the cover. -/
  F : ∀ i, SheafOfModules.{u} (S.over (U i))
  /-- The gluing isomorphisms `F i |(U i ⊓ U j) ≅ F j |(U i ⊓ U j)`. -/
  φ : ∀ i j, (res S (inf_le_left : U i ⊓ U j ≤ U i)).obj (F i) ≅
    (res S (inf_le_right : U i ⊓ U j ≤ U j)).obj (F j)
  /-- The identity condition `φ i i = id`. -/
  φ_self : ∀ i, (φ i i).hom = 𝟙 _
  /-- The cocycle condition `φ i k = φ j k ∘ φ i j` on `U i ⊓ U j ⊓ U k`. -/
  cocycle : ∀ i j k,
    restrictIso (T := U i ⊓ U j ⊓ U k) inf_le_left (φ i j) ≪≫
      restrictIso (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (φ j k) =
    restrictIso (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (φ i k)

namespace GluingData

variable (D : GluingData X S)

/-- A family of isomorphisms `ψ i : F|_{U i} ≅ F i` is compatible with the gluing isomorphisms
when `ψ j = φ i j ∘ ψ i` on `U i ⊓ U j`. -/
def Compatible (F : SheafOfModules.{u} S)
    (ψ : ∀ i, (SheafOfModules.overFunctor S (D.U i)).obj F ≅ D.F i) : Prop :=
  ∀ i j, ((SheafOfModules.overFunctorMap S (homOfLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i))).app
        F).symm ≪≫ (res S inf_le_left).mapIso (ψ i) ≪≫ D.φ i j =
    ((SheafOfModules.overFunctorMap S (homOfLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j))).app
        F).symm ≪≫ (res S inf_le_right).mapIso (ψ j)

/-- `F i` pushed forward to `X`: sections over `V` are the sections of `F i` over `U i ⨯ V`. -/
noncomputable abbrev P (i : D.ι) : SheafOfModules.{u} S := (pf S (D.U i)).obj (D.F i)

/-- `F j |(U i ⊓ U j)` pushed forward to `X`. -/
noncomputable abbrev Q (i j : D.ι) : SheafOfModules.{u} S :=
  (pf S (D.U i ⊓ D.U j)).obj ((res S inf_le_right).obj (D.F j))

/-- Restriction from `U i` to `U i ⊓ U j` followed by `φ i j`. -/
noncomputable def α (i j : D.ι) : D.P i ⟶ D.Q i j :=
  resMor S inf_le_left (D.F i) ≫ (pf S _).map (D.φ i j).hom

/-- Restriction from `U j` to `U i ⊓ U j`. -/
noncomputable def β (i j : D.ι) : D.P j ⟶ D.Q i j := resMor S inf_le_right (D.F j)

/-- The product of the `P i`, as a presheaf of modules. -/
noncomputable def piP : PresheafOfModules.{u} S.obj where
  obj V := ModuleCat.of (S.obj.obj V) (∀ i, (D.P i).val.obj V)
  map {V V'} f := ModuleCat.semilinearMapAddEquiv (S.obj.map f).hom _ _
    { toFun s i := (D.P i).val.map f (s i)
      map_add' x y := by funext i; exact map_add _ (x i) (y i)
      map_smul' r x := by funext i; exact (D.P i).val.map_smul f r (x i) }
  map_id V := by
    ext s
    funext i
    exact congrArg (fun g => g (s i)) (congrArg (fun g => ConcreteCategory.hom g)
      ((D.P i).val.map_id V))
  map_comp f g := by
    ext s
    funext i
    exact (D.P i).val.map_comp_apply f g (s i)

lemma piP_map_apply {V V' : (Opens X)ᵒᵖ} (f : V ⟶ V') (s : D.piP.obj V) (i : D.ι) :
    (D.piP.map f s : ∀ i, (D.P i).val.obj V') i = (D.P i).val.map f (s i) := rfl

/-- The compatible families. -/
noncomputable def N : D.piP.Submodule where
  obj V :=
    { carrier := {s | ∀ i j, (D.α i j).val.app V (s i) = (D.β i j).val.app V (s j)}
      add_mem' {a b} ha hb i j := by
        change (D.α i j).val.app V (a i + b i) = (D.β i j).val.app V (a j + b j)
        rw [map_add, map_add, ha i j, hb i j]
      zero_mem' i j := by
        change (D.α i j).val.app V 0 = (D.β i j).val.app V 0
        rw [map_zero, map_zero]
      smul_mem' r a ha i j := by
        change (D.α i j).val.app V (r • a i) = (D.β i j).val.app V (r • a j)
        rw [map_smul, map_smul, ha i j] }
  map {V V'} f s hs i j := by
    change (D.α i j).val.app V' ((D.P i).val.map f (s i)) =
      (D.β i j).val.app V' ((D.P j).val.map f (s j))
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hs i j]

lemma mem_N {V : (Opens X)ᵒᵖ} (s : D.piP.obj V) :
    s ∈ D.N.obj V ↔ ∀ i j, (D.α i j).val.app V (s i) = (D.β i j).val.app V (s j) := Iff.rfl

/-- The glued presheaf of modules. -/
noncomputable abbrev Gpre : PresheafOfModules.{u} S.obj := D.N.toPresheafOfModules

lemma Gpre_map_val {V V' : (Opens X)ᵒᵖ} (f : V ⟶ V') (s : D.Gpre.obj V) (i : D.ι) :
    ((D.Gpre.map f s).1 : ∀ i, (D.P i).val.obj V') i = (D.P i).val.map f (s.1 i) := rfl

lemma isSheaf_Gpre : Presheaf.IsSheaf (Opens.grothendieckTopology X) D.Gpre.presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X) D.Gpre.presheaf).2 ?_
  intro κ W sf hsf
  have hc : ∀ i k l, (D.P i).val.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op
      ((sf k).1 i) = (D.P i).val.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op
      ((sf l).1 i) := fun i k l => congrArg (fun t : D.Gpre.obj _ => t.1 i) (hsf k l)
  choose g hg using fun i => sheaf_glue S (D.P i) W (fun k => le_iSup W k) le_rfl
    (fun k => (sf k).1 i) (hc i)
  have hmem : (g : D.piP.obj (op (iSup W))) ∈ D.N.obj (op (iSup W)) := by
    intro i j
    refine sheaf_ext S (D.Q i j) W (fun k => le_iSup W k) le_rfl _ _ fun k => ?_
    rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply, hg, hg]
    exact (sf k).2 i j
  refine ⟨⟨g, hmem⟩, fun k => ?_, fun t ht => ?_⟩
  · exact Subtype.ext (funext fun i => hg i k)
  · refine Subtype.ext (funext fun i => ?_)
    refine sheaf_ext S (D.P i) W (fun k => le_iSup W k) le_rfl _ _ fun k => ?_
    rw [hg]
    exact congrArg (fun t : D.Gpre.obj _ => t.1 i) (ht k)

/-- The glued sheaf of modules. -/
noncomputable def glue : SheafOfModules.{u} S := ⟨D.Gpre, D.isSheaf_Gpre⟩

lemma φ_nat (i j : D.ι) {A B : Over (D.U i ⊓ D.U j)} (h : A.left ≤ B.left)
    (x : (D.F i).val.obj (op ((Over.map (homOfLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i))).obj B))) :
    (D.φ i j).hom.val.app (op A) (rm (D.F i).val (A := (Over.map _).obj A)
      (B := (Over.map (homOfLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i))).obj B) h x) =
      rm (D.F j).val (A := (Over.map (homOfLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j))).obj A)
        (B := (Over.map (homOfLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j))).obj B) h
        ((D.φ i j).hom.val.app (op B) x) :=
  PresheafOfModules.naturality_apply (D.φ i j).hom.val (ovHom h).op x

lemma φ_self_apply (i : D.ι) (A : Over (D.U i ⊓ D.U i))
    (x : (D.F i).val.obj (op ((Over.map (homOfLE (inf_le_left : D.U i ⊓ D.U i ≤ D.U i))).obj A))) :
    (D.φ i i).hom.val.app (op A) x = x := by
  rw [D.φ_self]; rfl

lemma cocycle_apply (i j k : D.ι) (A : Over (D.U i ⊓ D.U j ⊓ D.U k))
    (x : (D.F i).val.obj (op ((Over.map (homOfLE (inf_le_left.trans inf_le_left :
      D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i))).obj A))) :
    (D.φ j k).hom.val.app (op ((Over.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
      inf_le_right : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j ⊓ D.U k))).obj A))
      ((D.φ i j).hom.val.app (op ((Over.map (homOfLE (inf_le_left :
        D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i ⊓ D.U j))).obj A)) x) =
    (D.φ i k).hom.val.app (op ((Over.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
      inf_le_right : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i ⊓ D.U k))).obj A)) x :=
  congrArg (fun e => e.hom.val.app (op A) x) (D.cocycle i j k)

lemma le_st_self (k : D.ι) (A : Over (D.U k)) : A.left ≤ (st (D.U k) A.left).left :=
  le_st_left (leOfHom A.hom) le_rfl

/-- The map `ψ k : glue|_{U k} ⟶ F k` on sections. -/
noncomputable def ψHom (k : D.ι) : (SheafOfModules.overFunctor S (D.U k)).obj D.glue ⟶ D.F k where
  val :=
    { app A := ModuleCat.ofHom (X := ((SheafOfModules.overFunctor S (D.U k)).obj D.glue).val.obj A)
        (Y := (D.F k).val.obj A)
        { toFun s := rm (D.F k).val (D.le_st_self k A.unop)
            ((s : D.Gpre.obj (op A.unop.left)).1 k)
          map_add' x y := map_add _ _ _
          map_smul' r x := by
            refine ((D.F k).val.map_smul (ovHom (D.le_st_self k A.unop)).op
              (S.obj.map (homOfLE (st_left_le_right (D.U k) A.unop.left)).op r)
              ((x : D.Gpre.obj (op A.unop.left)).1 k)).trans ?_
            refine (smul_eq_of_eq (D.F k).val (ring_over_map_self S _ _ r) _).trans ?_
            rfl }
      naturality {A A'} f := by
        ext x
        exact map_map_eq (D.F k).val _ _ _ _ _ }

lemma ψHom_apply (k : D.ι) (A : Over (D.U k)) (s : D.Gpre.obj (op A.left)) :
    (D.ψHom k).val.app (op A) s = rm (D.F k).val (D.le_st_self k A) (s.1 k) := rfl

lemma α_apply (i j : D.ι) (V : Opens X) (x : (D.P i).val.obj (op V)) :
    (D.α i j).val.app (op V) x = (D.φ i j).hom.val.app (op (st (D.U i ⊓ D.U j) V))
      (rm (D.F i).val (st_mono inf_le_left V) x) := rfl

lemma β_apply (i j : D.ι) (V : Opens X) (x : (D.P j).val.obj (op V)) :
    (D.β i j).val.app (op V) x = rm (D.F j).val (st_mono inf_le_right V) x := rfl

/-- Over an open `V ≤ U k`, a compatible family is determined by its `k`-th component. -/
lemma component_eq (k i : D.ι) {V : Opens X} (hV : V ≤ D.U k) (s : D.Gpre.obj (op V)) :
    s.1 i = rm (D.F i).val (A := st (D.U i) V)
      (B := (Over.map (homOfLE (inf_le_right : D.U k ⊓ D.U i ≤ D.U i))).obj
        (st (D.U k ⊓ D.U i) V)) (by opens_le) ((D.α k i).val.app (op V) (s.1 k)) := by
  rw [s.2 k i, β_apply]
  exact ((rm_rm _ _ _ _).trans (rm_self _ _ _)).symm

lemma ψHom_injective (k : D.ι) (A : Over (D.U k)) :
    Function.Injective ((D.ψHom k).val.app (op A)) := by
  intro (s : D.Gpre.obj (op A.left)) (s' : D.Gpre.obj (op A.left)) h
  have hA : A.left ≤ D.U k := leOfHom A.hom
  have h' : rm (D.F k).val (D.le_st_self k A) (s.1 k) =
    rm (D.F k).val (D.le_st_self k A) (s'.1 k) := h
  have hk : s.1 k = s'.1 k := rm_injective _ _ (st_left_le_right _ _) h'
  refine Subtype.ext (funext fun i => ?_)
  rw [D.component_eq k i hA s, D.component_eq k i hA s', hk]

/-- The compatible family determined by a section of `F k` over `A`. -/
noncomputable def secOf (k : D.ι) (A : Over (D.U k)) (t : (D.F k).val.obj (op A)) (i : D.ι) :
    (D.P i).val.obj (op A.left) :=
  rm (D.F i).val (A := st (D.U i) A.left)
    (B := (Over.map (homOfLE (inf_le_right : D.U k ⊓ D.U i ≤ D.U i))).obj
      (st (D.U k ⊓ D.U i) A.left)) (by have := leOfHom A.hom; opens_le)
    ((D.φ k i).hom.val.app (op (st (D.U k ⊓ D.U i) A.left))
      (rm (D.F k).val (B := A) (st_left_le_right _ _) t))

set_option maxHeartbeats 1000000 in
lemma secOf_mem (k : D.ι) (A : Over (D.U k)) (t : (D.F k).val.obj (op A)) :
    (D.secOf k A t : D.piP.obj (op A.left)) ∈ D.N.obj (op A.left) := by
  intro i j
  have hA : A.left ≤ D.U k := leOfHom A.hom
  -- the objects involved
  let V := A.left
  let T : Over (D.U k ⊓ D.U i ⊓ D.U j) := st _ V
  let Bki : Over (D.U k ⊓ D.U i) := st _ V
  let Bkj : Over (D.U k ⊓ D.U j) := st _ V
  let Bij : Over (D.U i ⊓ D.U j) := st _ V
  let Tki : Over (D.U k ⊓ D.U i) := (Over.map (homOfLE (inf_le_left :
    D.U k ⊓ D.U i ⊓ D.U j ≤ D.U k ⊓ D.U i))).obj T
  let Tij : Over (D.U i ⊓ D.U j) := (Over.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
    inf_le_right : D.U k ⊓ D.U i ⊓ D.U j ≤ D.U i ⊓ D.U j))).obj T
  let Tkj : Over (D.U k ⊓ D.U j) := (Over.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
    inf_le_right : D.U k ⊓ D.U i ⊓ D.U j ≤ D.U k ⊓ D.U j))).obj T
  let lki := homOfLE (inf_le_left : D.U k ⊓ D.U i ≤ D.U k)
  let rki := homOfLE (inf_le_right : D.U k ⊓ D.U i ≤ D.U i)
  let lkj := homOfLE (inf_le_left : D.U k ⊓ D.U j ≤ D.U k)
  let rkj := homOfLE (inf_le_right : D.U k ⊓ D.U j ≤ D.U j)
  let lij := homOfLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)
  let rij := homOfLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)
  have e1 : ((Over.map lij).obj Bij).left ≤ ((Over.map rki).obj Tki).left := by
    simp only [Bij, Tki, T, V]; opens_le
  have e2 : ((Over.map rki).obj Tki).left ≤ ((Over.map rki).obj Bki).left := by
    simp only [Bki, Tki, T, V]; opens_le
  have e3 : ((Over.map rij).obj Bij).left ≤ ((Over.map rkj).obj Tkj).left := by
    simp only [Bij, Tkj, T, V]; opens_le
  have e4 : ((Over.map rkj).obj Tkj).left ≤ ((Over.map rkj).obj Bkj).left := by
    simp only [Bkj, Tkj, T, V]; opens_le
  have e5 : ((Over.map lki).obj Bki).left ≤ A.left := st_left_le_right _ _
  have e6 : ((Over.map lkj).obj Bkj).left ≤ A.left := st_left_le_right _ _
  have L : (D.α i j).val.app (op V) (D.secOf k A t i) =
      rm (D.F j).val (A := (Over.map rij).obj Bij) (B := (Over.map rkj).obj Tkj) e3
        ((D.φ k j).hom.val.app (op Tkj)
          (rm (D.F k).val (A := (Over.map lki).obj Tki) (B := A) (e2.trans e5) t)) := by
    rw [α_apply]
    unfold secOf
    erw [rm_rm, ← rm_rm (D.F i).val e1 e2, ← D.φ_nat k i (A := Tki) (B := Bki) e2]
    change (D.φ i j).hom.val.app (op Bij) (rm (D.F i).val (A := (Over.map lij).obj Bij)
      (B := (Over.map lij).obj Tij) e1 ((D.φ k i).hom.val.app (op Tki) _)) = _
    erw [D.φ_nat i j (A := Bij) (B := Tij) e1]
    have hc : ∀ x, (D.φ i j).hom.val.app (op Tij) ((D.φ k i).hom.val.app (op Tki) x) =
        (D.φ k j).hom.val.app (op Tkj) x := fun x => D.cocycle_apply k i j T x
    refine (congrArg (rm (D.F j).val e1) (hc _)).trans ?_
    exact congrArg (rm (D.F j).val e3) (congrArg ((D.φ k j).hom.val.app (op Tkj))
      (rm_rm _ _ _ _))
  have R : (D.β i j).val.app (op V) (D.secOf k A t j) =
      rm (D.F j).val (A := (Over.map rij).obj Bij) (B := (Over.map rkj).obj Tkj) e3
        ((D.φ k j).hom.val.app (op Tkj)
          (rm (D.F k).val (A := (Over.map lkj).obj Tkj) (B := A) (e4.trans e6) t)) := by
    rw [β_apply]
    unfold secOf
    erw [rm_rm, ← rm_rm (D.F j).val e3 e4, ← D.φ_nat k j (A := Tkj) (B := Bkj) e4, rm_rm]
  exact L.trans R.symm

lemma ψHom_surjective (k : D.ι) (A : Over (D.U k)) :
    Function.Surjective ((D.ψHom k).val.app (op A)) := by
  intro t
  refine ⟨(⟨D.secOf k A t, D.secOf_mem k A t⟩ : D.Gpre.obj (op A.left)), ?_⟩
  change rm (D.F k).val (D.le_st_self k A) (D.secOf k A t k) = t
  unfold secOf
  erw [D.φ_self_apply k, rm_rm, rm_rm, rm_self]

instance isIso_ψHom (k : D.ι) : IsIso (D.ψHom k) :=
  isIso_of_bijective _ fun A => ⟨D.ψHom_injective k A.unop, D.ψHom_surjective k A.unop⟩

/-- The isomorphisms `ψ k : glue|_{U k} ≅ F k`. -/
noncomputable def ψ (k : D.ι) : (SheafOfModules.overFunctor S (D.U k)).obj D.glue ≅ D.F k :=
  asIso (D.ψHom k)

end GluingData

end ModuleGluing

end Hartshorne
