/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleSheafMonoidal
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Skyscraper sheaves of modules and the stalk adjunction

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`, and let `x : X`. For an `𝒪_{X,x}`-module `N`, the *skyscraper* `𝒪_X`-module
`moduleSkyscraper x N` has sections `N` over the opens containing `x` and `0` over the others,
with `𝒪_X(U)` acting on `N` through the germ map `𝒪_X(U) → 𝒪_{X,x}`. (To avoid case
distinctions, its sections over `U` are the functions `x ∈ U → N` on proofs of membership.)

The stalk at `x`, as a functor `moduleStalkFunctor x` from `𝒪_X`-modules to `𝒪_{X,x}`-modules, is
left adjoint to the skyscraper functor (`moduleStalkSkyscraperAdjunction`): a morphism `F ⟶ x_* N`
is the same thing as an `𝒪_{X,x}`-linear map `F_x → N`. Both functors are additive, and the
correspondence is an isomorphism of Hom groups (`moduleStalkSkyscraperHomAddEquiv`).
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace Hartshorne

namespace Ringed

open ModuleSheafTensor

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}} (x : X)

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

section Skyscraper

variable (N : ModuleCat.{u} (ringSheafStalk R x))

/-- The `𝒪_X(U)`-module structure on the sections `x ∈ U → N` of the skyscraper sheaf: a
section `r` acts through its germ at `x`. -/
noncomputable abbrev skyscraperSectionModule (U : Opens X) :
    Module (R.obj.obj (op U)) (PLift (x ∈ U) → N) where
  smul r f := fun h => TopCat.Presheaf.germ R.obj U x h.down r • f h
  one_smul f := funext fun h => by
    change TopCat.Presheaf.germ R.obj U x h.down 1 • f h = f h
    rw [map_one, one_smul]
  mul_smul r s f := funext fun h => by
    change TopCat.Presheaf.germ R.obj U x h.down (r * s) • f h =
      TopCat.Presheaf.germ R.obj U x h.down r • TopCat.Presheaf.germ R.obj U x h.down s • f h
    rw [map_mul, mul_smul]
  smul_zero r := funext fun h => smul_zero _
  smul_add r f g := funext fun h => smul_add _ (f h) (g h)
  add_smul r s f := funext fun h => by
    change TopCat.Presheaf.germ R.obj U x h.down (r + s) • f h =
      TopCat.Presheaf.germ R.obj U x h.down r • f h + TopCat.Presheaf.germ R.obj U x h.down s • f h
    rw [map_add, add_smul]
  zero_smul f := funext fun h => by
    change TopCat.Presheaf.germ R.obj U x h.down 0 • f h = 0
    rw [map_zero, zero_smul]

/-- The underlying presheaf of abelian groups of the skyscraper sheaf: `U ↦ (x ∈ U → N)`. -/
noncomputable def skyscraperAbPresheaf : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (PLift (x ∈ U.unop) → N)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := fun f h => f ⟨i.unop.le h.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

lemma skyscraperAbPresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (f : PLift (x ∈ U.unop) → N) (h : PLift (x ∈ V.unop)) :
    (skyscraperAbPresheaf x N).map i f h = f ⟨i.unop.le h.down⟩ := rfl

/-- The presheaf of `𝒪_X`-modules underlying the skyscraper sheaf. -/
noncomputable def skyscraperPresheafOfModules :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  letI : ∀ U : (Opens X)ᵒᵖ, Module ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U)
      ((skyscraperAbPresheaf x N).obj U) := fun U => skyscraperSectionModule x N U.unop
  PresheafOfModules.ofPresheaf (skyscraperAbPresheaf x N) (fun U V i r f => by
    funext h
    change TopCat.Presheaf.germ R.obj U.unop x (i.unop.le h.down) r • f ⟨i.unop.le h.down⟩ =
      TopCat.Presheaf.germ R.obj V.unop x h.down (R.obj.map i r) • f ⟨i.unop.le h.down⟩
    exact congrArg (· • f ⟨i.unop.le h.down⟩)
      (TopCat.Presheaf.germ_res_apply R.obj i.unop x h.down r).symm)

lemma skyscraperPresheafOfModules_presheaf :
    (skyscraperPresheafOfModules x N).presheaf = skyscraperAbPresheaf x N := rfl

lemma skyscraperAbPresheaf_isSheaf : TopCat.Presheaf.IsSheaf (skyscraperAbPresheaf x N) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have key : ∀ (i j : ι) (hi : x ∈ U i) (hj : x ∈ U j), sf i ⟨hi⟩ = sf j ⟨hj⟩ :=
    fun i j hi hj => congrFun (hsf i j) ⟨⟨hi, hj⟩⟩
  refine ⟨fun h => sf (Opens.mem_iSup.1 h.down).choose ⟨(Opens.mem_iSup.1 h.down).choose_spec⟩,
    ?_, ?_⟩
  · intro i
    funext hi
    exact key _ _ _ _
  · intro t ht
    funext h
    exact congrFun (ht (Opens.mem_iSup.1 h.down).choose) ⟨(Opens.mem_iSup.1 h.down).choose_spec⟩

/-- **The skyscraper `𝒪_X`-module** at `x` with value the `𝒪_{X,x}`-module `N`: its sections
over `U` are `N` if `x ∈ U` and `0` otherwise. -/
noncomputable def moduleSkyscraperObj : 𝓜 where
  val := skyscraperPresheafOfModules x N
  isSheaf := skyscraperAbPresheaf_isSheaf x N

variable {x N} in
lemma moduleSkyscraperObj_smul_apply {U : Opens X} (r : R.obj.obj (op U))
    (f : (moduleSkyscraperObj x N).val.obj (op U)) (h : x ∈ U) :
    (r • f : (moduleSkyscraperObj x N).val.obj (op U)) ⟨h⟩ =
      TopCat.Presheaf.germ R.obj U x h r • (f ⟨h⟩ : N) := rfl

/-- The morphism of skyscraper sheaves induced by a linear map. -/
noncomputable def moduleSkyscraperMap {N N' : ModuleCat.{u} (ringSheafStalk R x)} (g : N ⟶ N') :
    moduleSkyscraperObj x N ⟶ moduleSkyscraperObj x N' where
  val := PresheafOfModules.homMk
    { app _ := AddCommGrpCat.ofHom
        { toFun := fun f h => g (f h)
          map_zero' := funext fun _ => map_zero g.hom
          map_add' := fun _ _ => funext fun _ => map_add g.hom _ _ }
      naturality _ _ _ := rfl }
    (fun _ _ f => funext fun h => g.hom.map_smul _ (f h))

variable {x} in
lemma moduleSkyscraperMap_app_apply {N N' : ModuleCat.{u} (ringSheafStalk R x)} (g : N ⟶ N')
    {U : Opens X} (f : (moduleSkyscraperObj x N).val.obj (op U)) (h : x ∈ U) :
    (moduleSkyscraperMap x g).val.app (op U) f ⟨h⟩ = g (f ⟨h⟩) := rfl

/-- **The skyscraper functor** at `x`, from `𝒪_{X,x}`-modules to `𝒪_X`-modules. -/
noncomputable def moduleSkyscraper : ModuleCat.{u} (ringSheafStalk R x) ⥤ 𝓜 where
  obj N := moduleSkyscraperObj x N
  map g := moduleSkyscraperMap x g
  map_id _ := rfl
  map_comp _ _ := rfl

end Skyscraper

section Stalk

/-- **The stalk functor** at `x`, from `𝒪_X`-modules to `𝒪_{X,x}`-modules. -/
noncomputable def moduleStalkFunctor : 𝓜 ⥤ ModuleCat.{u} (ringSheafStalk R x) where
  obj F := ModuleCat.of _ (moduleStalk F.val x)
  map φ := ModuleCat.ofHom (stalkLinearMap φ.val x)
  map_id F := by
    ext s
    obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm F.val x s
    exact stalkAddMap_germ _ x U hU t
  map_comp φ ψ := by
    ext s
    obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm _ x s
    change stalkAddMap _ x _ = stalkAddMap _ x (stalkAddMap _ x _)
    rw [stalkAddMap_germ, stalkAddMap_germ, stalkAddMap_germ]
    rfl

lemma moduleStalkFunctor_map_germ {F G : 𝓜} (φ : F ⟶ G) (U : Opens X) (hU : x ∈ U)
    (s : F.val.obj (op U)) :
    (moduleStalkFunctor x).map φ (sectionGerm F.val x U hU s) =
      sectionGerm G.val x U hU (φ.val.app (op U) s) :=
  stalkAddMap_germ _ x U hU s

end Stalk

section Adjunction

variable {x}

/-- The morphism `F ⟶ x_* N` attached to a linear map `F_x → N`: a section `s` over `U ∋ x` goes
to the image of its germ. -/
noncomputable def toSkyscraper {F : 𝓜} {N : ModuleCat.{u} (ringSheafStalk R x)}
    (ψ : (moduleStalkFunctor x).obj F ⟶ N) : F ⟶ (moduleSkyscraper x).obj N where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun s h => ψ (sectionGerm F.val x U.unop h.down s)
          map_zero' := funext fun h =>
            (congrArg ψ.hom (map_zero (sectionGerm F.val x U.unop h.down))).trans
              (map_zero ψ.hom)
          map_add' := fun s t => funext fun h =>
            (congrArg ψ.hom (map_add (sectionGerm F.val x U.unop h.down) s t)).trans
              (map_add ψ.hom _ _) }
      naturality U V i := by
        ext s
        funext h
        exact congrArg ψ.hom (sectionGerm_res F.val x i.unop h.down s) }
    (fun U r s => funext fun h =>
      (congrArg ψ.hom (sectionGerm_smul F.val x U.unop h.down r s)).trans
        (ψ.hom.map_smul _ _))

lemma toSkyscraper_app_apply {F : 𝓜} {N : ModuleCat.{u} (ringSheafStalk R x)}
    (ψ : (moduleStalkFunctor x).obj F ⟶ N) (U : Opens X) (s : F.val.obj (op U)) (h : x ∈ U) :
    (toSkyscraper ψ).val.app (op U) s ⟨h⟩ = ψ (sectionGerm F.val x U h s) := rfl

/-- The additive map `F_x → N` attached to a morphism `F ⟶ x_* N`. -/
noncomputable def ofSkyscraperAdd {F : 𝓜} {N : ModuleCat.{u} (ringSheafStalk R x)}
    (φ : F ⟶ (moduleSkyscraper x).obj N) : moduleStalk F.val x ⟶ AddCommGrpCat.of N :=
  stalkDesc (fun U h => AddCommGrpCat.ofHom
      { toFun := fun s => φ.val.app (op U) s ⟨h⟩
        map_zero' := by
          change ((φ.val.app (op U)).hom 0) ⟨h⟩ = 0
          rw [map_zero]
          rfl
        map_add' := fun s t => by
          change ((φ.val.app (op U)).hom (s + t)) ⟨h⟩ = _
          rw [map_add]
          rfl })
    (fun U V i hV => by
      ext s
      exact congrArg (fun t : PLift (x ∈ V) → N => t ⟨hV⟩)
        (PresheafOfModules.naturality_apply φ.val i.op s))

lemma ofSkyscraperAdd_germ {F : 𝓜} {N : ModuleCat.{u} (ringSheafStalk R x)}
    (φ : F ⟶ (moduleSkyscraper x).obj N) (U : Opens X) (h : x ∈ U) (s : F.val.obj (op U)) :
    ofSkyscraperAdd φ (sectionGerm F.val x U h s) = φ.val.app (op U) s ⟨h⟩ :=
  stalkDesc_germ (P := F.val.presheaf) _ _ U h s

/-- The linear map `F_x → N` attached to a morphism `F ⟶ x_* N`. -/
noncomputable def ofSkyscraper {F : 𝓜} {N : ModuleCat.{u} (ringSheafStalk R x)}
    (φ : F ⟶ (moduleSkyscraper x).obj N) : (moduleStalkFunctor x).obj F ⟶ N :=
  ModuleCat.ofHom
    { toFun := ofSkyscraperAdd φ
      map_add' := map_add _
      map_smul' := fun r s => by
        obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm F.val x s
        obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm x r hU
        rw [← sectionGerm_res F.val x (homOfLE hWU) hW t, ← sectionGerm_smul, RingHom.id_apply,
          ofSkyscraperAdd_germ, ofSkyscraperAdd_germ, (φ.val.app (op W)).hom.map_smul]
        rfl }

lemma ofSkyscraper_germ {F : 𝓜} {N : ModuleCat.{u} (ringSheafStalk R x)}
    (φ : F ⟶ (moduleSkyscraper x).obj N) (U : Opens X) (h : x ∈ U) (s : F.val.obj (op U)) :
    ofSkyscraper φ (sectionGerm F.val x U h s) = φ.val.app (op U) s ⟨h⟩ :=
  ofSkyscraperAdd_germ φ U h s

variable (x) in
/-- Morphisms `F_x → N` of `𝒪_{X,x}`-modules correspond to morphisms `F ⟶ x_* N` of
`𝒪_X`-modules. -/
noncomputable def moduleStalkSkyscraperHomEquiv (F : 𝓜) (N : ModuleCat.{u} (ringSheafStalk R x)) :
    ((moduleStalkFunctor x).obj F ⟶ N) ≃ (F ⟶ (moduleSkyscraper x).obj N) where
  toFun := toSkyscraper
  invFun := ofSkyscraper
  left_inv ψ := by
    ext s
    obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm F.val x s
    exact ofSkyscraper_germ _ U hU t
  right_inv φ := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
    ext s
    funext h
    exact ofSkyscraper_germ φ U.unop h.down s

variable (x) in
/-- **The stalk–skyscraper adjunction.** The stalk functor at `x` is left adjoint to the
skyscraper functor at `x`. -/
noncomputable def moduleStalkSkyscraperAdjunction :
    moduleStalkFunctor x ⊣ moduleSkyscraper (R := R) x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := moduleStalkSkyscraperHomEquiv x
      homEquiv_naturality_left_symm := fun {F G N} f g => by
        ext s
        obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm F.val x s
        change ofSkyscraper (f ≫ g) _ = ofSkyscraper g ((moduleStalkFunctor x).map f _)
        rw [moduleStalkFunctor_map_germ, ofSkyscraper_germ, ofSkyscraper_germ]
        rfl
      homEquiv_naturality_right := fun f g => rfl }

lemma moduleStalkSkyscraperAdjunction_homEquiv_apply {F : 𝓜}
    {N : ModuleCat.{u} (ringSheafStalk R x)} (ψ : (moduleStalkFunctor x).obj F ⟶ N) (U : Opens X)
    (s : F.val.obj (op U)) (h : x ∈ U) :
    ((moduleStalkSkyscraperAdjunction x).homEquiv F N ψ).val.app (op U) s ⟨h⟩ =
      ψ (sectionGerm F.val x U h s) := rfl

variable (x) in
instance moduleSkyscraper_additive : (moduleSkyscraper (R := R) x).Additive where
  map_add {_ _} _ _ := SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => by
    ext s
    funext h
    rfl)

variable (x) in
instance moduleStalkFunctor_additive : (moduleStalkFunctor (R := R) x).Additive :=
  (moduleStalkSkyscraperAdjunction x).left_adjoint_additive

variable (x) in
/-- The stalk–skyscraper correspondence as an isomorphism of Hom groups:
`Hom(F_x, N) ≅ Hom(F, x_* N)` as additive groups. -/
noncomputable def moduleStalkSkyscraperHomAddEquiv (F : 𝓜)
    (N : ModuleCat.{u} (ringSheafStalk R x)) :
    ((moduleStalkFunctor x).obj F ⟶ N) ≃+ (F ⟶ (moduleSkyscraper x).obj N) :=
  (moduleStalkSkyscraperAdjunction x).homAddEquiv F N

lemma moduleStalkSkyscraperHomAddEquiv_apply {F : 𝓜} {N : ModuleCat.{u} (ringSheafStalk R x)}
    (ψ : (moduleStalkFunctor x).obj F ⟶ N) :
    moduleStalkSkyscraperHomAddEquiv x F N ψ = (moduleStalkSkyscraperAdjunction x).homEquiv F N ψ :=
  rfl

end Adjunction

end Ringed

end Hartshorne
