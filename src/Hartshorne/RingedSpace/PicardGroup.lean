/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality

/-!
# The Picard group of a ringed space

Hartshorne, *Algebraic Geometry*, II, Proposition 6.12 and the definition of `Pic X` (p. 143).

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`; `𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)`, and an `𝒪_X`-module is
invertible (`Hartshorne.Ringed.IsInvertible`) when it is locally free of rank one. We prove:

* **Proposition 6.12.** If `L` and `M` are invertible `𝒪_X`-modules, so is `L ⊗ M`
  (`isInvertible_moduleSheafTensor`); and for invertible `L` the evaluation map
  `L ⊗ L^∨ ⟶ 𝒪_X`, `l ⊗ ψ ↦ ψ(l)` (`moduleSheafDualEval`), is an isomorphism
  (`moduleSheafDualEval_isIso`, `moduleSheafDualEvalIso`). The dual `L^∨ = ℋom(L, 𝒪_X)` of an
  invertible sheaf is invertible (`isInvertible_moduleSheafDual`), and so is `𝒪_X`
  (`structureModule_isInvertible`).
* **The Picard group.** `Hartshorne.Ringed.Pic R` is the type of isomorphism classes of
  invertible `𝒪_X`-modules; it is a commutative group with multiplication induced by `⊗`
  (`Pic.mk_mul_mk`), identity the class of `𝒪_X` (`Pic.one_eq_mk`) and inverse the class of the
  dual (`Pic.inv_mk`).

A group of isomorphism classes needs no coherence data, only the existence of isomorphisms
`(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)` (`moduleSheafTensorAssoc`), `𝒪_X ⊗ F ≅ F` (`moduleSheafUnitTensor`),
`E ⊗ F ≅ F ⊗ E` (`moduleSheafTensorComm`), and the compatibility of `⊗` and of duals with
isomorphisms (`moduleSheafTensorIsoOfIso`, `moduleSheafDualIsoOfIso`). These all come from the
universal property of the tensor product. For associativity, morphisms out of `(A ⊗ B) ⊗ C` are
built from trilinear maps on sections (`ModuleSheafTrilinear.tensorDesc`) by currying the last
variable into `ℋom(C, H)`, and are determined by their values on elementary tensors
(`moduleSheafTensor_assoc_hom_ext`).

The local statements use local frames (`IsLocalFrame`): a frame of `E` over `U` indexed by `I`
makes `E|_U` free on `I` (`nonempty_over_iso_free_of_isLocalFrame`), so a module with frames of
size `r` around every point is locally free of rank `r` (`isLocallyFreeOfRank_of_isLocalFrame`).
Frames of `A` and `G` give a frame of `ℋom(A, G)` (`IsLocalFrame.homFrame`), and for invertible `L`
there is an isomorphism `L ⊗ M ≅ ℋom(L^∨, M)` (`tensorIsoHomDual`, from the double-dual and
dual-tensor isomorphisms), which gives the invertibility of `L ⊗ M`. The evaluation map is an
isomorphism because on every open inside a rank-one frame the presheaf-level pairing
`L(V) ⊗ L^∨(V) → 𝒪_X(V)` is bijective, and sheafification does not change stalks.

For a scheme `X`, `X.Modules` is definitionally `SheafOfModules (ringCatSheafOf X.sheaf)`, so the
Picard group of a scheme is `Pic X.sheaf`; `Scheme.Modules.isInvertible_iff_ringed` compares the
invertibility predicates.
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits
open scoped TensorProduct

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

set_option hygiene false in
/-- `𝒪_X`-modules. -/
local notation "𝓜" => SheafOfModules.{u} (ringCatSheafOf R)

set_option hygiene false in
/-- Sections of the structure sheaf over an open. -/
local notation3 "𝒪(" U ")" => R.obj.obj (Opposite.op U)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

private lemma modules_map_smul (A : 𝓜) {U V : Opens X} (f : op U ⟶ op V) (r : 𝒪(U))
    (x : Γ(A, U)) : A.val.presheaf.map f (r • x) = R.obj.map f r • A.val.presheaf.map f x :=
  A.val.map_smul f r x

private lemma hom_app_smul {A B : 𝓜} (φ : A ⟶ B) (U : Opens X) (r : 𝒪(U)) (x : Γ(A, U)) :
    sectionsMap φ U (r • x) = r • sectionsMap φ U x :=
  (φ.val.app (op U)).hom.map_smul r x

private lemma modules_hom_ext {A B : 𝓜} {f g : A ⟶ B}
    (h : ∀ U : Opens X, sectionsMap f U = sectionsMap g U) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact ConcreteCategory.congr_hom (h U.unop) x

section Biproducts

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] {J : Type*} [Fintype J]
  [DecidableEq J] (A : C)

private lemma sigma_ι_isoCoproduct_inv_π [HasCoproduct (fun _ : J => A)] (i j : J) :
    Sigma.ι (fun _ : J => A) i ≫ (biproduct.isoCoproduct (fun _ : J => A)).inv ≫
      biproduct.π (fun _ : J => A) j = if i = j then 𝟙 A else 0 := by
  rw [biproduct.isoCoproduct_inv, ← Category.assoc, Sigma.ι_desc, biproduct.ι_π]
  split_ifs with h
  · subst h; rfl
  · rfl

omit [DecidableEq J] in
private lemma sum_isoCoproduct_inv_π_sigma_ι [HasCoproduct (fun _ : J => A)] :
    ∑ i, ((biproduct.isoCoproduct (fun _ : J => A)).inv ≫ biproduct.π (fun _ : J => A) i) ≫
      Sigma.ι (fun _ : J => A) i = 𝟙 _ := by
  have h : ∀ i, Sigma.ι (fun _ : J => A) i =
      biproduct.ι (fun _ : J => A) i ≫ (biproduct.isoCoproduct (fun _ : J => A)).hom := by
    intro i
    rw [biproduct.isoCoproduct_hom, biproduct.ι_desc]
  simp_rw [h, Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc, ← Preadditive.sum_comp]
  have ht : ∑ j, biproduct.π (fun _ : J => A) j ≫ biproduct.ι (fun _ : J => A) j = 𝟙 _ :=
    IsBilimit.total (biproduct.isBilimit _)
  rw [ht, Category.id_comp, Iso.inv_hom_id]

end Biproducts

section FreeFrame

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable (U : Opens X) {I : Type u} [Fintype I] [DecidableEq I]

/-- The open `U` itself, as the terminal object of the opens contained in `U`. -/
private abbrev picOverTop : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))

/-- The restriction from `U` to a smaller open, on the opens contained in `U`. -/
private def picToOverTop (A : (Over U)ᵒᵖ) : picOverTop U ⟶ A :=
  (Over.homMk A.unop.hom (Category.comp_id _) : A.unop ⟶ Over.mk (𝟙 U)).op

/-- The `i`-th coordinate projection of a finite free module on the opens of `U`. -/
private noncomputable def picFreeProj (i : I) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)) ⟶
      SheafOfModules.unit ((ringCatSheafOf R).over U) :=
  (biproduct.isoCoproduct (fun _ : I => SheafOfModules.unit ((ringCatSheafOf R).over U))).inv ≫
    biproduct.π (fun _ : I => SheafOfModules.unit ((ringCatSheafOf R).over U)) i

private lemma picιFree_picFreeProj (i j : I) :
    SheafOfModules.ιFree i ≫ picFreeProj (R := R) U j = if i = j then 𝟙 _ else 0 :=
  sigma_ι_isoCoproduct_inv_π _ i j

omit [DecidableEq I] in
private lemma pic_sum_picFreeProj_ιFree :
    ∑ i, picFreeProj (R := R) U i ≫ SheafOfModules.ιFree (I := I) i = 𝟙 _ :=
  sum_isoCoproduct_inv_π_sigma_ι _

/-- The `i`-th standard section of the free module `𝒪_U^{⊕ I}` over `U`. -/
private noncomputable def picFreeVec (i : I) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.obj
      (picOverTop U) :=
  (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) i).val.app (picOverTop U)
    (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj (picOverTop U) from
      (1 : R.obj.obj (op U)))

omit [Fintype I] [DecidableEq I] in
private lemma picιFree_app_smul_one (i : I) (A : (Over U)ᵒᵖ) (r : R.obj.obj (op A.unop.left)) :
    r • (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
        (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from
          (1 : R.obj.obj (op A.unop.left))) =
      (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
        (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from r) := by
  have h :=
    ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A).hom.map_smul
    r (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from
      (1 : R.obj.obj (op A.unop.left)))
  refine h.symm.trans ?_
  congr 1
  exact mul_one r

omit [Fintype I] [DecidableEq I] in
private lemma picFreeVec_restrict (i : I) (A : (Over U)ᵒᵖ) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.map
        (picToOverTop U A) (picFreeVec U i) =
      (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
        (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from
          (1 : R.obj.obj (op A.unop.left))) := by
  have := ConcreteCategory.congr_hom
    ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.naturality
      (picToOverTop U A))
    (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj (picOverTop U) from
      (1 : R.obj.obj (op U)))
  refine this.symm.trans ?_
  change (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
    (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from
      R.obj.map (A.unop.hom).op 1) = _
  rw [map_one]

/-- The map `(a_i) ↦ ∑ a_i e_i|_A` for the standard sections of a finite free module. -/
private noncomputable def picFreeFrameMap (A : (Over U)ᵒᵖ) (a : I → R.obj.obj (op A.unop.left)) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.obj A :=
  ∑ i, a i •
    (show (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.obj A
    from (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.map
      (picToOverTop U A) (picFreeVec U i))

/-- The value of a morphism of module sheaves at a fixed section, as an additive map. -/
private noncomputable def picHomEvalAddHom {M N : SheafOfModules.{u} ((ringCatSheafOf R).over U)}
    (A : (Over U)ᵒᵖ) (x : M.val.obj A) : (M ⟶ N) →+ N.val.obj A where
  toFun φ := φ.val.app A x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The standard sections of a finite free module form a frame.** -/
private lemma picFreeFrameMap_bijective (A : (Over U)ᵒᵖ) :
    Function.Bijective (picFreeFrameMap (R := R) (I := I) U A) := by
  have hF : ∀ a, picFreeFrameMap (R := R) (I := I) U A a =
      ∑ i, (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
        (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from a i) := by
    intro a
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [picFreeVec_restrict, picιFree_app_smul_one]
  have hπι : ∀ (i j : I) (r : R.obj.obj (op A.unop.left)),
      (picFreeProj (R := R) U j).val.app A
        ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
          (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from r)) =
        if i = j then r else 0 := by
    intro i j r
    have := congrArg (fun φ => φ.val.app A
      (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from r))
      (picιFree_picFreeProj (R := R) U i j)
    refine this.trans ?_
    split_ifs <;> rfl
  have hsum :
      ∀ s : (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.obj A,
      ∑ i, (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
        ((picFreeProj (R := R) U i).val.app A s) = s := by
    intro s
    have := congrArg (picHomEvalAddHom U A s) (pic_sum_picFreeProj_ιFree (R := R) U (I := I))
    rw [map_sum] at this
    exact this
  have hΨ : ∀ a : I → R.obj.obj (op A.unop.left), (fun j => (show R.obj.obj (op A.unop.left) from
      (picFreeProj (R := R) U j).val.app A (picFreeFrameMap U A a))) = a := by
    intro a
    funext j
    rw [hF, map_sum]
    simp_rw [hπι]
    exact (Finset.sum_eq_single j (fun k _ hk => if_neg hk)
      (fun h' => absurd (Finset.mem_univ j) h')).trans (if_pos rfl)
  refine ⟨fun a b hab => ?_, fun s => ⟨fun j => (picFreeProj (R := R) U j).val.app A s, ?_⟩⟩
  · rw [← hΨ a, ← hΨ b, hab]
  · exact (hF _).trans (hsum s)

end FreeFrame

section TensorFunctoriality

variable {E E' E'' F F' F'' : 𝓜}

lemma modulesTensorMap_comp (φ : E ⟶ E') (φ' : E' ⟶ E'') (ψ : F ⟶ F') (ψ' : F' ⟶ F'') :
    modulesTensorMap (φ ≫ φ') (ψ ≫ ψ') = modulesTensorMap φ ψ ≫ modulesTensorMap φ' ψ' := by
  refine modulesTensor_hom_ext fun U e f => ?_
  change _ = sectionsMap (modulesTensorMap φ' ψ') U (sectionsMap (modulesTensorMap φ ψ) U
    ((moduleSheafTensorBilinear E F).app (op U) e f))
  rw [modulesTensorMap_tmul, modulesTensorMap_tmul, modulesTensorMap_tmul]
  rfl

lemma modulesTensorMap_id (E F : 𝓜) :
    modulesTensorMap (𝟙 E) (𝟙 F) = 𝟙 (moduleSheafTensor E F) := by
  refine modulesTensor_hom_ext fun U e f => ?_
  rw [modulesTensorMap_tmul]
  rfl

end TensorFunctoriality

section Helpers

private lemma pic_map_map (A : 𝓜) {U V W : Opens X} (i : V ≤ U) (j : W ≤ V)
    (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE j).op (A.val.presheaf.map (homOfLE i).op x) =
      A.val.presheaf.map (homOfLE (j.trans i)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma pic_map_id (A : 𝓜) {U : Opens X} (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE (le_refl U)).op x = x := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma pic_ring_map_id {U : Opens X} (r : 𝒪(U)) :
    R.obj.map (homOfLE (le_refl U)).op r = r := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma pic_hom_naturality {A B : 𝓜} (φ : A ⟶ B) {U V : Opens X} (h : V ≤ U)
    (x : Γ(A, U)) :
    sectionsMap φ V (A.val.presheaf.map (homOfLE h).op x) =
      B.val.presheaf.map (homOfLE h).op (sectionsMap φ U x) :=
  ConcreteCategory.congr_hom ((modulesMapPresheaf φ).naturality (homOfLE h).op) x

end Helpers

section TensorIsos

/-- The morphism out of a tensor product attached to a bilinear map sends `e ⊗ f` to `β(e, f)`. -/
lemma moduleSheafTensorHomEquiv_symm_tmul {E F H : 𝓜} (β : ModuleSheafBilinear E F H)
    {U : Opens X} (e : Γ(E, U)) (f : Γ(F, U)) :
    sectionsMap ((moduleSheafTensorHomEquiv E F H).symm β) U
        ((moduleSheafTensorBilinear E F).app (op U) e f) = β.app (op U) e f := by
  have := congrArg (fun γ : ModuleSheafBilinear _ _ _ => γ.app (op U) e f)
    ((moduleSheafTensorHomEquiv_apply ((moduleSheafTensorHomEquiv E F H).symm β)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) β))
  exact this

/-- Tensor products of isomorphic modules are isomorphic. -/
noncomputable def moduleSheafTensorIsoOfIso {E E' F F' : 𝓜} (α : E ≅ E') (β : F ≅ F') :
    @Iso 𝓜 _ (moduleSheafTensor E F) (moduleSheafTensor E' F') where
  hom := modulesTensorMap α.hom β.hom
  inv := modulesTensorMap α.inv β.inv
  hom_inv_id := by
    rw [← modulesTensorMap_comp, α.hom_inv_id, β.hom_inv_id, modulesTensorMap_id]
  inv_hom_id := by
    rw [← modulesTensorMap_comp, α.inv_hom_id, β.inv_hom_id, modulesTensorMap_id]

/-- The bilinear map `(e, f) ↦ f ⊗ e`. -/
noncomputable def tensorFlipBilinear (E F : 𝓜) :
    ModuleSheafBilinear E F (moduleSheafTensor F E) where
  app U := ((moduleSheafTensorBilinear F E).app U).flip
  naturality i e f := (moduleSheafTensorBilinear F E).naturality i f e

/-- The symmetry map `E ⊗ F ⟶ F ⊗ E`, `e ⊗ f ↦ f ⊗ e`. -/
noncomputable def moduleSheafTensorFlip (E F : 𝓜) :
    @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) (moduleSheafTensor F E) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (tensorFlipBilinear E F)

/-- The symmetry map sends `e ⊗ f` to `f ⊗ e`. -/
lemma moduleSheafTensorFlip_tmul (E F : 𝓜) {U : Opens X} (e : Γ(E, U)) (f : Γ(F, U)) :
    sectionsMap (moduleSheafTensorFlip E F) U ((moduleSheafTensorBilinear E F).app (op U) e f) =
      (moduleSheafTensorBilinear F E).app (op U) f e :=
  moduleSheafTensorHomEquiv_symm_tmul _ e f

/-- **Commutativity of the tensor product:** `E ⊗ F ≅ F ⊗ E`. -/
noncomputable def moduleSheafTensorComm (E F : 𝓜) :
    @Iso 𝓜 _ (moduleSheafTensor E F) (moduleSheafTensor F E) where
  hom := moduleSheafTensorFlip E F
  inv := moduleSheafTensorFlip F E
  hom_inv_id := by
    refine modulesTensor_hom_ext fun U e f => ?_
    change sectionsMap (moduleSheafTensorFlip F E) U
      (sectionsMap (moduleSheafTensorFlip E F) U _) = _
    rw [moduleSheafTensorFlip_tmul, moduleSheafTensorFlip_tmul]
    rfl
  inv_hom_id := by
    refine modulesTensor_hom_ext fun U e f => ?_
    change sectionsMap (moduleSheafTensorFlip E F) U
      (sectionsMap (moduleSheafTensorFlip F E) U _) = _
    rw [moduleSheafTensorFlip_tmul, moduleSheafTensorFlip_tmul]
    rfl

/-- The bilinear map `(r, f) ↦ r f` from `𝒪_X × F` to `F`. -/
noncomputable def unitSMulBilinear (F : 𝓜) :
    ModuleSheafBilinear (structureModule R) F F where
  app U := LinearMap.lsmul 𝒪(U.unop) Γ(F, U.unop)
  naturality i r f := F.val.map_smul i r f

/-- The map `F ⟶ 𝒪_X ⊗ F`, `f ↦ 1 ⊗ f`. -/
noncomputable def unitTensorInv (F : 𝓜) :
    F ⟶ moduleSheafTensor (structureModule R) F :=
  modulesHomMk (fun U => ((moduleSheafTensorBilinear (structureModule R) F).app (op U))
      (show Γ(structureModule R, U) from (1 : 𝒪(U))))
    (fun U V i f => by
      change (moduleSheafTensorBilinear (structureModule R) F).app (op V)
          (show Γ(structureModule R, V) from (1 : 𝒪(V))) (F.val.presheaf.map (homOfLE i).op f) =
        (moduleSheafTensor (structureModule R) F).val.map (homOfLE i).op
          ((moduleSheafTensorBilinear (structureModule R) F).app (op U)
            (show Γ(structureModule R, U) from (1 : 𝒪(U))) f)
      refine Eq.trans ?_ ((moduleSheafTensorBilinear (structureModule R) F).naturality
        (homOfLE i).op _ f).symm
      congr 1
      exact congrArg _ (map_one (R.obj.map (homOfLE i).op).hom).symm)

/-- **The structure sheaf is a unit for the tensor product:** `𝒪_X ⊗ F ≅ F`. -/
noncomputable def moduleSheafUnitTensor (F : 𝓜) :
    @Iso 𝓜 _ (moduleSheafTensor (structureModule R) F) F where
  hom := (moduleSheafTensorHomEquiv _ _ _).symm (unitSMulBilinear F)
  inv := unitTensorInv F
  hom_inv_id := by
    refine modulesTensor_hom_ext fun U r f => ?_
    change sectionsMap (unitTensorInv F) U (sectionsMap ((moduleSheafTensorHomEquiv _ _ _).symm
      (unitSMulBilinear F)) U _) = _
    rw [moduleSheafTensorHomEquiv_symm_tmul]
    change (moduleSheafTensorBilinear (structureModule R) F).app (op U)
        (show Γ(structureModule R, U) from (1 : 𝒪(U))) ((show 𝒪(U) from r) • f) = _
    erw [LinearMap.map_smul, ← LinearMap.map_smul₂]
    exact congrArg (fun a => (moduleSheafTensorBilinear (structureModule R) F).app (op U) a f)
      (mul_one (show 𝒪(U) from r))
  inv_hom_id := by
    refine modules_hom_ext fun U => ?_
    ext f
    change sectionsMap ((moduleSheafTensorHomEquiv _ _ _).symm (unitSMulBilinear F)) U
      ((moduleSheafTensorBilinear (structureModule R) F).app (op U)
        (show Γ(structureModule R, U) from (1 : 𝒪(U))) f) = f
    rw [moduleSheafTensorHomEquiv_symm_tmul]
    exact one_smul _ f

end TensorIsos

section Frames

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A frame over `U` restricts to a frame over any smaller open. -/
lemma IsLocalFrame.restrictLE {A : 𝓜} {U V : Opens X} {e : ι → Γ(A, U)}
    (hA : IsLocalFrame A U e) (hVU : V ≤ U) :
    IsLocalFrame A V (fun i => A.val.presheaf.map (homOfLE hVU).op (e i)) := by
  intro W hW
  have key : ⇑(localFrameMap A (fun i => A.val.presheaf.map (homOfLE hVU).op (e i)) hW) =
      ⇑(localFrameMap A e (hW.trans hVU)) := by
    funext a
    rw [localFrameMap_apply, localFrameMap_apply]
    simp_rw [pic_map_map]
  rw [key]
  exact hA W _

/-- A frame reindexed along an equivalence of index types. -/
lemma IsLocalFrame.reindex {A : 𝓜} {U : Opens X} {e : ι → Γ(A, U)}
    (hA : IsLocalFrame A U e) (σ : κ ≃ ι) : IsLocalFrame A U (e ∘ σ) := by
  intro V h
  have key : ⇑(localFrameMap A (e ∘ σ) h) =
      ⇑(localFrameMap A e h) ∘ ⇑(σ.arrowCongr (Equiv.refl 𝒪(V))) := by
    funext a
    rw [Function.comp_apply, localFrameMap_apply, localFrameMap_apply]
    exact Fintype.sum_equiv σ _ _ (fun k => by simp; rfl)
  rw [key]
  exact (hA V h).comp (σ.arrowCongr (Equiv.refl 𝒪(V))).bijective

/-- A module locally free of rank `r` has frames indexed by `Fin r` near every point. -/
lemma exists_isLocalFrame_of_isLocallyFreeOfRank {E : 𝓜} {r : ℕ}
    (hE : IsLocallyFreeOfRank E r) (x : X) :
    ∃ (U : Opens X) (e : ULift.{u} (Fin r) → Γ(E, U)), x ∈ U ∧ IsLocalFrame E U e := by
  classical
  obtain ⟨U, hxU, ⟨α⟩⟩ := hE x
  exact ⟨U, _, hxU, isLocalFrame_of_over_iso α⟩

private lemma sectionsMap_iso_bijective {A B : 𝓜} (α : A ≅ B) (V : Opens X) :
    Function.Bijective (sectionsMap α.hom V) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨sectionsMap α.inv V, fun x => ?_, fun y => ?_⟩
  · exact ConcreteCategory.congr_hom (congrArg (fun f => sectionsMap f V) α.hom_inv_id) x
  · exact ConcreteCategory.congr_hom (congrArg (fun f => sectionsMap f V) α.inv_hom_id) y

/-- A frame transported along an isomorphism of modules. -/
lemma IsLocalFrame.of_iso {A B : 𝓜} (α : B ≅ A) {U : Opens X} {e : ι → Γ(B, U)}
    (hB : IsLocalFrame B U e) : IsLocalFrame A U (fun i => sectionsMap α.hom U (e i)) := by
  intro V h
  have key : ⇑(localFrameMap A (fun i => sectionsMap α.hom U (e i)) h) =
      sectionsMap α.hom V ∘ localFrameMap B e h := by
    funext a
    rw [Function.comp_apply, localFrameMap_apply, localFrameMap_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hom_app_smul]
    congr 1
    exact (pic_hom_naturality α.hom h (e i)).symm
  rw [key]
  exact (sectionsMap_iso_bijective α V).comp (hB V h)

/-- The section of `E|_U` on the opens of `U` given by restricting a section over `U`. -/
private noncomputable def overSection {E : 𝓜} {U : Opens X} (s : Γ(E, U)) :
    (E.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun A => (show (E.over U).val.obj A from E.val.presheaf.map A.unop.hom.op s))
    (fun A B f => by
      change E.val.presheaf.map f.unop.left.op (E.val.presheaf.map A.unop.hom.op s) =
        E.val.presheaf.map B.unop.hom.op s
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w f.unop])

/-- The morphism `𝒪_U^{⊕ I} ⟶ E|_U` sending the `i`-th basis vector to `e i`. -/
private noncomputable def frameHom {I : Type u} {E : 𝓜} {U : Opens X} (e : I → Γ(E, U)) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)) ⟶ E.over U :=
  (E.over U).freeHomEquiv.symm (fun i => overSection (e i))

private lemma frameHom_ιFree {I : Type u} {E : 𝓜} {U : Opens X} (e : I → Γ(E, U)) (i : I)
    (A : (Over U)ᵒᵖ) :
    (frameHom e).val.app A
        ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
          (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from
            (1 : R.obj.obj (op A.unop.left)))) =
      E.val.presheaf.map A.unop.hom.op (e i) := by
  have h : (E.over U).freeHomEquiv (frameHom e) i = overSection (e i) := by
    simp only [frameHom, Equiv.apply_symm_apply]
  exact congrArg (fun s : (E.over U).sections => s.1 A) h

/-- A morphism of module sheaves on the opens of `U` that is bijective on all sections is an
isomorphism. -/
private lemma over_isIso_of_bijective {U : Opens X}
    {M N : SheafOfModules.{u} ((ringCatSheafOf R).over U)} (φ : M ⟶ N)
    (h : ∀ A, Function.Bijective (φ.val.app A)) : IsIso φ := by
  have : (SheafOfModules.forget ((ringCatSheafOf R).over U)).ReflectsIsomorphisms :=
    (SheafOfModules.fullyFaithfulForget _).reflectsIsomorphisms
  have : (SheafOfModules.forget ((ringCatSheafOf R).over U) ⋙
      PresheafOfModules.toPresheaf _).ReflectsIsomorphisms :=
    reflectsIsomorphisms_comp _ _
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget ((ringCatSheafOf R).over U) ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro A
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (h A)

private lemma frameHom_bijective {I : Type u} [Fintype I] [DecidableEq I] {E : 𝓜} {U : Opens X}
    {e : I → Γ(E, U)} (he : IsLocalFrame E U e) (A : (Over U)ᵒᵖ) :
    Function.Bijective ((frameHom e).val.app A) := by
  have key : ⇑((frameHom e).val.app A) ∘ picFreeFrameMap U A =
      ⇑(localFrameMap E e (leOfHom A.unop.hom)) := by
    funext a
    rw [Function.comp_apply, picFreeFrameMap, map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (localFrameMap_apply E e _ a).symm
    refine (((frameHom e).val.app A).hom.map_smul (a i) _).trans ?_
    congr 1
    exact (congrArg ((frameHom e).val.app A) (picFreeVec_restrict U i A)).trans
      (frameHom_ιFree e i A)
  have hb := he _ (leOfHom A.unop.hom)
  rw [← key] at hb
  exact (Function.Bijective.of_comp_iff _ (picFreeFrameMap_bijective U A)).mp hb

/-- A frame of `E` over `U` indexed by `I` makes `E|_U` free on `I`. -/
lemma nonempty_over_iso_free_of_isLocalFrame {I : Type u} [Fintype I] [DecidableEq I]
    {E : 𝓜} {U : Opens X} {e : I → Γ(E, U)} (h : IsLocalFrame E U e) :
    Nonempty (E.over U ≅ SheafOfModules.free I) := by
  have : IsIso (frameHom e) := over_isIso_of_bijective _ (frameHom_bijective h)
  exact ⟨(asIso (frameHom e)).symm⟩

/-- A module with frames indexed by `Fin r` near every point is locally free of rank `r`. -/
lemma isLocallyFreeOfRank_of_isLocalFrame {E : 𝓜} {r : ℕ}
    (h : ∀ x : X, ∃ (U : Opens X) (e : ULift.{u} (Fin r) → Γ(E, U)), x ∈ U ∧ IsLocalFrame E U e) :
    IsLocallyFreeOfRank E r := fun x => by
  classical
  obtain ⟨U, e, hx, he⟩ := h x
  exact ⟨U, hx, nonempty_over_iso_free_of_isLocalFrame he⟩

/-- The unit section is a frame of the structure sheaf. -/
lemma structureModule_isLocalFrame :
    IsLocalFrame (structureModule R) ⊤
      (fun _ : ULift.{u} (Fin 1) => show Γ(structureModule R, ⊤) from (1 : 𝒪(⊤))) := by
  intro V h
  have key : ⇑(localFrameMap (structureModule R)
      (fun _ : ULift.{u} (Fin 1) => show Γ(structureModule R, ⊤) from (1 : 𝒪(⊤))) h) =
      ⇑(Equiv.funUnique (ULift.{u} (Fin 1)) 𝒪(V)) := by
    funext a
    rw [localFrameMap_apply, Fintype.sum_unique]
    change a default * R.obj.map (homOfLE h).op 1 = a default
    rw [map_one, mul_one]
  rw [key]
  exact (Equiv.funUnique (ULift.{u} (Fin 1)) 𝒪(V)).bijective

/-- The structure sheaf is invertible. -/
theorem structureModule_isInvertible : IsInvertible (structureModule R) :=
  isLocallyFreeOfRank_of_isLocalFrame fun _ => ⟨⊤, _, by simp, structureModule_isLocalFrame⟩

/-- **The dual of an invertible sheaf is invertible.** -/
theorem isInvertible_moduleSheafDual {L : 𝓜} (hL : IsInvertible L) :
    IsInvertible (moduleSheafDual L) :=
  isLocallyFreeOfRank_of_isLocalFrame fun x => by
    obtain ⟨U, e, hx, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hL x
    exact ⟨U, _, hx, he.dual⟩

/-- The restriction to `V` of the local morphism with values `g` on a frame takes the values
`g|_V` on the restricted frame. -/
lemma IsLocalFrame.localFrameEval_restrict_homOfValues [DecidableEq ι] {A G : 𝓜}
    {U : Opens X} {e : ι → Γ(A, U)} (hA : IsLocalFrame A U e) (g : ι → Γ(G, U)) {V : Opens X}
    (h : V ≤ U) :
    localFrameEval e h ((moduleSheafHom A G).val.presheaf.map (homOfLE h).op
        (hA.homOfValues (le_refl U) g)) = fun j => G.val.presheaf.map (homOfLE h).op (g j) := by
  funext j
  rw [localFrameEval_apply, moduleSheafHomEval_restrict, IsLocalFrame.homOfValues_eval,
    hA.coord_self, Finset.sum_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij, zero_smul])
      (fun hj => absurd (Finset.mem_univ j) hj), Pi.single_eq_same, one_smul]

/-- Frames of `A` and `G` over `U` give a frame of `ℋom(A, G)` over `U`. -/
lemma IsLocalFrame.homFrame [DecidableEq ι] {A G : 𝓜} {U : Opens X} {e : ι → Γ(A, U)}
    {f : κ → Γ(G, U)} (hA : IsLocalFrame A U e) (hG : IsLocalFrame G U f) :
    IsLocalFrame (moduleSheafHom A G) U
      (fun p : ι × κ => hA.homOfValues (le_refl U) (Pi.single p.1 (f p.2))) := by
  intro V h
  rw [← Function.Bijective.of_comp_iff' (hA.localFrameEval_bijective (G := G) h)]
  have key : ⇑(localFrameEval (G := G) e h) ∘ ⇑(localFrameMap (moduleSheafHom A G)
      (fun p : ι × κ => hA.homOfValues (le_refl U) (Pi.single p.1 (f p.2))) h) =
      ⇑((Equiv.curry ι κ 𝒪(V)).trans
        (Equiv.piCongrRight fun _ => (LinearEquiv.ofBijective _ (hG V h)).toEquiv)) := by
    funext c i
    rw [Function.comp_apply, localFrameMap_apply, map_sum, Finset.sum_apply]
    simp_rw [map_smul, Pi.smul_apply, hA.localFrameEval_restrict_homOfValues]
    change _ = localFrameMap G f h (fun k => c (i, k))
    rw [localFrameMap_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.single_eq_same]
    · intro a _ hai
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Pi.single_eq_of_ne (Ne.symm hai), map_zero, smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [key]
  exact Equiv.bijective _

end Frames

section TensorInvertible

/-- For an invertible `L`, `L ⊗ M ≅ ℋom(L^∨, M)`. -/
noncomputable def tensorIsoHomDual {L : 𝓜} (hL : IsInvertible L) (M : 𝓜) :
    @Iso 𝓜 _ (moduleSheafTensor L M) (moduleSheafHom (moduleSheafDual L) M) :=
  moduleSheafTensorIsoOfIso
      (moduleSheafDoubleDualIso L hL.isFiniteLocallyFree) (Iso.refl M) ≪≫
    moduleSheafDualTensorIso (moduleSheafDual L) M
      (isInvertible_moduleSheafDual hL).isFiniteLocallyFree

/-- **Hartshorne II, Proposition 6.12 (first part).** The tensor product of two invertible
sheaves is invertible. -/
theorem isInvertible_moduleSheafTensor {L M : 𝓜} (hL : IsInvertible L)
    (hM : IsInvertible M) : IsInvertible (moduleSheafTensor L M) := by
  refine isLocallyFreeOfRank_of_isLocalFrame fun x => ?_
  obtain ⟨U₁, e, hx₁, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hL x
  obtain ⟨U₂, f, hx₂, hf⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hM x
  have hd := (he.restrictLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).dual
  have hf' := hf.restrictLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)
  exact ⟨U₁ ⊓ U₂, _, ⟨hx₁, hx₂⟩, ((hd.homFrame hf').of_iso (tensorIsoHomDual hL M).symm).reindex
    (Equiv.prodUnique (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1))).symm⟩

end TensorInvertible

section Evaluation

private lemma pic_stalk_bijective {Y : TopCat.{u}} {P Q : TopCat.Presheaf AddCommGrpCat.{u} Y}
    (p : P ⟶ Q) {x : Y} {U : Opens Y} (hx : x ∈ U)
    (hp : ∀ V : Opens Y, V ≤ U → Function.Bijective (p.app (op V))) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map p) := by
  constructor
  · intro s t hst
    obtain ⟨V, hVU, hxV, s, rfl⟩ := P.exists_le_germ_eq s hx
    obtain ⟨V', hV'U, hxV', t, rfl⟩ := P.exists_le_germ_eq t hx
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
    obtain ⟨W, hxW, iV, iV', heq⟩ := Q.germ_eq x hxV hxV' _ _ hst
    have hWU : W ≤ U := (leOfHom iV).trans hVU
    have e : ∀ {V₁ V₂ : Opens Y} (i : V₂ ⟶ V₁) (a : ToType (P.obj (op V₁))),
        Q.map i.op (p.app (op V₁) a) = p.app (op V₂) (P.map i.op a) := fun i a => by
      rw [← ConcreteCategory.comp_apply, ← p.naturality, ConcreteCategory.comp_apply]
    rw [e, e] at heq
    have := (hp W hWU).1 heq
    rw [← TopCat.Presheaf.germ_res_apply P iV x hxW,
      ← TopCat.Presheaf.germ_res_apply P iV' x hxW, this]
  · intro t
    obtain ⟨V, hVU, hxV, t, rfl⟩ := Q.exists_le_germ_eq t hx
    obtain ⟨s, rfl⟩ := (hp V hVU).2 t
    exact ⟨P.germ V x hxV s, TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _⟩

variable (L : 𝓜)

/-- The evaluation pairing `L × L^∨ → 𝒪_X`, `(l, ψ) ↦ ψ(l)`. -/
noncomputable def dualEvalBilinear :
    ModuleSheafBilinear L (moduleSheafDual L) (structureModule R) where
  app U := LinearMap.mk₂ _
    (fun (l : Γ(L, U.unop)) (ψ : Γ(moduleSheafDual L, U.unop)) => dualEval ψ (le_refl U.unop) l)
    (fun l l' ψ => map_add _ l l')
    (fun r l ψ => map_smul _ r l)
    (fun l ψ ψ' => rfl)
    (fun r l ψ => by
      change moduleSheafHomEval (r • ψ) (le_refl U.unop) l =
        (show 𝒪(U.unop) from r) *
          (show 𝒪(U.unop) from moduleSheafHomEval ψ (le_refl U.unop) l)
      erw [moduleSheafHomEval_smul, pic_ring_map_id]
      rfl)
  naturality {U V} i l ψ :=
    (moduleSheafHomEval_natural ψ (le_refl U.unop) (leOfHom i.unop) l).symm

/-- **The evaluation map** `L ⊗ L^∨ ⟶ 𝒪_X`, `l ⊗ ψ ↦ ψ(l)`. -/
noncomputable def moduleSheafDualEval :
    @Quiver.Hom 𝓜 _ (moduleSheafTensor L (moduleSheafDual L)) (structureModule R) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (dualEvalBilinear L)

/-- The evaluation map sends `l ⊗ ψ` to `ψ(l)`. -/
lemma moduleSheafDualEval_tmul {U : Opens X} (l : Γ(L, U)) (ψ : Γ(moduleSheafDual L, U)) :
    sectionsMap (moduleSheafDualEval L) U
        ((moduleSheafTensorBilinear L (moduleSheafDual L)).app (op U) l ψ) =
      dualEval ψ (le_refl U) l :=
  moduleSheafTensorHomEquiv_symm_tmul _ l ψ

/-- The presheaf-level map `U ↦ L(U) ⊗ L^∨(U) → 𝒪_X(U)` underlying the evaluation map. -/
noncomputable abbrev dualEvalPresheafMap :
    (moduleSheafTensorPresheaf L (moduleSheafDual L)).presheaf ⟶ (structureModule R).val.presheaf :=
  (PresheafOfModules.toPresheaf _).map
    (moduleSheafTensorUnit L (moduleSheafDual L) ≫ (moduleSheafDualEval L).val)

variable {L}

/-- The presheaf-level evaluation map sends `l ⊗ ψ` to `ψ(l)`. -/
lemma dualEvalPresheafMap_tmul {V : Opens X} (l : Γ(L, V)) (ψ : Γ(moduleSheafDual L, V)) :
    (dualEvalPresheafMap L).app (op V)
        (show (moduleSheafTensorPresheaf L (moduleSheafDual L)).obj (op V) from l ⊗ₜ ψ) =
      dualEval ψ (le_refl V) l :=
  moduleSheafDualEval_tmul L l ψ

/-- On every open inside a rank-one frame of `L`, the pairing `L(V) ⊗ L^∨(V) → 𝒪_X(V)` is
bijective. -/
lemma dualEvalPresheafMap_bijective {ι : Type*} [Fintype ι] [Unique ι]
    {U : Opens X} {e : ι → Γ(L, U)} (hL : IsLocalFrame L U e) {V : Opens X} (h : V ≤ U) :
    Function.Bijective ((dualEvalPresheafMap L).app (op V)) := by
  let c : Γ(L, V) ≃ₗ[𝒪(V)] 𝒪(V) :=
    (hL.coord h).trans (LinearEquiv.funUnique ι 𝒪(V) 𝒪(V))
  let d : Γ(moduleSheafDual L, V) ≃ₗ[𝒪(V)] 𝒪(V) :=
    (LinearEquiv.ofBijective (localFrameEval (G := structureModule R) e h)
      (hL.localFrameEval_bijective h)).trans (LinearEquiv.funUnique ι 𝒪(V) 𝒪(V))
  let T : TensorProduct 𝒪(V) Γ(L, V) Γ(moduleSheafDual L, V) ≃ₗ[𝒪(V)] 𝒪(V) :=
    (TensorProduct.congr c d).trans (TensorProduct.lid 𝒪(V) 𝒪(V))
  have key : ∀ t, (dualEvalPresheafMap L).app (op V) t = T t := by
    intro t
    change TensorProduct 𝒪(V) Γ(L, V) Γ(moduleSheafDual L, V) at t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero T).symm
    | tmul l ψ =>
      refine (dualEvalPresheafMap_tmul l ψ).trans ?_
      simp only [T, c, d, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        TensorProduct.lid_tmul, LinearEquiv.funUnique_apply]
      conv_lhs => rw [← hL.localFrameMap_coord h l]
      rw [localFrameMap_apply, Fintype.sum_unique, map_smul]
      rfl
    | add a b ha hb => exact (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans
        (map_add T a b).symm)
  have : ⇑((dualEvalPresheafMap L).app (op V)) = ⇑T := funext key
  rw [this]
  exact T.bijective

variable (L)

/-- If `L` has frames of rank one locally, the evaluation map is an isomorphism. -/
lemma isIso_moduleSheafDualEval_of_localFrames
    (hL : ∀ x : X, ∃ (U : Opens X) (e : ULift.{u} (Fin 1) → Γ(L, U)), x ∈ U ∧
      IsLocalFrame L U e) :
    IsIso (moduleSheafDualEval L) := by
  refine modules_isIso_of_stalk_bijective _ fun x => ?_
  obtain ⟨U, e, hx, hLU⟩ := hL x
  have h1 := pic_stalk_bijective (dualEvalPresheafMap L) hx
    (fun V h => dualEvalPresheafMap_bijective hLU h)
  have h2 := ModuleSheafTensor.moduleSheafTensorUnitStalk_bijective L (moduleSheafDual L) x
  have hc : dualEvalPresheafMap L =
      @CategoryStruct.comp (TopCat.Presheaf AddCommGrpCat.{u} X) _ _ _ _
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (moduleSheafTensorPresheaf L (moduleSheafDual L)).presheaf)
        (modulesMapPresheaf (moduleSheafDualEval L)) :=
    (PresheafOfModules.toPresheaf _).map_comp _ _
  have e := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (moduleSheafTensorPresheaf L (moduleSheafDual L)).presheaf)
    (modulesMapPresheaf (moduleSheafDualEval L))
  rw [hc, e] at h1
  exact (Function.Bijective.of_comp_iff _ h2).mp h1

/-- **Hartshorne II, Proposition 6.12 (second part).** For an invertible sheaf `L`, the
evaluation map `L ⊗ L^∨ ⟶ 𝒪_X` is an isomorphism. -/
theorem moduleSheafDualEval_isIso (hL : IsInvertible L) : IsIso (moduleSheafDualEval L) :=
  isIso_moduleSheafDualEval_of_localFrames L (exists_isLocalFrame_of_isLocallyFreeOfRank hL)

/-- The isomorphism `L ⊗ L^∨ ≅ 𝒪_X` given by evaluation, for an invertible sheaf `L`. -/
noncomputable def moduleSheafDualEvalIso (hL : IsInvertible L) :
    @Iso 𝓜 _ (moduleSheafTensor L (moduleSheafDual L)) (structureModule R) :=
  haveI := moduleSheafDualEval_isIso L hL
  asIso (moduleSheafDualEval L)

end Evaluation

section Associativity

/-- A trilinear morphism `A × B × C → H` of `𝒪_X`-modules: for every open `U`, an
`𝒪_X(U)`-trilinear map `A(U) × B(U) × C(U) → H(U)`, compatible with restriction. -/
structure ModuleSheafTrilinear (A B C H : 𝓜) where
  /-- The trilinear map on sections over `U`, linear in the last variable. -/
  app (U : Opens X) : Γ(A, U) → Γ(B, U) → Γ(C, U) →ₗ[𝒪(U)] Γ(H, U)
  add_left (U : Opens X) (a a' : Γ(A, U)) (b : Γ(B, U)) :
    app U (a + a') b = app U a b + app U a' b
  smul_left (U : Opens X) (r : 𝒪(U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    app U (r • a) b = r • app U a b
  add_mid (U : Opens X) (a : Γ(A, U)) (b b' : Γ(B, U)) :
    app U a (b + b') = app U a b + app U a b'
  smul_mid (U : Opens X) (r : 𝒪(U)) (a : Γ(A, U)) (b : Γ(B, U)) :
    app U a (r • b) = r • app U a b
  naturality {U V : Opens X} (i : V ≤ U) (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    H.val.presheaf.map (homOfLE i).op (app U a b c) =
      app V (A.val.presheaf.map (homOfLE i).op a) (B.val.presheaf.map (homOfLE i).op b)
        (C.val.presheaf.map (homOfLE i).op c)

namespace ModuleSheafTrilinear

variable {A B C H : 𝓜} (τ : ModuleSheafTrilinear A B C H)

/-- The local morphism `c ↦ τ(a, b, c)` attached to sections `a`, `b` over `U`. -/
noncomputable def homSection {U : Opens X} (a : Γ(A, U)) (b : Γ(B, U)) :
    Γ(moduleSheafHom C H, U) :=
  moduleSheafHomMk
    (fun V h => τ.app V (A.val.presheaf.map (homOfLE h).op a) (B.val.presheaf.map (homOfLE h).op b))
    (fun V V' hV j x => by
      rw [τ.naturality j, pic_map_map, pic_map_map])

/-- Evaluating `τ.homSection a b` at `c` gives `τ(a, b, c)`. -/
lemma homSection_eval {U : Opens X} (a : Γ(A, U)) (b : Γ(B, U)) {V : Opens X} (h : V ≤ U)
    (c : Γ(C, V)) :
    moduleSheafHomEval (τ.homSection a b) h c =
      τ.app V (A.val.presheaf.map (homOfLE h).op a) (B.val.presheaf.map (homOfLE h).op b) c := rfl

/-- The local morphisms `τ.homSection a b` are compatible with restriction. -/
lemma homSection_restrict {U V : Opens X} (i : V ≤ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    (moduleSheafHom C H).val.presheaf.map (homOfLE i).op (τ.homSection a b) =
      τ.homSection (A.val.presheaf.map (homOfLE i).op a) (B.val.presheaf.map (homOfLE i).op b) :=
  moduleSheafHomEval_ext fun W h => LinearMap.ext fun c => by
    change τ.app W (A.val.presheaf.map (homOfLE (h.trans i)).op a)
        (B.val.presheaf.map (homOfLE (h.trans i)).op b) c =
      τ.app W (A.val.presheaf.map (homOfLE h).op (A.val.presheaf.map (homOfLE i).op a))
        (B.val.presheaf.map (homOfLE h).op (B.val.presheaf.map (homOfLE i).op b)) c
    rw [pic_map_map, pic_map_map]

/-- The sections `τ.homSection a b`, as a bilinear map in `a` and `b`. -/
noncomputable def homSectionBilinear (U : Opens X) :
    Γ(A, U) →ₗ[𝒪(U)] Γ(B, U) →ₗ[𝒪(U)] Γ(moduleSheafHom C H, U) :=
  LinearMap.mk₂ _ (fun a b => τ.homSection a b)
    (fun a a' b => moduleSheafHomEval_ext fun V h => LinearMap.ext fun c => by
      change τ.app V (A.val.presheaf.map (homOfLE h).op (a + a'))
          (B.val.presheaf.map (homOfLE h).op b) c =
        τ.app V (A.val.presheaf.map (homOfLE h).op a) (B.val.presheaf.map (homOfLE h).op b) c +
          τ.app V (A.val.presheaf.map (homOfLE h).op a') (B.val.presheaf.map (homOfLE h).op b) c
      rw [map_add, τ.add_left]
      rfl)
    (fun r a b => moduleSheafHomEval_ext fun V h => LinearMap.ext fun c => by
      change τ.app V (A.val.presheaf.map (homOfLE h).op (r • a))
          (B.val.presheaf.map (homOfLE h).op b) c =
        R.obj.map (homOfLE h).op r •
          τ.app V (A.val.presheaf.map (homOfLE h).op a) (B.val.presheaf.map (homOfLE h).op b) c
      rw [modules_map_smul, τ.smul_left]
      rfl)
    (fun a b b' => moduleSheafHomEval_ext fun V h => LinearMap.ext fun c => by
      change τ.app V (A.val.presheaf.map (homOfLE h).op a)
          (B.val.presheaf.map (homOfLE h).op (b + b')) c =
        τ.app V (A.val.presheaf.map (homOfLE h).op a) (B.val.presheaf.map (homOfLE h).op b) c +
          τ.app V (A.val.presheaf.map (homOfLE h).op a) (B.val.presheaf.map (homOfLE h).op b') c
      rw [map_add, τ.add_mid]
      rfl)
    (fun r a b => moduleSheafHomEval_ext fun V h => LinearMap.ext fun c => by
      change τ.app V (A.val.presheaf.map (homOfLE h).op a)
          (B.val.presheaf.map (homOfLE h).op (r • b)) c =
        R.obj.map (homOfLE h).op r •
          τ.app V (A.val.presheaf.map (homOfLE h).op a) (B.val.presheaf.map (homOfLE h).op b) c
      rw [modules_map_smul, τ.smul_mid]
      rfl)

/-- The bilinear morphism `A × B → ℋom(C, H)` attached to a trilinear morphism. -/
noncomputable def toBilinearHom : ModuleSheafBilinear A B (moduleSheafHom C H) where
  app U := τ.homSectionBilinear U.unop
  naturality i a b := τ.homSection_restrict (leOfHom i.unop) a b

/-- The morphism `(A ⊗ B) ⊗ C ⟶ H`, `(a ⊗ b) ⊗ c ↦ τ(a, b, c)`. -/
noncomputable def tensorDesc :
    @Quiver.Hom 𝓜 _ (moduleSheafTensor (moduleSheafTensor A B) C) H :=
  (moduleSheafTensorHomEquiv _ _ _).symm
    { app U := (homUncurry ((moduleSheafTensorHomEquiv _ _ _).symm τ.toBilinearHom)).app U |>.flip
      naturality i t c :=
        (homUncurry ((moduleSheafTensorHomEquiv _ _ _).symm τ.toBilinearHom)).naturality i c t }

/-- The morphism `τ.tensorDesc` sends `(a ⊗ b) ⊗ c` to `τ(a, b, c)`. -/
lemma tensorDesc_tmul {U : Opens X} (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    sectionsMap τ.tensorDesc U ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op U)
      ((moduleSheafTensorBilinear A B).app (op U) a b) c) = τ.app U a b c := by
  refine (moduleSheafTensorHomEquiv_symm_tmul _ _ c).trans ?_
  change moduleSheafHomEval (sectionsMap ((moduleSheafTensorHomEquiv _ _ _).symm
    τ.toBilinearHom) U ((moduleSheafTensorBilinear A B).app (op U) a b)) (le_refl U) c = _
  refine (congrArg (fun ψ => moduleSheafHomEval ψ (le_refl U) c)
    (moduleSheafTensorHomEquiv_symm_tmul τ.toBilinearHom a b)).trans ?_
  change τ.app U (A.val.presheaf.map (homOfLE (le_refl U)).op a)
    (B.val.presheaf.map (homOfLE (le_refl U)).op b) c = _
  rw [pic_map_id, pic_map_id]

end ModuleSheafTrilinear

/-- Two morphisms out of `(A ⊗ B) ⊗ C` agreeing on all elementary tensors `(a ⊗ b) ⊗ c` are
equal. -/
lemma moduleSheafTensor_assoc_hom_ext {A B C H : 𝓜}
    {φ ψ : @Quiver.Hom 𝓜 _ (moduleSheafTensor (moduleSheafTensor A B) C) H}
    (h : ∀ (U : Opens X) (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)),
      sectionsMap φ U ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op U)
        ((moduleSheafTensorBilinear A B).app (op U) a b) c) =
      sectionsMap ψ U ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op U)
        ((moduleSheafTensorBilinear A B).app (op U) a b) c)) : φ = ψ := by
  let flipB : ∀ (χ : @Quiver.Hom 𝓜 _ (moduleSheafTensor (moduleSheafTensor A B) C) H),
      ModuleSheafBilinear C (moduleSheafTensor A B) H := fun χ =>
    { app U := (moduleSheafTensorHomEquiv _ _ H χ).app U |>.flip
      naturality i c t := (moduleSheafTensorHomEquiv _ _ H χ).naturality i t c }
  have hcurry : bilinearCurry (flipB φ) = bilinearCurry (flipB ψ) := by
    refine modulesTensor_hom_ext fun U a b => moduleSheafHomEval_ext fun V hV =>
      LinearMap.ext fun c => ?_
    change sectionsMap φ V ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op V)
        ((moduleSheafTensor A B).val.map (homOfLE hV).op
          ((moduleSheafTensorBilinear A B).app (op U) a b)) c) =
      sectionsMap ψ V ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op V)
        ((moduleSheafTensor A B).val.map (homOfLE hV).op
          ((moduleSheafTensorBilinear A B).app (op U) a b)) c)
    have hn : (moduleSheafTensor A B).val.map (homOfLE hV).op
        ((moduleSheafTensorBilinear A B).app (op U) a b) =
        (moduleSheafTensorBilinear A B).app (op V) (A.val.presheaf.map (homOfLE hV).op a)
          (B.val.presheaf.map (homOfLE hV).op b) :=
      (moduleSheafTensorBilinear A B).naturality _ a b
    erw [hn]
    exact h V _ _ c
  have hflip : flipB φ = flipB ψ := bilinearCurryEquiv.injective hcurry
  apply (moduleSheafTensorHomEquiv _ _ H).injective
  ext U t c
  exact congrArg (fun β : ModuleSheafBilinear C (moduleSheafTensor A B) H => β.app U c t) hflip

variable (L M N : 𝓜)

/-- The tensor product of two `𝒪_X`-modules, as an object of `𝓜`. -/
noncomputable abbrev modulesTensorObj (E F : 𝓜) : 𝓜 := moduleSheafTensor E F

/-- The trilinear map `(l, m, n) ↦ l ⊗ (m ⊗ n)`. -/
noncomputable def assocTrilinear :
    ModuleSheafTrilinear L M N (modulesTensorObj L (modulesTensorObj M N)) where
  app U l m := by
    let f := ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U) l).comp
      ((moduleSheafTensorBilinear M N).app (op U) m)
    exact f
  add_left U l l' m := LinearMap.ext fun _ =>
    LinearMap.map_add₂ ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U)) l l' _
  smul_left U r l m := LinearMap.ext fun _ =>
    LinearMap.map_smul₂ ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U))
      (show (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) from r) l _
  add_mid U l m m' := LinearMap.ext fun n =>
    (congrArg ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U) l)
      (LinearMap.map_add₂ ((moduleSheafTensorBilinear M N).app (op U)) m m' n)).trans
      (map_add _ _ _)
  smul_mid U r l m := LinearMap.ext fun n =>
    (congrArg ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op U) l)
      (LinearMap.map_smul₂ ((moduleSheafTensorBilinear M N).app (op U))
        (show (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) from r) m n)).trans
      (map_smul _ _ _)
  naturality {U V} i l m n :=
    ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).naturality (homOfLE i).op l _).trans
      (congrArg ((moduleSheafTensorBilinear L (moduleSheafTensor M N)).app (op V) _)
        ((moduleSheafTensorBilinear M N).naturality (homOfLE i).op m n))

/-- The trilinear map `(m, n, l) ↦ (l ⊗ m) ⊗ n`. -/
noncomputable def assocInvTrilinear :
    ModuleSheafTrilinear M N L (modulesTensorObj (modulesTensorObj L M) N) where
  app U m n := by
    let g := ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U)).flip
    let h := ((moduleSheafTensorBilinear L M).app (op U)).flip
    let f := (g n).comp (h m)
    exact f
  add_left U m m' n := LinearMap.ext fun l =>
    (congrArg (fun x => (moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U) x n)
      (LinearMap.map_add ((moduleSheafTensorBilinear L M).app (op U) l) m m')).trans
      (LinearMap.map_add₂ ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U))
        _ _ n)
  smul_left U r m n := LinearMap.ext fun l =>
    (congrArg (fun x => (moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U) x n)
      (LinearMap.map_smul ((moduleSheafTensorBilinear L M).app (op U) l)
        (show (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) from r) m)).trans
      (LinearMap.map_smul₂ ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U))
        _ _ n)
  add_mid U m n n' := LinearMap.ext fun l =>
    LinearMap.map_add ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U)
      ((moduleSheafTensorBilinear L M).app (op U) l m)) n n'
  smul_mid U r m n := LinearMap.ext fun l =>
    LinearMap.map_smul ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op U)
      ((moduleSheafTensorBilinear L M).app (op U) l m))
      (show (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) from r) n
  naturality {U V} i m n l :=
    ((moduleSheafTensorBilinear (moduleSheafTensor L M) N).naturality (homOfLE i).op _ n).trans
      (congrArg (fun x => (moduleSheafTensorBilinear (moduleSheafTensor L M) N).app (op V) x _)
        ((moduleSheafTensorBilinear L M).naturality (homOfLE i).op l m))

/-- **Associativity of the tensor product:** `(L ⊗ M) ⊗ N ≅ L ⊗ (M ⊗ N)`. -/
noncomputable def moduleSheafTensorAssoc :
    @Iso 𝓜 _ (moduleSheafTensor (moduleSheafTensor L M) N)
      (moduleSheafTensor L (moduleSheafTensor M N)) where
  hom := (assocTrilinear L M N).tensorDesc
  inv := (moduleSheafTensorComm L (moduleSheafTensor M N)).hom ≫
    (assocInvTrilinear L M N).tensorDesc
  hom_inv_id := by
    refine moduleSheafTensor_assoc_hom_ext fun U l m n => ?_
    change sectionsMap (assocInvTrilinear L M N).tensorDesc U
      (sectionsMap (moduleSheafTensorFlip L (moduleSheafTensor M N)) U
        (sectionsMap (assocTrilinear L M N).tensorDesc U _)) = _
    refine (congrArg (fun x => sectionsMap (assocInvTrilinear L M N).tensorDesc U
      (sectionsMap (moduleSheafTensorFlip L (moduleSheafTensor M N)) U x))
        ((assocTrilinear L M N).tensorDesc_tmul l m n)).trans ?_
    refine (congrArg (fun x => sectionsMap (assocInvTrilinear L M N).tensorDesc U x)
      (moduleSheafTensorFlip_tmul L (moduleSheafTensor M N) l _)).trans ?_
    exact (assocInvTrilinear L M N).tensorDesc_tmul m n l
  inv_hom_id := by
    have h : (assocInvTrilinear L M N).tensorDesc ≫ (assocTrilinear L M N).tensorDesc =
        (moduleSheafTensorComm L (moduleSheafTensor M N)).inv := by
      refine moduleSheafTensor_assoc_hom_ext fun U m n l => ?_
      change sectionsMap (assocTrilinear L M N).tensorDesc U
        (sectionsMap (assocInvTrilinear L M N).tensorDesc U _) =
        sectionsMap (moduleSheafTensorFlip (moduleSheafTensor M N) L) U _
      refine (congrArg (fun x => sectionsMap (assocTrilinear L M N).tensorDesc U x)
        ((assocInvTrilinear L M N).tensorDesc_tmul m n l)).trans ?_
      refine ((assocTrilinear L M N).tensorDesc_tmul l m n).trans ?_
      exact (moduleSheafTensorFlip_tmul (moduleSheafTensor M N) L _ l).symm
    exact (Category.assoc _ _ _).trans ((congrArg _ h).trans (Iso.hom_inv_id _))

end Associativity

section DualCongr

/-- The functoriality of `ℋom` is compatible with composition. -/
lemma moduleSheafHomMap_comp {F F' F'' G G' G'' : 𝓜} (f : F' ⟶ F) (g : G ⟶ G')
    (f' : F'' ⟶ F') (g' : G' ⟶ G'') :
    moduleSheafHomMap f g ≫ moduleSheafHomMap f' g' = moduleSheafHomMap (f' ≫ f) (g ≫ g') := by
  refine modules_hom_ext fun U => ?_
  ext ψ
  exact moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => rfl

/-- `ℋom` sends identities to the identity. -/
lemma moduleSheafHomMap_id (F G : 𝓜) :
    moduleSheafHomMap (𝟙 F) (𝟙 G) = 𝟙 _ := by
  refine modules_hom_ext fun U => ?_
  ext ψ
  exact moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => rfl

/-- Isomorphic modules have isomorphic duals. -/
noncomputable def moduleSheafDualIsoOfIso {L L' : 𝓜} (α : L ≅ L') :
    moduleSheafDual L ≅ moduleSheafDual L' where
  hom := moduleSheafHomMap α.inv (𝟙 _)
  inv := moduleSheafHomMap α.hom (𝟙 _)
  hom_inv_id := by
    rw [moduleSheafHomMap_comp, α.hom_inv_id, Category.id_comp, moduleSheafHomMap_id]
  inv_hom_id := by
    rw [moduleSheafHomMap_comp, α.inv_hom_id, Category.id_comp, moduleSheafHomMap_id]

end DualCongr

section PicardGroup

variable (R) in
/-- Two invertible `𝒪_X`-modules are related when they are isomorphic. -/
def invertibleModulesSetoid : Setoid {L : 𝓜 // IsInvertible L} where
  r L M := Nonempty (L.1 ≅ M.1)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

variable (R) in
/-- **The Picard group** `Pic X` of the ringed space `(X, 𝒪_X)`: the isomorphism classes of
invertible `𝒪_X`-modules. -/
def Pic : Type (u + 1) :=
  Quotient (invertibleModulesSetoid R)

namespace Pic

/-- The class in `Pic X` of an invertible `𝒪_X`-module. -/
def mk (L : 𝓜) (hL : IsInvertible L) : Pic R :=
  Quotient.mk _ ⟨L, hL⟩

/-- Every element of `Pic X` is the class of an invertible module. -/
lemma mk_surjective (c : Pic R) : ∃ (L : 𝓜) (hL : IsInvertible L), mk L hL = c := by
  obtain ⟨⟨L, hL⟩, rfl⟩ := Quotient.exists_rep c
  exact ⟨L, hL, rfl⟩

/-- Two invertible modules have the same class exactly when they are isomorphic. -/
lemma mk_eq_mk_iff {L M : 𝓜} (hL : IsInvertible L) (hM : IsInvertible M) :
    mk L hL = mk M hM ↔ Nonempty (L ≅ M) :=
  Quotient.eq (r := invertibleModulesSetoid R)

/-- The group structure on `Pic X`: multiplication is the tensor product, the identity is the
class of `𝒪_X`, and the inverse is the class of the dual `ℋom(L, 𝒪_X)`. -/
noncomputable instance instCommGroup : CommGroup (Pic R) where
  mul := Quotient.map₂
    (fun L M => ⟨moduleSheafTensor L.1 M.1, isInvertible_moduleSheafTensor L.2 M.2⟩)
    (fun _ _ ⟨α⟩ _ _ ⟨β⟩ => ⟨moduleSheafTensorIsoOfIso α β⟩)
  one := mk (structureModule R) structureModule_isInvertible
  inv := Quotient.map (fun L => ⟨moduleSheafDual L.1, isInvertible_moduleSheafDual L.2⟩)
    (fun _ _ ⟨α⟩ => ⟨moduleSheafDualIsoOfIso α⟩)
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun L M N =>
    Quotient.sound ⟨moduleSheafTensorAssoc L.1 M.1 N.1⟩
  one_mul a := Quotient.inductionOn a fun L => Quotient.sound ⟨moduleSheafUnitTensor L.1⟩
  mul_one a := Quotient.inductionOn a fun L =>
    Quotient.sound ⟨moduleSheafTensorComm _ _ ≪≫ moduleSheafUnitTensor L.1⟩
  inv_mul_cancel a := Quotient.inductionOn a fun L =>
    Quotient.sound ⟨moduleSheafTensorComm _ _ ≪≫ moduleSheafDualEvalIso L.1 L.2⟩
  mul_comm a b := Quotient.inductionOn₂ a b fun L M =>
    Quotient.sound ⟨moduleSheafTensorComm L.1 M.1⟩

/-- Multiplication in `Pic X` is induced by the tensor product. -/
lemma mk_mul_mk {L M : 𝓜} (hL : IsInvertible L) (hM : IsInvertible M) :
    mk L hL * mk M hM = mk (moduleSheafTensor L M) (isInvertible_moduleSheafTensor hL hM) :=
  rfl

/-- The identity of `Pic X` is the class of `𝒪_X`. -/
lemma one_eq_mk : (1 : Pic R) = mk (structureModule R) structureModule_isInvertible :=
  rfl

/-- The inverse in `Pic X` is the class of the dual `ℋom(L, 𝒪_X)`. -/
lemma inv_mk {L : 𝓜} (hL : IsInvertible L) :
    (mk L hL)⁻¹ = mk (moduleSheafDual L) (isInvertible_moduleSheafDual hL) :=
  rfl

end Pic

end PicardGroup

end Ringed

end Hartshorne
