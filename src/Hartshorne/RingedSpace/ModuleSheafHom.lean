/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AbelianSheafHom
import Hartshorne.Scheme.ModuleSheafTensor
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.Topology.Sheaves.Module

/-!
# The sheaf of local module morphisms on a ringed space

Hartshorne, *Algebraic Geometry*, II.5 (p. 109).

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`; `𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)`. For `𝒪_X`-modules `F` and
`G`, the restriction `F|_U` to an open `U` is the module sheaf `F.over U` over `𝒪_X|_U` on the
opens contained in `U` (its sections over `V ⊆ U` are `F(V)`); Mathlib's
`TopologicalSpace.Opens.sheafOfModulesEquivOver` identifies it with a module sheaf on the
subspace `U`. We construct the `𝒪_X`-module `ℋom(F, G)` (`Hartshorne.Ringed.moduleSheafHom`)
with sections `U ↦ Hom_{𝒪_U}(F|_U, G|_U)`, restriction by restricting morphisms, and the
`𝒪_X(U)`-module structure given by pointwise multiplication by restricted sections. Its global
sections are the morphisms `F ⟶ G` (`moduleSheafHomGlobalSectionsLinearEquiv`), and pre- and
postcomposition give morphisms of module sheaves (`moduleSheafHomMap`). Everything is bundled
in `Hartshorne.Ringed.moduleSheafHomData`.

For a scheme `X`, `X.Modules` is definitionally `SheafOfModules (ringCatSheafOf X.sheaf)`, so this
applies to schemes with `R := X.sheaf`.

The sheaf property is obtained by realizing the local module morphisms as the subpresheaf of the
sheaf of local morphisms of the underlying abelian sheaves (`TopCat.Sheaf.abelianSheafHom`)
cut out by linearity, which is a local condition.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace Hartshorne

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

private abbrev localModuleHom (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X) :
    Type u :=
  SheafOfModules.over F U ⟶ SheafOfModules.over G U

private noncomputable def localModuleScalar (G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (r : R.obj.obj (op U)) : End (SheafOfModules.over G U) :=
  { val :=
    { app V := ModuleCat.ofHom (X := (SheafOfModules.over G U).val.obj V)
          (Y := (SheafOfModules.over G U).val.obj V) <|
          LinearMap.lsmul (R.obj.obj (op V.unop.left)) (G.val.obj (op V.unop.left))
            (R.obj.map V.unop.hom.op r)
      naturality := by
        intro V W f
        ext x
        change G.val.obj (op V.unop.left) at x
        change R.obj.map W.unop.hom.op r • G.val.map f.unop.left.op x =
          G.val.map f.unop.left.op (R.obj.map V.unop.hom.op r • x)
        have h := G.val.map_smul f.unop.left.op (R.obj.map V.unop.hom.op r) x
        have hr : R.obj.map W.unop.hom.op r =
            R.obj.map f.unop.left.op (R.obj.map V.unop.hom.op r) := by
          rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, f.unop.w]
        rw [hr]
        exact h.symm } }

private lemma localModuleScalar_app (G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X)
    (r : R.obj.obj (op U)) (V : (Over U)ᵒᵖ) (x : G.val.obj (op V.unop.left)) :
    (localModuleScalar G U r).val.app V x = R.obj.map V.unop.hom.op r • x :=
  rfl

private noncomputable def localModuleScalarRingHom (G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) : R.obj.obj (op U) →+* End (SheafOfModules.over G U) where
  toFun := localModuleScalar G U
  map_zero' := by
    apply SheafOfModules.hom_ext
    ext V x
    change G.val.obj (op V.unop.left) at x
    change R.obj.map V.unop.hom.op (0 : R.obj.obj (op U)) • x = 0
    simp
  map_one' := by
    apply SheafOfModules.hom_ext
    ext V x
    change G.val.obj (op V.unop.left) at x
    change R.obj.map V.unop.hom.op (1 : R.obj.obj (op U)) • x = x
    simp
  map_add' r s := by
    apply SheafOfModules.hom_ext
    ext V x
    change G.val.obj (op V.unop.left) at x
    change R.obj.map V.unop.hom.op (r + s) • x =
      R.obj.map V.unop.hom.op r • x + R.obj.map V.unop.hom.op s • x
    simp [add_smul]
  map_mul' r s := by
    apply SheafOfModules.hom_ext
    ext V x
    change G.val.obj (op V.unop.left) at x
    change R.obj.map V.unop.hom.op (r * s) • x =
      R.obj.map V.unop.hom.op r • (R.obj.map V.unop.hom.op s • x)
    simp [mul_smul]

private noncomputable abbrev localModuleHomModule (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) : Module (R.obj.obj (op U)) (localModuleHom F G U) :=
  Module.compHom _ (localModuleScalarRingHom G U)

private lemma local_module_smul_app (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X)
    (r : R.obj.obj (op U)) (φ : localModuleHom F G U) (V : (Over U)ᵒᵖ)
    (x : F.val.obj (op V.unop.left)) :
    (letI := localModuleHomModule F G U; (r • φ).val.app V x) =
      (let y : G.val.obj (op V.unop.left) := φ.val.app V x
       R.obj.map V.unop.hom.op r • y) := by
  change (localModuleScalar G U r).val.app V (φ.val.app V x) = _
  exact localModuleScalar_app G U r V _

private noncomputable def localModuleRestrict (F G : SheafOfModules.{u} (ringCatSheafOf R))
    {U V : Opens X} (i : V ⟶ U) (φ : localModuleHom F G U) : localModuleHom F G V :=
  (SheafOfModules.overFunctorMap (ringCatSheafOf R) i).inv.app F ≫
    (SheafOfModules.overMap (ringCatSheafOf R) i).map φ ≫
    (SheafOfModules.overFunctorMap (ringCatSheafOf R) i).hom.app G

private lemma local_module_restrict_app (F G : SheafOfModules.{u} (ringCatSheafOf R))
    {U V W : Opens X} (i : V ⟶ U) (j : W ⟶ V) (φ : localModuleHom F G U)
    (x : F.val.obj (op W)) :
    (localModuleRestrict F G i φ).val.app (op (Over.mk j)) x =
      φ.val.app (op (Over.mk (j ≫ i))) x :=
  rfl

private lemma local_module_restrict_id (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (φ : localModuleHom F G U) : localModuleRestrict F G (𝟙 U) φ = φ := by
  apply SheafOfModules.hom_ext
  ext A x
  change F.val.obj (op A.unop.left) at x
  have h := local_module_restrict_app F G (𝟙 U) A.unop.hom φ x
  change (localModuleRestrict F G (𝟙 U) φ).val.app A x = φ.val.app A x at h
  exact h

private lemma local_module_restrict_comp (F G : SheafOfModules.{u} (ringCatSheafOf R))
    {U V W : Opens X} (i : V ⟶ U) (j : W ⟶ V) (φ : localModuleHom F G U) :
    localModuleRestrict F G j (localModuleRestrict F G i φ) =
      localModuleRestrict F G (j ≫ i) φ := by
  apply SheafOfModules.hom_ext
  ext A x
  change F.val.obj (op A.unop.left) at x
  have h₁ := local_module_restrict_app F G j A.unop.hom (localModuleRestrict F G i φ) x
  have h₂ := local_module_restrict_app F G i (A.unop.hom ≫ j) φ x
  have h₃ := local_module_restrict_app F G (j ≫ i) A.unop.hom φ x
  change (localModuleRestrict F G j (localModuleRestrict F G i φ)).val.app A x = _ at h₁
  change (localModuleRestrict F G i φ).val.app (op (Over.mk (A.unop.hom ≫ j))) x =
    φ.val.app (op (Over.mk (A.unop.hom ≫ (j ≫ i)))) x at h₂
  change (localModuleRestrict F G (j ≫ i) φ).val.app A x = _ at h₃
  exact h₁.trans (h₂.trans h₃.symm)

private lemma local_module_restrict_zero (F G : SheafOfModules.{u} (ringCatSheafOf R))
    {U V : Opens X} (i : V ⟶ U) : localModuleRestrict F G i 0 = 0 := by
  apply SheafOfModules.hom_ext
  ext A x
  change F.val.obj (op A.unop.left) at x
  have h := local_module_restrict_app F G i A.unop.hom 0 x
  change (localModuleRestrict F G i 0).val.app A x = 0 at h
  exact h

private lemma local_module_restrict_add (F G : SheafOfModules.{u} (ringCatSheafOf R))
    {U V : Opens X} (i : V ⟶ U) (φ ψ : localModuleHom F G U) :
    localModuleRestrict F G i (φ + ψ) =
      localModuleRestrict F G i φ + localModuleRestrict F G i ψ := by
  apply SheafOfModules.hom_ext
  ext A x
  change F.val.obj (op A.unop.left) at x
  have h := local_module_restrict_app F G i A.unop.hom (φ + ψ) x
  have hφ := local_module_restrict_app F G i A.unop.hom φ x
  have hψ := local_module_restrict_app F G i A.unop.hom ψ x
  change (localModuleRestrict F G i (φ + ψ)).val.app A x =
    φ.val.app (op (Over.mk (A.unop.hom ≫ i))) x +
      ψ.val.app (op (Over.mk (A.unop.hom ≫ i))) x at h
  change (localModuleRestrict F G i φ).val.app A x = _ at hφ
  change (localModuleRestrict F G i ψ).val.app A x = _ at hψ
  exact h.trans (congrArg₂ (fun a b : G.val.obj (op A.unop.left) ↦ a + b) hφ.symm hψ.symm)

private noncomputable def moduleHomPresheafAb (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (localModuleHom F G U.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := localModuleRestrict F G f.unop
      map_zero' := local_module_restrict_zero F G f.unop
      map_add' := local_module_restrict_add F G f.unop }
  map_id U := by
    ext φ : 2
    exact local_module_restrict_id F G U.unop φ
  map_comp f g := by
    ext φ : 2
    exact (local_module_restrict_comp F G f.unop g.unop φ).symm

private lemma local_module_restrict_smul (F G : SheafOfModules.{u} (ringCatSheafOf R))
    {U V : Opens X} (i : V ⟶ U) (r : R.obj.obj (op U)) (φ : localModuleHom F G U) :
    letI := localModuleHomModule F G U
    letI := localModuleHomModule F G V
    localModuleRestrict F G i (r • φ) =
      R.obj.map i.op r • localModuleRestrict F G i φ := by
  let := localModuleHomModule F G U
  let := localModuleHomModule F G V
  apply SheafOfModules.hom_ext
  ext A x
  change F.val.obj (op A.unop.left) at x
  have h₁ := local_module_restrict_app F G i A.unop.hom (r • φ) x
  have h₂ := local_module_smul_app F G U r φ (op (Over.mk (A.unop.hom ≫ i))) x
  have h₃ := local_module_smul_app F G V (R.obj.map i.op r)
    (localModuleRestrict F G i φ) A x
  have hφ := local_module_restrict_app F G i A.unop.hom φ x
  change (localModuleRestrict F G i (r • φ)).val.app A x = _ at h₁
  change (localModuleRestrict F G i φ).val.app A x = _ at hφ
  have hr : R.obj.map (A.unop.hom ≫ i).op r =
      R.obj.map A.unop.hom.op (R.obj.map i.op r) := by
    rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]
  exact h₁.trans (h₂.trans ((congrArg₂
    (fun a : R.obj.obj (op A.unop.left) ↦ fun y : G.val.obj (op A.unop.left) ↦ a • y)
    hr hφ.symm).trans h₃.symm))

private noncomputable def moduleHomPresheaf (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    PresheafOfModules.{u} (ringCatSheafOf R).obj := by
  letI (U : (Opens X)ᵒᵖ) : Module ((ringCatSheafOf R).obj.obj U)
      ((moduleHomPresheafAb F G).obj U) := localModuleHomModule F G U.unop
  refine PresheafOfModules.ofPresheaf (R := (ringCatSheafOf R).obj)
    (moduleHomPresheafAb F G) ?_
  intro U V i r φ
  exact local_module_restrict_smul F G i.unop r φ

private noncomputable abbrev moduleHomAmbient (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf (ringCatSheafOf R)).obj F)
    ((SheafOfModules.toSheaf (ringCatSheafOf R)).obj G)

private noncomputable def localModuleForget (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (φ : localModuleHom F G U) : (moduleHomAmbient F G).obj.obj (op U) :=
  ⟨(PresheafOfModules.toPresheaf ((ringCatSheafOf R).over U).obj).map φ.val⟩

private noncomputable def moduleHomForget (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    moduleHomPresheafAb F G ⟶ (moduleHomAmbient F G).obj where
  app U := AddCommGrpCat.ofHom
    { toFun := localModuleForget F G U.unop
      map_zero' := by ext A x; rfl
      map_add' := by intro φ ψ; ext A x; rfl }
  naturality U V i := by
    ext φ : 2
    apply CategoryTheory.Sheaf.hom_ext
    ext A x
    change F.val.obj (op A.unop.left) at x
    have h := local_module_restrict_app F G i.unop A.unop.hom φ x
    change (localModuleRestrict F G i.unop φ).val.app A x =
      φ.val.app (op (Over.mk (A.unop.hom ≫ i.unop))) x
    exact h

private lemma module_hom_forget_injective (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) : Function.Injective ((moduleHomForget F G).app (op U)) := by
  intro φ ψ h
  change localModuleForget F G U φ = localModuleForget F G U ψ at h
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf ((ringCatSheafOf R).over U).obj).map_injective
  exact congrArg (fun f ↦ f.hom) h

private def moduleHomLinear (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X)
    (α : (moduleHomAmbient F G).obj.obj (op U)) : Prop :=
  ∀ (A : (Over U)ᵒᵖ) (r : R.obj.obj (op A.unop.left)) (x : F.val.obj (op A.unop.left)),
    α.hom.app A (r • x) =
      (let y : G.val.obj (op A.unop.left) := α.hom.app A x; r • y)

private lemma module_hom_linear_of_module (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (φ : localModuleHom F G U) :
    moduleHomLinear F G U (localModuleForget F G U φ) := by
  intro A r x
  exact (φ.val.app A).hom.map_smul r x

private noncomputable def moduleHomOfLinear (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (α : (moduleHomAmbient F G).obj.obj (op U))
    (hα : moduleHomLinear F G U α) : localModuleHom F G U := by
  refine ⟨PresheafOfModules.homMk α.hom ?_⟩
  intro A r x
  exact hα A r x

private lemma local_module_forget_of_linear (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (α : (moduleHomAmbient F G).obj.obj (op U))
    (hα : moduleHomLinear F G U α) :
    localModuleForget F G U (moduleHomOfLinear F G U α hα) = α := by
  apply CategoryTheory.Sheaf.hom_ext
  ext A x
  rfl

private lemma module_hom_linear_iff (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X)
    (α : (moduleHomAmbient F G).obj.obj (op U)) :
    moduleHomLinear F G U α ↔
      ∃ φ : localModuleHom F G U, localModuleForget F G U φ = α := by
  constructor
  · intro hα
    exact ⟨moduleHomOfLinear F G U α hα, local_module_forget_of_linear F G U α hα⟩
  · rintro ⟨φ, rfl⟩
    exact module_hom_linear_of_module F G U φ

private noncomputable def moduleHomImage (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    Subfunctor ((moduleHomAmbient F G).obj ⋙ forget AddCommGrpCat) :=
  Subfunctor.range (Functor.whiskerRight (moduleHomForget F G) (forget AddCommGrpCat))

private lemma module_hom_image_iff (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X)
    (α : (moduleHomAmbient F G).obj.obj (op U)) :
    α ∈ (moduleHomImage F G).obj (op U) ↔ moduleHomLinear F G U α := by
  change (∃ φ : localModuleHom F G U, localModuleForget F G U φ = α) ↔ _
  exact (module_hom_linear_iff F G U α).symm

private lemma module_target_type_is_sheaf (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (G.val.presheaf ⋙ forget AddCommGrpCat) := by
  exact (isSheaf_iff_isSheaf_of_type (Opens.grothendieckTopology X) _).mp
    ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) G.val.presheaf).mp
      G.isSheaf)

private lemma ambient_hom_naturality (F G : SheafOfModules.{u} (ringCatSheafOf R))
    {U W : Opens X} (α : (moduleHomAmbient F G).obj.obj (op U)) (A : (Over U)ᵒᵖ)
    (j : W ⟶ A.unop.left) (x : F.val.obj (op A.unop.left)) :
    α.hom.app (op (Over.mk (j ≫ A.unop.hom))) (F.val.map j.op x) =
      G.val.map j.op (α.hom.app A x) := by
  let a : Over.mk (j ≫ A.unop.hom) ⟶ A.unop := Over.homMk j
  have h := ConcreteCategory.congr_hom (α.hom.naturality a.op) x
  change α.hom.app (op (Over.mk (j ≫ A.unop.hom))) (F.val.map j.op x) =
    G.val.map j.op (α.hom.app A x) at h
  exact h

private lemma ambient_hom_smul_eq_after_restrict (F G : SheafOfModules.{u} (ringCatSheafOf R))
    {U W : Opens X} (α : (moduleHomAmbient F G).obj.obj (op U)) (A : (Over U)ᵒᵖ)
    (j : W ⟶ A.unop.left)
    (hα : moduleHomLinear F G W
      ((moduleHomAmbient F G).obj.map (j ≫ A.unop.hom).op α))
    (r : R.obj.obj (op A.unop.left)) (x : F.val.obj (op A.unop.left)) :
    G.val.map j.op (α.hom.app A (r • x)) =
      (let y : G.val.obj (op A.unop.left) := α.hom.app A x;
        G.val.map j.op (r • y)) := by
  have h := hα (op (Over.mk (𝟙 W))) (R.obj.map j.op r) (F.val.map j.op x)
  change α.hom.app (op (Over.mk (j ≫ A.unop.hom)))
      (R.obj.map j.op r • F.val.map j.op x) =
    (let y : G.val.obj (op W) := α.hom.app (op (Over.mk (j ≫ A.unop.hom)))
      (F.val.map j.op x); R.obj.map j.op r • y) at h
  have h₁ := ambient_hom_naturality F G α A j (r • x)
  have h₂ := ambient_hom_naturality F G α A j x
  let y : G.val.obj (op A.unop.left) := α.hom.app A x
  have h₃ := G.val.map_smul j.op r y
  have h₄ := F.val.map_smul j.op r x
  exact h₁.symm.trans ((congrArg
    (fun z : F.val.obj (op W) ↦ α.hom.app (op (Over.mk (j ≫ A.unop.hom))) z)
    h₄).trans (h.trans ((congrArg
      (fun z : G.val.obj (op W) ↦ R.obj.map j.op r • z) h₂).trans h₃.symm)))

private lemma module_hom_linear_of_local (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) (α : (moduleHomAmbient F G).obj.obj (op U)) (S : Sieve U)
    (hS : S ∈ Opens.grothendieckTopology X U)
    (hα : ∀ (V : Opens X) (i : V ⟶ U), S i →
      moduleHomLinear F G V ((moduleHomAmbient F G).obj.map i.op α)) :
    moduleHomLinear F G U α := by
  intro A r x
  apply ((module_target_type_is_sheaf G) (S.pullback A.unop.hom)
    ((Opens.grothendieckTopology X).pullback_stable A.unop.hom hS)).isSeparatedFor.ext
  intro W j hj
  exact ambient_hom_smul_eq_after_restrict F G α A j
    (hα W (j ≫ A.unop.hom) hj) r x

private lemma module_hom_image_is_sheaf (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (moduleHomImage F G).toFunctor := by
  have hA := (isSheaf_iff_isSheaf_of_type (Opens.grothendieckTopology X) _).mp
    ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)
      (moduleHomAmbient F G).obj).mp (moduleHomAmbient F G).property)
  apply ((moduleHomImage F G).isSheaf_iff hA).mpr
  intro U α hS
  apply (module_hom_image_iff F G U.unop α).mpr
  apply module_hom_linear_of_local F G U.unop α
    ((moduleHomImage F G).sieveOfSection α) hS
  intro V i hi
  exact (module_hom_image_iff F G V ((moduleHomAmbient F G).obj.map i.op α)).mp hi

private lemma module_hom_forget_type_mono (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    Mono (Functor.whiskerRight (moduleHomForget F G) (forget AddCommGrpCat)) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  exact (mono_iff_injective _).mpr (module_hom_forget_injective F G U.unop)

private noncomputable def moduleHomImageIso (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    moduleHomPresheafAb F G ⋙ forget AddCommGrpCat ≅ (moduleHomImage F G).toFunctor := by
  let p : moduleHomPresheafAb F G ⋙ forget AddCommGrpCat ⟶
      (moduleHomAmbient F G).obj ⋙ forget AddCommGrpCat :=
    Functor.whiskerRight (moduleHomForget F G) (forget AddCommGrpCat)
  have hp : Mono p := module_hom_forget_type_mono F G
  have hi : IsIso (Subfunctor.toRange p) :=
    @Subfunctor.instIsIsoFunctorTypeToRangeOfMono _ _ _ _ p hp
  exact @asIso _ _ _ _ (Subfunctor.toRange p) hi

private lemma module_hom_presheaf_is_sheaf (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    TopCat.Presheaf.IsSheaf (moduleHomPresheaf F G).presheaf := by
  change TopCat.Presheaf.IsSheaf (moduleHomPresheafAb F G)
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)
    (moduleHomPresheafAb F G)).mpr
  apply (isSheaf_iff_isSheaf_of_type (Opens.grothendieckTopology X) _).mpr
  exact Presieve.isSheaf_iso (Opens.grothendieckTopology X)
    (moduleHomImageIso F G).symm (module_hom_image_is_sheaf F G)

/-- **The sheaf Hom of module sheaves on a ringed space.** The sheaf `U ↦ Hom(F|_U, G|_U)` of
local linear morphisms between two module sheaves, restricted by restricting morphisms. Its
module action is pointwise multiplication by restricted structure-sheaf sections. -/
noncomputable def moduleSheafHom (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    SheafOfModules.{u} (ringCatSheafOf R) where
  val := moduleHomPresheaf F G
  isSheaf := module_hom_presheaf_is_sheaf F G

/-- The canonical `𝒪_X(U)`-module structure on the morphisms `F|_U ⟶ G|_U`: a section `r`
acts by postcomposition with multiplication by the restrictions of `r`. -/
noncomputable abbrev moduleSheafHomOverModule (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (U : Opens X) : Module (R.obj.obj (op U)) (F.over U ⟶ G.over U) :=
  localModuleHomModule F G U

/-- Sections of the module sheaf Hom over `U` are the morphisms `F|_U ⟶ G|_U` of the
restricted module sheaves. -/
noncomputable def moduleSheafHomOverSectionsAddEquiv
    (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X) :
    (moduleSheafHom F G).val.obj (op U) ≃+ (F.over U ⟶ G.over U) :=
  AddEquiv.refl _

/-- The identification of sections over `U` with the morphisms `F|_U ⟶ G|_U` is
`𝒪_X(U)`-linear for the pointwise action. -/
noncomputable def moduleSheafHomOverSectionsLinearEquiv
    (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X) :
    letI := moduleSheafHomOverModule F G U
    (moduleSheafHom F G).val.obj (op U) ≃ₗ[R.obj.obj (op U)] (F.over U ⟶ G.over U) := by
  letI := moduleSheafHomOverModule F G U
  exact { toAddEquiv := moduleSheafHomOverSectionsAddEquiv F G U
          map_smul' := fun _ _ ↦ rfl }

/-- The scalar action on the morphisms `F|_U ⟶ G|_U` is pointwise multiplication by the
restricted section. -/
lemma moduleSheafHomOver_smul_app (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X)
    (r : R.obj.obj (op U)) (φ : F.over U ⟶ G.over U) (V : (Over U)ᵒᵖ)
    (x : F.val.obj (op V.unop.left)) :
    (letI := moduleSheafHomOverModule F G U; (r • φ).val.app V x) =
      (let y : G.val.obj (op V.unop.left) := φ.val.app V x
       R.obj.map V.unop.hom.op r • y) :=
  local_module_smul_app F G U r φ V x

/-- Sections over `U` are also the morphisms of the corresponding module sheaves on the subspace
`U`, through Mathlib's equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver`. -/
noncomputable def moduleSheafHomSubspaceSectionsAddEquiv
    (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X) :
    (moduleSheafHom F G).val.obj (op U) ≃+
      ((U.sheafOfModulesEquivOver (ringCatSheafOf R)).functor.obj (F.over U) ⟶
        (U.sheafOfModulesEquivOver (ringCatSheafOf R)).functor.obj (G.over U)) := by
  let e := U.sheafOfModulesEquivOver (ringCatSheafOf R)
  letI : e.functor.IsLeftAdjoint := e.isLeftAdjoint_functor
  letI : e.functor.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  refine
    { toEquiv := e.fullyFaithfulFunctor.homEquiv
      map_add' := ?_ }
  intro φ ψ
  exact e.functor.map_add

private noncomputable def localModuleGlobalize (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (φ : localModuleHom F G ⊤) : F ⟶ G where
  val :=
    { app V := φ.val.app (op (Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top))))
      naturality {V W} f := by
        let a : Over.mk (homOfLE (show W.unop ≤ ⊤ from le_top)) ⟶
            Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) := Over.homMk f.unop
        have h := φ.val.naturality a.op
        exact h }

private lemma local_module_globalize_over (F G : SheafOfModules.{u} (ringCatSheafOf R))
    (φ : localModuleHom F G ⊤) : (localModuleGlobalize F G φ).over ⊤ = φ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  change F.val.obj (op A.unop.left) at x
  let B := Over.mk (homOfLE (show A.unop.left ≤ ⊤ from le_top))
  let a : A.unop ⟶ B := Over.homMk (𝟙 _)
  have h := CategoryTheory.congr_fun (φ.val.naturality a.op) x
  change (φ.val.app (op B)).hom (F.val.map (𝟙 (op A.unop.left)) x) =
    G.val.map (𝟙 (op A.unop.left)) ((φ.val.app A).hom x) at h
  rw [PresheafOfModules.map_id, PresheafOfModules.map_id] at h
  exact h

/-- Global sections of the module sheaf Hom are canonically the morphisms `F ⟶ G`. -/
noncomputable def moduleSheafHomGlobalSectionsAddEquiv
    (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    (moduleSheafHom F G).val.obj (op ⊤) ≃+ (F ⟶ G) where
  toFun := localModuleGlobalize F G
  invFun φ := φ.over ⊤
  left_inv := local_module_globalize_over F G
  right_inv φ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    rfl
  map_add' φ ψ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    rfl

private noncomputable def localModuleGlobalizeRingHom
    (G : SheafOfModules.{u} (ringCatSheafOf R)) : End (G.over ⊤) →+* End G where
  toFun := localModuleGlobalize G G
  map_zero' := (moduleSheafHomGlobalSectionsAddEquiv G G).map_zero
  map_add' := (moduleSheafHomGlobalSectionsAddEquiv G G).map_add
  map_one' := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    rfl
  map_mul' φ ψ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    rfl

/-- A global structure-sheaf section acts on a module sheaf by pointwise multiplication. -/
noncomputable def moduleSheafHomGlobalScalarRingHom (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    R.obj.obj (op ⊤) →+* End G :=
  (localModuleGlobalizeRingHom G).comp (localModuleScalarRingHom G ⊤)

/-- The canonical global structure-ring action on module-sheaf morphisms, by postcomposition. -/
noncomputable abbrev moduleSheafHomGlobalHomModule (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    Module (R.obj.obj (op ⊤)) (F ⟶ G) :=
  Module.compHom _ (moduleSheafHomGlobalScalarRingHom G)

/-- **Global sections of the sheaf Hom.** The global sections of `ℋom(F, G)` are the morphisms
`F ⟶ G`, linearly for the canonical pointwise action of `𝒪_X(X)`. -/
noncomputable def moduleSheafHomGlobalSectionsLinearEquiv
    (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    letI := moduleSheafHomGlobalHomModule F G
    (moduleSheafHom F G).val.obj (op ⊤) ≃ₗ[R.obj.obj (op ⊤)] (F ⟶ G) := by
  letI := moduleSheafHomGlobalHomModule F G
  refine
    { toAddEquiv := moduleSheafHomGlobalSectionsAddEquiv F G
      map_smul' := ?_ }
  intro r φ
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rfl

/-- The global scalar endomorphism acts by the restricted scalar on every open. -/
lemma moduleSheafHom_global_scalar_app (G : SheafOfModules.{u} (ringCatSheafOf R))
    (r : R.obj.obj (op ⊤)) (V : Opens X) (x : G.val.obj (op V)) :
    (moduleSheafHomGlobalScalarRingHom G r).val.app (op V) x =
      R.obj.map (homOfLE (show V ≤ ⊤ from le_top)).op r • x := by
  exact localModuleScalar_app G ⊤ r
    (op (Over.mk (homOfLE (show V ≤ ⊤ from le_top)))) x

/-- The global identification is natural in both arguments under pre- and postcomposition. -/
lemma moduleSheafHom_global_naturality {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : F' ⟶ F) (g : G ⟶ G') (σ : (moduleSheafHom F G).val.obj (op ⊤)) :
    moduleSheafHomGlobalSectionsAddEquiv F' G'
        (f.over ⊤ ≫ moduleSheafHomOverSectionsAddEquiv F G ⊤ σ ≫ g.over ⊤) =
      f ≫ moduleSheafHomGlobalSectionsAddEquiv F G σ ≫ g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rfl

private lemma local_module_scalar_naturality {F G : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : F ⟶ G) (U : Opens X) (r : R.obj.obj (op U)) :
    localModuleScalar F U r ≫ f.over U = f.over U ≫ localModuleScalar G U r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  change F.val.obj (op A.unop.left) at x
  have h := (f.val.app (op A.unop.left)).hom.map_smul
    (R.obj.map A.unop.hom.op r) x
  exact h

private noncomputable def localModuleHomMap {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : F' ⟶ F) (g : G ⟶ G') (U : Opens X) :
    letI := localModuleHomModule F G U
    letI := localModuleHomModule F' G' U
    localModuleHom F G U →ₗ[R.obj.obj (op U)] localModuleHom F' G' U := by
  letI := localModuleHomModule F G U
  letI := localModuleHomModule F' G' U
  refine
    { toFun := fun φ ↦ f.over U ≫ φ ≫ g.over U
      map_add' := ?_
      map_smul' := ?_ }
  · intro φ ψ
    simp only [Preadditive.add_comp, Preadditive.comp_add]
  · intro r φ
    change f.over U ≫ (φ ≫ localModuleScalar G U r) ≫ g.over U =
      (f.over U ≫ φ ≫ g.over U) ≫ localModuleScalar G' U r
    simp only [Category.assoc]
    rw [local_module_scalar_naturality g U r]

/-- The morphism of module sheaves `ℋom(F, G) ⟶ ℋom(F', G')` induced by precomposition with
`f : F' ⟶ F` and postcomposition with `g : G ⟶ G'`. -/
noncomputable def moduleSheafHomMap {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : F' ⟶ F) (g : G ⟶ G') : moduleSheafHom F G ⟶ moduleSheafHom F' G' := by
  letI (U : (Opens X)ᵒᵖ) : Module ((ringCatSheafOf R).obj.obj U)
      ((moduleHomPresheafAb F G).obj U) :=
    localModuleHomModule F G U.unop
  letI (U : (Opens X)ᵒᵖ) : Module ((ringCatSheafOf R).obj.obj U)
      ((moduleHomPresheafAb F' G').obj U) :=
    localModuleHomModule F' G' U.unop
  exact
    { val :=
      { app U := ModuleCat.ofHom (localModuleHomMap f g U.unop)
        naturality {U V} i := by
          ext φ : 2
          apply SheafOfModules.hom_ext
          apply PresheafOfModules.hom_ext
          intro A
          ext x
          rfl } }

/-- On each open, the map of Hom sheaves is pre- and postcomposition of local morphisms. -/
lemma moduleSheafHom_map_app {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : F' ⟶ F) (g : G ⟶ G') (U : Opens X) (σ : (moduleSheafHom F G).val.obj (op U)) :
    moduleSheafHomOverSectionsAddEquiv F' G' U ((moduleSheafHomMap f g).val.app (op U) σ) =
      f.over U ≫ moduleSheafHomOverSectionsAddEquiv F G U σ ≫ g.over U := rfl

/-- The global linear identification is natural through the map of Hom sheaves. -/
lemma moduleSheafHom_global_map {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : F' ⟶ F) (g : G ⟶ G') (σ : (moduleSheafHom F G).val.obj (op ⊤)) :
    moduleSheafHomGlobalSectionsLinearEquiv F' G' ((moduleSheafHomMap f g).val.app (op ⊤) σ) =
      f ≫ moduleSheafHomGlobalSectionsLinearEquiv F G σ ≫ g :=
  moduleSheafHom_global_naturality f g σ

variable (R) in
/-- The module-sheaf Hom construction on a ringed space, with its identification of sections
over `U` with the morphisms `F|_U ⟶ G|_U` (also on the subspace `U`), the morphisms induced by
pre- and postcomposition, and the linear identification of global sections with `F ⟶ G`. -/
structure ModuleSheafHomData where
  /-- The module sheaf `ℋom(F, G)`. -/
  obj (F G : SheafOfModules.{u} (ringCatSheafOf R)) : SheafOfModules.{u} (ringCatSheafOf R)
  /-- Sections over `U` identify additively with the morphisms `F|_U ⟶ G|_U`. -/
  overSections (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X) :
    (obj F G).val.obj (op U) ≃+ (F.over U ⟶ G.over U)
  /-- The same sections as morphisms of the module sheaves on the subspace `U`. -/
  subspaceSections (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X) :
    (obj F G).val.obj (op U) ≃+
      ((U.sheafOfModulesEquivOver (ringCatSheafOf R)).functor.obj (F.over U) ⟶
        (U.sheafOfModulesEquivOver (ringCatSheafOf R)).functor.obj (G.over U))
  /-- Pre- and postcomposition are morphisms of module sheaves. -/
  map {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F) (g : G ⟶ G') :
    obj F G ⟶ obj F' G'
  /-- Global sections identify linearly with morphisms for the pointwise action. -/
  globalSections (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    letI := moduleSheafHomGlobalHomModule F G
    (obj F G).val.obj (op ⊤) ≃ₗ[R.obj.obj (op ⊤)] (F ⟶ G)
  /-- The subspace identification is the over-site one followed by the equivalence. -/
  subspaceSections_eq (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X)
      (σ : (obj F G).val.obj (op U)) :
    subspaceSections F G U σ =
      (U.sheafOfModulesEquivOver (ringCatSheafOf R)).functor.map (overSections F G U σ)
  /-- Scalar multiplication of sections is pointwise multiplication by restricted sections. -/
  smul_app (F G : SheafOfModules.{u} (ringCatSheafOf R)) (U : Opens X) (r : R.obj.obj (op U))
      (σ : (obj F G).val.obj (op U)) (V : (Over U)ᵒᵖ) (x : F.val.obj (op V.unop.left)) :
    (overSections F G U (r • σ)).val.app V x =
      (let y : G.val.obj (op V.unop.left) := (overSections F G U σ).val.app V x
       R.obj.map V.unop.hom.op r • y)
  /-- Restriction of sections is the restriction of morphisms. -/
  over_restriction (F G : SheafOfModules.{u} (ringCatSheafOf R)) {U V : Opens X} (i : V ⟶ U)
      (σ : (obj F G).val.obj (op U)) :
    overSections F G V ((obj F G).val.map i.op σ) =
      (SheafOfModules.overFunctorMap (ringCatSheafOf R) i).inv.app F ≫
        (SheafOfModules.overMap (ringCatSheafOf R) i).map (overSections F G U σ) ≫
        (SheafOfModules.overFunctorMap (ringCatSheafOf R) i).hom.app G
  /-- The induced map is pre- and postcomposition on every open. -/
  map_app {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F) (g : G ⟶ G')
      (U : Opens X) (σ : (obj F G).val.obj (op U)) :
    overSections F' G' U ((map f g).val.app (op U) σ) =
      f.over U ≫ overSections F G U σ ≫ g.over U
  /-- The global action is pointwise multiplication by restricted global sections. -/
  global_scalar_app (G : SheafOfModules.{u} (ringCatSheafOf R)) (r : R.obj.obj (op ⊤))
      (V : Opens X) (x : G.val.obj (op V)) :
    (moduleSheafHomGlobalScalarRingHom G r).val.app (op V) x =
      R.obj.map (homOfLE (show V ≤ ⊤ from le_top)).op r • x
  /-- The global identification is the same local morphism on every open. -/
  global_app (F G : SheafOfModules.{u} (ringCatSheafOf R)) (σ : (obj F G).val.obj (op ⊤))
      (V : Opens X) (x : F.val.obj (op V)) :
    (globalSections F G σ).val.app (op V) x =
      (overSections F G ⊤ σ).val.app (op (Over.mk (homOfLE (show V ≤ ⊤ from le_top)))) x
  /-- Global identifications are natural through the induced maps. -/
  global_map {F F' G G' : SheafOfModules.{u} (ringCatSheafOf R)} (f : F' ⟶ F) (g : G ⟶ G')
      (σ : (obj F G).val.obj (op ⊤)) :
    globalSections F' G' ((map f g).val.app (op ⊤) σ) = f ≫ globalSections F G σ ≫ g

variable (R) in
/-- **The sheaf Hom of module sheaves on a ringed space** (Hartshorne II.5, p. 109): the module
sheaf `ℋom(F, G)` with its local, subspace and global identifications and its functoriality. -/
noncomputable def moduleSheafHomData : ModuleSheafHomData R where
  obj := moduleSheafHom
  overSections := moduleSheafHomOverSectionsAddEquiv
  subspaceSections := moduleSheafHomSubspaceSectionsAddEquiv
  map := moduleSheafHomMap
  globalSections := moduleSheafHomGlobalSectionsLinearEquiv
  subspaceSections_eq := by intros; rfl
  smul_app := moduleSheafHomOver_smul_app
  over_restriction := by intros; rfl
  map_app := moduleSheafHom_map_app
  global_scalar_app := moduleSheafHom_global_scalar_app
  global_app := by intros; rfl
  global_map := moduleSheafHom_global_map

end Ringed

end Hartshorne
