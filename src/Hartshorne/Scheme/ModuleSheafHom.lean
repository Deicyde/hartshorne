/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AbelianSheafHom
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # The sheaf of local module morphisms -/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

variable {X : Scheme.{u}}

private abbrev localModuleHom (F G : X.Modules) (U : X.Opens) : Type u :=
  SheafOfModules.over F U ⟶ SheafOfModules.over G U

private noncomputable def localModuleScalar (G : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) : End (SheafOfModules.over G U) := by
  letI (V : (Over U)ᵒᵖ) : Module ((X.ringCatSheaf.over U).obj.obj V)
      ((SheafOfModules.over G U).val.obj V) :=
    ((SheafOfModules.over G U).val.obj V).isModule
  letI (V : (Over U)ᵒᵖ) : Module Γ(X, V.unop.left) ((SheafOfModules.over G U).val.obj V) :=
    ((SheafOfModules.over G U).val.obj V).isModule
  exact
    { val :=
      { app V := by
          letI : Module ((X.ringCatSheaf.over U).obj.obj V)
              ((SheafOfModules.over G U).val.obj V) :=
            ((SheafOfModules.over G U).val.obj V).isModule
          letI : CommRing ((X.ringCatSheaf.over U).obj.obj V) :=
            inferInstanceAs (CommRing Γ(X, V.unop.left))
          exact ModuleCat.ofHom (X := (SheafOfModules.over G U).val.obj V)
            (Y := (SheafOfModules.over G U).val.obj V) <|
            LinearMap.lsmul ((X.ringCatSheaf.over U).obj.obj V)
              ((SheafOfModules.over G U).val.obj V) (X.presheaf.map V.unop.hom.op r)
        naturality := by
          intro V W f
          ext x
          change (X.presheaf.map W.unop.hom.op r) • G.presheaf.map f.unop.left.op x =
            G.presheaf.map f.unop.left.op ((X.presheaf.map V.unop.hom.op r) • x)
          have h := G.map_smul f.unop.left (X.presheaf.map V.unop.hom.op r) x
          have hr : X.presheaf.map W.unop.hom.op r =
              X.presheaf.map f.unop.left.op (X.presheaf.map V.unop.hom.op r) := by
            rw [← X.presheaf.map_comp_apply, ← op_comp, f.unop.w]
          exact (congrArg (fun a : Γ(X, W.unop.left) ↦
            a • (G.presheaf.map f.unop.left.op x : Γ(G, W.unop.left))) hr).trans h.symm } }

private lemma localModuleScalar_app (G : X.Modules) (U : X.Opens) (r : Γ(X, U))
    (V : (Over U)ᵒᵖ) (x : Γ(G, V.unop.left)) :
    (localModuleScalar G U r).val.app V x = X.presheaf.map V.unop.hom.op r • x :=
  rfl

private noncomputable def localModuleScalarRingHom (G : X.Modules) (U : X.Opens) :
    Γ(X, U) →+* End (SheafOfModules.over G U) where
  toFun := localModuleScalar G U
  map_zero' := by
    apply SheafOfModules.hom_ext
    ext V x
    change Γ(G, V.unop.left) at x
    change X.presheaf.map V.unop.hom.op (0 : Γ(X, U)) • x = 0
    simp
  map_one' := by
    apply SheafOfModules.hom_ext
    ext V x
    change Γ(G, V.unop.left) at x
    change X.presheaf.map V.unop.hom.op (1 : Γ(X, U)) • x = x
    simp
  map_add' r s := by
    apply SheafOfModules.hom_ext
    ext V x
    change Γ(G, V.unop.left) at x
    change X.presheaf.map V.unop.hom.op (r + s) • x =
      X.presheaf.map V.unop.hom.op r • x + X.presheaf.map V.unop.hom.op s • x
    simp [add_smul]
  map_mul' r s := by
    apply SheafOfModules.hom_ext
    ext V x
    change Γ(G, V.unop.left) at x
    change X.presheaf.map V.unop.hom.op (r * s) • x =
      X.presheaf.map V.unop.hom.op r • (X.presheaf.map V.unop.hom.op s • x)
    simp [mul_smul]

private noncomputable abbrev localModuleHomModule (F G : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (localModuleHom F G U) :=
  Module.compHom _ (localModuleScalarRingHom G U)

private lemma local_module_smul_app (F G : X.Modules) (U : X.Opens) (r : Γ(X, U))
    (φ : localModuleHom F G U) (V : (Over U)ᵒᵖ) (x : Γ(F, V.unop.left)) :
    (letI := localModuleHomModule F G U; (r • φ).val.app V x) =
      (let y : Γ(G, V.unop.left) := φ.val.app V x
       X.presheaf.map V.unop.hom.op r • y) := by
  change (localModuleScalar G U r).val.app V (φ.val.app V x) = _
  exact localModuleScalar_app G U r V _

private noncomputable def localModuleRestrict (F G : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (φ : localModuleHom F G U) : localModuleHom F G V :=
  (SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app F ≫
    (SheafOfModules.overMap X.ringCatSheaf i).map φ ≫
    (SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app G

private lemma local_module_restrict_app (F G : X.Modules) {U V W : X.Opens}
    (i : V ⟶ U) (j : W ⟶ V) (φ : localModuleHom F G U) (x : Γ(F, W)) :
    (localModuleRestrict F G i φ).val.app (op (Over.mk j)) x =
      φ.val.app (op (Over.mk (j ≫ i))) x :=
  rfl

private lemma local_module_restrict_id (F G : X.Modules) (U : X.Opens)
    (φ : localModuleHom F G U) : localModuleRestrict F G (𝟙 U) φ = φ := by
  apply SheafOfModules.hom_ext
  ext A x
  change Γ(F, A.unop.left) at x
  have h := local_module_restrict_app F G (𝟙 U) A.unop.hom φ x
  change (localModuleRestrict F G (𝟙 U) φ).val.app A x = φ.val.app A x at h
  exact h

private lemma local_module_restrict_comp (F G : X.Modules) {U V W : X.Opens}
    (i : V ⟶ U) (j : W ⟶ V) (φ : localModuleHom F G U) :
    localModuleRestrict F G j (localModuleRestrict F G i φ) =
      localModuleRestrict F G (j ≫ i) φ := by
  apply SheafOfModules.hom_ext
  ext A x
  change Γ(F, A.unop.left) at x
  have h₁ := local_module_restrict_app F G j A.unop.hom (localModuleRestrict F G i φ) x
  have h₂ := local_module_restrict_app F G i (A.unop.hom ≫ j) φ x
  have h₃ := local_module_restrict_app F G (j ≫ i) A.unop.hom φ x
  change (localModuleRestrict F G j (localModuleRestrict F G i φ)).val.app A x = _ at h₁
  change (localModuleRestrict F G i φ).val.app (op (Over.mk (A.unop.hom ≫ j))) x =
    φ.val.app (op (Over.mk (A.unop.hom ≫ (j ≫ i)))) x at h₂
  change (localModuleRestrict F G (j ≫ i) φ).val.app A x = _ at h₃
  exact h₁.trans (h₂.trans h₃.symm)

private lemma local_module_restrict_zero (F G : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) : localModuleRestrict F G i 0 = 0 := by
  apply SheafOfModules.hom_ext
  ext A x
  change Γ(F, A.unop.left) at x
  have h := local_module_restrict_app F G i A.unop.hom 0 x
  change (localModuleRestrict F G i 0).val.app A x = 0 at h
  exact h

private lemma local_module_restrict_add (F G : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (φ ψ : localModuleHom F G U) :
    localModuleRestrict F G i (φ + ψ) =
      localModuleRestrict F G i φ + localModuleRestrict F G i ψ := by
  apply SheafOfModules.hom_ext
  ext A x
  change Γ(F, A.unop.left) at x
  have h := local_module_restrict_app F G i A.unop.hom (φ + ψ) x
  have hφ := local_module_restrict_app F G i A.unop.hom φ x
  have hψ := local_module_restrict_app F G i A.unop.hom ψ x
  change (localModuleRestrict F G i (φ + ψ)).val.app A x =
    φ.val.app (op (Over.mk (A.unop.hom ≫ i))) x +
      ψ.val.app (op (Over.mk (A.unop.hom ≫ i))) x at h
  change (localModuleRestrict F G i φ).val.app A x = _ at hφ
  change (localModuleRestrict F G i ψ).val.app A x = _ at hψ
  exact h.trans (congrArg₂ (fun a b : Γ(G, A.unop.left) ↦ a + b) hφ.symm hψ.symm)

private noncomputable def moduleHomPresheafAb (F G : X.Modules) :
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

private lemma local_module_restrict_smul (F G : X.Modules) {U V : X.Opens}
    (i : V ⟶ U) (r : Γ(X, U)) (φ : localModuleHom F G U) :
    letI := localModuleHomModule F G U
    letI := localModuleHomModule F G V
    localModuleRestrict F G i (r • φ) =
      X.presheaf.map i.op r • localModuleRestrict F G i φ := by
  let := localModuleHomModule F G U
  let := localModuleHomModule F G V
  apply SheafOfModules.hom_ext
  ext A x
  change Γ(F, A.unop.left) at x
  have h₁ := local_module_restrict_app F G i A.unop.hom (r • φ) x
  have h₂ := local_module_smul_app F G U r φ (op (Over.mk (A.unop.hom ≫ i))) x
  have h₃ := local_module_smul_app F G V (X.presheaf.map i.op r)
    (localModuleRestrict F G i φ) A x
  have hφ := local_module_restrict_app F G i A.unop.hom φ x
  change (localModuleRestrict F G i (r • φ)).val.app A x = _ at h₁
  change (localModuleRestrict F G i φ).val.app A x = _ at hφ
  have hr : X.presheaf.map (A.unop.hom ≫ i).op r =
      X.presheaf.map A.unop.hom.op (X.presheaf.map i.op r) := by
    rw [op_comp, X.presheaf.map_comp_apply]
  exact h₁.trans (h₂.trans ((congrArg₂
    (fun a : Γ(X, A.unop.left) ↦ fun y : Γ(G, A.unop.left) ↦ a • y)
    hr hφ.symm).trans h₃.symm))

private noncomputable def moduleHomPresheaf (F G : X.Modules) : X.PresheafOfModules := by
  letI (U : (X.Opens)ᵒᵖ) : Module (X.ringCatSheaf.obj.obj U)
      ((moduleHomPresheafAb F G).obj U) := localModuleHomModule F G U.unop
  refine PresheafOfModules.ofPresheaf (R := X.ringCatSheaf.obj)
    (moduleHomPresheafAb F G) ?_
  intro U V i r φ
  exact local_module_restrict_smul F G i.unop r φ

private noncomputable def localModuleForget (F G : X.Modules) (U : X.Opens)
    (φ : localModuleHom F G U) :
    (TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)).obj.obj (op U) :=
  ⟨(PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map φ.val⟩

private noncomputable def moduleHomForget (F G : X.Modules) :
    moduleHomPresheafAb F G ⟶
      (TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)).obj where
  app U := AddCommGrpCat.ofHom
    { toFun := localModuleForget F G U.unop
      map_zero' := by ext A x; rfl
      map_add' := by intro φ ψ; ext A x; rfl }
  naturality U V i := by
    ext φ : 2
    apply CategoryTheory.Sheaf.hom_ext
    ext A x
    change Γ(F, A.unop.left) at x
    have h := local_module_restrict_app F G i.unop A.unop.hom φ x
    change (localModuleRestrict F G i.unop φ).val.app A x =
      φ.val.app (op (Over.mk (A.unop.hom ≫ i.unop))) x
    exact h

private lemma module_hom_forget_injective (F G : X.Modules) (U : X.Opens) :
    Function.Injective ((moduleHomForget F G).app (op U)) := by
  intro φ ψ h
  change localModuleForget F G U φ = localModuleForget F G U ψ at h
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj).map_injective
  exact congrArg (fun f ↦ f.hom) h

private def moduleHomLinear (F G : X.Modules) (U : X.Opens)
    (α : (TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)).obj.obj (op U)) : Prop :=
  ∀ (A : (Over U)ᵒᵖ) (r : Γ(X, A.unop.left)) (x : Γ(F, A.unop.left)),
    α.hom.app A (r • x) =
      (let y : Γ(G, A.unop.left) := α.hom.app A x; r • y)

private lemma module_hom_linear_of_module (F G : X.Modules) (U : X.Opens)
    (φ : localModuleHom F G U) : moduleHomLinear F G U (localModuleForget F G U φ) := by
  intro A r x
  exact (φ.val.app A).hom.map_smul r x

private noncomputable def moduleHomOfLinear (F G : X.Modules) (U : X.Opens)
    (α : (TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)).obj.obj (op U))
    (hα : moduleHomLinear F G U α) : localModuleHom F G U := by
  refine ⟨PresheafOfModules.homMk α.hom ?_⟩
  intro A r x
  exact hα A r x

private lemma local_module_forget_of_linear (F G : X.Modules) (U : X.Opens)
    (α : (TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)).obj.obj (op U))
    (hα : moduleHomLinear F G U α) :
    localModuleForget F G U (moduleHomOfLinear F G U α hα) = α := by
  apply CategoryTheory.Sheaf.hom_ext
  ext A x
  rfl

private lemma module_hom_linear_iff (F G : X.Modules) (U : X.Opens)
    (α : (TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)).obj.obj (op U)) :
    moduleHomLinear F G U α ↔
      ∃ φ : localModuleHom F G U, localModuleForget F G U φ = α := by
  constructor
  · intro hα
    exact ⟨moduleHomOfLinear F G U α hα, local_module_forget_of_linear F G U α hα⟩
  · rintro ⟨φ, rfl⟩
    exact module_hom_linear_of_module F G U φ

private noncomputable def moduleHomImage (F G : X.Modules) :
    Subfunctor ((TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)).obj ⋙ forget AddCommGrpCat) :=
  Subfunctor.range (Functor.whiskerRight (moduleHomForget F G) (forget AddCommGrpCat))

private lemma module_hom_image_iff (F G : X.Modules) (U : X.Opens)
    (α : (TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)).obj.obj (op U)) :
    α ∈ (moduleHomImage F G).obj (op U) ↔ moduleHomLinear F G U α := by
  change (∃ φ : localModuleHom F G U, localModuleForget F G U φ = α) ↔ _
  exact (module_hom_linear_iff F G U α).symm

private noncomputable abbrev moduleHomAmbient (F G : X.Modules) :
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  TopCat.Sheaf.abelianSheafHom ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj G)

private lemma ambient_hom_restrict_app (F G : X.Modules) {U V W : X.Opens}
    (i : V ⟶ U) (j : W ⟶ V) (α : (moduleHomAmbient F G).obj.obj (op U))
    (x : Γ(F, W)) :
    (((moduleHomAmbient F G).obj.map i.op α).hom.app (op (Over.mk j))) x =
      α.hom.app (op (Over.mk (j ≫ i))) x :=
  rfl

private lemma module_target_type_is_sheaf (G : X.Modules) :
    Presieve.IsSheaf (Opens.grothendieckTopology X)
      (G.presheaf ⋙ forget AddCommGrpCat) := by
  exact (isSheaf_iff_isSheaf_of_type (Opens.grothendieckTopology X) _).mp
    ((TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) G.presheaf).mp G.isSheaf)

private lemma ambient_hom_naturality (F G : X.Modules) {U W : X.Opens}
    (α : (moduleHomAmbient F G).obj.obj (op U)) (A : (Over U)ᵒᵖ)
    (j : W ⟶ A.unop.left) (x : Γ(F, A.unop.left)) :
    α.hom.app (op (Over.mk (j ≫ A.unop.hom))) (F.presheaf.map j.op x) =
      G.presheaf.map j.op (α.hom.app A x) := by
  let a : Over.mk (j ≫ A.unop.hom) ⟶ A.unop := Over.homMk j
  have h := ConcreteCategory.congr_hom (α.hom.naturality a.op) x
  change α.hom.app (op (Over.mk (j ≫ A.unop.hom))) (F.presheaf.map j.op x) =
    G.presheaf.map j.op (α.hom.app A x) at h
  exact h

private lemma ambient_hom_smul_eq_after_restrict (F G : X.Modules) {U W : X.Opens}
    (α : (moduleHomAmbient F G).obj.obj (op U)) (A : (Over U)ᵒᵖ)
    (j : W ⟶ A.unop.left)
    (hα : moduleHomLinear F G W
      ((moduleHomAmbient F G).obj.map (j ≫ A.unop.hom).op α))
    (r : Γ(X, A.unop.left)) (x : Γ(F, A.unop.left)) :
    G.presheaf.map j.op (α.hom.app A (r • x)) =
      (let y : Γ(G, A.unop.left) := α.hom.app A x; G.presheaf.map j.op (r • y)) := by
  have h := hα (op (Over.mk (𝟙 W))) (X.presheaf.map j.op r) (F.presheaf.map j.op x)
  change α.hom.app (op (Over.mk (j ≫ A.unop.hom)))
      (X.presheaf.map j.op r • F.presheaf.map j.op x) =
    (let y : Γ(G, W) := α.hom.app (op (Over.mk (j ≫ A.unop.hom)))
      (F.presheaf.map j.op x); X.presheaf.map j.op r • y) at h
  have h₁ := ambient_hom_naturality F G α A j (r • x)
  have h₂ := ambient_hom_naturality F G α A j x
  let y : Γ(G, A.unop.left) := α.hom.app A x
  have h₃ := G.map_smul j r y
  exact h₁.symm.trans ((congrArg
    (fun z : Γ(F, W) ↦ α.hom.app (op (Over.mk (j ≫ A.unop.hom))) z)
    (F.map_smul j r x)).trans (h.trans ((congrArg
      (fun z : Γ(G, W) ↦ X.presheaf.map j.op r • z) h₂).trans h₃.symm)))

private lemma module_hom_linear_of_local (F G : X.Modules) (U : X.Opens)
    (α : (moduleHomAmbient F G).obj.obj (op U)) (S : Sieve U)
    (hS : S ∈ Opens.grothendieckTopology X U)
    (hα : ∀ (V : X.Opens) (i : V ⟶ U), S i →
      moduleHomLinear F G V ((moduleHomAmbient F G).obj.map i.op α)) :
    moduleHomLinear F G U α := by
  intro A r x
  apply ((module_target_type_is_sheaf G) (S.pullback A.unop.hom)
    ((Opens.grothendieckTopology X).pullback_stable A.unop.hom hS)).isSeparatedFor.ext
  intro W j hj
  exact ambient_hom_smul_eq_after_restrict F G α A j
    (hα W (j ≫ A.unop.hom) hj) r x

private lemma module_hom_image_is_sheaf (F G : X.Modules) :
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

private lemma module_hom_forget_type_mono (F G : X.Modules) :
    Mono (Functor.whiskerRight (moduleHomForget F G) (forget AddCommGrpCat)) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  exact (mono_iff_injective _).mpr (module_hom_forget_injective F G U.unop)

private noncomputable def moduleHomImageIso (F G : X.Modules) :
    moduleHomPresheafAb F G ⋙ forget AddCommGrpCat ≅ (moduleHomImage F G).toFunctor := by
  let p : moduleHomPresheafAb F G ⋙ forget AddCommGrpCat ⟶
      (moduleHomAmbient F G).obj ⋙ forget AddCommGrpCat :=
    Functor.whiskerRight (moduleHomForget F G) (forget AddCommGrpCat)
  have hp : Mono p := module_hom_forget_type_mono F G
  have hi : IsIso (Subfunctor.toRange p) :=
    @Subfunctor.instIsIsoFunctorTypeToRangeOfMono _ _ _ _ p hp
  exact @asIso _ _ _ _ (Subfunctor.toRange p) hi

private lemma module_hom_presheaf_is_sheaf (F G : X.Modules) :
    TopCat.Presheaf.IsSheaf (moduleHomPresheaf F G).presheaf := by
  change TopCat.Presheaf.IsSheaf (moduleHomPresheafAb F G)
  apply (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)
    (moduleHomPresheafAb F G)).mpr
  apply (isSheaf_iff_isSheaf_of_type (Opens.grothendieckTopology X) _).mpr
  exact Presieve.isSheaf_iso (Opens.grothendieckTopology X)
    (moduleHomImageIso F G).symm (module_hom_image_is_sheaf F G)

/-- The sheaf of local linear morphisms between two module sheaves. Its module action is
pointwise multiplication by restricted structure-sheaf sections. -/
noncomputable def moduleSheafHom (F G : X.Modules) : X.Modules where
  val := moduleHomPresheaf F G
  isSheaf := module_hom_presheaf_is_sheaf F G

/-- Sections of the module sheaf Hom are the local linear maps on the over-site. -/
noncomputable def moduleSheafHomOverSectionsAddEquiv (F G : X.Modules) (U : X.Opens) :
    Γ(moduleSheafHom F G, U) ≃+ localModuleHom F G U :=
  AddEquiv.refl _

/-- The local section identification preserves the canonical structure-ring action. -/
noncomputable def moduleSheafHomOverSectionsLinearEquiv (F G : X.Modules) (U : X.Opens) :
    letI := localModuleHomModule F G U
    Γ(moduleSheafHom F G, U) ≃ₗ[Γ(X, U)] localModuleHom F G U := by
  letI := localModuleHomModule F G U
  exact { toAddEquiv := moduleSheafHomOverSectionsAddEquiv F G U
          map_smul' := fun _ _ ↦ rfl }

/-- On every open subscheme, sections are the actual morphisms of restricted module sheaves. -/
noncomputable def moduleSheafHomSectionsAddEquiv (F G : X.Modules) (U : X.Opens) :
    Γ(moduleSheafHom F G, U) ≃+
      ((Scheme.Modules.restrictFunctor U.ι).obj F ⟶
        (Scheme.Modules.restrictFunctor U.ι).obj G) := by
  let e := Scheme.Modules.overEquiv U
  let a := (Scheme.Modules.overFunctorEquiv U).app F
  let b := (Scheme.Modules.overFunctorEquiv U).app G
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  refine
    { toEquiv := (e.fullyFaithfulFunctor.homEquiv).trans (Iso.homCongr a b)
      map_add' := ?_ }
  intro φ ψ
  change localModuleHom F G U at φ ψ
  change a.inv ≫ e.functor.map (φ + ψ) ≫ b.hom =
    (a.inv ≫ e.functor.map φ ≫ b.hom) + (a.inv ≫ e.functor.map ψ ≫ b.hom)
  rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

private noncomputable def localModuleGlobalize (F G : X.Modules)
    (φ : localModuleHom F G ⊤) : F ⟶ G where
  val :=
    { app V := φ.val.app (op (Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top))))
      naturality {V W} f := by
        let a : Over.mk (homOfLE (show W.unop ≤ ⊤ from le_top)) ⟶
            Over.mk (homOfLE (show V.unop ≤ ⊤ from le_top)) := Over.homMk f.unop
        have h := φ.val.naturality a.op
        ext x
        exact CategoryTheory.congr_fun h x }

private lemma local_module_globalize_over (F G : X.Modules)
    (φ : localModuleHom F G ⊤) : (localModuleGlobalize F G φ).over ⊤ = φ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  change Γ(F, A.unop.left) at x
  let B := Over.mk (homOfLE (show A.unop.left ≤ ⊤ from le_top))
  let a : A.unop ⟶ B := Over.homMk (𝟙 _)
  have h := CategoryTheory.congr_fun (φ.val.naturality a.op) x
  change (φ.val.app (op B)).hom ((F.presheaf.map (𝟙 (op A.unop.left))).hom x) =
    (G.presheaf.map (𝟙 (op A.unop.left))).hom ((φ.val.app A).hom x) at h
  rw [F.presheaf.map_id, G.presheaf.map_id] at h
  exact h

/-- Global sections of the module sheaf Hom are canonically the actual module morphisms. -/
noncomputable def moduleSheafHomGlobalSectionsAddEquiv (F G : X.Modules) :
    Γ(moduleSheafHom F G, ⊤) ≃+ (F ⟶ G) where
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

private noncomputable def localModuleGlobalizeRingHom (G : X.Modules) :
    End (G.over ⊤) →+* End G where
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

/-- A global structure-ring section acts on a module sheaf by pointwise multiplication. -/
noncomputable def moduleSheafHomGlobalScalarRingHom (G : X.Modules) : Γ(X, ⊤) →+* End G :=
  (localModuleGlobalizeRingHom G).comp (localModuleScalarRingHom G ⊤)

/-- The canonical global structure-ring action on module-sheaf morphisms, by postcomposition. -/
noncomputable abbrev moduleSheafHomGlobalHomModule (F G : X.Modules) :
    Module Γ(X, ⊤) (F ⟶ G) :=
  Module.compHom _ (moduleSheafHomGlobalScalarRingHom G)

/-- The global identification is linear for the canonical pointwise structure-ring action. -/
noncomputable def moduleSheafHomGlobalSectionsLinearEquiv (F G : X.Modules) :
    letI := moduleSheafHomGlobalHomModule F G
    Γ(moduleSheafHom F G, ⊤) ≃ₗ[Γ(X, ⊤)] (F ⟶ G) := by
  letI := moduleSheafHomGlobalHomModule F G
  refine
    { toAddEquiv := moduleSheafHomGlobalSectionsAddEquiv F G
      map_smul' := ?_ }
  intro r φ
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rfl

/-- The global scalar endomorphism acts by the restricted scalar on every smaller open. -/
lemma module_sheaf_hom_global_scalar_app (G : X.Modules) (r : Γ(X, ⊤))
    (V : X.Opens) (x : Γ(G, V)) :
    (moduleSheafHomGlobalScalarRingHom G r).val.app (op V) x =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r • x := by
  exact localModuleScalar_app G ⊤ r
    (op (Over.mk (homOfLE (show V ≤ ⊤ from le_top)))) x

/-- The native open-subscheme identification has the same component on every smaller open. -/
lemma module_sheaf_hom_sections_app (F G : X.Modules) (U : X.Opens)
    (σ : Γ(moduleSheafHom F G, U)) (W : U.toScheme.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor U.ι).obj F, W)) :
    (moduleSheafHomSectionsAddEquiv F G U σ).val.app (op W) x =
      (moduleSheafHomOverSectionsAddEquiv F G U σ).val.app
        (op (U.overEquivalence.inverse.obj W)) x := by
  rfl

/-- Under the native open identification, scalars multiply pointwise by their restrictions. -/
lemma module_sheaf_hom_sections_smul_app (F G : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (σ : Γ(moduleSheafHom F G, U)) (W : U.toScheme.Opens)
    (x : Γ((Scheme.Modules.restrictFunctor U.ι).obj F, W)) :
    (moduleSheafHomSectionsAddEquiv F G U (r • σ)).val.app (op W) x =
      (let y : Γ(G, (U.overEquivalence.inverse.obj W).left) :=
        (moduleSheafHomSectionsAddEquiv F G U σ).val.app (op W) x
       X.presheaf.map (U.overEquivalence.inverse.obj W).hom.op r • y) := by
  rw [module_sheaf_hom_sections_app, module_sheaf_hom_sections_app]
  exact local_module_smul_app F G U r σ (op (U.overEquivalence.inverse.obj W)) x

/-- The canonical comparison between nested native restrictions and direct restriction. -/
noncomputable def moduleSheafHomRestrictionIso (F : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj F) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj F := by
  let e := Scheme.Modules.overEquiv V
  let c := Scheme.Modules.overMapCompOverEquiv i
  let d := SheafOfModules.overFunctorMap X.ringCatSheaf i
  exact (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).mapIso
      ((Scheme.Modules.overFunctorEquiv U).app F).symm ≪≫
    (c.app (F.over U)).symm ≪≫ e.functor.mapIso (d.app F) ≪≫
    (Scheme.Modules.overFunctorEquiv V).app F

private lemma hom_congr_natural_comparison
    {C D E H : Type*} [Category* C] [Category* D] [Category* E] [Category* H]
    (K : C ⥤ D) (A : D ⥤ H) (B : C ⥤ E) (R : E ⥤ H) (c : K ⋙ A ≅ B ⋙ R)
    {F₀ G₀ : C} {F₁ G₁ : D} {F₂ G₂ : E} {F₃ G₃ : H}
    (dF : K.obj F₀ ≅ F₁) (dG : K.obj G₀ ≅ G₁)
    (aF : B.obj F₀ ≅ F₂) (aG : B.obj G₀ ≅ G₂)
    (bF : A.obj F₁ ≅ F₃) (bG : A.obj G₁ ≅ G₃) (φ : F₀ ⟶ G₀) :
    bF.inv ≫ A.map (dF.inv ≫ K.map φ ≫ dG.hom) ≫ bG.hom =
      (R.mapIso aF.symm ≪≫ (c.app F₀).symm ≪≫ A.mapIso dF ≪≫ bF).inv ≫
        R.map (aF.inv ≫ B.map φ ≫ aG.hom) ≫
        (R.mapIso aG.symm ≪≫ (c.app G₀).symm ≪≫ A.mapIso dG ≪≫ bG).hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [Iso.map_hom_inv_id_assoc]
  simp only [Iso.app_hom, Iso.app_inv]
  have h := c.hom.naturality φ
  simp only [Functor.comp_map] at h
  rw [← reassoc_of% h]
  simp only [Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Section restriction corresponds to the native restriction of module morphisms. -/
lemma module_sheaf_hom_sections_restrict (F G : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (σ : Γ(moduleSheafHom F G, U)) :
    moduleSheafHomSectionsAddEquiv F G V ((moduleSheafHom F G).presheaf.map i.op σ) =
      (moduleSheafHomRestrictionIso F i).inv ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map
          (moduleSheafHomSectionsAddEquiv F G U σ) ≫
        (moduleSheafHomRestrictionIso G i).hom := by
  exact hom_congr_natural_comparison (SheafOfModules.overMap X.ringCatSheaf i)
    (Scheme.Modules.overEquiv V).functor (Scheme.Modules.overEquiv U).functor
    (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i)))
    (Scheme.Modules.overMapCompOverEquiv i)
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app F)
    ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app G)
    ((Scheme.Modules.overFunctorEquiv U).app F) ((Scheme.Modules.overFunctorEquiv U).app G)
    ((Scheme.Modules.overFunctorEquiv V).app F) ((Scheme.Modules.overFunctorEquiv V).app G) σ

/-- The global identification is natural in both arguments under actual pre- and postcomposition. -/
lemma module_sheaf_hom_global_naturality {F F' G G' : X.Modules} (f : F' ⟶ F) (g : G ⟶ G')
    (σ : Γ(moduleSheafHom F G, ⊤)) :
    moduleSheafHomGlobalSectionsAddEquiv F' G'
        (f.over ⊤ ≫ moduleSheafHomOverSectionsAddEquiv F G ⊤ σ ≫ g.over ⊤) =
      f ≫ moduleSheafHomGlobalSectionsAddEquiv F G σ ≫ g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  rfl

private lemma local_module_scalar_naturality {F G : X.Modules} (f : F ⟶ G)
    (U : X.Opens) (r : Γ(X, U)) :
    localModuleScalar F U r ≫ f.over U = f.over U ≫ localModuleScalar G U r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  change Γ(F, A.unop.left) at x
  have h := (f.val.app (op A.unop.left)).hom.map_smul
    (X.presheaf.map A.unop.hom.op r) x
  exact h

private noncomputable def localModuleHomMap {F F' G G' : X.Modules}
    (f : F' ⟶ F) (g : G ⟶ G') (U : X.Opens) :
    letI := localModuleHomModule F G U
    letI := localModuleHomModule F' G' U
    localModuleHom F G U →ₗ[Γ(X, U)] localModuleHom F' G' U := by
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

/-- The genuine module-sheaf map induced by pre- and postcomposition. -/
noncomputable def moduleSheafHomMap {F F' G G' : X.Modules} (f : F' ⟶ F) (g : G ⟶ G') :
    moduleSheafHom F G ⟶ moduleSheafHom F' G' := by
  letI (U : X.Opensᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) ((moduleHomPresheafAb F G).obj U) :=
    localModuleHomModule F G U.unop
  letI (U : X.Opensᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) ((moduleHomPresheafAb F' G').obj U) :=
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

/-- On each open, the genuine sheaf map is the canonical map on local linear morphisms. -/
lemma module_sheaf_hom_map_app {F F' G G' : X.Modules} (f : F' ⟶ F) (g : G ⟶ G')
    (U : X.Opens) (σ : Γ(moduleSheafHom F G, U)) :
    moduleSheafHomOverSectionsAddEquiv F' G' U ((moduleSheafHomMap f g).val.app (op U) σ) =
      f.over U ≫ moduleSheafHomOverSectionsAddEquiv F G U σ ≫ g.over U := rfl

/-- The global linear identification is natural through the genuine map of Hom module sheaves. -/
lemma module_sheaf_hom_global_map {F F' G G' : X.Modules} (f : F' ⟶ F) (g : G ⟶ G')
    (σ : Γ(moduleSheafHom F G, ⊤)) :
    moduleSheafHomGlobalSectionsLinearEquiv F' G' ((moduleSheafHomMap f g).val.app (op ⊤) σ) =
      f ≫ moduleSheafHomGlobalSectionsLinearEquiv F G σ ≫ g :=
  module_sheaf_hom_global_naturality f g σ

private def moduleSheafHomGlobalApp
    (obj : X.Modules → X.Modules → X.Modules)
    (overSections : ∀ (F G : X.Modules) (U : X.Opens), Γ(obj F G, U) ≃+ (F.over U ⟶ G.over U))
    (globalSections : ∀ (F G : X.Modules),
      letI := moduleSheafHomGlobalHomModule F G
      Γ(obj F G, ⊤) ≃ₗ[Γ(X, ⊤)] (F ⟶ G)) : Prop :=
  ∀ (F G : X.Modules) (σ : Γ(obj F G, ⊤)) (V : X.Opens) (x : Γ(F, V)),
    (globalSections F G σ).val.app (op V) x =
      (overSections F G ⊤ σ).val.app (op (Over.mk (homOfLE (show V ≤ ⊤ from le_top)))) x

private theorem moduleSheafHomGlobalApp_iff
    (obj : X.Modules → X.Modules → X.Modules)
    (overSections : ∀ (F G : X.Modules) (U : X.Opens), Γ(obj F G, U) ≃+ (F.over U ⟶ G.over U))
    (globalSections : ∀ (F G : X.Modules),
      letI := moduleSheafHomGlobalHomModule F G
      Γ(obj F G, ⊤) ≃ₗ[Γ(X, ⊤)] (F ⟶ G)) :
    moduleSheafHomGlobalApp obj overSections globalSections ↔
      ∀ (F G : X.Modules) (σ : Γ(obj F G, ⊤)) (V : X.Opens) (x : Γ(F, V)),
        (globalSections F G σ).val.app (op V) x =
          (overSections F G ⊤ σ).val.app (op (Over.mk (homOfLE (show V ≤ ⊤ from le_top)))) x :=
  Iff.rfl

/-- The compatible module-sheaf Hom construction, local identifications, and global linear data. -/
structure ModuleSheafHomData (X : Scheme.{u}) where
  /-- The genuine family of module sheaves. -/
  obj (F G : X.Modules) : X.Modules
  /-- Sections identify additively with all local linear morphisms on the over-site. -/
  overSections (F G : X.Modules) (U : X.Opens) : Γ(obj F G, U) ≃+ (F.over U ⟶ G.over U)
  /-- The corresponding actual morphisms on each open subscheme. -/
  sections (F G : X.Modules) (U : X.Opens) : Γ(obj F G, U) ≃+
    ((Scheme.Modules.restrictFunctor U.ι).obj F ⟶ (Scheme.Modules.restrictFunctor U.ι).obj G)
  /-- Pre- and postcomposition are genuine morphisms of module sheaves. -/
  map {F F' G G' : X.Modules} (f : F' ⟶ F) (g : G ⟶ G') : obj F G ⟶ obj F' G'
  /-- Global sections identify linearly with actual morphisms for the canonical pointwise action. -/
  globalSections (F G : X.Modules) :
    letI := moduleSheafHomGlobalHomModule F G
    Γ(obj F G, ⊤) ≃ₗ[Γ(X, ⊤)] (F ⟶ G)
  /-- The native open identification agrees on every smaller open with the local morphism. -/
  sections_app (F G : X.Modules) (U : X.Opens) (σ : Γ(obj F G, U))
      (W : U.toScheme.Opens) (x : Γ((Scheme.Modules.restrictFunctor U.ι).obj F, W)) :
    (sections F G U σ).val.app (op W) x =
      (overSections F G U σ).val.app (op (U.overEquivalence.inverse.obj W)) x
  /-- The same native section identification carries scalar multiplication to its pointwise action. -/
  smul_app (F G : X.Modules) (U : X.Opens) (r : Γ(X, U)) (σ : Γ(obj F G, U))
      (W : U.toScheme.Opens) (x : Γ((Scheme.Modules.restrictFunctor U.ι).obj F, W)) :
    (sections F G U (r • σ)).val.app (op W) x =
      (let y : Γ(G, (U.overEquivalence.inverse.obj W).left) :=
        (sections F G U σ).val.app (op W) x
       X.presheaf.map (U.overEquivalence.inverse.obj W).hom.op r • y)
  /-- The same sections restrict by the canonical restriction of over-site morphisms. -/
  over_restriction (F G : X.Modules) {U V : X.Opens} (i : V ⟶ U) (σ : Γ(obj F G, U)) :
    overSections F G V ((obj F G).presheaf.map i.op σ) =
      (SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app F ≫
        (SheafOfModules.overMap X.ringCatSheaf i).map (overSections F G U σ) ≫
        (SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app G
  /-- Under the native open identification, this is the native restriction of morphisms. -/
  restriction (F G : X.Modules) {U V : X.Opens} (i : V ⟶ U) (σ : Γ(obj F G, U)) :
    sections F G V ((obj F G).presheaf.map i.op σ) =
      (moduleSheafHomRestrictionIso F i).inv ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map (sections F G U σ) ≫
        (moduleSheafHomRestrictionIso G i).hom
  /-- The genuine module-sheaf map has canonical pre- and postcomposition components. -/
  map_app {F F' G G' : X.Modules} (f : F' ⟶ F) (g : G ⟶ G')
      (U : X.Opens) (σ : Γ(obj F G, U)) :
    overSections F' G' U ((map f g).val.app (op U) σ) =
      f.over U ≫ overSections F G U σ ≫ g.over U
  /-- The fixed global Hom action is pointwise multiplication by restricted global scalars. -/
  global_scalar_app (G : X.Modules) (r : Γ(X, ⊤)) (V : X.Opens) (x : Γ(G, V)) :
    (moduleSheafHomGlobalScalarRingHom G r).val.app (op V) x =
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op r • x
  /-- The global linear identification is the same local morphism on every open. -/
  global_app : moduleSheafHomGlobalApp obj overSections globalSections
  /-- Global linear identifications are natural through the same genuine sheaf maps. -/
  global_map {F F' G G' : X.Modules} (f : F' ⟶ F) (g : G ⟶ G') (σ : Γ(obj F G, ⊤)) :
    globalSections F' G' ((map f g).val.app (op ⊤) σ) =
      f ≫ globalSections F G σ ≫ g

/-- The source-faithful module-sheaf Hom family with its compatible local and global interfaces. -/
noncomputable def moduleSheafHomData (X : Scheme.{u}) : ModuleSheafHomData X where
  obj := moduleSheafHom
  overSections := moduleSheafHomOverSectionsAddEquiv
  sections := moduleSheafHomSectionsAddEquiv
  map := moduleSheafHomMap
  globalSections := moduleSheafHomGlobalSectionsLinearEquiv
  sections_app := module_sheaf_hom_sections_app
  smul_app := module_sheaf_hom_sections_smul_app
  over_restriction := by
    intros
    rfl
  restriction := module_sheaf_hom_sections_restrict
  map_app := module_sheaf_hom_map_app
  global_scalar_app := module_sheaf_hom_global_scalar_app
  global_app := (moduleSheafHomGlobalApp_iff _ _ _).mpr (by
    intros
    rfl)
  global_map := module_sheaf_hom_global_map

end Hartshorne
