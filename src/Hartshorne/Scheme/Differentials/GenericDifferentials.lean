/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ConstantSheaf
import Hartshorne.Scheme.RelativeDifferentials
import Hartshorne.Scheme.DimensionAtClosedPoint
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Generic values of differentials on an integral scheme

Supporting construction for Hartshorne, *Algebraic Geometry*, III.7, the residue discussion on
p. 248.

Let `X` be an integral scheme over a field `k`, with function field `K`. For a `K`-module `V`,
the constant sheaf with value `V` is an `𝒪_X`-module: a section `r` of `𝒪_X` over `U` acts on a
locally constant map `s : U → V` through its germ at the generic point, `(r • s)(x) = r_η • s(x)`.
The derivation `d : K → Ω_{K/k}`, applied to germs at the generic point, is a relative derivation
of `𝒪_X` with values in this module, so the universal property of `Ω_{X/k}` gives an
`𝒪_X`-linear map from `Ω_{X/k}` to the constant sheaf `Ω_K` with value `Ω_{K/k}`; it sends `d a`
to the constant map with value `d(a_η)`.

Every element of `Ω_{K/k}` is the generic value of a section of `Ω_{X/k}` over some nonempty open
set: the generic values form a `K`-submodule containing `d K`, which spans `Ω_{K/k}`.

## Main definitions

* `Hartshorne.genericConstantModule`: the constant sheaf with value a `K`-module, as `𝒪_X`-module.
* `Hartshorne.functionFieldDifferentials`: the module `Ω_{K/k}`.
* `Hartshorne.differentialsToGeneric`: the map `Ω_{X/k} ⟶ Ω_K`.

## Main results

* `Hartshorne.differentialsToGeneric_d`: the map sends `d a` to `d(a_η)`.
* `Hartshorne.exists_differentialsToGeneric_eq`: every element of `Ω_{K/k}` is a generic value.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace Hartshorne

universe u

section Module

variable {X : Scheme.{u}} [IrreducibleSpace X]

/-- An open set containing some point contains the generic point. -/
theorem genericPoint_mem_of_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, Set.mem_univ x, hx⟩

/-- The germ at the generic point, for an open set `U` and a point of `U` witnessing that `U`
contains the generic point. It does not depend on the point. -/
def genericGerm (U : X.Opens) (x : U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) (genericPoint_mem_of_mem x.2)).hom

theorem genericGerm_eq (U : X.Opens) (x y : U) : genericGerm U x = genericGerm U y :=
  rfl

theorem genericGerm_res {U V : X.Opens} (i : V ⟶ U) (x : V) (r : Γ(X, U)) :
    genericGerm V x (X.presheaf.map i.op r) = genericGerm U ⟨x.1, i.le x.2⟩ r :=
  X.presheaf.germ_res_apply i _ _ r

variable (V : Type u) [AddCommGroup V] [Module X.functionField V]

/-- A section `r` over `U` acts on a locally constant map `U → V` through its generic germ. -/
def genericSMul (U : X.Opens) (r : Γ(X, U)) (s : LocallyConstant U V) : LocallyConstant U V :=
  ⟨fun x => genericGerm U x r • s x,
    (IsLocallyConstant.of_constant (fun x : U => genericGerm U x r) fun _ _ => rfl).comp₂
      s.isLocallyConstant (· • ·)⟩

theorem genericSMul_apply (U : X.Opens) (r : Γ(X, U)) (s : LocallyConstant U V) (x : U) :
    genericSMul V U r s x = genericGerm U x r • s x :=
  rfl

/-- The `Γ(X, U)`-module structure on locally constant maps `U → V`. -/
@[instance_reducible] def genericModule (U : X.Opens) : Module Γ(X, U) (LocallyConstant U V) where
  smul := genericSMul V U
  one_smul s := LocallyConstant.ext fun x => by
    change genericGerm U x 1 • s x = s x
    rw [map_one, one_smul]
  mul_smul r t s := LocallyConstant.ext fun x => by
    change genericGerm U x (r * t) • s x = genericGerm U x r • (genericGerm U x t • s x)
    rw [map_mul, mul_smul]
  smul_zero r := LocallyConstant.ext fun x => smul_zero (genericGerm U x r)
  smul_add r s t := LocallyConstant.ext fun x => smul_add (genericGerm U x r) (s x) (t x)
  add_smul r t s := LocallyConstant.ext fun x => by
    change genericGerm U x (r + t) • s x = genericGerm U x r • s x + genericGerm U x t • s x
    rw [map_add, add_smul]
  zero_smul s := LocallyConstant.ext fun x => by
    change genericGerm U x 0 • s x = 0
    rw [map_zero, zero_smul]

/-- The module structures on the sections of the constant sheaf. -/
abbrev genericModuleInst (U : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U)
      ((constantSheaf X.toTopCat (AddCommGrpCat.of V)).obj.obj U) :=
  genericModule V U.unop

attribute [local instance] genericModuleInst

theorem genericModule_map_smul ⦃U W : (X.Opens)ᵒᵖ⦄ (i : U ⟶ W) (r : X.ringCatSheaf.obj.obj U)
    (m : (constantSheaf X.toTopCat (AddCommGrpCat.of V)).obj.obj U) :
    (constantSheaf X.toTopCat (AddCommGrpCat.of V)).obj.map i (r • m) =
      X.ringCatSheaf.obj.map i r • (constantSheaf X.toTopCat (AddCommGrpCat.of V)).obj.map i m :=
  LocallyConstant.ext fun x => by
    exact congrArg (· • (show LocallyConstant U.unop V from m) ⟨x.1, i.unop.le x.2⟩)
      (genericGerm_res i.unop x (show Γ(X, U.unop) from r)).symm

/-- **The constant sheaf with value a `K`-module `V`, as an `𝒪_X`-module**: sections over `U`
are the locally constant maps `U → V`, and a section of `𝒪_X` acts through its germ at the
generic point. -/
def genericConstantModule : X.Modules where
  val := PresheafOfModules.ofPresheaf (constantSheaf X.toTopCat (AddCommGrpCat.of V)).obj
    (genericModule_map_smul V)
  isSheaf := (constantSheaf X.toTopCat (AddCommGrpCat.of V)).property

/-- The underlying sheaf of abelian groups is the constant sheaf. -/
theorem toSheaf_genericConstantModule :
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (genericConstantModule V) =
      constantSheaf X.toTopCat (AddCommGrpCat.of V) :=
  rfl

theorem genericConstantModule_smul_apply (U : X.Opens) (r : Γ(X, U))
    (s : Γ(genericConstantModule V, U)) (x : U) :
    (show LocallyConstant U V from r • s) x = genericGerm U x r • (show LocallyConstant U V from s) x :=
  rfl

end Module

section Derivation

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))

/-- The module `Ω_{K/k}` of differentials of the function field `K` over `k`. -/
abbrev functionFieldDifferentials : Type u :=
  @KaehlerDifferential k X.functionField _ _ (functionFieldAlgebra f)

/-- The universal derivation `d : K → Ω_{K/k}`. -/
def functionFieldD : X.functionField →+ functionFieldDifferentials f :=
  letI := functionFieldAlgebra f
  (KaehlerDifferential.D k X.functionField).toAddMonoidHom

theorem functionFieldD_mul (a b : X.functionField) :
    functionFieldD f (a * b) = a • functionFieldD f b + b • functionFieldD f a :=
  letI := functionFieldAlgebra f
  (KaehlerDifferential.D k X.functionField).leibniz a b

/-- The image of the universal derivation spans `Ω_{K/k}` over `K`. -/
theorem span_range_functionFieldD :
    Submodule.span X.functionField (Set.range (functionFieldD f)) = ⊤ :=
  letI := functionFieldAlgebra f
  KaehlerDifferential.span_range_derivation k X.functionField

theorem functionFieldD_germ_app_top (t : Γ(Spec (.of k), ⊤)) :
    functionFieldD f (X.presheaf.germ (f ⁻¹ᵁ ⊤) (genericPoint X) trivial (f.app ⊤ t)) = 0 := by
  let := functionFieldAlgebra f
  have h : X.presheaf.germ (f ⁻¹ᵁ ⊤) (genericPoint X) trivial (f.app ⊤ t) =
      algebraMap k X.functionField ((Scheme.ΓSpecIso (.of k)).hom t) := by
    change _ = X.presheaf.germ (f ⁻¹ᵁ ⊤) (genericPoint X) trivial
      (f.app ⊤ ((Scheme.ΓSpecIso (.of k)).inv ((Scheme.ΓSpecIso (.of k)).hom t)))
    rw [Iso.hom_inv_id_apply]
  rw [h]
  exact (KaehlerDifferential.D k X.functionField).map_algebraMap _

/-- The sections whose generic germ has vanishing differential. -/
def genericDKerSubring (U : X.Opens) : Subring Γ(X, U) where
  carrier := {a | ∀ x : U, functionFieldD f (genericGerm U x a) = 0}
  mul_mem' {a b} ha hb x := by
    simp only [map_mul, functionFieldD_mul, ha x, hb x, smul_zero, add_zero]
  one_mem' x := by
    have h := functionFieldD_mul f 1 1
    rw [mul_one, one_smul] at h
    change functionFieldD f (genericGerm U x 1) = 0
    rw [map_one]
    simpa using h
  add_mem' {a b} ha hb x := by
    simp only [map_add, ha x, hb x, add_zero]
  zero_mem' x := by simp
  neg_mem' {a} ha x := by simp [ha x]

/-- The presheaf of sections whose generic germ has vanishing differential. -/
def genericDKerPresheaf : TopCat.Presheaf CommRingCat X where
  obj U := CommRingCat.of (genericDKerSubring f U.unop)
  map {U W} i := CommRingCat.ofHom ((X.presheaf.map i).hom.restrict _ _
    (fun a ha x => by
      change functionFieldD f (genericGerm W.unop x (X.presheaf.map i.unop.op a)) = 0
      rw [genericGerm_res]
      exact ha _))
  map_id U := by
    ext a
    change X.presheaf.map (𝟙 U) a.1 = a.1
    rw [X.presheaf.map_id]
    rfl
  map_comp i j := by
    ext a
    change X.presheaf.map (i ≫ j) a.1 = X.presheaf.map j (X.presheaf.map i a.1)
    rw [X.presheaf.map_comp]
    rfl

theorem genericDKerPresheaf_isSheaf : (genericDKerPresheaf f).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hsf' : TopCat.Presheaf.IsCompatible X.presheaf U (fun i => (sf i).1) :=
    fun i j => congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hsu⟩ := X.sheaf.existsUnique_gluing U _ hsf'
  have hmem : s ∈ genericDKerSubring f (iSup U) := by
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 x.2
    have h1 := (sf i).2 ⟨x.1, hi⟩
    have h2 : X.presheaf.map (Opens.leSupr U i).op s = (sf i).1 := hs i
    rw [← h2] at h1
    exact (congrArg (functionFieldD f)
      (genericGerm_res (Opens.leSupr U i) ⟨x.1, hi⟩ (show Γ(X, iSup U) from s))).symm.trans h1
  exact ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i),
    fun t ht => Subtype.ext (hsu t.1 fun i => congrArg Subtype.val (ht i))⟩

/-- The sheaf of sections whose generic germ has vanishing differential. -/
def genericDKerSheaf : TopCat.Sheaf CommRingCat X :=
  ⟨genericDKerPresheaf f, genericDKerPresheaf_isSheaf f⟩

/-- Its inclusion into the structure sheaf. -/
def genericDKerSheafι : genericDKerSheaf f ⟶ X.sheaf :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (R := genericDKerSubring f U.unop)
        (S := X.presheaf.obj U) (genericDKerSubring f U.unop).subtype
      naturality _ _ _ := rfl }

omit [IsIntegral X] in
theorem eq_top_of_mem_preimage {V : (Spec (.of k)).Opens} {x : X} (hx : x ∈ f ⁻¹ᵁ V) :
    V = ⊤ := by
  ext y
  simp only [Opens.coe_top, Set.mem_univ, iff_true]
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rw [Subsingleton.elim y (f x)]
  exact hx

theorem c_app_mem_genericDKerSubring (V : (Spec (.of k)).Opens) (t : Γ(Spec (.of k), V)) :
    f.app V t ∈ genericDKerSubring f (f ⁻¹ᵁ V) := by
  intro x
  obtain rfl := eq_top_of_mem_preimage f x.2
  exact functionFieldD_germ_app_top f t

/-- The structure map of `X` over `Spec k` factors through the vanishing subsheaf. -/
def genericDCFactor : (Spec (.of k)).sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat f.base).obj (genericDKerSheaf f) :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom (R := (Spec (.of k)).presheaf.obj V)
        (S := genericDKerSubring f (f ⁻¹ᵁ V.unop))
        ((f.app V.unop).hom.codRestrict _ (fun t => c_app_mem_genericDKerSubring f V.unop t))
      naturality _ _ i := by
        ext t
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (f.c.naturality i) t }

theorem inverseImageStructureSheafMap_eq_genericD :
    Scheme.inverseImageStructureSheafMap f =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv
        _ _).symm (genericDCFactor f) ≫ genericDKerSheafι f := by
  rw [Scheme.inverseImageStructureSheafMap, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1

theorem inverseImageStructureSheafMap_mem_genericDKerSubring (U : X.Opensᵒᵖ)
    (a : (Scheme.inverseImageStructureSheaf f).obj.obj U) :
    (Scheme.inverseImageStructureSheafMap f).hom.app U a ∈ genericDKerSubring f U.unop := by
  have h := congrArg (fun φ => φ.hom.app U a) (inverseImageStructureSheafMap_eq_genericD f)
  simp only at h
  rw [h]
  exact Subtype.property _

/-- The relative derivation `𝒪_X → Ω_K`, `a ↦ d(a_η)`. -/
def genericDerivation : (genericConstantModule (functionFieldDifferentials f)).val.Derivation'
    (Scheme.inverseImageStructureSheafMap f).hom where
  d {U} :=
    { toFun a := (⟨fun x => functionFieldD f (genericGerm U.unop x a),
        IsLocallyConstant.of_constant _ fun _ _ => rfl⟩ :
          LocallyConstant U.unop (functionFieldDifferentials f))
      map_zero' := LocallyConstant.ext fun x =>
        (congrArg (functionFieldD f) (genericGerm U.unop x).map_zero).trans (map_zero _)
      map_add' a b := LocallyConstant.ext fun x =>
        (congrArg (functionFieldD f) ((genericGerm U.unop x).map_add a b)).trans (map_add _ _ _) }
  d_mul {U} a b := LocallyConstant.ext fun x => by
    change functionFieldD f (genericGerm U.unop x (a * b)) =
      genericGerm U.unop x a • functionFieldD f (genericGerm U.unop x b) +
        genericGerm U.unop x b • functionFieldD f (genericGerm U.unop x a)
    exact (congrArg (functionFieldD f) ((genericGerm U.unop x).map_mul a b)).trans
      (functionFieldD_mul f _ _)
  d_map {U W} i a := LocallyConstant.ext fun x => by
    change functionFieldD f (genericGerm W.unop x (X.presheaf.map i a)) =
      functionFieldD f (genericGerm U.unop ⟨x.1, i.unop.le x.2⟩ a)
    exact congrArg (functionFieldD f) (genericGerm_res i.unop x a)
  d_app {U} a := LocallyConstant.ext fun x =>
    inverseImageStructureSheafMap_mem_genericDKerSubring f U a x

/-- **The map `Ω_{X/k} ⟶ Ω_K`** to the constant sheaf with value `Ω_{K/k}`, given by the
universal property of `Ω_{X/k}` applied to the derivation `a ↦ d(a_η)`. -/
def differentialsToGeneric :
    Scheme.relativeDifferentials f ⟶ genericConstantModule (functionFieldDifferentials f) :=
  (Scheme.relativeDifferentialsHomEquiv f _).symm (genericDerivation f)

/-- The map `Ω_{X/k} ⟶ Ω_K` sends `d a` to the constant map with value `d(a_η)`. -/
theorem differentialsToGeneric_d (U : X.Opens) (a : Γ(X, U)) (x : U) :
    (show LocallyConstant U (functionFieldDifferentials f) from
      (differentialsToGeneric f).app U ((Scheme.relativeDifferentialsD f).hom.app (op U) a)) x =
      functionFieldD f (genericGerm U x a) := by
  have h := Scheme.relativeDifferentialsHomEquiv_apply f _ (differentialsToGeneric f)
  rw [differentialsToGeneric, Equiv.apply_symm_apply] at h
  have h2 := congrArg (fun D => (D.d (X := op U) a :
    LocallyConstant U (functionFieldDifferentials f)) x) h
  exact h2.symm

/-- The value at a point of the image of a restricted section. -/
theorem differentialsToGeneric_res {U W : X.Opens} (i : W ⟶ U)
    (s : Γ(Scheme.relativeDifferentials f, U)) (y : W) :
    (show LocallyConstant W (functionFieldDifferentials f) from (differentialsToGeneric f).app W
      ((Scheme.relativeDifferentials f).presheaf.map i.op s)) y =
      (show LocallyConstant U (functionFieldDifferentials f) from
        (differentialsToGeneric f).app U s) ⟨y.1, i.le y.2⟩ := by
  have h := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf (differentialsToGeneric f)).naturality i.op) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  exact congrArg (fun m => (show LocallyConstant W (functionFieldDifferentials f) from m) y) h

/-- The value at a point of the image of a multiple of a section. -/
theorem differentialsToGeneric_smul {U : X.Opens} (r : Γ(X, U))
    (s : Γ(Scheme.relativeDifferentials f, U)) (y : U) :
    (show LocallyConstant U (functionFieldDifferentials f) from (differentialsToGeneric f).app U
      (r • s)) y = genericGerm U y r •
      (show LocallyConstant U (functionFieldDifferentials f) from
        (differentialsToGeneric f).app U s) y := by
  rw [Scheme.Modules.Hom.app_smul]
  rfl

/-- The generic values of sections over nonempty open sets form a `K`-submodule. -/
def genericValues : Submodule X.functionField (functionFieldDifferentials f) where
  carrier := {ω | ∃ (U : X.Opens) (_ : Nonempty U) (s : Γ(Scheme.relativeDifferentials f, U)),
    ∀ y : U, (show LocallyConstant U (functionFieldDifferentials f) from
      (differentialsToGeneric f).app U s) y = ω}
  zero_mem' := ⟨⊤, ⟨⟨genericPoint X, trivial⟩⟩, 0, fun y => by rw [map_zero]; rfl⟩
  add_mem' {ω₁ ω₂} := by
    rintro ⟨U₁, ⟨x₁⟩, s₁, h₁⟩ ⟨U₂, ⟨x₂⟩, s₂, h₂⟩
    have hη : genericPoint X ∈ U₁ ⊓ U₂ :=
      ⟨genericPoint_mem_of_mem x₁.2, genericPoint_mem_of_mem x₂.2⟩
    refine ⟨U₁ ⊓ U₂, ⟨⟨_, hη⟩⟩,
      (Scheme.relativeDifferentials f).presheaf.map (homOfLE inf_le_left).op s₁ +
        (Scheme.relativeDifferentials f).presheaf.map (homOfLE inf_le_right).op s₂, fun y => ?_⟩
    rw [map_add]
    change (show LocallyConstant (U₁ ⊓ U₂ : X.Opens) (functionFieldDifferentials f) from _) y +
      (show LocallyConstant (U₁ ⊓ U₂ : X.Opens) (functionFieldDifferentials f) from _) y = _
    rw [differentialsToGeneric_res, differentialsToGeneric_res, h₁, h₂]
  smul_mem' z {ω} := by
    rintro ⟨U, ⟨x⟩, s, h⟩
    obtain ⟨W, hW, e, rfl⟩ := X.presheaf.exists_germ_eq z
    have hη : genericPoint X ∈ U ⊓ W := ⟨genericPoint_mem_of_mem x.2, hW⟩
    refine ⟨U ⊓ W, ⟨⟨_, hη⟩⟩, X.presheaf.map (homOfLE (inf_le_right : U ⊓ W ≤ W)).op e •
        (Scheme.relativeDifferentials f).presheaf.map (homOfLE (inf_le_left : U ⊓ W ≤ U)).op s,
      fun y => ?_⟩
    rw [differentialsToGeneric_smul, differentialsToGeneric_res, h, genericGerm_res]
    rfl

/-- **Every rational differential is a generic value**: every element of `Ω_{K/k}` is the generic
value of a section of `Ω_{X/k}` over some nonempty open set. -/
theorem exists_differentialsToGeneric_eq (ω : functionFieldDifferentials f) :
    ∃ (U : X.Opens) (_ : Nonempty U) (s : Γ(Scheme.relativeDifferentials f, U)),
      ∀ y : U, (show LocallyConstant U (functionFieldDifferentials f) from
        (differentialsToGeneric f).app U s) y = ω := by
  have hle : Submodule.span X.functionField (Set.range (functionFieldD f)) ≤ genericValues f := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    obtain ⟨W, hW, a, rfl⟩ := X.presheaf.exists_germ_eq z
    exact ⟨W, ⟨⟨_, hW⟩⟩, (Scheme.relativeDifferentialsD f).hom.app (op W) a,
      fun y => differentialsToGeneric_d f W a y⟩
  rw [span_range_functionFieldD] at hle
  exact hle (Submodule.mem_top (x := ω))

end Derivation

end Hartshorne
