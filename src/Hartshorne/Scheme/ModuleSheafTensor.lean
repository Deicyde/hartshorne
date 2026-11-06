/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Tensor products of module sheaves

Hartshorne, *Algebraic Geometry*, II.5 (p. 109).

Let `(X, 𝒪_X)` be a ringed space, given here by a topological space `X` together with a sheaf
`R` of commutative rings on `X`; sheaves of `𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)`.
For a scheme `X`, `X.Modules` is definitionally `SheafOfModules (ringCatSheafOf X.sheaf)`, so
everything below applies to `𝒪_X`-modules on schemes.

For `𝒪_X`-modules `F` and `G` we define `moduleSheafTensor F G` (that is, `F ⊗_{𝒪_X} G`) as the
sheafification of the presheaf of modules `U ↦ F(U) ⊗_{𝒪_X(U)} G(U)`, and prove:

* the balanced universal property: `moduleSheafTensorHomEquiv` is a bijection, natural in the
  target (`moduleSheafTensorHomEquiv_comp`), between morphisms `F ⊗ G ⟶ H` and families of
  `𝒪_X(U)`-bilinear maps `F(U) × G(U) → H(U)` compatible with restriction
  (`ModuleSheafBilinear F G H`); it is given by composing with the universal bilinear map
  `moduleSheafTensorBilinear F G`, which therefore satisfies `moduleSheafTensor_universal`;
* the stalk isomorphism `moduleSheafTensorStalkIso : (F ⊗ G)ₓ ≃ₗ[𝒪_{X,x}] Fₓ ⊗[𝒪_{X,x}] Gₓ`,
  which sends the germ of `f ⊗ g` to `fₓ ⊗ gₓ` (`moduleSheafTensorStalkIso_germ`).

The stalk computation combines the fact that the unit of sheafification induces isomorphisms on
stalks with a direct proof that the stalk of the presheaf tensor product is the tensor product of
the stalks (tensor products commute with the filtered colimits defining stalks, even though the
base rings vary with the open set).
-/

universe u

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open scoped TensorProduct

namespace Hartshorne

variable {X : TopCat.{u}}

/-- The sheaf of rings underlying a sheaf of commutative rings. Its underlying presheaf is
reducibly `R.obj ⋙ forget₂ CommRingCat RingCat`, on which presheaves of modules carry their
monoidal structure. -/
abbrev ringCatSheafOf (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  ⟨R.obj ⋙ forget₂ CommRingCat RingCat.{u},
    ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R).property⟩

variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The presheaf of modules `U ↦ F(U) ⊗_{𝒪_X(U)} G(U)`. -/
noncomputable abbrev moduleSheafTensorPresheaf (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  F.val ⊗ G.val

/-- **Tensor product of module sheaves.** The `𝒪_X`-module `F ⊗_{𝒪_X} G`, defined as the
sheafification of the presheaf `U ↦ F(U) ⊗_{𝒪_X(U)} G(U)`. -/
noncomputable def moduleSheafTensor (F G : SheafOfModules.{u} (ringCatSheafOf R)) :
    SheafOfModules.{u} (ringCatSheafOf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).obj
    (moduleSheafTensorPresheaf F G)

/-- A balanced (bilinear) morphism `F × G → H` of `𝒪_X`-modules: for every open `U`, an
`𝒪_X(U)`-bilinear map `F(U) × G(U) → H(U)`, compatible with restriction. -/
structure ModuleSheafBilinear (F G H : SheafOfModules.{u} (ringCatSheafOf R)) where
  /-- The bilinear map on sections over `U`. -/
  app (U : (Opens X)ᵒᵖ) :
    F.val.obj U →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U]
      G.val.obj U →ₗ[(R.obj ⋙ forget₂ CommRingCat RingCat).obj U] H.val.obj U
  /-- Compatibility with restriction. -/
  naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : F.val.obj U) (g : G.val.obj U) :
    H.val.map i (app U f g) = app V (F.val.map i f) (G.val.map i g)

namespace ModuleSheafBilinear

variable {F G H K : SheafOfModules.{u} (ringCatSheafOf R)}

@[ext]
lemma ext {β γ : ModuleSheafBilinear F G H}
    (h : ∀ U f g, β.app U f g = γ.app U f g) : β = γ := by
  cases β; cases γ
  congr
  funext U
  exact LinearMap.ext₂ (h U)

/-- Composition of a bilinear morphism with a morphism of `𝒪_X`-modules. -/
noncomputable def postcomp (β : ModuleSheafBilinear F G H) (φ : H ⟶ K) :
    ModuleSheafBilinear F G K where
  app U := (β.app U).compr₂ (φ.val.app U).hom
  naturality i f g := by
    have h := congrArg (fun k => k.hom (β.app _ f g)) (φ.val.naturality i)
    exact h.symm.trans (congrArg (fun y => (φ.val.app _).hom y) (β.naturality i f g))

@[simp]
lemma postcomp_app (β : ModuleSheafBilinear F G H) (φ : H ⟶ K) (U : (Opens X)ᵒᵖ)
    (f : F.val.obj U) (g : G.val.obj U) :
    (β.postcomp φ).app U f g = φ.val.app U (β.app U f g) := rfl

lemma postcomp_postcomp {L : SheafOfModules.{u} (ringCatSheafOf R)}
    (β : ModuleSheafBilinear F G H) (φ : H ⟶ K) (ψ : K ⟶ L) :
    (β.postcomp φ).postcomp ψ = β.postcomp (φ ≫ ψ) := by
  ext U f g
  rfl

end ModuleSheafBilinear

variable {F G H : SheafOfModules.{u} (ringCatSheafOf R)}

namespace ModuleSheafTensor

variable (F G H) in
/-- Morphisms out of the presheaf tensor product are the bilinear morphisms. -/
noncomputable def presheafHomEquivBilinear :
    (moduleSheafTensorPresheaf F G ⟶ H.val) ≃ ModuleSheafBilinear F G H where
  toFun ψ :=
    { app U := LinearMap.mk₂ _ (fun f g => (ψ.app U).hom (f ⊗ₜ g))
        (fun f f' g => (congrArg (ψ.app U).hom (TensorProduct.add_tmul f f' g)).trans
          (map_add _ _ _))
        (fun r f g => (congrArg (ψ.app U).hom (TensorProduct.smul_tmul' r f g).symm).trans
          (map_smul _ _ _))
        (fun f g g' => (congrArg (ψ.app U).hom (TensorProduct.tmul_add f g g')).trans
          (map_add _ _ _))
        (fun r f g => (congrArg (ψ.app U).hom (TensorProduct.tmul_smul r f g)).trans
          (map_smul _ _ _))
      naturality i f g := by
        have h := congrArg (fun k => k.hom (f ⊗ₜ g)) (ψ.naturality i)
        exact h.symm }
  invFun β :=
    { app U := ModuleCat.ofHom (TensorProduct.lift (β.app U))
      naturality i := by
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro f g
        exact (β.naturality i f g).symm }
  left_inv ψ := by
    ext U : 1
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro f g
    rfl
  right_inv β := by
    ext U f g
    rfl

end ModuleSheafTensor

open ModuleSheafTensor

variable (F G) in
/-- The canonical map from the presheaf tensor product to its sheafification. -/
noncomputable def moduleSheafTensorUnit :
    moduleSheafTensorPresheaf F G ⟶ (moduleSheafTensor F G).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).unit.app
    (moduleSheafTensorPresheaf F G)

variable (F G H) in
/-- **Universal property of the tensor product.** Morphisms `F ⊗_{𝒪_X} G ⟶ H` correspond
bijectively to bilinear morphisms `F × G → H`. -/
noncomputable def moduleSheafTensorHomEquiv :
    (moduleSheafTensor F G ⟶ H) ≃ ModuleSheafBilinear F G H :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf R).obj)).homEquiv
    (moduleSheafTensorPresheaf F G) H).trans (presheafHomEquivBilinear F G H)

variable (F G) in
/-- The universal bilinear morphism `F × G → F ⊗_{𝒪_X} G`, `(f, g) ↦ f ⊗ g`. -/
noncomputable def moduleSheafTensorBilinear : ModuleSheafBilinear F G (moduleSheafTensor F G) :=
  presheafHomEquivBilinear F G _ (moduleSheafTensorUnit F G)

lemma moduleSheafTensorBilinear_app (U : (Opens X)ᵒᵖ) (f : F.val.obj U) (g : G.val.obj U) :
    (moduleSheafTensorBilinear F G).app U f g = (moduleSheafTensorUnit F G).app U (f ⊗ₜ g) :=
  rfl

lemma moduleSheafTensorHomEquiv_apply (φ : moduleSheafTensor F G ⟶ H) :
    moduleSheafTensorHomEquiv F G H φ = (moduleSheafTensorBilinear F G).postcomp φ := by
  ext U f g
  rfl

lemma moduleSheafTensorHomEquiv_comp {K : SheafOfModules.{u} (ringCatSheafOf R)}
    (φ : moduleSheafTensor F G ⟶ H) (ψ : H ⟶ K) :
    moduleSheafTensorHomEquiv F G K (φ ≫ ψ) = (moduleSheafTensorHomEquiv F G H φ).postcomp ψ := by
  rw [moduleSheafTensorHomEquiv_apply, moduleSheafTensorHomEquiv_apply,
    ModuleSheafBilinear.postcomp_postcomp]

/-- **Balanced universal property.** Every bilinear morphism `F × G → H` factors uniquely
through the universal bilinear morphism `F × G → F ⊗_{𝒪_X} G`. -/
theorem moduleSheafTensor_universal (β : ModuleSheafBilinear F G H) :
    ∃! φ : moduleSheafTensor F G ⟶ H, (moduleSheafTensorBilinear F G).postcomp φ = β := by
  refine ⟨(moduleSheafTensorHomEquiv F G H).symm β, ?_, fun φ hφ => ?_⟩
  · dsimp only
    rw [← moduleSheafTensorHomEquiv_apply, Equiv.apply_symm_apply]
  · rw [← hφ, ← moduleSheafTensorHomEquiv_apply, Equiv.symm_apply_apply]

variable (R) in
/-- The stalk `𝒪_{X,x}` of the structure sheaf. -/
noncomputable abbrev ringSheafStalk (x : X) : CommRingCat.{u} :=
  TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X) R.obj x

/-- The stalk of a presheaf of modules, as an abelian group with its `𝒪_{X,x}`-module structure. -/
noncomputable abbrev moduleStalk (M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (x : X) : AddCommGrpCat.{u} :=
  TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.presheaf x

namespace ModuleSheafTensor

open CategoryTheory.Limits

/-- An additive map out of a stalk built from compatible additive maps on sections. -/
noncomputable def stalkDesc {P : TopCat.Presheaf AddCommGrpCat.{u} X} {x : X}
    {A : AddCommGrpCat.{u}}
    (φ : ∀ U : Opens X, x ∈ U → (P.obj (op U) ⟶ A))
    (hφ : ∀ (U V : Opens X) (i : V ⟶ U) (hV : x ∈ V), P.map i.op ≫ φ V hV = φ U (i.le hV)) :
    TopCat.Presheaf.stalk P x ⟶ A :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ P)
    { pt := A
      ι :=
        { app U := φ U.unop.1 U.unop.2
          naturality U V i := by
            exact (hφ U.unop.1 V.unop.1 i.unop V.unop.2).trans (Category.comp_id _).symm } }

lemma stalkDesc_germ {P : TopCat.Presheaf AddCommGrpCat.{u} X} {x : X} {A : AddCommGrpCat.{u}}
    (φ : ∀ U : Opens X, x ∈ U → (P.obj (op U) ⟶ A))
    (hφ : ∀ (U V : Opens X) (i : V ⟶ U) (hV : x ∈ V), P.map i.op ≫ φ V hV = φ U (i.le hV))
    (U : Opens X) (hU : x ∈ U) (s : P.obj (op U)) :
    stalkDesc φ hφ (TopCat.Presheaf.germ P U x hU s) = φ U hU s := by
  change (TopCat.Presheaf.germ P U x hU ≫ stalkDesc φ hφ) s = _
  exact ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion x).op ⋙ P) _ (op (⟨U, hU⟩ : OpenNhds x))) s

/-- The germ map on sections of a presheaf of modules. -/
noncomputable def sectionGerm (M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    (x : X) (U : Opens X) (hU : x ∈ U) : M.obj (op U) →+ moduleStalk M x :=
  (TopCat.Presheaf.germ M.presheaf U x hU).hom

/-- Restriction of sections of a presheaf of modules along an inclusion of opens. -/
noncomputable def res (M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat))
    {U V : Opens X} (i : V ⟶ U) : M.obj (op U) →+ M.obj (op V) :=
  (M.restrictₛₗ i.op).toAddMonoidHom

section Germs

variable (M : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) (x : X)

lemma res_res {U V W : Opens X} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) (m : M.obj (op U)) :
    res M j (res M i m) = res M k m := by
  change M.map j.op (M.map i.op m) = M.map k.op m
  rw [← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply M (Subsingleton.elim _ _) m

lemma res_id {U : Opens X} (i : U ⟶ U) (m : M.obj (op U)) : res M i m = m := by
  change M.map i.op m = m
  rw [Subsingleton.elim i (𝟙 U)]
  simp
  rfl

lemma sectionGerm_res {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V) (m : M.obj (op U)) :
    sectionGerm M x V hV (res M i m) = sectionGerm M x U (i.le hV) m :=
  TopCat.Presheaf.germ_res_apply M.presheaf i x hV m

lemma sectionGerm_smul (U : Opens X) (hU : x ∈ U)
    (r : (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) (m : M.obj (op U)) :
    sectionGerm M x U hU (r • m) =
      TopCat.Presheaf.germ R.obj U x hU r • sectionGerm M x U hU m :=
  PresheafOfModules.germ_smul (R := R.obj) M x U hU r m

lemma exists_sectionGerm (s : moduleStalk M x) :
    ∃ (U : Opens X) (hU : x ∈ U) (m : M.obj (op U)), sectionGerm M x U hU m = s :=
  TopCat.Presheaf.exists_germ_eq M.presheaf s

lemma exists_le_sectionGerm (s : moduleStalk M x) {V : Opens X} (hV : x ∈ V) :
    ∃ U ≤ V, ∃ (hU : x ∈ U) (m : M.obj (op U)), sectionGerm M x U hU m = s :=
  TopCat.Presheaf.exists_le_germ_eq M.presheaf s hV

lemma exists_le_ringGerm (r : ringSheafStalk R x) {V : Opens X} (hV : x ∈ V) :
    ∃ U ≤ V, ∃ (hU : x ∈ U) (c : (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)),
      TopCat.Presheaf.germ R.obj U x hU c = r :=
  TopCat.Presheaf.exists_le_germ_eq R.obj r hV

lemma moduleStalk_addHom_ext {A : Type u} [AddCommGroup A] {φ ψ : moduleStalk M x →+ A}
    (h : ∀ (U : Opens X) (hU : x ∈ U) (m : M.obj (op U)),
      φ (sectionGerm M x U hU m) = ψ (sectionGerm M x U hU m)) : φ = ψ := by
  ext s
  obtain ⟨U, hU, m, rfl⟩ := exists_sectionGerm M x s
  exact h U hU m

end Germs

section PresheafTensorStalk

variable (M₁ M₂ : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) (x : X)

/-- The pairing of sections into the tensor product of stalks. -/
noncomputable def germPairing (U : Opens X) (hU : x ∈ U) :
    M₁.obj (op U) →+ M₂.obj (op U) →+ (moduleStalk M₁ x ⊗[ringSheafStalk R x] moduleStalk M₂ x) :=
  AddMonoidHom.mk' (fun f => (TensorProduct.mk (ringSheafStalk R x) (moduleStalk M₁ x)
      (moduleStalk M₂ x) (sectionGerm M₁ x U hU f)).toAddMonoidHom.comp (sectionGerm M₂ x U hU))
    (fun f f' => by ext g; simp)

lemma germPairing_apply (U : Opens X) (hU : x ∈ U) (f : M₁.obj (op U)) (g : M₂.obj (op U)) :
    germPairing M₁ M₂ x U hU f g = sectionGerm M₁ x U hU f ⊗ₜ sectionGerm M₂ x U hU g := rfl

lemma germPairing_balanced (U : Opens X) (hU : x ∈ U)
    (r : (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) (f : M₁.obj (op U))
    (g : M₂.obj (op U)) :
    germPairing M₁ M₂ x U hU (r • f) g = germPairing M₁ M₂ x U hU f (r • g) := by
  rw [germPairing_apply, germPairing_apply, sectionGerm_smul, sectionGerm_smul,
    TensorProduct.smul_tmul]

/-- The map `M₁(U) ⊗ M₂(U) → M₁ₓ ⊗ M₂ₓ`. -/
noncomputable def tensorStalkComponent (U : Opens X) (hU : x ∈ U) :
    M₁.obj (op U) ⊗[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] M₂.obj (op U) →+
      (moduleStalk M₁ x ⊗[ringSheafStalk R x] moduleStalk M₂ x) :=
  TensorProduct.liftAddHom (germPairing M₁ M₂ x U hU) (germPairing_balanced M₁ M₂ x U hU)

lemma tensorStalkComponent_tmul (U : Opens X) (hU : x ∈ U) (f : M₁.obj (op U))
    (g : M₂.obj (op U)) :
    tensorStalkComponent M₁ M₂ x U hU (f ⊗ₜ g) =
      sectionGerm M₁ x U hU f ⊗ₜ sectionGerm M₂ x U hU g :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- The comparison map from the stalk of the presheaf tensor product. -/
noncomputable def presheafTensorStalkToTensor :
    moduleStalk (M₁ ⊗ M₂) x ⟶
      AddCommGrpCat.of (moduleStalk M₁ x ⊗[ringSheafStalk R x] moduleStalk M₂ x) :=
  stalkDesc (fun U hU => AddCommGrpCat.ofHom (tensorStalkComponent M₁ M₂ x U hU))
    (fun U V i hV => by
      ext t
      change M₁.obj (op U) ⊗[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] M₂.obj (op U) at t
      refine TensorProduct.induction_on t ?_ ?_ ?_
      · exact (map_zero _).trans (map_zero _).symm
      · intro f g
        change tensorStalkComponent M₁ M₂ x V hV (res M₁ i f ⊗ₜ res M₂ i g) =
          tensorStalkComponent M₁ M₂ x U (i.le hV) (f ⊗ₜ g)
        rw [tensorStalkComponent_tmul, tensorStalkComponent_tmul, sectionGerm_res,
          sectionGerm_res]
      · intro a b ha hb
        exact (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ a b).symm))

lemma presheafTensorStalkToTensor_germ (U : Opens X) (hU : x ∈ U)
    (t : M₁.obj (op U) ⊗[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] M₂.obj (op U)) :
    presheafTensorStalkToTensor M₁ M₂ x (sectionGerm (M₁ ⊗ M₂) x U hU t) =
      tensorStalkComponent M₁ M₂ x U hU t :=
  stalkDesc_germ (P := (M₁ ⊗ M₂).presheaf)
    (fun U hU => AddCommGrpCat.ofHom (tensorStalkComponent M₁ M₂ x U hU)) _ U hU t

/-- The germ of the tensor product of two sections over the same open. -/
noncomputable def tensorGerm (U : Opens X) (hU : x ∈ U) :
    M₁.obj (op U) →+ M₂.obj (op U) →+ moduleStalk (M₁ ⊗ M₂) x :=
  AddMonoidHom.mk' (fun f => (sectionGerm (M₁ ⊗ M₂) x U hU).comp
      (TensorProduct.mk _ (M₁.obj (op U)) (M₂.obj (op U)) f).toAddMonoidHom)
    (fun f f' => by
      ext g
      exact (congrArg (sectionGerm (M₁ ⊗ M₂) x U hU) (TensorProduct.add_tmul f f' g)).trans
        (map_add _ _ _))

lemma tensorGerm_apply (U : Opens X) (hU : x ∈ U) (f : M₁.obj (op U)) (g : M₂.obj (op U)) :
    tensorGerm M₁ M₂ x U hU f g = sectionGerm (M₁ ⊗ M₂) x U hU (f ⊗ₜ g) := rfl

lemma tensorGerm_res {U V : Opens X} (i : V ⟶ U) (hV : x ∈ V) (f : M₁.obj (op U))
    (g : M₂.obj (op U)) :
    tensorGerm M₁ M₂ x V hV (res M₁ i f) (res M₂ i g) = tensorGerm M₁ M₂ x U (i.le hV) f g :=
  sectionGerm_res (M₁ ⊗ M₂) x i hV (f ⊗ₜ g)

lemma tensorGerm_indep {U V W W' : Opens X} (f : M₁.obj (op U)) (g : M₂.obj (op V))
    (iU : W ⟶ U) (iV : W ⟶ V) (iU' : W' ⟶ U) (iV' : W' ⟶ V) (hW : x ∈ W) (hW' : x ∈ W') :
    tensorGerm M₁ M₂ x W hW (res M₁ iU f) (res M₂ iV g) =
      tensorGerm M₁ M₂ x W' hW' (res M₁ iU' f) (res M₂ iV' g) := by
  let a : W ⊓ W' ⟶ W := homOfLE inf_le_left
  let b : W ⊓ W' ⟶ W' := homOfLE inf_le_right
  rw [← tensorGerm_res M₁ M₂ x a (Opens.mem_inf.2 ⟨hW, hW'⟩),
    ← tensorGerm_res M₁ M₂ x b (Opens.mem_inf.2 ⟨hW, hW'⟩),
    res_res M₁ iU a (a ≫ iU), res_res M₂ iV a (a ≫ iV), res_res M₁ iU' b (a ≫ iU),
    res_res M₂ iV' b (a ≫ iV)]

/-- For a fixed section `f` of `M₁` over `U`, the map `M₂ₓ → (M₁ ⊗ M₂)ₓ`, `gₓ ↦ (f ⊗ g)ₓ`. -/
noncomputable def tensorStalkInner (U : Opens X) (hU : x ∈ U) (f : M₁.obj (op U)) :
    moduleStalk M₂ x ⟶ moduleStalk (M₁ ⊗ M₂) x :=
  stalkDesc (fun V hV => AddCommGrpCat.ofHom
      ((tensorGerm M₁ M₂ x (U ⊓ V) (Opens.mem_inf.2 ⟨hU, hV⟩) (res M₁ (homOfLE inf_le_left) f)).comp
        (res M₂ (homOfLE inf_le_right))))
    (fun V V' i hV' => by
      ext g
      change M₂.obj (op V) at g
      change tensorGerm M₁ M₂ x (U ⊓ V') (Opens.mem_inf.2 ⟨hU, hV'⟩)
          (res M₁ (homOfLE inf_le_left) f)
          (res M₂ (homOfLE inf_le_right) (res M₂ i g)) =
        tensorGerm M₁ M₂ x (U ⊓ V) (Opens.mem_inf.2 ⟨hU, i.le hV'⟩) (res M₁ (homOfLE inf_le_left) f)
          (res M₂ (homOfLE inf_le_right) g)
      rw [res_res M₂ i (homOfLE inf_le_right) (homOfLE (inf_le_right.trans i.le))]
      exact tensorGerm_indep M₁ M₂ x f g _ _ _ _ _ _)

lemma tensorStalkInner_germ (U : Opens X) (hU : x ∈ U) (f : M₁.obj (op U)) {V W : Opens X}
    (hV : x ∈ V) (g : M₂.obj (op V)) (iU : W ⟶ U) (iV : W ⟶ V) (hW : x ∈ W) :
    tensorStalkInner M₁ M₂ x U hU f (sectionGerm M₂ x V hV g) =
      tensorGerm M₁ M₂ x W hW (res M₁ iU f) (res M₂ iV g) :=
  (stalkDesc_germ (P := M₂.presheaf) _ _ V hV g).trans
    (tensorGerm_indep M₁ M₂ x f g _ _ _ _ _ _)

/-- The bi-additive map `M₁ₓ → M₂ₓ → (M₁ ⊗ M₂)ₓ`. -/
noncomputable def tensorStalkOuter :
    moduleStalk M₁ x ⟶ AddCommGrpCat.of (moduleStalk M₂ x →+ moduleStalk (M₁ ⊗ M₂) x) :=
  stalkDesc (fun U hU => AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun f => (tensorStalkInner M₁ M₂ x U hU f).hom) (fun f f' => by
        refine moduleStalk_addHom_ext M₂ x (fun V hV g => ?_)
        rw [AddMonoidHom.add_apply]
        rw [tensorStalkInner_germ M₁ M₂ x U hU _ hV g (homOfLE inf_le_left)
            (homOfLE inf_le_right) (Opens.mem_inf.2 ⟨hU, hV⟩),
          tensorStalkInner_germ M₁ M₂ x U hU f hV g (homOfLE inf_le_left)
            (homOfLE inf_le_right) (Opens.mem_inf.2 ⟨hU, hV⟩),
          tensorStalkInner_germ M₁ M₂ x U hU f' hV g (homOfLE inf_le_left)
            (homOfLE inf_le_right) (Opens.mem_inf.2 ⟨hU, hV⟩), map_add, map_add,
          AddMonoidHom.add_apply])))
    (fun U U' i hU' => by
      refine AddCommGrpCat.ext (fun f => ?_)
      change M₁.obj (op U) at f
      change (tensorStalkInner M₁ M₂ x U' hU' (res M₁ i f)).hom =
        (tensorStalkInner M₁ M₂ x U (i.le hU') f).hom
      refine moduleStalk_addHom_ext M₂ x (fun V hV g => ?_)
      change tensorStalkInner M₁ M₂ x U' hU' (res M₁ i f) (sectionGerm M₂ x V hV g) =
        tensorStalkInner M₁ M₂ x U (i.le hU') f (sectionGerm M₂ x V hV g)
      rw [tensorStalkInner_germ M₁ M₂ x U' hU' _ hV g (homOfLE inf_le_left)
          (homOfLE inf_le_right) (Opens.mem_inf.2 ⟨hU', hV⟩),
        tensorStalkInner_germ M₁ M₂ x U (i.le hU') f hV g (homOfLE inf_le_left ≫ i)
          (homOfLE inf_le_right) (Opens.mem_inf.2 ⟨hU', hV⟩),
        res_res M₁ i (homOfLE inf_le_left) (homOfLE inf_le_left ≫ i)])

/-- The bi-additive pairing `M₁ₓ × M₂ₓ → (M₁ ⊗ M₂)ₓ`. -/
noncomputable def tensorStalkPairing :
    moduleStalk M₁ x →+ moduleStalk M₂ x →+ moduleStalk (M₁ ⊗ M₂) x :=
  (tensorStalkOuter M₁ M₂ x).hom

lemma tensorStalkPairing_germ {U V W : Opens X} (hU : x ∈ U) (f : M₁.obj (op U)) (hV : x ∈ V)
    (g : M₂.obj (op V)) (iU : W ⟶ U) (iV : W ⟶ V) (hW : x ∈ W) :
    tensorStalkPairing M₁ M₂ x (sectionGerm M₁ x U hU f) (sectionGerm M₂ x V hV g) =
      tensorGerm M₁ M₂ x W hW (res M₁ iU f) (res M₂ iV g) := by
  have h : tensorStalkPairing M₁ M₂ x (sectionGerm M₁ x U hU f) =
      (tensorStalkInner M₁ M₂ x U hU f).hom :=
    stalkDesc_germ (P := M₁.presheaf) _ _ U hU f
  rw [h]
  exact tensorStalkInner_germ M₁ M₂ x U hU f hV g iU iV hW

lemma tensorStalkPairing_germ_self {W : Opens X} (hW : x ∈ W) (f : M₁.obj (op W))
    (g : M₂.obj (op W)) :
    tensorStalkPairing M₁ M₂ x (sectionGerm M₁ x W hW f) (sectionGerm M₂ x W hW g) =
      tensorGerm M₁ M₂ x W hW f g := by
  rw [tensorStalkPairing_germ M₁ M₂ x hW f hW g (𝟙 W) (𝟙 W) hW, res_id, res_id]

lemma tensorStalkPairing_balanced (r : ringSheafStalk R x) (a : moduleStalk M₁ x)
    (b : moduleStalk M₂ x) :
    tensorStalkPairing M₁ M₂ x (r • a) b = tensorStalkPairing M₁ M₂ x a (r • b) := by
  obtain ⟨V, hV, g, rfl⟩ := exists_sectionGerm M₂ x b
  obtain ⟨U, hUV, hU, f, rfl⟩ := exists_le_sectionGerm M₁ x a hV
  obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm x r hU
  rw [← sectionGerm_res M₁ x (homOfLE hWU) hW f,
    ← sectionGerm_res M₂ x (homOfLE (hWU.trans hUV)) hW g,
    ← sectionGerm_smul, ← sectionGerm_smul, tensorStalkPairing_germ_self,
    tensorStalkPairing_germ_self, tensorGerm_apply, tensorGerm_apply]
  exact congrArg (sectionGerm (M₁ ⊗ M₂) x W hW) (TensorProduct.smul_tmul _ _ _)

/-- The inverse comparison map `M₁ₓ ⊗ M₂ₓ → (M₁ ⊗ M₂)ₓ`. -/
noncomputable def tensorToPresheafTensorStalk :
    moduleStalk M₁ x ⊗[ringSheafStalk R x] moduleStalk M₂ x →+ moduleStalk (M₁ ⊗ M₂) x :=
  TensorProduct.liftAddHom (tensorStalkPairing M₁ M₂ x) (tensorStalkPairing_balanced M₁ M₂ x)

lemma tensorToPresheafTensorStalk_tmul (a : moduleStalk M₁ x) (b : moduleStalk M₂ x) :
    tensorToPresheafTensorStalk M₁ M₂ x (a ⊗ₜ b) = tensorStalkPairing M₁ M₂ x a b :=
  TensorProduct.liftAddHom_tmul _ _ _ _

lemma tensorStalkComponent_smul (W : Opens X) (hW : x ∈ W)
    (c : (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op W))
    (t : M₁.obj (op W) ⊗[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op W)] M₂.obj (op W)) :
    tensorStalkComponent M₁ M₂ x W hW (c • t) =
      TopCat.Presheaf.germ R.obj W x hW c • tensorStalkComponent M₁ M₂ x W hW t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul f g =>
    rw [TensorProduct.smul_tmul', tensorStalkComponent_tmul, tensorStalkComponent_tmul,
      sectionGerm_smul, TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]

lemma presheafTensorStalkToTensor_smul (r : ringSheafStalk R x) (s : moduleStalk (M₁ ⊗ M₂) x) :
    presheafTensorStalkToTensor M₁ M₂ x (r • s) = r • presheafTensorStalkToTensor M₁ M₂ x s := by
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm (M₁ ⊗ M₂) x s
  obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm x r hU
  rw [← sectionGerm_res (M₁ ⊗ M₂) x (homOfLE hWU) hW t, ← sectionGerm_smul]
  exact (presheafTensorStalkToTensor_germ M₁ M₂ x W hW _).trans
    ((tensorStalkComponent_smul M₁ M₂ x W hW c _).trans
      (congrArg (TopCat.Presheaf.germ R.obj W x hW c • ·)
        (presheafTensorStalkToTensor_germ M₁ M₂ x W hW _).symm))

lemma tensorToPresheafTensorStalk_comp_left (s : moduleStalk (M₁ ⊗ M₂) x) :
    tensorToPresheafTensorStalk M₁ M₂ x (presheafTensorStalkToTensor M₁ M₂ x s) = s := by
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm (M₁ ⊗ M₂) x s
  change M₁.obj (op U) ⊗[(R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)] M₂.obj (op U) at t
  rw [presheafTensorStalkToTensor_germ]
  induction t using TensorProduct.induction_on with
  | zero => exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
  | tmul f g =>
    rw [tensorStalkComponent_tmul, tensorToPresheafTensorStalk_tmul,
      tensorStalkPairing_germ_self, tensorGerm_apply]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    exact (map_add _ _ _).symm

lemma presheafTensorStalkToTensor_comp_right
    (z : moduleStalk M₁ x ⊗[ringSheafStalk R x] moduleStalk M₂ x) :
    presheafTensorStalkToTensor M₁ M₂ x (tensorToPresheafTensorStalk M₁ M₂ x z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b =>
    obtain ⟨V, hV, g, rfl⟩ := exists_sectionGerm M₂ x b
    obtain ⟨U, hU, f, rfl⟩ := exists_sectionGerm M₁ x a
    have hW : x ∈ U ⊓ V := Opens.mem_inf.2 ⟨hU, hV⟩
    rw [tensorToPresheafTensorStalk_tmul,
      tensorStalkPairing_germ M₁ M₂ x hU f hV g (homOfLE inf_le_left) (homOfLE inf_le_right) hW,
      tensorGerm_apply, presheafTensorStalkToTensor_germ, tensorStalkComponent_tmul,
      sectionGerm_res, sectionGerm_res]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The stalk of the presheaf tensor product is the tensor product of the stalks. -/
noncomputable def presheafTensorStalkIso :
    moduleStalk (M₁ ⊗ M₂) x ≃ₗ[ringSheafStalk R x]
      (moduleStalk M₁ x ⊗[ringSheafStalk R x] moduleStalk M₂ x) where
  toFun := presheafTensorStalkToTensor M₁ M₂ x
  map_add' := map_add _
  map_smul' := presheafTensorStalkToTensor_smul M₁ M₂ x
  invFun := tensorToPresheafTensorStalk M₁ M₂ x
  left_inv := tensorToPresheafTensorStalk_comp_left M₁ M₂ x
  right_inv := presheafTensorStalkToTensor_comp_right M₁ M₂ x

end PresheafTensorStalk

section SheafTensorStalk

variable (F G : SheafOfModules.{u} (ringCatSheafOf R)) (x : X)

/-- The map on stalks induced by the sheafification unit of the presheaf tensor product. -/
noncomputable def moduleSheafTensorUnitStalk :
    moduleStalk (moduleSheafTensorPresheaf F G) x →+ moduleStalk (moduleSheafTensor F G).val x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (moduleSheafTensorPresheaf F G).presheaf)).hom

lemma moduleSheafTensorUnitStalk_bijective :
    Function.Bijective (moduleSheafTensorUnitStalk F G x) := by
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    (moduleSheafTensorPresheaf F G).presheaf
  exact ConcreteCategory.bijective_of_isIso _

lemma moduleSheafTensorUnitStalk_germ (W : Opens X) (hW : x ∈ W)
    (t : (moduleSheafTensorPresheaf F G).obj (op W)) :
    moduleSheafTensorUnitStalk F G x (sectionGerm (moduleSheafTensorPresheaf F G) x W hW t) =
      sectionGerm (moduleSheafTensor F G).val x W hW ((moduleSheafTensorUnit F G).app (op W) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) W x hW
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (moduleSheafTensorPresheaf F G).presheaf) t

lemma moduleSheafTensorUnitStalk_smul (r : ringSheafStalk R x)
    (s : moduleStalk (moduleSheafTensorPresheaf F G) x) :
    moduleSheafTensorUnitStalk F G x (r • s) = r • moduleSheafTensorUnitStalk F G x s := by
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm (moduleSheafTensorPresheaf F G) x s
  obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm x r hU
  rw [← sectionGerm_res (moduleSheafTensorPresheaf F G) x (homOfLE hWU) hW t,
    ← sectionGerm_smul, moduleSheafTensorUnitStalk_germ, moduleSheafTensorUnitStalk_germ,
    ← sectionGerm_smul]
  exact congrArg (sectionGerm (moduleSheafTensor F G).val x W hW)
    (((moduleSheafTensorUnit F G).app (op W)).hom.map_smul c _)

/-- The stalk map of the sheafification unit, as an `𝒪_{X,x}`-linear equivalence. -/
noncomputable def moduleSheafTensorUnitStalkEquiv :
    moduleStalk (moduleSheafTensorPresheaf F G) x ≃ₗ[ringSheafStalk R x]
      moduleStalk (moduleSheafTensor F G).val x :=
  LinearEquiv.ofBijective
    { toFun := moduleSheafTensorUnitStalk F G x
      map_add' := map_add _
      map_smul' := moduleSheafTensorUnitStalk_smul F G x }
    (moduleSheafTensorUnitStalk_bijective F G x)

end SheafTensorStalk

end ModuleSheafTensor

section SheafTensorStalk

variable (F G : SheafOfModules.{u} (ringCatSheafOf R)) (x : X)

/-- **Stalks of a tensor product.** The canonical isomorphism
`(F ⊗_{𝒪_X} G)ₓ ≅ Fₓ ⊗_{𝒪_{X,x}} Gₓ` of `𝒪_{X,x}`-modules. -/
noncomputable def moduleSheafTensorStalkIso :
    moduleStalk (moduleSheafTensor F G).val x ≃ₗ[ringSheafStalk R x]
      (moduleStalk F.val x ⊗[ringSheafStalk R x] moduleStalk G.val x) :=
  (moduleSheafTensorUnitStalkEquiv F G x).symm.trans (presheafTensorStalkIso F.val G.val x)

theorem moduleSheafTensorStalkIso_germ (U : Opens X) (hU : x ∈ U) (f : F.val.obj (op U))
    (g : G.val.obj (op U)) :
    moduleSheafTensorStalkIso F G x
        (TopCat.Presheaf.germ (moduleSheafTensor F G).val.presheaf U x hU
          ((moduleSheafTensorBilinear F G).app (op U) f g)) =
      TopCat.Presheaf.germ F.val.presheaf U x hU f ⊗ₜ
        TopCat.Presheaf.germ G.val.presheaf U x hU g := by
  have h : TopCat.Presheaf.germ (moduleSheafTensor F G).val.presheaf U x hU
      ((moduleSheafTensorBilinear F G).app (op U) f g) =
      moduleSheafTensorUnitStalkEquiv F G x
        (sectionGerm (moduleSheafTensorPresheaf F G) x U hU (f ⊗ₜ g)) :=
    (moduleSheafTensorUnitStalk_germ F G x U hU _).symm
  rw [h, moduleSheafTensorStalkIso, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact (presheafTensorStalkToTensor_germ F.val G.val x U hU _).trans
    (tensorStalkComponent_tmul F.val G.val x U hU f g)

end SheafTensorStalk

end Hartshorne
