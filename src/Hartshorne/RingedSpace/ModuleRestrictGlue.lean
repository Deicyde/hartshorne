/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtRestrict
import Hartshorne.RingedSpace.ModuleGluing

/-!
# Gluing morphisms of modules restricted to open subspaces

Let `(X, 𝒪_X)` be a ringed space with commutative structure sheaf and `{V k}` an open cover of `X`.
Morphisms `ψ k : E|_{V k} ⟶ T|_{V k}` of modules on the open subspaces `V k` that agree on overlaps
(`Hartshorne.Ringed.RestrictGlue.Compatible`, stated on sections over the opens of `X` contained in
`V k ∩ V l`) glue to a morphism `E ⟶ T` (`Hartshorne.Ringed.RestrictGlue.glueHom`, restricting to
`ψ k` by `glueHom_restrict`); morphisms agreeing on every `V k` are equal
(`hom_ext_of_moduleRestrict`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

/- Sections of a restricted module are only definitionally sections of the original module. -/
set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Ringed

namespace RestrictGlue

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The open of the subspace `V` cut out by an open `U` of `X`. -/
abbrev subOpen (V U : Opens X) : Opens ((Opens.toTopCat X).obj V) :=
  (Opens.map V.inclusion').obj U

/-- For `U ⊆ V`, the open `subOpen V U` of the subspace `V` has image `U`. -/
lemma functor_obj_subOpen {V U : Opens X} (h : U ≤ V) :
    V.isOpenEmbedding.functor.obj (subOpen V U) = U := by
  rw [Opens.functor_map_eq_inf]
  exact inf_eq_left.mpr h

/-- Restriction maps compose. -/
lemma map_map (M : SheafOfModules.{u} (ringCatSheafOf R)) {U₁ U₂ U₃ : Opens X} (h₁ : U₂ ≤ U₁)
    (h₂ : U₃ ≤ U₂) (x : M.val.obj (op U₁)) :
    M.val.map (homOfLE h₂).op (M.val.map (homOfLE h₁).op x) =
      M.val.map (homOfLE (h₂.trans h₁)).op x :=
  ModuleGluing.mapX_map _ M.val _ _ _ x

/-- Restriction from an open to itself is the identity. -/
lemma map_self (M : SheafOfModules.{u} (ringCatSheafOf R)) {U : Opens X} (h : U ≤ U)
    (x : M.val.obj (op U)) : M.val.map (homOfLE h).op x = x := by
  rw [ModuleGluing.opensOp_hom_ext (homOfLE h).op (𝟙 (op U)), PresheafOfModules.map_id]
  rfl

variable {E T : SheafOfModules.{u} (ringCatSheafOf R)}

/-- A morphism `E|_V ⟶ T|_V` evaluated on sections over an open `U ⊆ V` of `X`. -/
noncomputable def localApp {V : Opens X}
    (ψ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T) {U : Opens X} (h : U ≤ V)
    (x : E.val.obj (op U)) : T.val.obj (op U) :=
  T.val.map (homOfLE (functor_obj_subOpen h).ge).op
    (ψ.val.app (op (subOpen V U)) (E.val.map (homOfLE (functor_obj_subOpen h).le).op x))

/-- `localApp` commutes with restriction to smaller opens. -/
lemma localApp_naturality {V : Opens X}
    (ψ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T) {U U' : Opens X} (h : U ≤ V)
    (h' : U' ≤ U) (x : E.val.obj (op U)) :
    T.val.map (homOfLE h').op (localApp ψ h x) =
      localApp ψ (h'.trans h) (E.val.map (homOfLE h').op x) := by
  have hm : subOpen V U' ≤ subOpen V U := (Opens.map V.inclusion').monotone h'
  have hc : V.isOpenEmbedding.functor.obj (subOpen V U') ≤
      V.isOpenEmbedding.functor.obj (subOpen V U) := V.isOpenEmbedding.isOpenMap.functor.monotone hm
  have hn : ψ.val.app (op (subOpen V U'))
      (E.val.map (homOfLE hc).op (E.val.map (homOfLE (functor_obj_subOpen h).le).op x)) =
      T.val.map (homOfLE hc).op (ψ.val.app (op (subOpen V U))
        (E.val.map (homOfLE (functor_obj_subOpen h).le).op x)) :=
    PresheafOfModules.naturality_apply ψ.val (homOfLE hm).op _
  simp only [localApp]
  rw [map_map, map_map, ← map_map E (functor_obj_subOpen h).le hc, hn, map_map]

/-- `localApp` of a restricted global morphism is the morphism on sections. -/
lemma localApp_map {V : Opens X} (φ : E ⟶ T) {U : Opens X} (h : U ≤ V) (x : E.val.obj (op U)) :
    localApp ((moduleRestrict V).map φ) h x = φ.val.app (op U) x := by
  have hn : φ.val.app (op (V.isOpenEmbedding.functor.obj (subOpen V U)))
      (E.val.map (homOfLE (functor_obj_subOpen h).le).op x) =
      T.val.map (homOfLE (functor_obj_subOpen h).le).op (φ.val.app (op U) x) :=
    PresheafOfModules.naturality_apply φ.val _ x
  simp only [localApp]
  erw [hn]
  rw [map_map, map_self]

/-- `localApp` of a composite is the composite of the `localApp`s. -/
lemma localApp_comp {Z : SheafOfModules.{u} (ringCatSheafOf R)} {V : Opens X}
    (φ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T)
    (χ : (moduleRestrict V).obj T ⟶ (moduleRestrict V).obj Z) {U : Opens X} (h : U ≤ V)
    (x : E.val.obj (op U)) : localApp (φ ≫ χ) h x = localApp χ h (localApp φ h x) := by
  simp only [localApp]
  rw [map_map T, map_self]
  rfl

/-- `localApp` sends `0` to `0`. -/
lemma localApp_zero {V : Opens X}
    (ψ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T) {U : Opens X} (h : U ≤ V) :
    localApp ψ h 0 = 0 := by
  simp only [localApp, map_zero]

/-- `localApp` is additive. -/
lemma localApp_add {V : Opens X}
    (ψ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T) {U : Opens X} (h : U ≤ V)
    (x y : E.val.obj (op U)) : localApp ψ h (x + y) = localApp ψ h x + localApp ψ h y := by
  simp only [localApp, map_add]

/-- `localApp` is `𝒪_X(U)`-linear. -/
lemma localApp_smul {V : Opens X}
    (ψ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T) {U : Opens X} (h : U ≤ V)
    (a : R.obj.obj (op U)) (x : E.val.obj (op U)) :
    localApp ψ h (a • x) = a • localApp ψ h x := by
  simp only [localApp]
  erw [PresheafOfModules.map_smul, (ψ.val.app _).hom.map_smul, PresheafOfModules.map_smul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact congrArg (fun g => ((ringCatSheafOf R).obj.map g).hom a)
    (ModuleGluing.opensOp_hom_ext _ (𝟙 _)) |>.trans (by rw [CategoryTheory.Functor.map_id]; rfl)



/-- The inverse of an isomorphism of modules is inverse on sections. -/
lemma app_inv_app {V : Opens X} {A B : SheafOfModules.{u} (ringCatSheafOf (restrictRingSheaf R V))}
    (ψ : A ⟶ B) [IsIso ψ] (W : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ) (z : B.val.obj W) :
    ψ.val.app W ((inv ψ).val.app W z) = z := by
  rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
    IsIso.inv_hom_id]
  rfl

/-- The inverse of an isomorphism of modules is inverse on sections. -/
lemma inv_app_app {V : Opens X} {A B : SheafOfModules.{u} (ringCatSheafOf (restrictRingSheaf R V))}
    (ψ : A ⟶ B) [IsIso ψ] (W : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ) (z : A.val.obj W) :
    (inv ψ).val.app W (ψ.val.app W z) = z := by
  rw [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val,
    IsIso.hom_inv_id]
  rfl

/-- `localApp` of the inverse of an isomorphism is a right inverse. -/
lemma localApp_localApp_inv {V : Opens X}
    (ψ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T) [IsIso ψ] {U : Opens X}
    (h : U ≤ V) (y : T.val.obj (op U)) : localApp ψ h (localApp (inv ψ) h y) = y := by
  simp only [localApp]
  rw [map_map E, map_self, app_inv_app, map_map, map_self]

/-- `localApp` of the inverse of an isomorphism is a left inverse. -/
lemma localApp_inv_localApp {V : Opens X}
    (ψ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T) [IsIso ψ] {U : Opens X}
    (h : U ≤ V) (x : E.val.obj (op U)) : localApp (inv ψ) h (localApp ψ h x) = x := by
  simp only [localApp]
  rw [map_map T, map_self, inv_app_app, map_map, map_self]

section Glue

variable {κ : Type u} (V : κ → Opens X)
  (ψ : ∀ k, (moduleRestrict (V k)).obj E ⟶ (moduleRestrict (V k)).obj T)

/-- Local morphisms `E|_{V k} ⟶ T|_{V k}` agree on overlaps: on sections over every open
`U ⊆ V k ∩ V l` they induce the same map. -/
def Compatible : Prop :=
  ∀ k l (U : Opens X) (h₁ : U ≤ V k) (h₂ : U ≤ V l) (x : E.val.obj (op U)),
    localApp (ψ k) h₁ x = localApp (ψ l) h₂ x

variable {V} (hcov : ⊤ ≤ iSup V)

include hcov in
/-- Every open is covered by its intersections with the members of the cover. -/
lemma le_iSup_inf (U : Opens X) : U ≤ iSup fun k => U ⊓ V k := by
  rw [← inf_iSup_eq]
  exact le_inf le_rfl (le_top.trans hcov)

variable {ψ} (hψ : Compatible V ψ)

include hcov hψ in
/-- The local images of a section glue. -/
lemma exists_glue (U : Opens X) (x : E.val.obj (op U)) :
    ∃ s : T.val.obj (op U), ∀ k, T.val.map (homOfLE (inf_le_left : U ⊓ V k ≤ U)).op s =
      localApp (ψ k) inf_le_right (E.val.map (homOfLE (inf_le_left : U ⊓ V k ≤ U)).op x) := by
  refine ModuleGluing.sheaf_glue _ T (fun k => U ⊓ V k) (fun _ => inf_le_left)
    (le_iSup_inf hcov U) _ fun k l => ?_
  dsimp only
  rw [localApp_naturality, localApp_naturality, map_map, map_map]
  exact hψ k l _ _ _ _

include hcov in
/-- Sections agreeing on the members of the cover are equal. -/
lemma sections_ext (U : Opens X) (s t : T.val.obj (op U))
    (h : ∀ k, T.val.map (homOfLE (inf_le_left : U ⊓ V k ≤ U)).op s =
      T.val.map (homOfLE (inf_le_left : U ⊓ V k ≤ U)).op t) : s = t :=
  ModuleGluing.sheaf_ext _ T (fun k => U ⊓ V k) (fun _ => inf_le_left) (le_iSup_inf hcov U) s t h

/-- The glued map on sections over `U`. -/
noncomputable def glueApp (U : Opens X) (x : E.val.obj (op U)) : T.val.obj (op U) :=
  (exists_glue hcov hψ U x).choose

/-- The glued section restricts to the local images. -/
lemma glueApp_spec (U : Opens X) (x : E.val.obj (op U)) (k : κ) :
    T.val.map (homOfLE (inf_le_left : U ⊓ V k ≤ U)).op (glueApp hcov hψ U x) =
      localApp (ψ k) inf_le_right (E.val.map (homOfLE (inf_le_left : U ⊓ V k ≤ U)).op x) :=
  (exists_glue hcov hψ U x).choose_spec k

/-- The glued map is additive. -/
lemma glueApp_add (U : Opens X) (x y : E.val.obj (op U)) :
    glueApp hcov hψ U (x + y) = glueApp hcov hψ U x + glueApp hcov hψ U y :=
  sections_ext hcov U _ _ fun k => by
    rw [map_add, glueApp_spec, glueApp_spec, glueApp_spec, map_add, localApp_add]

/-- The glued map is linear. -/
lemma glueApp_smul (U : Opens X) (a : R.obj.obj (op U)) (x : E.val.obj (op U)) :
    glueApp hcov hψ U (a • x) = a • glueApp hcov hψ U x :=
  sections_ext hcov U _ _ fun k => by
    erw [T.val.map_smul, glueApp_spec, glueApp_spec, E.val.map_smul, localApp_smul]

/-- The glued map commutes with restriction. -/
lemma glueApp_naturality {U U' : Opens X} (h : U' ≤ U) (x : E.val.obj (op U)) :
    T.val.map (homOfLE h).op (glueApp hcov hψ U x) =
      glueApp hcov hψ U' (E.val.map (homOfLE h).op x) :=
  sections_ext hcov U' _ _ fun k => by
    rw [glueApp_spec, map_map, ← map_map T (inf_le_left : U ⊓ V k ≤ U)
      (inf_le_inf_right (V k) h : U' ⊓ V k ≤ U ⊓ V k), glueApp_spec, localApp_naturality,
      map_map, map_map]

/-- Over an open contained in `V k`, the glued map is the map induced by `ψ k`. -/
lemma glueApp_eq {U : Opens X} {k : κ} (h : U ≤ V k) (x : E.val.obj (op U)) :
    glueApp hcov hψ U x = localApp (ψ k) h x := by
  have h0 : U ≤ U ⊓ V k := le_inf le_rfl h
  rw [← map_self T (le_refl U) (glueApp hcov hψ U x),
    ← map_map T (inf_le_left : U ⊓ V k ≤ U) h0, glueApp_spec, localApp_naturality, map_map,
    map_self]

/-- **Gluing morphisms of modules along an open cover.** Local morphisms `E|_{V k} ⟶ T|_{V k}`
that agree on overlaps glue to a morphism `E ⟶ T`. -/
noncomputable def glueHom : E ⟶ T :=
  ⟨{ app U := ModuleCat.ofHom (X := E.val.obj U) (Y := T.val.obj U)
      { toFun := glueApp hcov hψ U.unop
        map_add' := glueApp_add hcov hψ U.unop
        map_smul' := glueApp_smul hcov hψ U.unop }
     naturality {U U'} i := by
       ext x
       exact (glueApp_naturality hcov hψ (leOfHom i.unop) x).symm }⟩

/-- The glued morphism on sections. -/
lemma glueHom_app (U : Opens X) (x : E.val.obj (op U)) :
    (glueHom hcov hψ).val.app (op U) x = glueApp hcov hψ U x :=
  rfl

/-- The image of an open of the subspace `V` is contained in `V`. -/
lemma functor_obj_le {V : Opens X} (W : Opens ((Opens.toTopCat X).obj V)) :
    V.isOpenEmbedding.functor.obj W ≤ V := by
  conv_rhs => rw [← Opens.isOpenEmbedding_obj_top V]
  exact V.isOpenEmbedding.isOpenMap.functor.monotone le_top

/-- `localApp` over the image of an open `W` of the subspace is evaluation at `W`. -/
lemma localApp_eq_app {V : Opens X}
    (φ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T)
    (W : Opens ((Opens.toTopCat X).obj V)) (x : E.val.obj (op (V.isOpenEmbedding.functor.obj W))) :
    localApp φ (functor_obj_le W) x = φ.val.app (op W) x := by
  have hW : subOpen V (V.isOpenEmbedding.functor.obj W) = W := Opens.map_functor_eq W
  have hc : V.isOpenEmbedding.functor.obj (subOpen V (V.isOpenEmbedding.functor.obj W)) ≤
      V.isOpenEmbedding.functor.obj W := V.isOpenEmbedding.isOpenMap.functor.monotone hW.le
  have hn : φ.val.app (op (subOpen V (V.isOpenEmbedding.functor.obj W)))
      (E.val.map (homOfLE hc).op x) = T.val.map (homOfLE hc).op (φ.val.app (op W) x) :=
    PresheafOfModules.naturality_apply φ.val (homOfLE hW.le).op x
  simp only [localApp]
  rw [hn, map_map, map_self]


/-- `localApp` computed through any open `c` of the subspace `V` whose image is `U`. -/
lemma localApp_eq_of_functor_obj_eq {V : Opens X}
    (φ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T) {U : Opens X} (h : U ≤ V)
    (c : Opens ((Opens.toTopCat X).obj V)) (hc : V.isOpenEmbedding.functor.obj c = U)
    (x : E.val.obj (op U)) :
    localApp φ h x = T.val.map (homOfLE hc.ge).op (φ.val.app (op c)
      (E.val.map (homOfLE hc.le).op x)) := by
  have hW : subOpen V U = c := by
    rw [← hc]
    exact Opens.map_functor_eq c
  subst hW
  rfl

/-- The glued morphism restricts to the given local morphisms. -/
theorem glueHom_restrict (k : κ) : (moduleRestrict (V k)).map (glueHom hcov hψ) = ψ k := by
  apply SheafOfModules.hom_ext
  ext W x : 3
  exact (glueApp_eq hcov hψ (functor_obj_le W.unop) x).trans (localApp_eq_app (ψ k) W.unop x)

include hcov in
/-- Morphisms of modules that agree on the members of an open cover are equal. -/
theorem hom_ext_of_moduleRestrict {φ₁ φ₂ : E ⟶ T}
    (h : ∀ k, (moduleRestrict (V k)).map φ₁ = (moduleRestrict (V k)).map φ₂) : φ₁ = φ₂ := by
  apply SheafOfModules.hom_ext
  ext U x : 3
  refine sections_ext hcov U.unop _ _ fun k => ?_
  have e₁ := localApp_map (V := V k) φ₁ (inf_le_right : U.unop ⊓ V k ≤ V k)
    (E.val.map (homOfLE (inf_le_left : U.unop ⊓ V k ≤ U.unop)).op x)
  have e₂ := localApp_map (V := V k) φ₂ (inf_le_right : U.unop ⊓ V k ≤ V k)
    (E.val.map (homOfLE (inf_le_left : U.unop ⊓ V k ≤ U.unop)).op x)
  rw [h k] at e₁
  erw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  exact e₁.symm.trans e₂


/-- Glued isomorphisms form an isomorphism. -/
theorem isIso_glueHom (hiso : ∀ k, IsIso (ψ k)) : IsIso (glueHom hcov hψ) := by
  have hψ' : Compatible V (fun k => inv (ψ k)) := fun k l U h₁ h₂ y => by
    have hinj : Function.Injective (localApp (ψ k) h₁) := fun a b hab => by
      rw [← localApp_inv_localApp (ψ k) h₁ a, hab, localApp_inv_localApp]
    apply hinj
    rw [localApp_localApp_inv, hψ k l U h₁ h₂, localApp_localApp_inv]
  refine ⟨⟨glueHom hcov hψ', hom_ext_of_moduleRestrict hcov fun k => ?_,
    hom_ext_of_moduleRestrict hcov fun k => ?_⟩⟩
  · rw [Functor.map_comp, glueHom_restrict, glueHom_restrict, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  · rw [Functor.map_comp, glueHom_restrict, glueHom_restrict, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]

end Glue

end RestrictGlue

end Ringed

end Hartshorne
