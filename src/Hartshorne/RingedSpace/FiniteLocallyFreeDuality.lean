/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.ModuleSheafHom
import Hartshorne.RingedSpace.LocallyFree

/-!
# Duality for finite locally free sheaves on a ringed space

Hartshorne, *Algebraic Geometry*, II, Exercise 5.1(a)–(c).

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`; `𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)`. For an `𝒪_X`-module `E` write
`E^∨ = ℋom(E, 𝒪_X)` (`Hartshorne.Ringed.moduleSheafDual`), where `ℋom` is
`Hartshorne.Ringed.moduleSheafHom` and `⊗` is `Hartshorne.moduleSheafTensor`. A *finite locally
free* module is one that is locally free of finite rank (`Hartshorne.Ringed.IsFiniteLocallyFree`):
every point has an open neighbourhood `U` with `E|_U ≅ 𝒪_U^n` for some `n`. We prove:

* (a) the canonical evaluation map `E ⟶ E^∨∨` (`moduleSheafDoubleDualMap`) is natural in `E`
  and, for finite locally free `E`, an isomorphism (`moduleSheafDoubleDualMap_isIso`,
  `moduleSheafDoubleDualIso`);
* (b) the canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)`, induced by `(ψ, f) ↦ (x ↦ ψ(x) f)`
  (`moduleSheafDualTensorMap`), is natural in `E` and `F` and, for finite locally free `E` and
  any `F`, an isomorphism (`moduleSheafDualTensorMap_isIso`, `moduleSheafDualTensorIso`);
* (c) for all `𝒪_X`-modules `E`, `F`, `G` there is a bijection
  `Hom(E ⊗ F, G) ≃ Hom(F, ℋom(E, G))` (`moduleSheafTensorHomAdjunction`), natural in `E`, `F`
  and `G`; it is additive, so an isomorphism of abelian groups
  (`moduleSheafTensorHomAddEquiv`). No finiteness is needed here.

The proofs of (a) and (b) are local. A *local frame* of `E` over an open `U` is a finite family
of sections `e_i ∈ E(U)` such that on every open `V ⊆ U` each section of `E` is uniquely an
`𝒪_X(V)`-linear combination of the restrictions `e_i|_V` (`IsLocalFrame`). The standard sections
of a finite free module on the opens of `U` form a frame, so a finite locally free module has
frames on an open cover (`exists_isLocalFrame_of_isFiniteLocallyFree`). Local morphisms out of
`E` over `V ⊆ U` are determined by, and can be prescribed through, their values on a frame;
hence the dual frame `e_i^∨` is a frame of `E^∨` (`IsLocalFrame.dual`). On opens inside `U`, the
double-dual map and the presheaf-level map `E^∨(V) ⊗ F(V) → ℋom(E, F)(V)` are then bijective,
and a morphism of sheaves that is bijective on all small enough opens around every point (or on
stalks) is an isomorphism.

For a scheme `X`, `X.Modules` is definitionally `SheafOfModules (ringCatSheafOf X.sheaf)`, so all
of this applies to schemes with `R := X.sheaf`; `Scheme.Modules.isFiniteLocallyFree_iff`
translates the finiteness hypothesis, and `Scheme.Modules.tensorHomAddEquiv` states (c) with Hom
groups in `X.Modules`.
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

/-- The sections of an `𝒪_X`-module over an open, as an abelian group, are a module over the
sections of `𝒪_X`. -/
scoped instance (M : SheafOfModules.{u} (ringCatSheafOf R)) (U : (Opens X)ᵒᵖ) :
    Module (R.obj.obj U) (M.val.presheaf.obj U) :=
  inferInstanceAs (Module (R.obj.obj U) (M.val.obj U))

/-- The morphism of underlying presheaves of abelian groups of a morphism of `𝒪_X`-modules. -/
noncomputable abbrev modulesMapPresheaf {A B : 𝓜} (φ : A ⟶ B) :
    A.val.presheaf ⟶ B.val.presheaf :=
  (PresheafOfModules.toPresheaf _).map φ.val

/-- A morphism of `𝒪_X`-modules on the sections over an open. -/
noncomputable abbrev sectionsMap {A B : 𝓜} (φ : A ⟶ B) (U : Opens X) : Γ(A, U) ⟶ Γ(B, U) :=
  (forget₂ _ _).map (φ.val.app (op U))

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

/-- For a section `ψ` of `ℋom(E, G)` over `W` and an open `V ⊆ W`, the linear map
`E(V) → G(V)` given by `ψ`. -/
noncomputable def moduleSheafHomEval {E G : 𝓜} {W : Opens X}
    (ψ : Γ(moduleSheafHom E G, W)) {V : Opens X} (h : V ≤ W) :
    Γ(E, V) →ₗ[𝒪(V)] Γ(G, V) :=
  ((moduleSheafHomOverSectionsAddEquiv E G W ψ).val.app (op (Over.mk (homOfLE h)))).hom

lemma moduleSheafHomEval_restrict {E G : 𝓜} {W W' V : Opens X}
    (ψ : Γ(moduleSheafHom E G, W)) (i : W' ≤ W) (h : V ≤ W') :
    moduleSheafHomEval ((moduleSheafHom E G).val.presheaf.map (homOfLE i).op ψ) h =
      moduleSheafHomEval ψ (h.trans i) := rfl

lemma moduleSheafHomEval_add {E G : 𝓜} {W V : Opens X}
    (ψ φ : Γ(moduleSheafHom E G, W)) (h : V ≤ W) :
    moduleSheafHomEval (ψ + φ) h = moduleSheafHomEval ψ h + moduleSheafHomEval φ h := rfl

lemma moduleSheafHomEval_smul {E G : 𝓜} {W V : Opens X}
    (r : 𝒪(W)) (ψ : Γ(moduleSheafHom E G, W)) (h : V ≤ W) (x : Γ(E, V)) :
    moduleSheafHomEval (r • ψ) h x = R.obj.map (homOfLE h).op r • moduleSheafHomEval ψ h x :=
  rfl

lemma moduleSheafHomEval_natural {E G : 𝓜} {W V V' : Opens X}
    (ψ : Γ(moduleSheafHom E G, W)) (h : V ≤ W) (i : V' ≤ V) (x : Γ(E, V)) :
    moduleSheafHomEval ψ (i.trans h) (E.val.presheaf.map (homOfLE i).op x) =
      G.val.presheaf.map (homOfLE i).op (moduleSheafHomEval ψ h x) := by
  let a : Over.mk (homOfLE (i.trans h)) ⟶ Over.mk (homOfLE h) := Over.homMk (homOfLE i)
  exact ConcreteCategory.congr_hom
    ((moduleSheafHomOverSectionsAddEquiv E G W ψ).val.naturality a.op) x

lemma moduleSheafHomEval_ext {E G : 𝓜} {W : Opens X}
    {ψ φ : Γ(moduleSheafHom E G, W)}
    (hψφ : ∀ (V : Opens X) (h : V ≤ W), moduleSheafHomEval ψ h = moduleSheafHomEval φ h) :
    ψ = φ := by
  apply (moduleSheafHomOverSectionsAddEquiv E G W).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  exact LinearMap.congr_fun (hψφ A.unop.left (leOfHom A.unop.hom)) x

/-- The section of `ℋom(E, G)` over `W` given by a family of linear maps `E(V) → G(V)`, `V ⊆ W`,
compatible with restriction. -/
noncomputable def moduleSheafHomMk {E G : 𝓜} {W : Opens X}
    (f : ∀ V : Opens X, V ≤ W → Γ(E, V) →ₗ[𝒪(V)] Γ(G, V))
    (hf : ∀ (V V' : Opens X) (hV : V ≤ W) (i : V' ≤ V) (x : Γ(E, V)),
      f V' (i.trans hV) (E.val.presheaf.map (homOfLE i).op x) =
        G.val.presheaf.map (homOfLE i).op (f V hV x)) :
    Γ(moduleSheafHom E G, W) :=
  (moduleSheafHomOverSectionsAddEquiv E G W).symm
    ⟨{ app A := ModuleCat.ofHom (X := (SheafOfModules.over E W).val.obj A)
          (Y := (SheafOfModules.over G W).val.obj A) (f A.unop.left (leOfHom A.unop.hom))
       naturality {A B} a := by
         ext x
         exact hf A.unop.left B.unop.left (leOfHom A.unop.hom) (leOfHom a.unop.left) x }⟩

lemma moduleSheafHomEval_mk {E G : 𝓜} {W : Opens X}
    (f : ∀ V : Opens X, V ≤ W → Γ(E, V) →ₗ[𝒪(V)] Γ(G, V))
    (hf : ∀ (V V' : Opens X) (hV : V ≤ W) (i : V' ≤ V) (x : Γ(E, V)),
      f V' (i.trans hV) (E.val.presheaf.map (homOfLE i).op x) =
        G.val.presheaf.map (homOfLE i).op (f V hV x)) {V : Opens X} (h : V ≤ W) :
    moduleSheafHomEval (moduleSheafHomMk f hf) h = f V h := rfl

private lemma modules_map_map (A : 𝓜) {U V W : Opens X} (i : V ≤ U) (j : W ≤ V)
    (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE j).op (A.val.presheaf.map (homOfLE i).op x) =
      A.val.presheaf.map (homOfLE (j.trans i)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma modules_map_id (A : 𝓜) {U : Opens X} (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE (le_refl U)).op x = x := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma ring_map_id {U : Opens X} (r : 𝒪(U)) :
    R.obj.map (homOfLE (le_refl U)).op r = r := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The morphism of `𝒪_X`-modules given by a family of linear maps on sections compatible with
restriction. -/
noncomputable def modulesHomMk {A B : 𝓜}
    (f : ∀ U : Opens X, Γ(A, U) →ₗ[𝒪(U)] Γ(B, U))
    (hf : ∀ (U V : Opens X) (i : V ≤ U) (x : Γ(A, U)),
      f V (A.val.presheaf.map (homOfLE i).op x) = B.val.presheaf.map (homOfLE i).op (f U x)) :
    A ⟶ B :=
  ⟨{ app U := ModuleCat.ofHom (X := A.val.obj U) (Y := B.val.obj U) (f U.unop)
     naturality {U V} i := by
       ext x
       exact hf U.unop V.unop (leOfHom i.unop) x }⟩

lemma modulesHomMk_app {A B : 𝓜} (f : ∀ U : Opens X, Γ(A, U) →ₗ[𝒪(U)] Γ(B, U))
    (hf : ∀ (U V : Opens X) (i : V ≤ U) (x : Γ(A, U)),
      f V (A.val.presheaf.map (homOfLE i).op x) = B.val.presheaf.map (homOfLE i).op (f U x))
    (U : Opens X) (x : Γ(A, U)) : sectionsMap (modulesHomMk f hf) U x = f U x := rfl

section Adjunction

variable {E F G : 𝓜}

/-- The local morphism `e ↦ β(e, f)` attached to a section `f` of `F`. -/
noncomputable def bilinearCurrySection (β : ModuleSheafBilinear E F G) (U : Opens X)
    (f : Γ(F, U)) :
    Γ(moduleSheafHom E G, U) :=
  moduleSheafHomMk (fun V h => (β.app (op V)).flip (F.val.presheaf.map (homOfLE h).op f))
    (by
      intro V V' hV i x
      change β.app (op V') (E.val.presheaf.map (homOfLE i).op x)
          (F.val.presheaf.map (homOfLE (i.trans hV)).op f) =
        G.val.presheaf.map (homOfLE i).op (β.app (op V) x (F.val.presheaf.map (homOfLE hV).op f))
      rw [← modules_map_map F hV i]
      exact (β.naturality (homOfLE i).op x _).symm)

lemma bilinearCurrySection_eval (β : ModuleSheafBilinear E F G) (U : Opens X) (f : Γ(F, U))
    {V : Opens X} (h : V ≤ U) (e : Γ(E, V)) :
    moduleSheafHomEval (bilinearCurrySection β U f) h e =
      β.app (op V) e (F.val.presheaf.map (homOfLE h).op f) := rfl

/-- The morphism `F ⟶ ℋom(E, G)`, `f ↦ (e ↦ β(e, f))`, attached to a bilinear map `β`. -/
noncomputable def bilinearCurry (β : ModuleSheafBilinear E F G) : F ⟶ moduleSheafHom E G :=
  modulesHomMk (fun U =>
    { toFun := bilinearCurrySection β U
      map_add' := fun f f' => moduleSheafHomEval_ext fun V h => by
        ext e
        change β.app (op V) e (F.val.presheaf.map (homOfLE h).op (f + f')) =
          β.app (op V) e (F.val.presheaf.map (homOfLE h).op f) +
            β.app (op V) e (F.val.presheaf.map (homOfLE h).op f')
        rw [map_add]
        exact map_add (β.app (op V) e) _ _
      map_smul' := fun r f => moduleSheafHomEval_ext fun V h => by
        ext e
        rw [RingHom.id_apply, moduleSheafHomEval_smul, bilinearCurrySection_eval,
          bilinearCurrySection_eval, modules_map_smul]
        exact map_smul (β.app (op V) e) _ _ })
    (fun U V i f => moduleSheafHomEval_ext fun W h => by
      ext e
      change β.app (op W) e
          (F.val.presheaf.map (homOfLE h).op (F.val.presheaf.map (homOfLE i).op f)) =
        β.app (op W) e (F.val.presheaf.map (homOfLE (h.trans i)).op f)
      rw [modules_map_map])

private lemma homUncurry_naturality (φ : F ⟶ moduleSheafHom E G) {U V : Opens X} (i : V ≤ U)
    (e : Γ(E, U)) (f : Γ(F, U)) :
    G.val.presheaf.map (homOfLE i).op (moduleSheafHomEval (sectionsMap φ U f) (le_refl U) e) =
      moduleSheafHomEval (sectionsMap φ V (F.val.presheaf.map (homOfLE i).op f)) (le_refl V)
        (E.val.presheaf.map (homOfLE i).op e) := by
  rw [← moduleSheafHomEval_natural]
  have h := ConcreteCategory.congr_hom ((modulesMapPresheaf φ).naturality (homOfLE i).op) f
  change sectionsMap φ V (F.val.presheaf.map (homOfLE i).op f) =
    (moduleSheafHom E G).val.presheaf.map (homOfLE i).op (sectionsMap φ U f) at h
  rw [h, moduleSheafHomEval_restrict]

private lemma homUncurry_smul (φ : F ⟶ moduleSheafHom E G) (U : Opens X) (r : 𝒪(U))
    (e : Γ(E, U)) (f : Γ(F, U)) :
    moduleSheafHomEval (sectionsMap φ U (r • f)) (le_refl U) e =
      r • moduleSheafHomEval (sectionsMap φ U f) (le_refl U) e := by
  rw [hom_app_smul, moduleSheafHomEval_smul, ring_map_id]

/-- The bilinear map `(e, f) ↦ φ(f)(e)` attached to `φ : F ⟶ ℋom(E, G)`. -/
noncomputable def homUncurry (φ : F ⟶ moduleSheafHom E G) : ModuleSheafBilinear E F G where
  app U := LinearMap.mk₂ _ (fun (e : Γ(E, U.unop)) (f : Γ(F, U.unop)) =>
      moduleSheafHomEval (sectionsMap φ U.unop f) (le_refl U.unop) e)
    (fun e e' f => map_add _ e e')
    (fun r e f => map_smul _ r e)
    (fun (e : Γ(E, U.unop)) (f f' : Γ(F, U.unop)) => by
      change moduleSheafHomEval (sectionsMap φ U.unop (f + f')) _ e = _
      rw [map_add]; rfl)
    (fun r e f => homUncurry_smul φ U.unop r e f)
  naturality {U V} i e f := homUncurry_naturality φ (leOfHom i.unop) e f

lemma bilinearCurry_app_eval (β : ModuleSheafBilinear E F G) (U : Opens X) (f : Γ(F, U))
    {V : Opens X} (h : V ≤ U) (e : Γ(E, V)) :
    moduleSheafHomEval (sectionsMap (bilinearCurry β) U f) h e =
      β.app (op V) e (F.val.presheaf.map (homOfLE h).op f) := rfl

/-- Bilinear maps `E × F → G` correspond to morphisms `F ⟶ ℋom(E, G)`. -/
noncomputable def bilinearCurryEquiv :
    ModuleSheafBilinear E F G ≃ (F ⟶ moduleSheafHom E G) where
  toFun := bilinearCurry
  invFun := homUncurry
  left_inv β := by
    ext U e f
    exact congrArg (β.app U e) (modules_map_id F (U := U.unop) f)
  right_inv φ := by
    refine modules_hom_ext fun U => ?_
    ext f
    refine moduleSheafHomEval_ext fun V h => ?_
    ext e
    change moduleSheafHomEval (sectionsMap φ V (F.val.presheaf.map (homOfLE h).op f))
        (le_refl V) e =
      moduleSheafHomEval (sectionsMap φ U f) h e
    have hn := ConcreteCategory.congr_hom ((modulesMapPresheaf φ).naturality (homOfLE h).op) f
    change sectionsMap φ V (F.val.presheaf.map (homOfLE h).op f) =
      (moduleSheafHom E G).val.presheaf.map (homOfLE h).op (sectionsMap φ U f) at hn
    rw [hn, moduleSheafHomEval_restrict]

variable (E F G) in
/-- **Hartshorne II, Exercise 5.1(c): the tensor–Hom adjunction.** For all `𝒪_X`-modules `E`, `F`,
`G` (Hartshorne assumes `E` finite locally free; not needed here), morphisms `E ⊗ F ⟶ G`
correspond bijectively to morphisms `F ⟶ ℋom(E, G)`: a morphism `φ` corresponds to
`f ↦ (e ↦ φ(e ⊗ f))`. -/
noncomputable def moduleSheafTensorHomAdjunction :
    (@Quiver.Hom 𝓜 _ (moduleSheafTensor E F) G) ≃ (F ⟶ moduleSheafHom E G) :=
  (moduleSheafTensorHomEquiv E F G).trans bilinearCurryEquiv

lemma moduleSheafTensorHomAdjunction_app_eval
    (φ : @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) G) (U : Opens X) (f : Γ(F, U))
    {V : Opens X} (h : V ≤ U) (e : Γ(E, V)) :
    moduleSheafHomEval (sectionsMap (moduleSheafTensorHomAdjunction E F G φ) U f) h e =
      sectionsMap φ V ((moduleSheafTensorBilinear E F).app (op V) e
        (F.val.presheaf.map (homOfLE h).op f)) :=
  rfl

/-- The tensor–Hom adjunction is natural in `G`. -/
lemma moduleSheafTensorHomAdjunction_naturality_target {G' : 𝓜}
    (φ : @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) G) (g : G ⟶ G') :
    moduleSheafTensorHomAdjunction E F G' (φ ≫ g) =
      moduleSheafTensorHomAdjunction E F G φ ≫ moduleSheafHomMap (𝟙 E) g := by
  refine modules_hom_ext fun U => ?_
  ext f
  refine moduleSheafHomEval_ext fun V h => ?_
  ext e
  rfl

/-- The tensor–Hom bijection is additive. -/
lemma moduleSheafTensorHomAdjunction_add (φ ψ : @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) G) :
    moduleSheafTensorHomAdjunction E F G (φ + ψ) =
      moduleSheafTensorHomAdjunction E F G φ + moduleSheafTensorHomAdjunction E F G ψ := by
  refine modules_hom_ext fun U => ?_
  ext f
  refine moduleSheafHomEval_ext fun V h => ?_
  ext e
  rfl

variable (E F G) in
/-- **Hartshorne II, Exercise 5.1(c): the tensor–Hom isomorphism of groups.** For all
`𝒪_X`-modules `E`, `F`, `G` (Hartshorne assumes `E` finite locally free; not needed here), the
bijection `moduleSheafTensorHomAdjunction` is additive, giving an isomorphism of abelian groups
`Hom(E ⊗ F, G) ≅ Hom(F, ℋom(E, G))`. -/
noncomputable def moduleSheafTensorHomAddEquiv :
    (@Quiver.Hom 𝓜 _ (moduleSheafTensor E F) G) ≃+ (F ⟶ moduleSheafHom E G) where
  toEquiv := moduleSheafTensorHomAdjunction E F G
  map_add' := moduleSheafTensorHomAdjunction_add

@[simp]
lemma moduleSheafTensorHomAddEquiv_apply (φ : @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) G) :
    moduleSheafTensorHomAddEquiv E F G φ = moduleSheafTensorHomAdjunction E F G φ := rfl

lemma moduleSheafTensorHomAddEquiv_toEquiv :
    (moduleSheafTensorHomAddEquiv E F G).toEquiv = moduleSheafTensorHomAdjunction E F G := rfl

end Adjunction

section Locality

private lemma stalkFunctor_map_bijective_of_locally_bijective {Y : TopCat.{u}}
    {P Q : TopCat.Presheaf AddCommGrpCat.{u} Y} (p : P ⟶ Q) {x : Y} {U : Opens Y} (hx : x ∈ U)
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

/-- A morphism of `𝒪_X`-modules inducing bijections on all stalks is an isomorphism. -/
lemma modules_isIso_of_stalk_bijective {A B : 𝓜} (φ : A ⟶ B)
    (h : ∀ x : X, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (modulesMapPresheaf φ))) :
    IsIso φ := by
  have : (SheafOfModules.forget (ringCatSheafOf R)).ReflectsIsomorphisms :=
    (SheafOfModules.fullyFaithfulForget _).reflectsIsomorphisms
  have : (SheafOfModules.forget (ringCatSheafOf R) ⋙
      PresheafOfModules.toPresheaf (ringCatSheafOf R).obj).ReflectsIsomorphisms :=
    reflectsIsomorphisms_comp _ _
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget (ringCatSheafOf R) ⋙ PresheafOfModules.toPresheaf _),
    NatTrans.isIso_iff_isIso_app]
  intro U
  let f : (⟨A.val.presheaf, A.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      ⟨B.val.presheaf, B.isSheaf⟩ := ⟨modulesMapPresheaf φ⟩
  have hb := TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U.unop
    (fun x _ => h x)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

/-- A morphism of `𝒪_X`-modules is an isomorphism if every point has an open neighbourhood on
all of whose open subsets it is bijective on sections. -/
lemma modules_isIso_of_locally_bijective {A B : 𝓜} (φ : A ⟶ B)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ V : Opens X, V ≤ U → Function.Bijective (sectionsMap φ V)) :
    IsIso φ :=
  modules_isIso_of_stalk_bijective φ fun x => by
    obtain ⟨W, hxW, hW⟩ := h x
    exact stalkFunctor_map_bijective_of_locally_bijective (modulesMapPresheaf φ) hxW hW

end Locality

section Frames

variable {ι : Type*} [Fintype ι]

/-- The map `(a_i) ↦ ∑ a_i e_i|_V`. -/
noncomputable def localFrameMap (A : 𝓜) {U : Opens X} (e : ι → Γ(A, U)) {V : Opens X}
    (h : V ≤ U) : (ι → 𝒪(V)) →ₗ[𝒪(V)] Γ(A, V) :=
  Fintype.linearCombination 𝒪(V) (fun i => A.val.presheaf.map (homOfLE h).op (e i))

lemma localFrameMap_apply (A : 𝓜) {U : Opens X} (e : ι → Γ(A, U)) {V : Opens X}
    (h : V ≤ U) (a : ι → 𝒪(V)) :
    localFrameMap A e h a = ∑ i, a i • A.val.presheaf.map (homOfLE h).op (e i) :=
  Fintype.linearCombination_apply _ _ _

/-- A finite family of sections over `U` is a *local frame* if on every smaller open `V` every
section is uniquely a linear combination of the restricted family. -/
def IsLocalFrame (A : 𝓜) (U : Opens X) (e : ι → Γ(A, U)) : Prop :=
  ∀ (V : Opens X) (h : V ≤ U), Function.Bijective (localFrameMap A e h)

lemma localFrameMap_restrict (A : 𝓜) {U : Opens X} (e : ι → Γ(A, U)) {V V' : Opens X}
    (h : V ≤ U) (j : V' ≤ V) (a : ι → 𝒪(V)) :
    A.val.presheaf.map (homOfLE j).op (localFrameMap A e h a) =
      localFrameMap A e (j.trans h) (fun i => R.obj.map (homOfLE j).op (a i)) := by
  rw [localFrameMap_apply, localFrameMap_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [modules_map_smul, modules_map_map]

lemma localFrameMap_single (A : 𝓜) {U : Opens X} (e : ι → Γ(A, U)) {V : Opens X}
    (h : V ≤ U) [DecidableEq ι] (j : ι) :
    localFrameMap A e h (Pi.single j 1) = A.val.presheaf.map (homOfLE h).op (e j) := by
  rw [localFrameMap, Fintype.linearCombination_apply_single, one_smul]

/-- Evaluation of a local morphism at the restricted frame vectors. -/
noncomputable def localFrameEval {A G : 𝓜} {U : Opens X} (e : ι → Γ(A, U))
    {W : Opens X} (hW : W ≤ U) : Γ(moduleSheafHom A G, W) →ₗ[𝒪(W)] (ι → Γ(G, W)) where
  toFun ψ j := moduleSheafHomEval ψ (le_refl W) (A.val.presheaf.map (homOfLE hW).op (e j))
  map_add' _ _ := rfl
  map_smul' r ψ := by
    funext j
    change moduleSheafHomEval (r • ψ) (le_refl W) _ = r • _
    rw [moduleSheafHomEval_smul, ring_map_id]

omit [Fintype ι] in
lemma localFrameEval_apply {A G : 𝓜} {U : Opens X} (e : ι → Γ(A, U)) {W : Opens X}
    (hW : W ≤ U) (ψ : Γ(moduleSheafHom A G, W)) (j : ι) :
    localFrameEval e hW ψ j =
      moduleSheafHomEval ψ (le_refl W) (A.val.presheaf.map (homOfLE hW).op (e j)) :=
  rfl

namespace IsLocalFrame

variable {A : 𝓜} {U : Opens X} {e : ι → Γ(A, U)} (hA : IsLocalFrame A U e)
include hA

/-- Coordinates with respect to a frame. -/
noncomputable def coord {V : Opens X} (h : V ≤ U) : Γ(A, V) ≃ₗ[𝒪(V)] (ι → 𝒪(V)) :=
  (LinearEquiv.ofBijective (localFrameMap A e h) (hA V h)).symm

lemma localFrameMap_coord {V : Opens X} (h : V ≤ U) (x : Γ(A, V)) :
    localFrameMap A e h (hA.coord h x) = x :=
  (LinearEquiv.ofBijective (localFrameMap A e h) (hA V h)).apply_symm_apply x

lemma coord_localFrameMap {V : Opens X} (h : V ≤ U) (a : ι → 𝒪(V)) :
    hA.coord h (localFrameMap A e h a) = a :=
  (LinearEquiv.ofBijective (localFrameMap A e h) (hA V h)).symm_apply_apply a

lemma coord_restrict {V V' : Opens X} (h : V ≤ U) (j : V' ≤ V) (x : Γ(A, V)) :
    hA.coord (j.trans h) (A.val.presheaf.map (homOfLE j).op x) =
      fun i => R.obj.map (homOfLE j).op (hA.coord h x i) := by
  have := localFrameMap_restrict A e h j (hA.coord h x)
  rw [hA.localFrameMap_coord] at this
  rw [this, coord_localFrameMap]

lemma coord_self [DecidableEq ι] {V : Opens X} (h : V ≤ U) (j : ι) :
    hA.coord h (A.val.presheaf.map (homOfLE h).op (e j)) = Pi.single j 1 := by
  rw [← localFrameMap_single A e h j, coord_localFrameMap]

lemma hom_ext {G : 𝓜} {W : Opens X} (hW : W ≤ U) {ψ φ : Γ(moduleSheafHom A G, W)}
    (hψφ : localFrameEval e hW ψ = localFrameEval e hW φ) : ψ = φ := by
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => ?_
  rw [← hA.localFrameMap_coord (h.trans hW) x, localFrameMap_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ← modules_map_map A hW h,
    moduleSheafHomEval_natural ψ (le_refl W) h, moduleSheafHomEval_natural φ (le_refl W) h]
  have := congrFun hψφ i
  rw [localFrameEval_apply, localFrameEval_apply] at this
  rw [this]

/-- The local morphism with prescribed values on a frame. -/
noncomputable def homOfValues {G : 𝓜} {W : Opens X} (hW : W ≤ U) (g : ι → Γ(G, W)) :
    Γ(moduleSheafHom A G, W) :=
  moduleSheafHomMk (fun V h => (Fintype.linearCombination 𝒪(V)
      (fun i => G.val.presheaf.map (homOfLE h).op (g i))) ∘ₗ (hA.coord (h.trans hW)).toLinearMap)
    (by
      intro V V' hV j x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Fintype.linearCombination_apply]
      rw [hA.coord_restrict (hV.trans hW) j x, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [modules_map_smul, modules_map_map])

lemma homOfValues_eval {G : 𝓜} {W : Opens X} (hW : W ≤ U) (g : ι → Γ(G, W))
    {V : Opens X} (h : V ≤ W) (x : Γ(A, V)) :
    moduleSheafHomEval (hA.homOfValues hW g) h x =
      ∑ i, hA.coord (h.trans hW) x i • G.val.presheaf.map (homOfLE h).op (g i) := by
  rw [homOfValues, moduleSheafHomEval_mk]
  exact Fintype.linearCombination_apply _ _ _

lemma localFrameEval_homOfValues {G : 𝓜} {W : Opens X} (hW : W ≤ U) (g : ι → Γ(G, W)) :
    localFrameEval e hW (hA.homOfValues hW g) = g := by
  classical
  funext j
  rw [localFrameEval_apply]
  change (Fintype.linearCombination 𝒪(W)
      (fun i => G.val.presheaf.map (homOfLE (le_refl W)).op (g i)))
    (hA.coord ((le_refl W).trans hW) (A.val.presheaf.map (homOfLE hW).op (e j))) = g j
  rw [hA.coord_self, Fintype.linearCombination_apply_single, one_smul, modules_map_id]

lemma localFrameEval_bijective {G : 𝓜} {W : Opens X} (hW : W ≤ U) :
    Function.Bijective (localFrameEval (G := G) e hW) :=
  ⟨fun _ _ h => hA.hom_ext hW h, fun g => ⟨hA.homOfValues hW g, hA.localFrameEval_homOfValues hW g⟩⟩

end IsLocalFrame

end Frames

section Dual

variable (R) in
/-- The structure sheaf `𝒪_X` as an `𝒪_X`-module. -/
noncomputable abbrev structureModule : 𝓜 := SheafOfModules.unit (ringCatSheafOf R)

/-- The dual `E^∨ = ℋom(E, 𝒪_X)` of an `𝒪_X`-module. -/
noncomputable abbrev moduleSheafDual (E : 𝓜) : 𝓜 :=
  moduleSheafHom E (structureModule R)

/-- Evaluation of a local section of the dual, valued in the structure sheaf. -/
noncomputable def dualEval {E : 𝓜} {W : Opens X} (ψ : Γ(moduleSheafDual E, W))
    {V : Opens X} (h : V ≤ W) : Γ(E, V) →ₗ[𝒪(V)] 𝒪(V) :=
  moduleSheafHomEval ψ h

lemma moduleSheafHomEval_map {E E' G G' : 𝓜} (f : E' ⟶ E) (g : G ⟶ G') {W : Opens X}
    (ψ : Γ(moduleSheafHom E G, W)) {V : Opens X} (h : V ≤ W) (x : Γ(E', V)) :
    moduleSheafHomEval (sectionsMap (moduleSheafHomMap f g) W ψ) h x =
      sectionsMap g V (moduleSheafHomEval ψ h (sectionsMap f V x)) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private lemma sum_single_smul {M : Type*} [AddCommGroup M] {R : Type*} [Ring R] [Module R M]
    [Fintype ι] (j : ι) (v : ι → M) : ∑ k, (Pi.single j (1 : R) : ι → R) k • v k = v j := by
  rw [← Fintype.linearCombination_apply R, Fintype.linearCombination_apply_single, one_smul]

omit [DecidableEq ι] in
lemma localFrameMap_eval {A G : 𝓜} {U : Opens X} (e : ι → Γ(A, U)) {V : Opens X} (h : V ≤ U)
    (ψ : Γ(moduleSheafHom A G, V)) (a : ι → 𝒪(V)) :
    moduleSheafHomEval ψ (le_refl V) (localFrameMap A e h a) =
      ∑ i, a i • localFrameEval e h ψ i := by
  rw [localFrameMap_apply, map_sum]
  simp_rw [map_smul]
  rfl

namespace IsLocalFrame

variable {A : 𝓜} {U : Opens X} {e : ι → Γ(A, U)} (hA : IsLocalFrame A U e)
include hA

/-- The dual frame `e_i^∨` of `E^∨` over `U`. -/
noncomputable def dualLocalFrame (i : ι) : Γ(moduleSheafDual A, U) :=
  hA.homOfValues (G := structureModule R) (le_refl U) (Pi.single i (1 : 𝒪(U)))

lemma localFrameEval_dualLocalFrame {V : Opens X} (h : V ≤ U) (i : ι) :
    localFrameEval e h ((moduleSheafDual A).val.presheaf.map (homOfLE h).op (hA.dualLocalFrame i)) =
      (Pi.single i (1 : 𝒪(V)) : ι → 𝒪(V)) := by
  funext j
  rw [localFrameEval_apply, moduleSheafHomEval_restrict, dualLocalFrame, homOfValues_eval,
    hA.coord_self, sum_single_smul]
  change R.obj.map (homOfLE h).op ((Pi.single i (1 : 𝒪(U)) : ι → 𝒪(U)) j) =
    (Pi.single i (1 : 𝒪(V)) : ι → 𝒪(V)) j
  by_cases hij : j = i
  · subst hij
    rw [Pi.single_eq_same, Pi.single_eq_same]
    exact map_one _
  · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij]
    exact map_zero _

lemma localFrameEval_localFrameMap_dualLocalFrame {V : Opens X} (h : V ≤ U) (a : ι → 𝒪(V)) :
    localFrameEval e h (localFrameMap (moduleSheafDual A) hA.dualLocalFrame h a) = a := by
  rw [localFrameMap_apply, map_sum]
  simp_rw [map_smul, hA.localFrameEval_dualLocalFrame h]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · change a j * (Pi.single j (1 : 𝒪(V)) : ι → 𝒪(V)) j = a j
    rw [Pi.single_eq_same, mul_one]
  · intro k _ hk
    change a k * (Pi.single k (1 : 𝒪(V)) : ι → 𝒪(V)) j = 0
    rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero]
  · intro h'; exact absurd (Finset.mem_univ j) h'

lemma localFrameMap_dualLocalFrame_localFrameEval {V : Opens X} (h : V ≤ U)
    (ψ : Γ(moduleSheafDual A, V)) :
    localFrameMap (moduleSheafDual A) hA.dualLocalFrame h (localFrameEval e h ψ) = ψ :=
  hA.hom_ext h (hA.localFrameEval_localFrameMap_dualLocalFrame h _)

/-- **The dual of a frame is a frame.** -/
lemma dual : IsLocalFrame (moduleSheafDual A) U hA.dualLocalFrame := fun V h =>
  ⟨fun a b hab => by
    rw [← hA.localFrameEval_localFrameMap_dualLocalFrame h a, hab,
      hA.localFrameEval_localFrameMap_dualLocalFrame h b],
   fun ψ => ⟨_, hA.localFrameMap_dualLocalFrame_localFrameEval h ψ⟩⟩

end IsLocalFrame

end Dual

section DoubleDual

/-- The section of `E^∨∨` over `U` given by evaluation at a section `x` of `E`. -/
noncomputable def doubleDualSection (E : 𝓜) {U : Opens X} (x : Γ(E, U)) :
    Γ(moduleSheafDual (moduleSheafDual E), U) :=
  moduleSheafHomMk
    (fun V h =>
      { toFun := fun ψ : Γ(moduleSheafDual E, V) =>
          moduleSheafHomEval ψ (le_refl V) (E.val.presheaf.map (homOfLE h).op x)
        map_add' := fun _ _ => rfl
        map_smul' := fun r ψ => by
          rw [RingHom.id_apply, moduleSheafHomEval_smul, ring_map_id] })
    (by
      intro V V' hV j ψ
      change moduleSheafHomEval ((moduleSheafDual E).val.presheaf.map (homOfLE j).op ψ) (le_refl V')
          (E.val.presheaf.map (homOfLE (j.trans hV)).op x) =
        (structureModule R).val.presheaf.map (homOfLE j).op
          (moduleSheafHomEval ψ (le_refl V) (E.val.presheaf.map (homOfLE hV).op x))
      rw [moduleSheafHomEval_restrict, ← modules_map_map E hV j,
        ← moduleSheafHomEval_natural ψ (le_refl V) j])

lemma doubleDualSection_eval (E : 𝓜) {U : Opens X} (x : Γ(E, U)) {V : Opens X}
    (h : V ≤ U) (ψ : Γ(moduleSheafDual E, V)) :
    moduleSheafHomEval (doubleDualSection E x) h ψ =
      moduleSheafHomEval ψ (le_refl V) (E.val.presheaf.map (homOfLE h).op x) := rfl

/-- The canonical map `E ⟶ E^∨∨`, sending a section to evaluation at it. -/
noncomputable def moduleSheafDoubleDualMap (E : 𝓜) :
    E ⟶ moduleSheafDual (moduleSheafDual E) :=
  modulesHomMk
    (fun U =>
      { toFun := doubleDualSection E
        map_add' := fun x y => moduleSheafHomEval_ext fun V h => LinearMap.ext fun ψ => by
          rw [moduleSheafHomEval_add, LinearMap.add_apply, doubleDualSection_eval,
            doubleDualSection_eval, doubleDualSection_eval, map_add, map_add]
        map_smul' := fun r x => moduleSheafHomEval_ext fun V h => LinearMap.ext fun ψ => by
          rw [RingHom.id_apply, moduleSheafHomEval_smul, doubleDualSection_eval,
            doubleDualSection_eval, modules_map_smul, map_smul] })
    (fun U V i x => moduleSheafHomEval_ext fun W h => LinearMap.ext fun ψ => by
      change moduleSheafHomEval (doubleDualSection E (E.val.presheaf.map (homOfLE i).op x)) h ψ =
        moduleSheafHomEval (doubleDualSection E x) (h.trans i) ψ
      rw [doubleDualSection_eval, doubleDualSection_eval, modules_map_map])

lemma moduleSheafDoubleDualMap_app_eval (E : 𝓜) {U : Opens X} (x : Γ(E, U))
    {V : Opens X} (h : V ≤ U) (ψ : Γ(moduleSheafDual E, V)) :
    moduleSheafHomEval (sectionsMap (moduleSheafDoubleDualMap E) U x) h ψ =
      moduleSheafHomEval ψ (le_refl V) (E.val.presheaf.map (homOfLE h).op x) := rfl

/-- The double-dual map is natural in `E`. -/
lemma moduleSheafDoubleDualMap_naturality {E E' : 𝓜} (f : E ⟶ E') :
    f ≫ moduleSheafDoubleDualMap E' =
      moduleSheafDoubleDualMap E ≫
        moduleSheafHomMap (moduleSheafHomMap f (𝟙 (structureModule R)))
          (𝟙 (structureModule R)) := by
  refine modules_hom_ext fun U => ?_
  ext x
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun ψ => ?_
  change moduleSheafHomEval ψ (le_refl V) (E'.val.presheaf.map (homOfLE h).op (sectionsMap f U x)) =
    moduleSheafHomEval ψ (le_refl V) (sectionsMap f V (E.val.presheaf.map (homOfLE h).op x))
  have := ConcreteCategory.congr_hom ((modulesMapPresheaf f).naturality (homOfLE h).op) x
  change sectionsMap f V (E.val.presheaf.map (homOfLE h).op x) =
    E'.val.presheaf.map (homOfLE h).op (sectionsMap f U x)
    at this
  rw [this]

lemma localFrameEval_doubleDualMap {ι : Type*} [Fintype ι] [DecidableEq ι] {E : 𝓜}
    {U : Opens X} {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) {V : Opens X} (h : V ≤ U)
    (a : ι → 𝒪(V)) :
    localFrameEval hE.dualLocalFrame h
      (sectionsMap (moduleSheafDoubleDualMap E) V (localFrameMap E e h a)) = a := by
  funext j
  rw [localFrameEval_apply, moduleSheafDoubleDualMap_app_eval, modules_map_id, localFrameMap_eval,
    hE.localFrameEval_dualLocalFrame h]
  rw [Finset.sum_eq_single j]
  · change a j * (Pi.single j (1 : 𝒪(V)) : ι → 𝒪(V)) j = a j
    rw [Pi.single_eq_same, mul_one]
  · intro k _ hk
    change a k * (Pi.single j (1 : 𝒪(V)) : ι → 𝒪(V)) k = 0
    rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ j) h'

/-- On an open with a frame, the double-dual map is bijective on sections. -/
lemma doubleDualMap_bijective_of_isLocalFrame {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : 𝓜} {U : Opens X} {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) {V : Opens X} (h : V ≤ U) :
    Function.Bijective (sectionsMap (moduleSheafDoubleDualMap E) V) := by
  have hc : sectionsMap (moduleSheafDoubleDualMap E) V ∘ localFrameMap E e h =
      localFrameMap _ hE.dual.dualLocalFrame h := by
    funext a
    exact hE.dual.hom_ext h ((localFrameEval_doubleDualMap hE h a).trans
      (hE.dual.localFrameEval_localFrameMap_dualLocalFrame h a).symm)
  rw [← Function.Bijective.of_comp_iff _ (hE V h), hc]
  exact hE.dual.dual V h

end DoubleDual

section DualTensor

/-- The local morphism `x ↦ ψ(x) f` attached to sections `ψ` of `E^∨` and `f` of `F`. -/
noncomputable def dualTensorSection {E F : 𝓜} {U : Opens X} (ψ : Γ(moduleSheafDual E, U))
    (f : Γ(F, U)) : Γ(moduleSheafHom E F, U) :=
  moduleSheafHomMk
    (fun V h => (LinearMap.toSpanSingleton 𝒪(V) Γ(F, V) (F.val.presheaf.map (homOfLE h).op f)) ∘ₗ
      dualEval ψ h)
    (by
      intro V V' hV j x
      change dualEval ψ (j.trans hV) (E.val.presheaf.map (homOfLE j).op x) •
          F.val.presheaf.map (homOfLE (j.trans hV)).op f =
        F.val.presheaf.map (homOfLE j).op (dualEval ψ hV x • F.val.presheaf.map (homOfLE hV).op f)
      rw [modules_map_smul, modules_map_map]
      congr 1
      exact moduleSheafHomEval_natural ψ hV j x)

lemma dualTensorSection_eval {E F : 𝓜} {U : Opens X} (ψ : Γ(moduleSheafDual E, U))
    (f : Γ(F, U)) {V : Opens X} (h : V ≤ U) (x : Γ(E, V)) :
    moduleSheafHomEval (dualTensorSection ψ f) h x =
      dualEval ψ h x • F.val.presheaf.map (homOfLE h).op f := rfl

private lemma modules_mul_smul (F : 𝓜) {V : Opens X} (r s : 𝒪(V)) (y : Γ(F, V)) :
    (r * s) • y = r • s • y :=
  mul_smul r s y

section
variable {E F : 𝓜} {U : Opens X}

lemma dualTensorSection_add_left (ψ ψ' : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) :
    dualTensorSection (ψ + ψ') f = dualTensorSection ψ f + dualTensorSection ψ' f :=
  moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_add, LinearMap.add_apply, dualTensorSection_eval,
      dualTensorSection_eval, dualTensorSection_eval]
    exact add_smul _ _ _

lemma dualTensorSection_smul_left (r : 𝒪(U)) (ψ : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) :
    dualTensorSection (r • ψ) f = r • dualTensorSection ψ f :=
  moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_smul, dualTensorSection_eval, dualTensorSection_eval]
    exact modules_mul_smul F (R.obj.map (homOfLE h).op r) (dualEval ψ h x) _

lemma dualTensorSection_add_right (ψ : Γ(moduleSheafDual E, U)) (f f' : Γ(F, U)) :
    dualTensorSection ψ (f + f') = dualTensorSection ψ f + dualTensorSection ψ f' :=
  moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_add, LinearMap.add_apply, dualTensorSection_eval,
      dualTensorSection_eval, dualTensorSection_eval, map_add]
    exact smul_add _ _ _

lemma dualTensorSection_smul_right (r : 𝒪(U)) (ψ : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) :
    dualTensorSection ψ (r • f) = r • dualTensorSection ψ f :=
  moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_smul, dualTensorSection_eval, dualTensorSection_eval,
      modules_map_smul]
    exact smul_comm _ _ _

lemma dualTensorSection_restrict (ψ : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) {V : Opens X}
    (i : V ≤ U) :
    (moduleSheafHom E F).val.presheaf.map (homOfLE i).op (dualTensorSection ψ f) =
      dualTensorSection ((moduleSheafDual E).val.presheaf.map (homOfLE i).op ψ)
        (F.val.presheaf.map (homOfLE i).op f) :=
  moduleSheafHomEval_ext fun W h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_restrict, dualTensorSection_eval, dualTensorSection_eval,
      modules_map_map]
    rfl

end

variable (E F : 𝓜) in
/-- The bilinear pairing `E^∨ × F → ℋom(E, F)`, `(ψ, f) ↦ (x ↦ ψ(x) f)`. -/
noncomputable def dualTensorBilinear :
    ModuleSheafBilinear (moduleSheafDual E) F (moduleSheafHom E F) where
  app U := LinearMap.mk₂ _
    (fun (ψ : Γ(moduleSheafDual E, U.unop)) (f : Γ(F, U.unop)) => dualTensorSection ψ f)
    (fun ψ ψ' f => dualTensorSection_add_left ψ ψ' f)
    (fun r ψ f => dualTensorSection_smul_left r ψ f)
    (fun ψ f f' => dualTensorSection_add_right ψ f f')
    (fun r ψ f => dualTensorSection_smul_right r ψ f)
  naturality {_ _} i ψ f := dualTensorSection_restrict ψ f (leOfHom i.unop)

variable (E F : 𝓜) in
/-- The canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)`, induced by `(ψ, f) ↦ (x ↦ ψ(x) f)`. -/
noncomputable def moduleSheafDualTensorMap :
    @Quiver.Hom 𝓜 _ (moduleSheafTensor (moduleSheafDual E) F) (moduleSheafHom E F) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (dualTensorBilinear E F)

lemma moduleSheafDualTensorMap_tmul {E F : 𝓜} {U : Opens X}
    (ψ : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) :
    (moduleSheafDualTensorMap E F).val.app (op U)
        ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ f) =
      dualTensorSection ψ f := by
  have := congrArg (fun β : ModuleSheafBilinear _ _ _ => β.app (op U) ψ f)
    ((moduleSheafTensorHomEquiv_apply (moduleSheafDualTensorMap E F)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) (dualTensorBilinear E F)))
  exact this

end DualTensor

section DualTensorIso

lemma tensor_localFrame_bijective {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → M)
    (c : M →ₗ[R] (ι → R)) (hc : ∀ m, ∑ j, c m j • b j = m)
    (hb : ∀ i, c (b i) = Pi.single i 1) (Φ : TensorProduct R M N →+ (ι → N))
    (hΦ : ∀ m n, Φ (m ⊗ₜ n) = fun j => c m j • n) : Function.Bijective Φ := by
  let L : (ι → N) →+ TensorProduct R M N :=
    ∑ j, (TensorProduct.mk R M N (b j)).toAddMonoidHom.comp (Pi.evalAddMonoidHom _ j)
  have hL : ∀ g, L g = ∑ j, b j ⊗ₜ g j := fun g => by
    simp [L]
  have hLΦ : ∀ t, L (Φ t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul m n =>
      rw [hΦ, hL]
      simp_rw [← TensorProduct.smul_tmul]
      rw [← TensorProduct.sum_tmul, hc]
    | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  refine ⟨Function.LeftInverse.injective hLΦ, fun g => ⟨L g, ?_⟩⟩
  rw [hL, map_sum]
  funext k
  simp_rw [hΦ, hb, Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Pi.single_eq_same, one_smul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne (Ne.symm hj), zero_smul]
  · intro h'; exact absurd (Finset.mem_univ k) h'

variable {E F : 𝓜}

/-- The presheaf-level map `U ↦ E^∨(U) ⊗ F(U) → ℋom(E, F)(U)` underlying the canonical map. -/
noncomputable abbrev dualTensorPresheafMap (E F : 𝓜) :
    (moduleSheafTensorPresheaf (moduleSheafDual E) F).presheaf ⟶
      (moduleSheafHom E F).val.presheaf :=
  (PresheafOfModules.toPresheaf _).map
    (moduleSheafTensorUnit (moduleSheafDual E) F ≫ (moduleSheafDualTensorMap E F).val)

lemma dualTensorPresheafMap_tmul {V : Opens X} (ψ : Γ(moduleSheafDual E, V)) (f : Γ(F, V)) :
    (dualTensorPresheafMap E F).app (op V)
        (show (moduleSheafTensorPresheaf (moduleSheafDual E) F).obj (op V) from ψ ⊗ₜ f) =
      dualTensorSection ψ f :=
  moduleSheafDualTensorMap_tmul ψ f

lemma dualTensorPresheafMap_bijective {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Opens X}
    {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) {V : Opens X} (h : V ≤ U) :
    Function.Bijective ((dualTensorPresheafMap E F).app (op V)) := by
  rw [← Function.Bijective.of_comp_iff' (hE.localFrameEval_bijective (G := F) h)]
  let Φ : TensorProduct 𝒪(V) Γ(moduleSheafDual E, V) Γ(F, V) →+ (ι → Γ(F, V)) :=
    (localFrameEval e h).toAddMonoidHom.comp ((dualTensorPresheafMap E F).app (op V)).hom
  have := tensor_localFrame_bijective (R := 𝒪(V)) (M := Γ(moduleSheafDual E, V)) (N := Γ(F, V))
    (fun j => (moduleSheafDual E).val.presheaf.map (homOfLE h).op (hE.dualLocalFrame j))
    (localFrameEval e h) (fun ψ => by
      rw [← localFrameMap_apply]
      exact hE.localFrameMap_dualLocalFrame_localFrameEval h ψ)
    (fun i => hE.localFrameEval_dualLocalFrame h i)
    Φ (fun ψ f => by
      funext j
      change localFrameEval e h ((dualTensorPresheafMap E F).app (op V)
        (show (moduleSheafTensorPresheaf (moduleSheafDual E) F).obj (op V) from ψ ⊗ₜ f)) j = _
      rw [dualTensorPresheafMap_tmul, localFrameEval_apply, dualTensorSection_eval, modules_map_id]
      rfl)
  exact this

/-- If `E` admits frames locally, the canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)` is an isomorphism. -/
lemma isIso_moduleSheafDualTensorMap_of_localFrames
    (hE : ∀ x : X, ∃ (U : Opens X) (ι : Type u) (_ : Fintype ι) (e : ι → Γ(E, U)),
      x ∈ U ∧ IsLocalFrame E U e) :
    IsIso (moduleSheafDualTensorMap E F) := by
  classical
  refine modules_isIso_of_stalk_bijective _ fun x => ?_
  obtain ⟨U, ι, _, e, hx, hEU⟩ := hE x
  have h1 := stalkFunctor_map_bijective_of_locally_bijective (dualTensorPresheafMap E F) hx
    (fun V h => dualTensorPresheafMap_bijective hEU h)
  have h2 := ModuleSheafTensor.moduleSheafTensorUnitStalk_bijective (moduleSheafDual E) F x
  have hc : dualTensorPresheafMap E F =
      @CategoryStruct.comp (TopCat.Presheaf AddCommGrpCat.{u} X) _ _ _ _
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (moduleSheafTensorPresheaf (moduleSheafDual E) F).presheaf)
        (modulesMapPresheaf (moduleSheafDualTensorMap E F)) :=
    (PresheafOfModules.toPresheaf _).map_comp _ _
  have e := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (moduleSheafTensorPresheaf (moduleSheafDual E) F).presheaf)
    (modulesMapPresheaf (moduleSheafDualTensorMap E F))
  rw [hc, e] at h1
  exact (Function.Bijective.of_comp_iff _ h2).mp h1

end DualTensorIso

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

section Naturality

variable {E E' F F' G : 𝓜}

/-- The bilinear map `(e, f) ↦ φ(e) ⊗ ψ(f)` used to define `φ ⊗ ψ`. -/
noncomputable def modulesTensorMapBilinear (φ : E ⟶ E') (ψ : F ⟶ F') :
    ModuleSheafBilinear E F (moduleSheafTensor E' F') where
  app U := ((moduleSheafTensorBilinear E' F').app U).compl₁₂ (φ.val.app U).hom (ψ.val.app U).hom
  naturality {U V} i e f := by
    have hφ := ConcreteCategory.congr_hom (φ.val.naturality i) e
    have hψ := ConcreteCategory.congr_hom (ψ.val.naturality i) f
    refine ((moduleSheafTensorBilinear E' F').naturality i _ _).trans ?_
    exact congrArg₂ (fun a b => (moduleSheafTensorBilinear E' F').app V a b) hφ.symm hψ.symm

/-- The tensor product `φ ⊗ ψ : E ⊗ F ⟶ E' ⊗ F'` of two morphisms of `𝒪_X`-modules. -/
noncomputable def modulesTensorMap (φ : E ⟶ E') (ψ : F ⟶ F') :
    @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) (moduleSheafTensor E' F') :=
  (moduleSheafTensorHomEquiv _ _ _).symm (modulesTensorMapBilinear φ ψ)

lemma modulesTensorMap_tmul (φ : E ⟶ E') (ψ : F ⟶ F') {U : Opens X} (e : Γ(E, U))
    (f : Γ(F, U)) :
    sectionsMap (modulesTensorMap φ ψ) U ((moduleSheafTensorBilinear E F).app (op U) e f) =
      (moduleSheafTensorBilinear E' F').app (op U) (sectionsMap φ U e) (sectionsMap ψ U f) := by
  have := congrArg (fun β : ModuleSheafBilinear _ _ _ => β.app (op U) e f)
    ((moduleSheafTensorHomEquiv_apply (modulesTensorMap φ ψ)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) (modulesTensorMapBilinear φ ψ)))
  exact this

/-- Two morphisms out of a tensor product agreeing on all elementary tensors are equal. -/
lemma modulesTensor_hom_ext {H : 𝓜}
    {φ ψ : @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) H}
    (h : ∀ (U : Opens X) (e : Γ(E, U)) (f : Γ(F, U)),
      sectionsMap φ U ((moduleSheafTensorBilinear E F).app (op U) e f) =
        sectionsMap ψ U ((moduleSheafTensorBilinear E F).app (op U) e f)) : φ = ψ := by
  apply (moduleSheafTensorHomEquiv E F H).injective
  exact (moduleSheafTensorHomEquiv_apply φ).trans ((ModuleSheafBilinear.ext
    fun U e f => h U.unop e f).trans (moduleSheafTensorHomEquiv_apply ψ).symm)

/-- The canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)` is natural in `F`. -/
lemma moduleSheafDualTensorMap_naturality_right (g : F ⟶ F') :
    modulesTensorMap (𝟙 (moduleSheafDual E)) g ≫ moduleSheafDualTensorMap E F' =
      moduleSheafDualTensorMap E F ≫ moduleSheafHomMap (𝟙 E) g := by
  refine modulesTensor_hom_ext fun U ψ f => ?_
  have h1 := modulesTensorMap_tmul (𝟙 (moduleSheafDual E)) g ψ f
  have h2 := moduleSheafDualTensorMap_tmul (E := E) (F := F') ψ (sectionsMap g U f)
  have h3 := moduleSheafDualTensorMap_tmul (E := E) (F := F) ψ f
  change sectionsMap (moduleSheafDualTensorMap E F') U
      (sectionsMap (modulesTensorMap (𝟙 (moduleSheafDual E)) g) U
      ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ f)) =
    sectionsMap (moduleSheafHomMap (𝟙 E) g) U (sectionsMap (moduleSheafDualTensorMap E F) U
      ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ f))
  rw [h1]
  erw [h2, h3]
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => ?_
  rw [moduleSheafHomEval_map, dualTensorSection_eval, dualTensorSection_eval,
    hom_app_smul]
  congr 1
  exact (ConcreteCategory.congr_hom ((modulesMapPresheaf g).naturality (homOfLE h).op) f).symm

/-- The canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)` is natural in `E`. -/
lemma moduleSheafDualTensorMap_naturality_left (f : E' ⟶ E) :
    modulesTensorMap (moduleSheafHomMap f (𝟙 (structureModule R))) (𝟙 F) ≫
        moduleSheafDualTensorMap E' F =
      moduleSheafDualTensorMap E F ≫ moduleSheafHomMap f (𝟙 F) := by
  refine modulesTensor_hom_ext fun U ψ y => ?_
  have h1 := modulesTensorMap_tmul (moduleSheafHomMap f (𝟙 (structureModule R))) (𝟙 F) ψ y
  have h2 := moduleSheafDualTensorMap_tmul (E := E') (F := F)
    (sectionsMap (moduleSheafHomMap f (𝟙 (structureModule R))) U ψ) y
  have h3 := moduleSheafDualTensorMap_tmul (E := E) (F := F) ψ y
  change sectionsMap (moduleSheafDualTensorMap E' F) U
      (sectionsMap (modulesTensorMap (moduleSheafHomMap f (𝟙 (structureModule R))) (𝟙 F)) U
      ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ y)) =
    sectionsMap (moduleSheafHomMap f (𝟙 F)) U (sectionsMap (moduleSheafDualTensorMap E F) U
      ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ y))
  rw [h1]
  erw [h2, h3]
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => ?_
  rw [moduleSheafHomEval_map, dualTensorSection_eval, dualTensorSection_eval]
  rfl

/-- The tensor–Hom adjunction is natural in `F`. -/
lemma moduleSheafTensorHomAdjunction_naturality_right
    (g : F' ⟶ F) (φ : @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) G) :
    moduleSheafTensorHomAdjunction E F' G (modulesTensorMap (𝟙 E) g ≫ φ) =
      g ≫ moduleSheafTensorHomAdjunction E F G φ := by
  refine modules_hom_ext fun U => ?_
  ext f
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun e => ?_
  change sectionsMap φ V (sectionsMap (modulesTensorMap (𝟙 E) g) V
      ((moduleSheafTensorBilinear E F').app (op V) e (F'.val.presheaf.map (homOfLE h).op f))) =
    sectionsMap φ V ((moduleSheafTensorBilinear E F).app (op V) e
      (F.val.presheaf.map (homOfLE h).op (sectionsMap g U f)))
  refine congrArg (sectionsMap φ V) ((modulesTensorMap_tmul _ _ e _).trans ?_)
  exact congrArg ((moduleSheafTensorBilinear E F).app (op V) e)
    (ConcreteCategory.congr_hom ((modulesMapPresheaf g).naturality (homOfLE h).op) f)

/-- The tensor–Hom adjunction is natural in `E`. -/
lemma moduleSheafTensorHomAdjunction_naturality_left
    (f : E' ⟶ E) (φ : @Quiver.Hom 𝓜 _ (moduleSheafTensor E F) G) :
    moduleSheafTensorHomAdjunction E' F G (modulesTensorMap f (𝟙 F) ≫ φ) =
      moduleSheafTensorHomAdjunction E F G φ ≫ moduleSheafHomMap f (𝟙 G) := by
  refine modules_hom_ext fun U => ?_
  ext y
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun e => ?_
  change sectionsMap φ V (sectionsMap (modulesTensorMap f (𝟙 F)) V
      ((moduleSheafTensorBilinear E' F).app (op V) e (F.val.presheaf.map (homOfLE h).op y))) =
    sectionsMap φ V ((moduleSheafTensorBilinear E F).app (op V) (sectionsMap f V e)
      (F.val.presheaf.map (homOfLE h).op y))
  exact congrArg (sectionsMap φ V) (modulesTensorMap_tmul _ _ e _)

end Naturality
section FreeFrame

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable (U : Opens X) {I : Type u} [Fintype I] [DecidableEq I]

/-- Module sheaves on the opens contained in `U` are modules over the sections of `𝒪_X`. -/
scoped instance (M : SheafOfModules.{u} ((ringCatSheafOf R).over U)) (A : (Over U)ᵒᵖ) :
    Module (R.obj.obj (op A.unop.left)) (M.val.obj A) :=
  (M.val.obj A).isModule

/-- The open `U` itself, as the terminal object of the opens contained in `U`. -/
private abbrev overTop : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))

/-- The restriction from `U` to a smaller open, on the opens contained in `U`. -/
private def toOverTop (A : (Over U)ᵒᵖ) : overTop U ⟶ A :=
  (Over.homMk A.unop.hom (Category.comp_id _) : A.unop ⟶ Over.mk (𝟙 U)).op

/-- The `i`-th coordinate projection of a finite free module on the opens of `U`. -/
private noncomputable def freeProj (i : I) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)) ⟶
      SheafOfModules.unit ((ringCatSheafOf R).over U) :=
  (biproduct.isoCoproduct (fun _ : I => SheafOfModules.unit ((ringCatSheafOf R).over U))).inv ≫
    biproduct.π (fun _ : I => SheafOfModules.unit ((ringCatSheafOf R).over U)) i

private lemma ιFree_freeProj (i j : I) :
    SheafOfModules.ιFree i ≫ freeProj (R := R) U j = if i = j then 𝟙 _ else 0 :=
  sigma_ι_isoCoproduct_inv_π _ i j

omit [DecidableEq I] in
private lemma sum_freeProj_ιFree :
    ∑ i, freeProj (R := R) U i ≫ SheafOfModules.ιFree (I := I) i = 𝟙 _ :=
  sum_isoCoproduct_inv_π_sigma_ι _

/-- The `i`-th standard section of the free module `𝒪_U^{⊕ I}` over `U`. -/
noncomputable def freeVec (i : I) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.obj (overTop U) :=
  (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) i).val.app (overTop U)
    (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj (overTop U) from
      (1 : R.obj.obj (op U)))

omit [Fintype I] [DecidableEq I] in
private lemma ιFree_app_smul_one (i : I) (A : (Over U)ᵒᵖ) (r : R.obj.obj (op A.unop.left)) :
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
private lemma freeVec_restrict (i : I) (A : (Over U)ᵒᵖ) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.map
        (toOverTop U A) (freeVec U i) =
      (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
        (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from
          (1 : R.obj.obj (op A.unop.left))) := by
  have := ConcreteCategory.congr_hom
    ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.naturality
      (toOverTop U A))
    (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj (overTop U) from
      (1 : R.obj.obj (op U)))
  refine this.symm.trans ?_
  change (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
    (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from
      R.obj.map (A.unop.hom).op 1) = _
  rw [map_one]

/-- The map `(a_i) ↦ ∑ a_i e_i|_A` for the standard sections of a finite free module. -/
private noncomputable def freeFrameMap (A : (Over U)ᵒᵖ) (a : I → R.obj.obj (op A.unop.left)) :
    (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.obj A :=
  ∑ i, a i •
    (show (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.obj A
    from (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.map
      (toOverTop U A) (freeVec U i))

/-- The value of a morphism of module sheaves at a fixed section, as an additive map. -/
private noncomputable def homEvalAddHom {M N : SheafOfModules.{u} ((ringCatSheafOf R).over U)}
    (A : (Over U)ᵒᵖ) (x : M.val.obj A) : (M ⟶ N) →+ N.val.obj A where
  toFun φ := φ.val.app A x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The standard sections of a finite free module form a frame.** -/
private lemma freeFrameMap_bijective (A : (Over U)ᵒᵖ) :
    Function.Bijective (freeFrameMap (R := R) (I := I) U A) := by
  have hF : ∀ a, freeFrameMap (R := R) (I := I) U A a =
      ∑ i, (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
        (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from a i) := by
    intro a
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [freeVec_restrict, ιFree_app_smul_one]
  have hπι : ∀ (i j : I) (r : R.obj.obj (op A.unop.left)),
      (freeProj (R := R) U j).val.app A
        ((SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
          (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from r)) =
        if i = j then r else 0 := by
    intro i j r
    have := congrArg (fun φ => φ.val.app A
      (show (SheafOfModules.unit ((ringCatSheafOf R).over U)).val.obj A from r))
      (ιFree_freeProj (R := R) U i j)
    refine this.trans ?_
    split_ifs <;> rfl
  have hsum :
      ∀ s : (SheafOfModules.free I : SheafOfModules.{u} ((ringCatSheafOf R).over U)).val.obj A,
      ∑ i, (SheafOfModules.ιFree (R := (ringCatSheafOf R).over U) (I := I) i).val.app A
        ((freeProj (R := R) U i).val.app A s) = s := by
    intro s
    have := congrArg (homEvalAddHom U A s) (sum_freeProj_ιFree (R := R) U (I := I))
    rw [map_sum] at this
    exact this
  have hΨ : ∀ a : I → R.obj.obj (op A.unop.left), (fun j => (show R.obj.obj (op A.unop.left) from
      (freeProj (R := R) U j).val.app A (freeFrameMap U A a))) = a := by
    intro a
    funext j
    rw [hF, map_sum]
    simp_rw [hπι]
    exact (Finset.sum_eq_single j (fun k _ hk => if_neg hk)
      (fun h' => absurd (Finset.mem_univ j) h')).trans (if_pos rfl)
  refine ⟨fun a b hab => ?_, fun s => ⟨fun j => (freeProj (R := R) U j).val.app A s, ?_⟩⟩
  · rw [← hΨ a, ← hΨ b, hab]
  · exact (hF _).trans (hsum s)

end FreeFrame

section LocallyFree

private lemma iso_inv_app_bijective {U' : Opens X}
    {S : Sheaf ((Opens.grothendieckTopology X).over U') RingCat.{u}}
    {M N : SheafOfModules.{u} S} (α : M ≅ N) (A : (Over U')ᵒᵖ) :
    Function.Bijective (α.inv.val.app A) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨α.hom.val.app A, fun y => ?_, fun x => ?_⟩
  · exact ConcreteCategory.congr_hom (congrArg (fun f => f.val.app A) α.inv_hom_id) y
  · exact ConcreteCategory.congr_hom (congrArg (fun f => f.val.app A) α.hom_inv_id) x

/-- A finite free presentation `E|_U ≅ 𝒪_U^{⊕ I}` gives a frame of `E` over `U`. -/
lemma isLocalFrame_of_over_iso {I : Type u} [Fintype I] [DecidableEq I] {E : 𝓜} {U : Opens X}
    (α : E.over U ≅ SheafOfModules.free I) :
    IsLocalFrame E U (fun i => α.inv.val.app (op (Over.mk (𝟙 U))) (freeVec U i)) := by
  intro V h
  let A : (Over U)ᵒᵖ := op (Over.mk (homOfLE h))
  have key : ⇑(localFrameMap (U := U) E
      (fun i => α.inv.val.app (op (Over.mk (𝟙 U))) (freeVec U i)) h) =
      α.inv.val.app A ∘ freeFrameMap U A := by
    funext a
    refine (localFrameMap_apply E _ h a).trans ?_
    rw [Function.comp_apply, freeFrameMap, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Eq.trans ?_ ((α.inv.val.app A).hom.map_smul (a i) _).symm
    congr 1
    exact (ConcreteCategory.congr_hom (α.inv.val.naturality (toOverTop U A)) (freeVec U i)).symm
  rw [key]
  exact (iso_inv_app_bijective α A).comp (freeFrameMap_bijective U A)

/-- A module locally free of finite rank admits frames locally. -/
lemma exists_isLocalFrame_of_isFiniteLocallyFree {E : 𝓜} (hE : IsFiniteLocallyFree E) (x : X) :
    ∃ (U : Opens X) (ι : Type u) (_ : Fintype ι) (e : ι → Γ(E, U)), x ∈ U ∧ IsLocalFrame E U e := by
  classical
  obtain ⟨U, hxU, r, ⟨α⟩⟩ := hE x
  exact ⟨U, ULift.{u} (Fin r), inferInstance, _, hxU, isLocalFrame_of_over_iso α⟩

end LocallyFree

section MainResults

variable (E : 𝓜)

/-- **Hartshorne II, Exercise 5.1(a).** For a locally free `𝒪_X`-module `E` of finite rank, the
canonical map `E ⟶ E^∨∨` is an isomorphism. -/
theorem moduleSheafDoubleDualMap_isIso (hE : IsFiniteLocallyFree E) :
    IsIso (moduleSheafDoubleDualMap E) :=
  modules_isIso_of_locally_bijective _ fun x => by
    classical
    obtain ⟨U, ι, _, e, hx, hEU⟩ := exists_isLocalFrame_of_isFiniteLocallyFree hE x
    exact ⟨U, hx, fun V h => doubleDualMap_bijective_of_isLocalFrame hEU h⟩

/-- The natural isomorphism `E ≅ E^∨∨` for a locally free `E` of finite rank. -/
noncomputable def moduleSheafDoubleDualIso (hE : IsFiniteLocallyFree E) :
    E ≅ moduleSheafDual (moduleSheafDual E) :=
  haveI := moduleSheafDoubleDualMap_isIso E hE
  asIso (moduleSheafDoubleDualMap E)

/-- **Hartshorne II, Exercise 5.1(b).** For a locally free `E` of finite rank and any
`𝒪_X`-module `F`, the canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)` is an isomorphism. -/
theorem moduleSheafDualTensorMap_isIso (F : 𝓜) (hE : IsFiniteLocallyFree E) :
    IsIso (moduleSheafDualTensorMap E F) :=
  isIso_moduleSheafDualTensorMap_of_localFrames (exists_isLocalFrame_of_isFiniteLocallyFree hE)

/-- The natural isomorphism `E^∨ ⊗ F ≅ ℋom(E, F)` for a locally free `E` of finite rank. -/
noncomputable def moduleSheafDualTensorIso (F : 𝓜) (hE : IsFiniteLocallyFree E) :
    moduleSheafTensor (moduleSheafDual E) F ≅ moduleSheafHom E F :=
  haveI := moduleSheafDualTensorMap_isIso E F hE
  asIso (moduleSheafDualTensorMap E F)

end MainResults

end Ringed

end Hartshorne

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The tensor product `E ⊗ F` of `𝒪_X`-modules on a scheme, as an object of `X.Modules`:
`Hartshorne.moduleSheafTensor` with `R := X.sheaf`. -/
noncomputable abbrev sheafTensor (E F : X.Modules) : X.Modules :=
  Hartshorne.moduleSheafTensor (R := X.sheaf) E F

/-- The sheaf `ℋom(E, G)` of `𝒪_X`-modules on a scheme, as an object of `X.Modules`:
`Hartshorne.Ringed.moduleSheafHom` with `R := X.sheaf`. -/
noncomputable abbrev sheafHom (E G : X.Modules) : X.Modules :=
  Hartshorne.Ringed.moduleSheafHom (R := X.sheaf) E G

/-- **Hartshorne II, Exercise 5.1(c), on a scheme.** For all `𝒪_X`-modules `E`, `F`, `G` on a
scheme `X` (Hartshorne assumes `E` finite locally free; not needed here), the tensor–Hom
isomorphism of abelian groups `Hom(E ⊗ F, G) ≅ Hom(F, ℋom(E, G))`, with Hom groups taken in the
category `X.Modules`: the ringed-space isomorphism
`Hartshorne.Ringed.moduleSheafTensorHomAddEquiv` with `R := X.sheaf`. -/
noncomputable def tensorHomAddEquiv (E F G : X.Modules) :
    (sheafTensor E F ⟶ G) ≃+ (F ⟶ sheafHom E G) :=
  Hartshorne.Ringed.moduleSheafTensorHomAddEquiv E F G

end AlgebraicGeometry.Scheme.Modules
