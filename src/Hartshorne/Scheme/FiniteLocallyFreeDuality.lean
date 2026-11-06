/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ModuleSheafHom
import Hartshorne.Scheme.ModuleSheafTensor
import Hartshorne.Scheme.LocallyFreeInvertible

/-!
# Duality for finite locally free sheaves

Hartshorne, *Algebraic Geometry*, II, Exercise 5.1(a)–(c).

Let `X` be a scheme. For an `𝒪_X`-module `E` write `E^∨ = ℋom(E, 𝒪_X)` (`moduleSheafDual`), where
`ℋom` is the module sheaf of local morphisms `moduleSheafHom` and `⊗` is `moduleSheafTensor`.
A *finite locally free* module is one that is locally free (`Scheme.Modules.IsLocallyFree`) and has
finite rank at every point (`Scheme.Modules.rankAt E x < ℵ₀`). We prove:

* (a) the canonical evaluation map `E ⟶ E^∨∨` (`moduleSheafDoubleDualMap`) is natural in `E`
  and, for finite locally free `E`, an isomorphism (`moduleSheafDoubleDualMap_isIso`,
  `moduleSheafDoubleDualIso`);
* (b) the canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)`, induced by `(ψ, f) ↦ (x ↦ ψ(x) f)`
  (`moduleSheafDualTensorMap`), is natural in `E` and `F` and, for finite locally free `E` and
  any `F`, an isomorphism (`moduleSheafDualTensorMap_isIso`, `moduleSheafDualTensorIso`);
* (c) for all `𝒪_X`-modules `E`, `F`, `G` there is a bijection
  `Hom(E ⊗ F, G) ≃ Hom(F, ℋom(E, G))` (`moduleSheafTensorHomAdjunction`), natural in `E`, `F`
  and `G`. No finiteness is needed here.

The proofs of (a) and (b) are local. A *local frame* of `E` over an open `U` is a finite family
of sections `e_i ∈ E(U)` such that on every open `V ⊆ U` each section of `E` is uniquely an
`𝒪_X(V)`-linear combination of the restrictions `e_i|_V` (`IsLocalFrame`). A free module of finite
rank has a frame (`free_isLocalFrame`), so a finite locally free module has frames on an open
cover (`exists_isLocalFrame_of_isLocallyFree`). Local morphisms out of `E` over `V ⊆ U` are
determined by, and can be prescribed through, their values on a frame; hence the dual frame
`e_i^∨` is a frame of `E^∨` (`IsLocalFrame.dual`). On opens inside `U`, the double-dual map and
the presheaf-level map `E^∨(V) ⊗ F(V) → ℋom(E, F)(V)` are then bijective, and a morphism of sheaves
that is bijective on all small enough opens around every point (or on stalks) is an isomorphism.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits
open scoped TensorProduct

namespace Hartshorne

variable {X : Scheme.{u}}

/-- For a section `ψ` of `ℋom(E, G)` over `W` and an open `V ⊆ W`, the linear map
`E(V) → G(V)` given by `ψ`. -/
noncomputable def moduleSheafHomEval {E G : X.Modules} {W : X.Opens}
    (ψ : Γ(moduleSheafHom E G, W)) {V : X.Opens} (h : V ≤ W) :
    Γ(E, V) →ₗ[Γ(X, V)] Γ(G, V) :=
  ((moduleSheafHomOverSectionsAddEquiv E G W ψ).val.app (op (Over.mk (homOfLE h)))).hom

lemma moduleSheafHomEval_restrict {E G : X.Modules} {W W' V : X.Opens}
    (ψ : Γ(moduleSheafHom E G, W)) (i : W' ≤ W) (h : V ≤ W') :
    moduleSheafHomEval ((moduleSheafHom E G).presheaf.map (homOfLE i).op ψ) h =
      moduleSheafHomEval ψ (h.trans i) := rfl

lemma moduleSheafHomEval_add {E G : X.Modules} {W V : X.Opens}
    (ψ φ : Γ(moduleSheafHom E G, W)) (h : V ≤ W) :
    moduleSheafHomEval (ψ + φ) h = moduleSheafHomEval ψ h + moduleSheafHomEval φ h := rfl

lemma moduleSheafHomEval_smul {E G : X.Modules} {W V : X.Opens}
    (r : Γ(X, W)) (ψ : Γ(moduleSheafHom E G, W)) (h : V ≤ W) (x : Γ(E, V)) :
    moduleSheafHomEval (r • ψ) h x = X.presheaf.map (homOfLE h).op r • moduleSheafHomEval ψ h x :=
  rfl

lemma moduleSheafHomEval_natural {E G : X.Modules} {W V V' : X.Opens}
    (ψ : Γ(moduleSheafHom E G, W)) (h : V ≤ W) (i : V' ≤ V) (x : Γ(E, V)) :
    moduleSheafHomEval ψ (i.trans h) (E.presheaf.map (homOfLE i).op x) =
      G.presheaf.map (homOfLE i).op (moduleSheafHomEval ψ h x) := by
  let a : Over.mk (homOfLE (i.trans h)) ⟶ Over.mk (homOfLE h) := Over.homMk (homOfLE i)
  exact ConcreteCategory.congr_hom
    ((moduleSheafHomOverSectionsAddEquiv E G W ψ).val.naturality a.op) x

lemma moduleSheafHomEval_ext {E G : X.Modules} {W : X.Opens}
    {ψ φ : Γ(moduleSheafHom E G, W)}
    (hψφ : ∀ (V : X.Opens) (h : V ≤ W), moduleSheafHomEval ψ h = moduleSheafHomEval φ h) :
    ψ = φ := by
  apply (moduleSheafHomOverSectionsAddEquiv E G W).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro A
  ext x
  exact LinearMap.congr_fun (hψφ A.unop.left (leOfHom A.unop.hom)) x

/-- The section of `ℋom(E, G)` over `W` given by a family of linear maps `E(V) → G(V)`, `V ⊆ W`,
compatible with restriction. -/
noncomputable def moduleSheafHomMk {E G : X.Modules} {W : X.Opens}
    (f : ∀ V : X.Opens, V ≤ W → Γ(E, V) →ₗ[Γ(X, V)] Γ(G, V))
    (hf : ∀ (V V' : X.Opens) (hV : V ≤ W) (i : V' ≤ V) (x : Γ(E, V)),
      f V' (i.trans hV) (E.presheaf.map (homOfLE i).op x) =
        G.presheaf.map (homOfLE i).op (f V hV x)) :
    Γ(moduleSheafHom E G, W) :=
  (moduleSheafHomOverSectionsAddEquiv E G W).symm
    ⟨{ app A := ModuleCat.ofHom (X := (SheafOfModules.over E W).val.obj A)
          (Y := (SheafOfModules.over G W).val.obj A) (f A.unop.left (leOfHom A.unop.hom))
       naturality {A B} a := by
         ext x
         exact hf A.unop.left B.unop.left (leOfHom A.unop.hom) (leOfHom a.unop.left) x }⟩

lemma moduleSheafHomEval_mk {E G : X.Modules} {W : X.Opens}
    (f : ∀ V : X.Opens, V ≤ W → Γ(E, V) →ₗ[Γ(X, V)] Γ(G, V))
    (hf : ∀ (V V' : X.Opens) (hV : V ≤ W) (i : V' ≤ V) (x : Γ(E, V)),
      f V' (i.trans hV) (E.presheaf.map (homOfLE i).op x) =
        G.presheaf.map (homOfLE i).op (f V hV x)) {V : X.Opens} (h : V ≤ W) :
    moduleSheafHomEval (moduleSheafHomMk f hf) h = f V h := rfl

private lemma modules_map_map (A : X.Modules) {U V W : X.Opens} (i : V ≤ U) (j : W ≤ V)
    (x : Γ(A, U)) :
    A.presheaf.map (homOfLE j).op (A.presheaf.map (homOfLE i).op x) =
      A.presheaf.map (homOfLE (j.trans i)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma modules_map_id (A : X.Modules) {U : X.Opens} (x : Γ(A, U)) :
    A.presheaf.map (homOfLE (le_refl U)).op x = x := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma ring_map_id {U : X.Opens} (r : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_refl U)).op r = r := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The morphism of `𝒪_X`-modules given by a family of linear maps on sections compatible with
restriction. -/
noncomputable def modulesHomMk {A B : X.Modules}
    (f : ∀ U : X.Opens, Γ(A, U) →ₗ[Γ(X, U)] Γ(B, U))
    (hf : ∀ (U V : X.Opens) (i : V ≤ U) (x : Γ(A, U)),
      f V (A.presheaf.map (homOfLE i).op x) = B.presheaf.map (homOfLE i).op (f U x)) :
    A ⟶ B :=
  ⟨{ app U := ModuleCat.ofHom (X := A.val.obj U) (Y := B.val.obj U) (f U.unop)
     naturality {U V} i := by
       ext x
       exact hf U.unop V.unop (leOfHom i.unop) x }⟩

lemma modulesHomMk_app {A B : X.Modules} (f : ∀ U : X.Opens, Γ(A, U) →ₗ[Γ(X, U)] Γ(B, U))
    (hf : ∀ (U V : X.Opens) (i : V ≤ U) (x : Γ(A, U)),
      f V (A.presheaf.map (homOfLE i).op x) = B.presheaf.map (homOfLE i).op (f U x))
    (U : X.Opens) (x : Γ(A, U)) : (modulesHomMk f hf).app U x = f U x := rfl

section Adjunction

variable {E F G : X.Modules}

/-- The local morphism `e ↦ β(e, f)` attached to a section `f` of `F`. -/
noncomputable def bilinearCurrySection (β : ModuleSheafBilinear E F G) (U : X.Opens)
    (f : Γ(F, U)) :
    Γ(moduleSheafHom E G, U) :=
  moduleSheafHomMk (fun V h => (β.app (op V)).flip (F.presheaf.map (homOfLE h).op f))
    (by
      intro V V' hV i x
      change β.app (op V') (E.presheaf.map (homOfLE i).op x)
          (F.presheaf.map (homOfLE (i.trans hV)).op f) =
        G.presheaf.map (homOfLE i).op (β.app (op V) x (F.presheaf.map (homOfLE hV).op f))
      rw [← modules_map_map F hV i]
      exact (β.naturality (homOfLE i).op x _).symm)

lemma bilinearCurrySection_eval (β : ModuleSheafBilinear E F G) (U : X.Opens) (f : Γ(F, U))
    {V : X.Opens} (h : V ≤ U) (e : Γ(E, V)) :
    moduleSheafHomEval (bilinearCurrySection β U f) h e =
      β.app (op V) e (F.presheaf.map (homOfLE h).op f) := rfl

/-- The morphism `F ⟶ ℋom(E, G)`, `f ↦ (e ↦ β(e, f))`, attached to a bilinear map `β`. -/
noncomputable def bilinearCurry (β : ModuleSheafBilinear E F G) : F ⟶ moduleSheafHom E G :=
  modulesHomMk (fun U =>
    { toFun := bilinearCurrySection β U
      map_add' := fun f f' => moduleSheafHomEval_ext fun V h => by
        ext e
        change β.app (op V) e (F.presheaf.map (homOfLE h).op (f + f')) =
          β.app (op V) e (F.presheaf.map (homOfLE h).op f) +
            β.app (op V) e (F.presheaf.map (homOfLE h).op f')
        rw [map_add]
        exact map_add (β.app (op V) e) _ _
      map_smul' := fun r f => moduleSheafHomEval_ext fun V h => by
        ext e
        rw [RingHom.id_apply, moduleSheafHomEval_smul, bilinearCurrySection_eval,
          bilinearCurrySection_eval, Scheme.Modules.map_smul]
        exact map_smul (β.app (op V) e) _ _ })
    (fun U V i f => moduleSheafHomEval_ext fun W h => by
      ext e
      change β.app (op W) e (F.presheaf.map (homOfLE h).op (F.presheaf.map (homOfLE i).op f)) =
        β.app (op W) e (F.presheaf.map (homOfLE (h.trans i)).op f)
      rw [modules_map_map])

private lemma homUncurry_naturality (φ : F ⟶ moduleSheafHom E G) {U V : X.Opens} (i : V ≤ U)
    (e : Γ(E, U)) (f : Γ(F, U)) :
    G.presheaf.map (homOfLE i).op (moduleSheafHomEval (φ.app U f) (le_refl U) e) =
      moduleSheafHomEval (φ.app V (F.presheaf.map (homOfLE i).op f)) (le_refl V)
        (E.presheaf.map (homOfLE i).op e) := by
  rw [← moduleSheafHomEval_natural]
  have h := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE i).op) f
  change φ.app V (F.presheaf.map (homOfLE i).op f) =
    (moduleSheafHom E G).presheaf.map (homOfLE i).op (φ.app U f) at h
  rw [h, moduleSheafHomEval_restrict]

private lemma homUncurry_smul (φ : F ⟶ moduleSheafHom E G) (U : X.Opens) (r : Γ(X, U))
    (e : Γ(E, U)) (f : Γ(F, U)) :
    moduleSheafHomEval (φ.app U (r • f)) (le_refl U) e =
      r • moduleSheafHomEval (φ.app U f) (le_refl U) e := by
  rw [Scheme.Modules.Hom.app_smul, moduleSheafHomEval_smul, ring_map_id]

/-- The bilinear map `(e, f) ↦ φ(f)(e)` attached to `φ : F ⟶ ℋom(E, G)`. -/
noncomputable def homUncurry (φ : F ⟶ moduleSheafHom E G) : ModuleSheafBilinear E F G where
  app U := LinearMap.mk₂ _ (fun (e : Γ(E, U.unop)) (f : Γ(F, U.unop)) =>
      moduleSheafHomEval (φ.app U.unop f) (le_refl U.unop) e)
    (fun e e' f => map_add _ e e')
    (fun r e f => map_smul _ r e)
    (fun (e : Γ(E, U.unop)) (f f' : Γ(F, U.unop)) => by
      change moduleSheafHomEval (φ.app U.unop (f + f')) _ e = _
      rw [map_add]; rfl)
    (fun r e f => homUncurry_smul φ U.unop r e f)
  naturality {U V} i e f := homUncurry_naturality φ (leOfHom i.unop) e f

lemma bilinearCurry_app_eval (β : ModuleSheafBilinear E F G) (U : X.Opens) (f : Γ(F, U))
    {V : X.Opens} (h : V ≤ U) (e : Γ(E, V)) :
    moduleSheafHomEval ((bilinearCurry β).app U f) h e =
      β.app (op V) e (F.presheaf.map (homOfLE h).op f) := rfl

/-- Bilinear maps `E × F → G` correspond to morphisms `F ⟶ ℋom(E, G)`. -/
noncomputable def bilinearCurryEquiv :
    ModuleSheafBilinear E F G ≃ (F ⟶ moduleSheafHom E G) where
  toFun := bilinearCurry
  invFun := homUncurry
  left_inv β := by
    ext U e f
    exact congrArg (β.app U e) (modules_map_id F (U := U.unop) f)
  right_inv φ := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext f
    refine moduleSheafHomEval_ext fun V h => ?_
    ext e
    change moduleSheafHomEval (φ.app V (F.presheaf.map (homOfLE h).op f)) (le_refl V) e =
      moduleSheafHomEval (φ.app U f) h e
    have hn := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) f
    change φ.app V (F.presheaf.map (homOfLE h).op f) =
      (moduleSheafHom E G).presheaf.map (homOfLE h).op (φ.app U f) at hn
    rw [hn, moduleSheafHomEval_restrict]

variable (E F G) in
/-- **Hartshorne II, Exercise 5.1(c): the tensor–Hom adjunction.** For all `𝒪_X`-modules `E`, `F`,
`G`, morphisms `E ⊗ F ⟶ G` correspond bijectively to morphisms `F ⟶ ℋom(E, G)`: a morphism
`φ` corresponds to `f ↦ (e ↦ φ(e ⊗ f))`. -/
noncomputable def moduleSheafTensorHomAdjunction :
    (@Quiver.Hom X.Modules _ (moduleSheafTensor E F) G) ≃ (F ⟶ moduleSheafHom E G) :=
  (moduleSheafTensorHomEquiv E F G).trans bilinearCurryEquiv

lemma moduleSheafTensorHomAdjunction_app_eval
    (φ : @Quiver.Hom X.Modules _ (moduleSheafTensor E F) G) (U : X.Opens) (f : Γ(F, U))
    {V : X.Opens} (h : V ≤ U) (e : Γ(E, V)) :
    moduleSheafHomEval ((moduleSheafTensorHomAdjunction E F G φ).app U f) h e =
      φ.app V ((moduleSheafTensorBilinear E F).app (op V) e (F.presheaf.map (homOfLE h).op f)) :=
  rfl

/-- The tensor–Hom adjunction is natural in `G`. -/
lemma moduleSheafTensorHomAdjunction_naturality_target {G' : X.Modules}
    (φ : @Quiver.Hom X.Modules _ (moduleSheafTensor E F) G) (g : G ⟶ G') :
    moduleSheafTensorHomAdjunction E F G' (φ ≫ g) =
      moduleSheafTensorHomAdjunction E F G φ ≫ moduleSheafHomMap (𝟙 E) g := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext f
  refine moduleSheafHomEval_ext fun V h => ?_
  ext e
  rfl

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
lemma modules_isIso_of_stalk_bijective {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ x : X, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.mapPresheaf)) :
    IsIso φ := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  let f : (⟨A.presheaf, A.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) ⟶
      ⟨B.presheaf, B.isSheaf⟩ := ⟨φ.mapPresheaf⟩
  have hb := TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U (fun x _ => h x)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

/-- A morphism of `𝒪_X`-modules is an isomorphism if every point has an open neighbourhood on
all of whose open subsets it is bijective on sections. -/
lemma modules_isIso_of_locally_bijective {A B : X.Modules} (φ : A ⟶ B)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U → Function.Bijective (φ.app V)) :
    IsIso φ :=
  modules_isIso_of_stalk_bijective φ fun x => by
    obtain ⟨W, hxW, hW⟩ := h x
    exact stalkFunctor_map_bijective_of_locally_bijective φ.mapPresheaf hxW hW

end Locality

section Frames

variable {ι : Type*} [Fintype ι]

/-- The map `(a_i) ↦ ∑ a_i e_i|_V`. -/
noncomputable def localFrameMap (A : X.Modules) {U : X.Opens} (e : ι → Γ(A, U)) {V : X.Opens}
    (h : V ≤ U) : (ι → Γ(X, V)) →ₗ[Γ(X, V)] Γ(A, V) :=
  Fintype.linearCombination Γ(X, V) (fun i => A.presheaf.map (homOfLE h).op (e i))

lemma localFrameMap_apply (A : X.Modules) {U : X.Opens} (e : ι → Γ(A, U)) {V : X.Opens}
    (h : V ≤ U) (a : ι → Γ(X, V)) :
    localFrameMap A e h a = ∑ i, a i • A.presheaf.map (homOfLE h).op (e i) :=
  Fintype.linearCombination_apply _ _ _

/-- A finite family of sections over `U` is a *local frame* if on every smaller open `V` every
section is uniquely a linear combination of the restricted family. -/
def IsLocalFrame (A : X.Modules) (U : X.Opens) (e : ι → Γ(A, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U), Function.Bijective (localFrameMap A e h)

lemma localFrameMap_restrict (A : X.Modules) {U : X.Opens} (e : ι → Γ(A, U)) {V V' : X.Opens}
    (h : V ≤ U) (j : V' ≤ V) (a : ι → Γ(X, V)) :
    A.presheaf.map (homOfLE j).op (localFrameMap A e h a) =
      localFrameMap A e (j.trans h) (fun i => X.presheaf.map (homOfLE j).op (a i)) := by
  rw [localFrameMap_apply, localFrameMap_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.map_smul, modules_map_map]

lemma localFrameMap_single (A : X.Modules) {U : X.Opens} (e : ι → Γ(A, U)) {V : X.Opens}
    (h : V ≤ U) [DecidableEq ι] (j : ι) :
    localFrameMap A e h (Pi.single j 1) = A.presheaf.map (homOfLE h).op (e j) := by
  rw [localFrameMap, Fintype.linearCombination_apply_single, one_smul]

/-- Evaluation of a local morphism at the restricted frame vectors. -/
noncomputable def localFrameEval {A G : X.Modules} {U : X.Opens} (e : ι → Γ(A, U))
    {W : X.Opens} (hW : W ≤ U) : Γ(moduleSheafHom A G, W) →ₗ[Γ(X, W)] (ι → Γ(G, W)) where
  toFun ψ j := moduleSheafHomEval ψ (le_refl W) (A.presheaf.map (homOfLE hW).op (e j))
  map_add' _ _ := rfl
  map_smul' r ψ := by
    funext j
    change moduleSheafHomEval (r • ψ) (le_refl W) _ = r • _
    rw [moduleSheafHomEval_smul, ring_map_id]

omit [Fintype ι] in
lemma localFrameEval_apply {A G : X.Modules} {U : X.Opens} (e : ι → Γ(A, U)) {W : X.Opens}
    (hW : W ≤ U) (ψ : Γ(moduleSheafHom A G, W)) (j : ι) :
    localFrameEval e hW ψ j =
      moduleSheafHomEval ψ (le_refl W) (A.presheaf.map (homOfLE hW).op (e j)) :=
  rfl

namespace IsLocalFrame

variable {A : X.Modules} {U : X.Opens} {e : ι → Γ(A, U)} (hA : IsLocalFrame A U e)
include hA

/-- Coordinates with respect to a frame. -/
noncomputable def coord {V : X.Opens} (h : V ≤ U) : Γ(A, V) ≃ₗ[Γ(X, V)] (ι → Γ(X, V)) :=
  (LinearEquiv.ofBijective (localFrameMap A e h) (hA V h)).symm

lemma localFrameMap_coord {V : X.Opens} (h : V ≤ U) (x : Γ(A, V)) :
    localFrameMap A e h (hA.coord h x) = x :=
  (LinearEquiv.ofBijective (localFrameMap A e h) (hA V h)).apply_symm_apply x

lemma coord_localFrameMap {V : X.Opens} (h : V ≤ U) (a : ι → Γ(X, V)) :
    hA.coord h (localFrameMap A e h a) = a :=
  (LinearEquiv.ofBijective (localFrameMap A e h) (hA V h)).symm_apply_apply a

lemma coord_restrict {V V' : X.Opens} (h : V ≤ U) (j : V' ≤ V) (x : Γ(A, V)) :
    hA.coord (j.trans h) (A.presheaf.map (homOfLE j).op x) =
      fun i => X.presheaf.map (homOfLE j).op (hA.coord h x i) := by
  have := localFrameMap_restrict A e h j (hA.coord h x)
  rw [hA.localFrameMap_coord] at this
  rw [this, coord_localFrameMap]

lemma coord_self [DecidableEq ι] {V : X.Opens} (h : V ≤ U) (j : ι) :
    hA.coord h (A.presheaf.map (homOfLE h).op (e j)) = Pi.single j 1 := by
  rw [← localFrameMap_single A e h j, coord_localFrameMap]

lemma hom_ext {G : X.Modules} {W : X.Opens} (hW : W ≤ U) {ψ φ : Γ(moduleSheafHom A G, W)}
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
noncomputable def homOfValues {G : X.Modules} {W : X.Opens} (hW : W ≤ U) (g : ι → Γ(G, W)) :
    Γ(moduleSheafHom A G, W) :=
  moduleSheafHomMk (fun V h => (Fintype.linearCombination Γ(X, V)
      (fun i => G.presheaf.map (homOfLE h).op (g i))) ∘ₗ (hA.coord (h.trans hW)).toLinearMap)
    (by
      intro V V' hV j x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Fintype.linearCombination_apply]
      rw [hA.coord_restrict (hV.trans hW) j x, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Scheme.Modules.map_smul, modules_map_map])

lemma homOfValues_eval {G : X.Modules} {W : X.Opens} (hW : W ≤ U) (g : ι → Γ(G, W))
    {V : X.Opens} (h : V ≤ W) (x : Γ(A, V)) :
    moduleSheafHomEval (hA.homOfValues hW g) h x =
      ∑ i, hA.coord (h.trans hW) x i • G.presheaf.map (homOfLE h).op (g i) := by
  rw [homOfValues, moduleSheafHomEval_mk]
  exact Fintype.linearCombination_apply _ _ _

lemma localFrameEval_homOfValues {G : X.Modules} {W : X.Opens} (hW : W ≤ U) (g : ι → Γ(G, W)) :
    localFrameEval e hW (hA.homOfValues hW g) = g := by
  classical
  funext j
  rw [localFrameEval_apply]
  change (Fintype.linearCombination Γ(X, W)
      (fun i => G.presheaf.map (homOfLE (le_refl W)).op (g i)))
    (hA.coord ((le_refl W).trans hW) (A.presheaf.map (homOfLE hW).op (e j))) = g j
  rw [hA.coord_self, Fintype.linearCombination_apply_single, one_smul, modules_map_id]

lemma localFrameEval_bijective {G : X.Modules} {W : X.Opens} (hW : W ≤ U) :
    Function.Bijective (localFrameEval (G := G) e hW) :=
  ⟨fun _ _ h => hA.hom_ext hW h, fun g => ⟨hA.homOfValues hW g, hA.localFrameEval_homOfValues hW g⟩⟩

end IsLocalFrame

end Frames

section Dual

variable (X) in
/-- The structure sheaf `𝒪_X` as an `𝒪_X`-module. -/
noncomputable abbrev structureModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- The dual `E^∨ = ℋom(E, 𝒪_X)` of an `𝒪_X`-module. -/
noncomputable abbrev moduleSheafDual (E : X.Modules) : X.Modules :=
  moduleSheafHom E (structureModule X)

/-- Evaluation of a local section of the dual, valued in the structure sheaf. -/
noncomputable def dualEval {E : X.Modules} {W : X.Opens} (ψ : Γ(moduleSheafDual E, W))
    {V : X.Opens} (h : V ≤ W) : Γ(E, V) →ₗ[Γ(X, V)] Γ(X, V) :=
  moduleSheafHomEval ψ h

lemma moduleSheafHomEval_map {E E' G G' : X.Modules} (f : E' ⟶ E) (g : G ⟶ G') {W : X.Opens}
    (ψ : Γ(moduleSheafHom E G, W)) {V : X.Opens} (h : V ≤ W) (x : Γ(E', V)) :
    moduleSheafHomEval ((moduleSheafHomMap f g).app W ψ) h x =
      g.app V (moduleSheafHomEval ψ h (f.app V x)) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
private lemma sum_single_smul {M : Type*} [AddCommGroup M] {R : Type*} [Ring R] [Module R M]
    [Fintype ι] (j : ι) (v : ι → M) : ∑ k, (Pi.single j (1 : R) : ι → R) k • v k = v j := by
  rw [← Fintype.linearCombination_apply R, Fintype.linearCombination_apply_single, one_smul]

omit [DecidableEq ι] in
lemma localFrameMap_eval {A G : X.Modules} {U : X.Opens} (e : ι → Γ(A, U)) {V : X.Opens} (h : V ≤ U)
    (ψ : Γ(moduleSheafHom A G, V)) (a : ι → Γ(X, V)) :
    moduleSheafHomEval ψ (le_refl V) (localFrameMap A e h a) =
      ∑ i, a i • localFrameEval e h ψ i := by
  rw [localFrameMap_apply, map_sum]
  simp_rw [map_smul]
  rfl

namespace IsLocalFrame

variable {A : X.Modules} {U : X.Opens} {e : ι → Γ(A, U)} (hA : IsLocalFrame A U e)
include hA

/-- The dual frame `e_i^∨` of `E^∨` over `U`. -/
noncomputable def dualLocalFrame (i : ι) : Γ(moduleSheafDual A, U) :=
  hA.homOfValues (G := structureModule X) (le_refl U) (Pi.single i (1 : Γ(X, U)))

lemma localFrameEval_dualLocalFrame {V : X.Opens} (h : V ≤ U) (i : ι) :
    localFrameEval e h ((moduleSheafDual A).presheaf.map (homOfLE h).op (hA.dualLocalFrame i)) =
      (Pi.single i (1 : Γ(X, V)) : ι → Γ(X, V)) := by
  funext j
  rw [localFrameEval_apply, moduleSheafHomEval_restrict, dualLocalFrame, homOfValues_eval,
    hA.coord_self, sum_single_smul]
  change X.presheaf.map (homOfLE h).op ((Pi.single i (1 : Γ(X, U)) : ι → Γ(X, U)) j) =
    (Pi.single i (1 : Γ(X, V)) : ι → Γ(X, V)) j
  by_cases hij : j = i
  · subst hij
    rw [Pi.single_eq_same, Pi.single_eq_same]
    exact map_one _
  · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij]
    exact map_zero _

lemma localFrameEval_localFrameMap_dualLocalFrame {V : X.Opens} (h : V ≤ U) (a : ι → Γ(X, V)) :
    localFrameEval e h (localFrameMap (moduleSheafDual A) hA.dualLocalFrame h a) = a := by
  rw [localFrameMap_apply, map_sum]
  simp_rw [map_smul, hA.localFrameEval_dualLocalFrame h]
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · change a j * (Pi.single j (1 : Γ(X, V)) : ι → Γ(X, V)) j = a j
    rw [Pi.single_eq_same, mul_one]
  · intro k _ hk
    change a k * (Pi.single k (1 : Γ(X, V)) : ι → Γ(X, V)) j = 0
    rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero]
  · intro h'; exact absurd (Finset.mem_univ j) h'

lemma localFrameMap_dualLocalFrame_localFrameEval {V : X.Opens} (h : V ≤ U)
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
noncomputable def doubleDualSection (E : X.Modules) {U : X.Opens} (x : Γ(E, U)) :
    Γ(moduleSheafDual (moduleSheafDual E), U) :=
  moduleSheafHomMk
    (fun V h =>
      { toFun := fun ψ : Γ(moduleSheafDual E, V) =>
          moduleSheafHomEval ψ (le_refl V) (E.presheaf.map (homOfLE h).op x)
        map_add' := fun _ _ => rfl
        map_smul' := fun r ψ => by
          rw [RingHom.id_apply, moduleSheafHomEval_smul, ring_map_id] })
    (by
      intro V V' hV j ψ
      change moduleSheafHomEval ((moduleSheafDual E).presheaf.map (homOfLE j).op ψ) (le_refl V')
          (E.presheaf.map (homOfLE (j.trans hV)).op x) =
        (structureModule X).presheaf.map (homOfLE j).op
          (moduleSheafHomEval ψ (le_refl V) (E.presheaf.map (homOfLE hV).op x))
      rw [moduleSheafHomEval_restrict, ← modules_map_map E hV j,
        ← moduleSheafHomEval_natural ψ (le_refl V) j])

lemma doubleDualSection_eval (E : X.Modules) {U : X.Opens} (x : Γ(E, U)) {V : X.Opens}
    (h : V ≤ U) (ψ : Γ(moduleSheafDual E, V)) :
    moduleSheafHomEval (doubleDualSection E x) h ψ =
      moduleSheafHomEval ψ (le_refl V) (E.presheaf.map (homOfLE h).op x) := rfl

/-- The canonical map `E ⟶ E^∨∨`, sending a section to evaluation at it. -/
noncomputable def moduleSheafDoubleDualMap (E : X.Modules) :
    E ⟶ moduleSheafDual (moduleSheafDual E) :=
  modulesHomMk
    (fun U =>
      { toFun := doubleDualSection E
        map_add' := fun x y => moduleSheafHomEval_ext fun V h => LinearMap.ext fun ψ => by
          rw [moduleSheafHomEval_add, LinearMap.add_apply, doubleDualSection_eval,
            doubleDualSection_eval, doubleDualSection_eval, map_add, map_add]
        map_smul' := fun r x => moduleSheafHomEval_ext fun V h => LinearMap.ext fun ψ => by
          rw [RingHom.id_apply, moduleSheafHomEval_smul, doubleDualSection_eval,
            doubleDualSection_eval, Scheme.Modules.map_smul, map_smul] })
    (fun U V i x => moduleSheafHomEval_ext fun W h => LinearMap.ext fun ψ => by
      change moduleSheafHomEval (doubleDualSection E (E.presheaf.map (homOfLE i).op x)) h ψ =
        moduleSheafHomEval (doubleDualSection E x) (h.trans i) ψ
      rw [doubleDualSection_eval, doubleDualSection_eval, modules_map_map])

lemma moduleSheafDoubleDualMap_app_eval (E : X.Modules) {U : X.Opens} (x : Γ(E, U))
    {V : X.Opens} (h : V ≤ U) (ψ : Γ(moduleSheafDual E, V)) :
    moduleSheafHomEval ((moduleSheafDoubleDualMap E).app U x) h ψ =
      moduleSheafHomEval ψ (le_refl V) (E.presheaf.map (homOfLE h).op x) := rfl

/-- The double-dual map is natural in `E`. -/
lemma moduleSheafDoubleDualMap_naturality {E E' : X.Modules} (f : E ⟶ E') :
    f ≫ moduleSheafDoubleDualMap E' =
      moduleSheafDoubleDualMap E ≫
        moduleSheafHomMap (moduleSheafHomMap f (𝟙 (structureModule X)))
          (𝟙 (structureModule X)) := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun ψ => ?_
  change moduleSheafHomEval ψ (le_refl V) (E'.presheaf.map (homOfLE h).op (f.app U x)) =
    moduleSheafHomEval ψ (le_refl V) (f.app V (E.presheaf.map (homOfLE h).op x))
  have := ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE h).op) x
  change f.app V (E.presheaf.map (homOfLE h).op x) = E'.presheaf.map (homOfLE h).op (f.app U x)
    at this
  rw [this]

lemma localFrameEval_doubleDualMap {ι : Type*} [Fintype ι] [DecidableEq ι] {E : X.Modules}
    {U : X.Opens} {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) {V : X.Opens} (h : V ≤ U)
    (a : ι → Γ(X, V)) :
    localFrameEval hE.dualLocalFrame h
      ((moduleSheafDoubleDualMap E).app V (localFrameMap E e h a)) = a := by
  funext j
  rw [localFrameEval_apply, moduleSheafDoubleDualMap_app_eval, modules_map_id, localFrameMap_eval,
    hE.localFrameEval_dualLocalFrame h]
  rw [Finset.sum_eq_single j]
  · change a j * (Pi.single j (1 : Γ(X, V)) : ι → Γ(X, V)) j = a j
    rw [Pi.single_eq_same, mul_one]
  · intro k _ hk
    change a k * (Pi.single j (1 : Γ(X, V)) : ι → Γ(X, V)) k = 0
    rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro h'; exact absurd (Finset.mem_univ j) h'

/-- On an open with a frame, the double-dual map is bijective on sections. -/
lemma doubleDualMap_bijective_of_isLocalFrame {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : X.Modules} {U : X.Opens} {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) {V : X.Opens} (h : V ≤ U) :
    Function.Bijective ((moduleSheafDoubleDualMap E).app V) := by
  have hc : (moduleSheafDoubleDualMap E).app V ∘ localFrameMap E e h =
      localFrameMap _ hE.dual.dualLocalFrame h := by
    funext a
    exact hE.dual.hom_ext h ((localFrameEval_doubleDualMap hE h a).trans
      (hE.dual.localFrameEval_localFrameMap_dualLocalFrame h a).symm)
  rw [← Function.Bijective.of_comp_iff _ (hE V h), hc]
  exact hE.dual.dual V h

end DoubleDual

section DualTensor

/-- The local morphism `x ↦ ψ(x) f` attached to sections `ψ` of `E^∨` and `f` of `F`. -/
noncomputable def dualTensorSection {E F : X.Modules} {U : X.Opens} (ψ : Γ(moduleSheafDual E, U))
    (f : Γ(F, U)) : Γ(moduleSheafHom E F, U) :=
  moduleSheafHomMk
    (fun V h => (LinearMap.toSpanSingleton Γ(X, V) Γ(F, V) (F.presheaf.map (homOfLE h).op f)) ∘ₗ
      dualEval ψ h)
    (by
      intro V V' hV j x
      change dualEval ψ (j.trans hV) (E.presheaf.map (homOfLE j).op x) •
          F.presheaf.map (homOfLE (j.trans hV)).op f =
        F.presheaf.map (homOfLE j).op (dualEval ψ hV x • F.presheaf.map (homOfLE hV).op f)
      rw [Scheme.Modules.map_smul, modules_map_map]
      congr 1
      exact moduleSheafHomEval_natural ψ hV j x)

lemma dualTensorSection_eval {E F : X.Modules} {U : X.Opens} (ψ : Γ(moduleSheafDual E, U))
    (f : Γ(F, U)) {V : X.Opens} (h : V ≤ U) (x : Γ(E, V)) :
    moduleSheafHomEval (dualTensorSection ψ f) h x =
      dualEval ψ h x • F.presheaf.map (homOfLE h).op f := rfl

private lemma modules_mul_smul (F : X.Modules) {V : X.Opens} (r s : Γ(X, V)) (y : Γ(F, V)) :
    (r * s) • y = r • s • y :=
  mul_smul r s y

section
variable {E F : X.Modules} {U : X.Opens}

lemma dualTensorSection_add_left (ψ ψ' : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) :
    dualTensorSection (ψ + ψ') f = dualTensorSection ψ f + dualTensorSection ψ' f :=
  moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_add, LinearMap.add_apply, dualTensorSection_eval,
      dualTensorSection_eval, dualTensorSection_eval]
    exact add_smul _ _ _

lemma dualTensorSection_smul_left (r : Γ(X, U)) (ψ : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) :
    dualTensorSection (r • ψ) f = r • dualTensorSection ψ f :=
  moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_smul, dualTensorSection_eval, dualTensorSection_eval]
    exact modules_mul_smul F (X.presheaf.map (homOfLE h).op r) (dualEval ψ h x) _

lemma dualTensorSection_add_right (ψ : Γ(moduleSheafDual E, U)) (f f' : Γ(F, U)) :
    dualTensorSection ψ (f + f') = dualTensorSection ψ f + dualTensorSection ψ f' :=
  moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_add, LinearMap.add_apply, dualTensorSection_eval,
      dualTensorSection_eval, dualTensorSection_eval, map_add]
    exact smul_add _ _ _

lemma dualTensorSection_smul_right (r : Γ(X, U)) (ψ : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) :
    dualTensorSection ψ (r • f) = r • dualTensorSection ψ f :=
  moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_smul, dualTensorSection_eval, dualTensorSection_eval,
      Scheme.Modules.map_smul]
    exact smul_comm _ _ _

lemma dualTensorSection_restrict (ψ : Γ(moduleSheafDual E, U)) (f : Γ(F, U)) {V : X.Opens}
    (i : V ≤ U) :
    (moduleSheafHom E F).presheaf.map (homOfLE i).op (dualTensorSection ψ f) =
      dualTensorSection ((moduleSheafDual E).presheaf.map (homOfLE i).op ψ)
        (F.presheaf.map (homOfLE i).op f) :=
  moduleSheafHomEval_ext fun W h => LinearMap.ext fun x => by
    rw [moduleSheafHomEval_restrict, dualTensorSection_eval, dualTensorSection_eval,
      modules_map_map]
    rfl

end

variable (E F : X.Modules) in
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

variable (E F : X.Modules) in
/-- The canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)`, induced by `(ψ, f) ↦ (x ↦ ψ(x) f)`. -/
noncomputable def moduleSheafDualTensorMap :
    @Quiver.Hom X.Modules _ (moduleSheafTensor (moduleSheafDual E) F) (moduleSheafHom E F) :=
  (moduleSheafTensorHomEquiv _ _ _).symm (dualTensorBilinear E F)

lemma moduleSheafDualTensorMap_tmul {E F : X.Modules} {U : X.Opens}
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

variable {E F : X.Modules}

/-- The presheaf-level map `U ↦ E^∨(U) ⊗ F(U) → ℋom(E, F)(U)` underlying the canonical map. -/
noncomputable abbrev dualTensorPresheafMap (E F : X.Modules) :
    (moduleSheafTensorPresheaf (moduleSheafDual E) F).presheaf ⟶ (moduleSheafHom E F).presheaf :=
  (PresheafOfModules.toPresheaf _).map
    (moduleSheafTensorUnit (moduleSheafDual E) F ≫ (moduleSheafDualTensorMap E F).val)

lemma dualTensorPresheafMap_tmul {V : X.Opens} (ψ : Γ(moduleSheafDual E, V)) (f : Γ(F, V)) :
    (dualTensorPresheafMap E F).app (op V)
        (show (moduleSheafTensorPresheaf (moduleSheafDual E) F).obj (op V) from ψ ⊗ₜ f) =
      dualTensorSection ψ f :=
  moduleSheafDualTensorMap_tmul ψ f

lemma dualTensorPresheafMap_bijective {ι : Type*} [Fintype ι] [DecidableEq ι] {U : X.Opens}
    {e : ι → Γ(E, U)} (hE : IsLocalFrame E U e) {V : X.Opens} (h : V ≤ U) :
    Function.Bijective ((dualTensorPresheafMap E F).app (op V)) := by
  rw [← Function.Bijective.of_comp_iff' (hE.localFrameEval_bijective (G := F) h)]
  let Φ : TensorProduct Γ(X, V) Γ(moduleSheafDual E, V) Γ(F, V) →+ (ι → Γ(F, V)) :=
    (localFrameEval e h).toAddMonoidHom.comp ((dualTensorPresheafMap E F).app (op V)).hom
  have := tensor_localFrame_bijective (R := Γ(X, V)) (M := Γ(moduleSheafDual E, V)) (N := Γ(F, V))
    (fun j => (moduleSheafDual E).presheaf.map (homOfLE h).op (hE.dualLocalFrame j))
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
    (hE : ∀ x : X, ∃ (U : X.Opens) (ι : Type u) (_ : Fintype ι) (e : ι → Γ(E, U)),
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
        (Scheme.Modules.Hom.mapPresheaf (moduleSheafDualTensorMap E F)) :=
    (PresheafOfModules.toPresheaf _).map_comp _ _
  have e := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map_comp
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (moduleSheafTensorPresheaf (moduleSheafDual E) F).presheaf)
    (Scheme.Modules.Hom.mapPresheaf (moduleSheafDualTensorMap E F))
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

section FreeFrame

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {Y : Scheme.{u}} {I : Type u} [Fintype I] [DecidableEq I]

/-- The `i`-th coordinate projection of a finite free module. -/
private noncomputable def freeProj (i : I) :
    (SheafOfModules.free I : SheafOfModules Y.ringCatSheaf) ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  (biproduct.isoCoproduct (fun _ : I => SheafOfModules.unit Y.ringCatSheaf)).inv ≫
    biproduct.π (fun _ : I => SheafOfModules.unit Y.ringCatSheaf) i

private lemma ιFree_freeProj (i j : I) :
    SheafOfModules.ιFree i ≫ freeProj (Y := Y) j = if i = j then 𝟙 _ else 0 :=
  sigma_ι_isoCoproduct_inv_π _ i j

omit [DecidableEq I] in
private lemma sum_freeProj_ιFree :
    ∑ i, freeProj (Y := Y) i ≫ SheafOfModules.ιFree (I := I) i = 𝟙 _ :=
  sum_isoCoproduct_inv_π_sigma_ι _

variable (Y I) in
/-- The free module `𝒪_Y^{⊕ I}` as an object of `Y.Modules`. -/
noncomputable abbrev freeModule : Y.Modules := SheafOfModules.free I

/-- The `i`-th inclusion `𝒪_Y ⟶ 𝒪_Y^{⊕ I}`, as a morphism of `Y.Modules`. -/
noncomputable def freeIncl (i : I) : structureModule Y ⟶ freeModule Y I :=
  SheafOfModules.ιFree i

/-- The `i`-th projection `𝒪_Y^{⊕ I} ⟶ 𝒪_Y`, as a morphism of `Y.Modules`. -/
noncomputable def freeProjM (i : I) : freeModule Y I ⟶ structureModule Y :=
  freeProj i

private lemma freeIncl_freeProjM (i j : I) :
    freeIncl (Y := Y) i ≫ freeProjM j = if i = j then 𝟙 _ else 0 :=
  ιFree_freeProj i j

omit [DecidableEq I] in
private lemma sum_freeProjM_freeIncl :
    ∑ i, freeProjM (Y := Y) (I := I) i ≫ freeIncl i = 𝟙 _ :=
  sum_freeProj_ιFree

omit [Fintype I] [DecidableEq I] in
private lemma freeIncl_app_smul_one (i : I) (V : Y.Opens) (r : Γ(Y, V)) :
    r • (freeIncl (Y := Y) (I := I) i).app V (1 : Γ(Y, V)) = (freeIncl i).app V r := by
  have h := Scheme.Modules.Hom.app_smul (freeIncl (Y := Y) (I := I) i) r
    (show Γ(structureModule Y, V) from (1 : Γ(Y, V)))
  refine h.symm.trans ?_
  congr 1
  exact mul_one r

omit [Fintype I] [DecidableEq I] in
private lemma freeIncl_app_restrict (i : I) {U V : Y.Opens} (h : V ≤ U) :
    (freeModule Y I).presheaf.map (homOfLE h).op
        ((freeIncl (Y := Y) (I := I) i).app U (1 : Γ(Y, U))) =
      (freeIncl i).app V (1 : Γ(Y, V)) := by
  have := ConcreteCategory.congr_hom
    ((freeIncl (Y := Y) (I := I) i).mapPresheaf.naturality (homOfLE h).op) (1 : Γ(Y, U))
  refine this.symm.trans ?_
  change (freeIncl (Y := Y) (I := I) i).app V (Y.presheaf.map (homOfLE h).op 1) = _
  rw [map_one]

/-- The value of a morphism of modules at a fixed section, as an additive map. -/
private noncomputable def homEvalAddHom {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) :
    (M ⟶ N) →+ Γ(N, V) where
  toFun φ := φ.app V x
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **The standard frame of a finite free module.** -/
lemma free_isLocalFrame :
    IsLocalFrame (freeModule Y I) ⊤ (fun i => (freeIncl (Y := Y) i).app ⊤ (1 : Γ(Y, ⊤))) := by
  intro V h
  have hF : ∀ a,
      localFrameMap (freeModule Y I) (fun i => (freeIncl (Y := Y) i).app ⊤ (1 : Γ(Y, ⊤))) h a =
      ∑ i, (freeIncl (Y := Y) i).app V (a i) := by
    intro a
    rw [localFrameMap_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [freeIncl_app_restrict, freeIncl_app_smul_one]
  have hπι : ∀ (i j : I) (r : Γ(Y, V)),
      (freeProjM (Y := Y) j).app V ((freeIncl (Y := Y) i).app V r) = if i = j then r else 0 := by
    intro i j r
    have := congrArg (fun φ => φ.app V r) (freeIncl_freeProjM (Y := Y) i j)
    refine this.trans ?_
    split_ifs <;> rfl
  have hsum : ∀ s : Γ(freeModule Y I, V),
      ∑ i, (freeIncl (Y := Y) i).app V ((freeProjM (Y := Y) i).app V s) = s := by
    intro s
    have := congrArg (homEvalAddHom V s) (sum_freeProjM_freeIncl (Y := Y) (I := I))
    rw [map_sum] at this
    exact this
  have hΨ : ∀ a, (fun j => (freeProjM (Y := Y) j).app V
      (localFrameMap (freeModule Y I) (fun i => (freeIncl (Y := Y) i).app ⊤ (1 : Γ(Y, ⊤))) h
        a)) = a := by
    intro a
    funext j
    rw [hF, map_sum]
    simp_rw [hπι]
    exact (Finset.sum_eq_single j (fun k _ hk => if_neg hk)
      (fun h' => absurd (Finset.mem_univ j) h')).trans (if_pos rfl)
  refine ⟨fun a b hab => ?_, fun s => ⟨fun j => (freeProjM (Y := Y) j).app V s, ?_⟩⟩
  · rw [← hΨ a, ← hΨ b, hab]
  · exact (hF _).trans (hsum s)

end FreeFrame

section LocallyFree

variable {ι : Type*} [Fintype ι]

/-- A frame transported along an isomorphism of modules. -/
lemma IsLocalFrame.of_iso {A B : X.Modules} (α : B ≅ A) {U : X.Opens} {e : ι → Γ(B, U)}
    (hB : IsLocalFrame B U e) : IsLocalFrame A U (fun i => α.hom.app U (e i)) := by
  intro V h
  have key : ⇑(localFrameMap A (fun i => α.hom.app U (e i)) h) =
      α.hom.app V ∘ localFrameMap B e h := by
    funext a
    rw [Function.comp_apply, localFrameMap_apply, localFrameMap_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Scheme.Modules.Hom.app_smul]
    congr 1
    exact (ConcreteCategory.congr_hom (α.hom.mapPresheaf.naturality (homOfLE h).op) (e i)).symm
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso (α.hom.app V)).comp (hB V h)

private lemma restrict_localFrameMap_eq (E : X.Modules) (U : X.Opens) (W : U.toScheme.Opens)
    (e : ι → Γ(E.restrict U.ι, ⊤)) (a : ι → Γ(X, U.ι ''ᵁ W)) :
    (Scheme.Modules.restrictAppIso U.ι E W).hom
        (localFrameMap (E.restrict U.ι) e (le_top : W ≤ ⊤) (fun i => (U.ι.appIso W).hom (a i))) =
      localFrameMap E (fun i => E.presheaf.map (homOfLE U.ι_image_top.ge).op
        ((Scheme.Modules.restrictAppIso U.ι E ⊤).hom (e i))) (U.ι_image_le W) a := by
  rw [localFrameMap_apply, localFrameMap_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Modules.map_restrictAppIso_hom_apply,
    modules_map_map, Iso.hom_inv_id_apply]

/-- A frame of the restriction `E|_U` over all of `U` gives a frame of `E` over `U`. -/
lemma IsLocalFrame.of_restrict {E : X.Modules} {U : X.Opens} {e : ι → Γ(E.restrict U.ι, ⊤)}
    (h : IsLocalFrame (E.restrict U.ι) ⊤ e) :
    IsLocalFrame E U (fun i => E.presheaf.map (homOfLE U.ι_image_top.ge).op
      ((Scheme.Modules.restrictAppIso U.ι E ⊤).hom (e i))) := by
  intro V hV
  obtain ⟨W, rfl⟩ : ∃ W : U.toScheme.Opens, U.ι ''ᵁ W = V :=
    ⟨U.ι ⁻¹ᵁ V, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]⟩
  have key : ⇑(localFrameMap E (fun i => E.presheaf.map (homOfLE U.ι_image_top.ge).op
      ((Scheme.Modules.restrictAppIso U.ι E ⊤).hom (e i))) hV) =
      (Scheme.Modules.restrictAppIso U.ι E W).hom ∘
        (localFrameMap (E.restrict U.ι) e (le_top : W ≤ ⊤)) ∘
        (fun a : ι → Γ(X, U.ι ''ᵁ W) => fun i => (U.ι.appIso W).hom (a i)) :=
    funext fun a => (restrict_localFrameMap_eq E U W e a).symm
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso _).comp ((h W le_top).comp
    (ConcreteCategory.bijective_of_isIso (U.ι.appIso W).hom).comp_left)

/-- A locally free module of finite rank at every point admits frames locally. -/
lemma exists_isLocalFrame_of_isLocallyFree {E : X.Modules} (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) (x : X) :
    ∃ (U : X.Opens) (ι : Type u) (_ : Fintype ι) (e : ι → Γ(E, U)), x ∈ U ∧ IsLocalFrame E U e := by
  classical
  obtain ⟨U, hxU, I, ⟨α⟩⟩ := hE x
  have hI : Finite I := by
    have := hfin x
    rw [Scheme.Modules.rankAt_eq E α hxU] at this
    exact Cardinal.lt_aleph0_iff_finite.mp this
  let _ : Fintype I := Fintype.ofFinite I
  exact ⟨U, I, inferInstance, _, hxU,
    ((free_isLocalFrame (Y := U.toScheme) (I := I)).of_iso α.symm).of_restrict⟩

end LocallyFree

section MainResults

variable (E : X.Modules)

/-- **Hartshorne II, Exercise 5.1(a).** For a finite locally free `𝒪_X`-module `E` (locally free
with finite rank at every point), the canonical map `E ⟶ E^∨∨` is an isomorphism. -/
theorem moduleSheafDoubleDualMap_isIso (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) : IsIso (moduleSheafDoubleDualMap E) :=
  modules_isIso_of_locally_bijective _ fun x => by
    classical
    obtain ⟨U, ι, _, e, hx, hEU⟩ := exists_isLocalFrame_of_isLocallyFree hE hfin x
    exact ⟨U, hx, fun V h => doubleDualMap_bijective_of_isLocalFrame hEU h⟩

/-- The natural isomorphism `E ≅ E^∨∨` for a finite locally free `E`. -/
noncomputable def moduleSheafDoubleDualIso (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) : E ≅ moduleSheafDual (moduleSheafDual E) :=
  haveI := moduleSheafDoubleDualMap_isIso E hE hfin
  asIso (moduleSheafDoubleDualMap E)

/-- **Hartshorne II, Exercise 5.1(b).** For a finite locally free `E` and any `𝒪_X`-module `F`, the
canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)` is an isomorphism. -/
theorem moduleSheafDualTensorMap_isIso (F : X.Modules) (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) : IsIso (moduleSheafDualTensorMap E F) :=
  isIso_moduleSheafDualTensorMap_of_localFrames (exists_isLocalFrame_of_isLocallyFree hE hfin)

/-- The natural isomorphism `E^∨ ⊗ F ≅ ℋom(E, F)` for a finite locally free `E`. -/
noncomputable def moduleSheafDualTensorIso (F : X.Modules) (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) :
    @Iso X.Modules _ (moduleSheafTensor (moduleSheafDual E) F) (moduleSheafHom E F) :=
  haveI := moduleSheafDualTensorMap_isIso E F hE hfin
  asIso (moduleSheafDualTensorMap E F)

end MainResults

section Naturality

variable {E E' F F' G : X.Modules}

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
    @Quiver.Hom X.Modules _ (moduleSheafTensor E F) (moduleSheafTensor E' F') :=
  (moduleSheafTensorHomEquiv _ _ _).symm (modulesTensorMapBilinear φ ψ)

lemma modulesTensorMap_tmul (φ : E ⟶ E') (ψ : F ⟶ F') {U : X.Opens} (e : Γ(E, U))
    (f : Γ(F, U)) :
    (modulesTensorMap φ ψ).app U ((moduleSheafTensorBilinear E F).app (op U) e f) =
      (moduleSheafTensorBilinear E' F').app (op U) (φ.app U e) (ψ.app U f) := by
  have := congrArg (fun β : ModuleSheafBilinear _ _ _ => β.app (op U) e f)
    ((moduleSheafTensorHomEquiv_apply (modulesTensorMap φ ψ)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) (modulesTensorMapBilinear φ ψ)))
  exact this

/-- Two morphisms out of a tensor product agreeing on all elementary tensors are equal. -/
lemma modulesTensor_hom_ext {H : X.Modules}
    {φ ψ : @Quiver.Hom X.Modules _ (moduleSheafTensor E F) H}
    (h : ∀ (U : X.Opens) (e : Γ(E, U)) (f : Γ(F, U)),
      φ.app U ((moduleSheafTensorBilinear E F).app (op U) e f) =
        ψ.app U ((moduleSheafTensorBilinear E F).app (op U) e f)) : φ = ψ := by
  apply (moduleSheafTensorHomEquiv E F H).injective
  exact (moduleSheafTensorHomEquiv_apply φ).trans ((ModuleSheafBilinear.ext
    fun U e f => h U.unop e f).trans (moduleSheafTensorHomEquiv_apply ψ).symm)

/-- The canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)` is natural in `F`. -/
lemma moduleSheafDualTensorMap_naturality_right (g : F ⟶ F') :
    modulesTensorMap (𝟙 (moduleSheafDual E)) g ≫ moduleSheafDualTensorMap E F' =
      moduleSheafDualTensorMap E F ≫ moduleSheafHomMap (𝟙 E) g := by
  refine modulesTensor_hom_ext fun U ψ f => ?_
  have h1 := modulesTensorMap_tmul (𝟙 (moduleSheafDual E)) g ψ f
  have h2 := moduleSheafDualTensorMap_tmul (E := E) (F := F') ψ (g.app U f)
  have h3 := moduleSheafDualTensorMap_tmul (E := E) (F := F) ψ f
  change (moduleSheafDualTensorMap E F').app U
      ((modulesTensorMap (𝟙 (moduleSheafDual E)) g).app U
      ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ f)) =
    (moduleSheafHomMap (𝟙 E) g).app U ((moduleSheafDualTensorMap E F).app U
      ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ f))
  rw [h1]
  erw [h2, h3]
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => ?_
  rw [moduleSheafHomEval_map, dualTensorSection_eval, dualTensorSection_eval,
    Scheme.Modules.Hom.app_smul]
  congr 1
  exact (ConcreteCategory.congr_hom (g.mapPresheaf.naturality (homOfLE h).op) f).symm

/-- The canonical map `E^∨ ⊗ F ⟶ ℋom(E, F)` is natural in `E`. -/
lemma moduleSheafDualTensorMap_naturality_left (f : E' ⟶ E) :
    modulesTensorMap (moduleSheafHomMap f (𝟙 (structureModule X))) (𝟙 F) ≫
        moduleSheafDualTensorMap E' F =
      moduleSheafDualTensorMap E F ≫ moduleSheafHomMap f (𝟙 F) := by
  refine modulesTensor_hom_ext fun U ψ y => ?_
  have h1 := modulesTensorMap_tmul (moduleSheafHomMap f (𝟙 (structureModule X))) (𝟙 F) ψ y
  have h2 := moduleSheafDualTensorMap_tmul (E := E') (F := F)
    ((moduleSheafHomMap f (𝟙 (structureModule X))).app U ψ) y
  have h3 := moduleSheafDualTensorMap_tmul (E := E) (F := F) ψ y
  change (moduleSheafDualTensorMap E' F).app U
      ((modulesTensorMap (moduleSheafHomMap f (𝟙 (structureModule X))) (𝟙 F)).app U
      ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ y)) =
    (moduleSheafHomMap f (𝟙 F)).app U ((moduleSheafDualTensorMap E F).app U
      ((moduleSheafTensorBilinear (moduleSheafDual E) F).app (op U) ψ y))
  rw [h1]
  erw [h2, h3]
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => ?_
  rw [moduleSheafHomEval_map, dualTensorSection_eval, dualTensorSection_eval]
  rfl

/-- The tensor–Hom adjunction is natural in `F`. -/
lemma moduleSheafTensorHomAdjunction_naturality_right
    (g : F' ⟶ F) (φ : @Quiver.Hom X.Modules _ (moduleSheafTensor E F) G) :
    moduleSheafTensorHomAdjunction E F' G (modulesTensorMap (𝟙 E) g ≫ φ) =
      g ≫ moduleSheafTensorHomAdjunction E F G φ := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext f
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun e => ?_
  change φ.app V ((modulesTensorMap (𝟙 E) g).app V
      ((moduleSheafTensorBilinear E F').app (op V) e (F'.presheaf.map (homOfLE h).op f))) =
    φ.app V ((moduleSheafTensorBilinear E F).app (op V) e
      (F.presheaf.map (homOfLE h).op (g.app U f)))
  refine congrArg (φ.app V) ((modulesTensorMap_tmul _ _ e _).trans ?_)
  exact congrArg ((moduleSheafTensorBilinear E F).app (op V) e)
    (ConcreteCategory.congr_hom (g.mapPresheaf.naturality (homOfLE h).op) f)

/-- The tensor–Hom adjunction is natural in `E`. -/
lemma moduleSheafTensorHomAdjunction_naturality_left
    (f : E' ⟶ E) (φ : @Quiver.Hom X.Modules _ (moduleSheafTensor E F) G) :
    moduleSheafTensorHomAdjunction E' F G (modulesTensorMap f (𝟙 F) ≫ φ) =
      moduleSheafTensorHomAdjunction E F G φ ≫ moduleSheafHomMap f (𝟙 G) := by
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext y
  refine moduleSheafHomEval_ext fun V h => LinearMap.ext fun e => ?_
  change φ.app V ((modulesTensorMap f (𝟙 F)).app V
      ((moduleSheafTensorBilinear E' F).app (op V) e (F.presheaf.map (homOfLE h).op y))) =
    φ.app V ((moduleSheafTensorBilinear E F).app (op V) (f.app V e)
      (F.presheaf.map (homOfLE h).op y))
  exact congrArg (φ.app V) (modulesTensorMap_tmul _ _ e _)

end Naturality

end Hartshorne
