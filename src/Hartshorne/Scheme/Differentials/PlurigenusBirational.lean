/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.CanonicalPullback
import Hartshorne.Scheme.Differentials.GeometricGenus
import Hartshorne.Scheme.Differentials.LocallyFreeSectionsExtend
import Hartshorne.Scheme.Differentials.BirationalMapDomain
import Hartshorne.Scheme.AmpleSectionsAffineBasis
import Hartshorne.Rational.ContractedCurves

/-!
# Birational invariance of plurigenera

Hartshorne, *Algebraic Geometry*, Exercise II.8.8 (p. 190).

For a scheme `X` over `k`, the `m`-th plurigenus is `P_m(X) = dim_k Γ(X, ω_X^{⊗m})`
(`Hartshorne.plurigenus`). If `X` and `X'` are nonsingular varieties, proper over an algebraically
closed field and birationally equivalent, then `P_m(X) = P_m(X')`
(`Hartshorne.plurigenus_eq_of_birational`). For `m = 1` this is Theorem II.8.19, the birational
invariance of the geometric genus (`Hartshorne.geometricGenus_eq_of_birational`), proved by the
same argument with `ω` in place of `ω^{⊗m}`.

The same argument with `⋀^q Ω_{X/k}`, which on a nonsingular variety of dimension `n` is locally
free of rank `n choose q`, shows that the dimension `h^{q,0}(X) = dim_k Γ(X, ⋀^q Ω_{X/k})` of the
space of regular `q`-forms (`Hartshorne.regularFormDimension`) is a birational invariant
(`Hartshorne.regularFormDimension_eq_of_birational`).

## Proof

As in the proof of Theorem II.8.19, run the pullback injection for `ω^{⊗m}` in both directions.
Let `V ⊆ X` be the domain of the birational map `X ⤏ X'` and `φ : V ⟶ X'` its representative;
`X \ V` has codimension at least two. Pullback of differentials along `φ` gives
`Γ(X', ω_{X'}^{⊗m}) → Γ(V, ⋀^n Ω_V^{⊗m})`. It is injective: on a nonempty open `W ⊆ V` where `φ` is
an open immersion it is followed by a map back to `ω_{X'}^{⊗m}|_W` and the composite is the
restriction, which is injective for a locally free sheaf of finite rank on an integral scheme
(`Hartshorne.injective_app_top_of_comp_eq_unit`). Pullback along the inclusion `V ⟶ X` gives
`Γ(X, ω_X^{⊗m}) → Γ(V, ⋀^n Ω_V^{⊗m})`, which is bijective: for an open immersion `g`, pullback
followed by the map `Ω_{V/k} ⟶ Ω_{X/k}|_V` is the restriction, and in the other order it is the
identity (`Hartshorne.bijective_app_top_of_restrict`); restriction of sections of the invertible
sheaf `ω_X^{⊗m}` to `V` is bijective by the codimension-two extension. The maps are `k`-linear,
so `dim_k Γ(X', ω_{X'}^{⊗m}) ≤ dim_k Γ(X, ω_X^{⊗m})`, and symmetrically.

Both compatibilities are proved for `Ω`, then carried to `⋀^n` and `⊗^m` through their universal
properties (`Hartshorne.exteriorPowerPushforwardMap`, `Hartshorne.exteriorPowerRestrictMap`,
`Hartshorne.tensorPowerPushforwardMap`, `Hartshorne.tensorPowerRestrictMap`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

namespace Hartshorne

open Scheme

section HomExt

variable {X : Scheme.{u}} {r : ℕ} {F H : X.Modules}

/-- The morphism `T^r F ⟶ H` attached to a multilinear morphism `β` sends `f₁ ⊗ ⋯ ⊗ fᵣ` to
`β(f₁, …, fᵣ)`. -/
theorem moduleSheafTensorPowerHomEquiv_symm_app
    (β : ModuleSheafMultilinear (R := X.sheaf) r F H) (U : X.Opensᵒᵖ)
    (m : Fin r → F.val.obj U) :
    ((moduleSheafTensorPowerHomEquiv r F H).symm β).val.app U
      ((moduleSheafTensorPowerMultilinear r F).app U m) = β.app U m :=
  congrArg (fun γ : ModuleSheafMultilinear r F H => γ.app U m)
    ((moduleSheafTensorPowerHomEquiv_apply _).symm.trans (Equiv.apply_symm_apply _ β))

/-- Morphisms out of `T^r F` agreeing on all local tensors `f₁ ⊗ ⋯ ⊗ fᵣ` are equal. -/
theorem moduleSheafTensorPower_hom_ext
    {φ ψ : moduleSheafTensorPower (R := X.sheaf) r F ⟶ H}
    (h : ∀ (U : X.Opensᵒᵖ) (m : Fin r → F.val.obj U),
      φ.val.app U ((moduleSheafTensorPowerMultilinear r F).app U m) =
        ψ.val.app U ((moduleSheafTensorPowerMultilinear r F).app U m)) : φ = ψ := by
  apply (moduleSheafTensorPowerHomEquiv r F H).injective
  refine (moduleSheafTensorPowerHomEquiv_apply φ).trans
    (Eq.trans ?_ (moduleSheafTensorPowerHomEquiv_apply ψ).symm)
  ext U m
  exact h U m

end HomExt

section Lifts

variable {Y V W : Scheme.{u}} {F : Y.Modules} {G : V.Modules}

/-- The morphism `⋀^n G ⟶ (⋀^n F)|_V`, `y₁ ∧ ⋯ ∧ yₙ ↦ β y₁ ∧ ⋯ ∧ β yₙ`, induced by
`β : G ⟶ F|_V` for an open immersion `g : V ⟶ Y`. -/
def exteriorPowerRestrictMap (g : V ⟶ Y) [IsOpenImmersion g] (β : G ⟶ F.restrict g) (n : ℕ) :
    moduleSheafExteriorPower (R := V.sheaf) n G ⟶
      Modules.restrict (moduleSheafExteriorPower (R := Y.sheaf) n F) g :=
  (moduleSheafExteriorPowerHomEquiv n _ _).symm
    ⟨((moduleSheafExteriorPowerMultilinear n F).restrict g).precompHom β,
      ((moduleSheafExteriorPowerMultilinear_isAlternating).restrict g).precompHom β⟩

theorem exteriorPowerRestrictMap_wedge (g : V ⟶ Y) [IsOpenImmersion g] (β : G ⟶ F.restrict g)
    (n : ℕ) (U : V.Opensᵒᵖ) (m : Fin n → G.val.obj U) :
    (exteriorPowerRestrictMap g β n).val.app U
        ((moduleSheafExteriorPowerMultilinear n G).app U m) =
      (moduleSheafExteriorPowerMultilinear n F).app (op (g ''ᵁ U.unop))
        (fun i => β.val.app U (m i)) :=
  moduleSheafExteriorPowerHomEquiv_symm_app _ _ U m

/-- The morphism `T^m F ⟶ f_*(T^m G)`, `x₁ ⊗ ⋯ ⊗ xₘ ↦ α x₁ ⊗ ⋯ ⊗ α xₘ`, induced by
`α : F ⟶ f_* G`. -/
def tensorPowerPushforwardMap (f : V ⟶ Y) (α : F ⟶ (Modules.pushforward f).obj G) (m : ℕ) :
    moduleSheafTensorPower (R := Y.sheaf) m F ⟶
      (Modules.pushforward f).obj (moduleSheafTensorPower (R := V.sheaf) m G) :=
  (moduleSheafTensorPowerHomEquiv m _ _).symm
    (((moduleSheafTensorPowerMultilinear m G).pushforward f).precompHom α)

theorem tensorPowerPushforwardMap_tprod (f : V ⟶ Y) (α : F ⟶ (Modules.pushforward f).obj G)
    (m : ℕ) (U : Y.Opensᵒᵖ) (x : Fin m → F.val.obj U) :
    (tensorPowerPushforwardMap f α m).val.app U
        ((moduleSheafTensorPowerMultilinear m F).app U x) =
      (moduleSheafTensorPowerMultilinear m G).app (op (f ⁻¹ᵁ U.unop))
        (fun i => α.val.app U (x i)) :=
  moduleSheafTensorPowerHomEquiv_symm_app _ U x

/-- The morphism `T^m G ⟶ (T^m F)|_V`, `y₁ ⊗ ⋯ ⊗ yₘ ↦ β y₁ ⊗ ⋯ ⊗ β yₘ`, induced by
`β : G ⟶ F|_V` for an open immersion `g : V ⟶ Y`. -/
def tensorPowerRestrictMap (g : V ⟶ Y) [IsOpenImmersion g] (β : G ⟶ F.restrict g) (m : ℕ) :
    moduleSheafTensorPower (R := V.sheaf) m G ⟶
      Modules.restrict (moduleSheafTensorPower (R := Y.sheaf) m F) g :=
  (moduleSheafTensorPowerHomEquiv m _ _).symm
    (((moduleSheafTensorPowerMultilinear m F).restrict g).precompHom β)

theorem tensorPowerRestrictMap_tprod (g : V ⟶ Y) [IsOpenImmersion g] (β : G ⟶ F.restrict g)
    (m : ℕ) (U : V.Opensᵒᵖ) (y : Fin m → G.val.obj U) :
    (tensorPowerRestrictMap g β m).val.app U
        ((moduleSheafTensorPowerMultilinear m G).app U y) =
      (moduleSheafTensorPowerMultilinear m F).app (op (g ''ᵁ U.unop))
        (fun i => β.val.app U (y i)) :=
  moduleSheafTensorPowerHomEquiv_symm_app _ U y

/-- The morphism `T^m G ⟶ j_*((T^m F)|_W)` induced by `β : G ⟶ j_*(F|_W)`, where `j : W ⟶ V`
and `j ≫ f : W ⟶ Y` is an open immersion. -/
def tensorPowerRestrictPushforwardMap (f : V ⟶ Y) (j : W ⟶ V) [IsOpenImmersion (j ≫ f)]
    (β : G ⟶ (Modules.pushforward j).obj (F.restrict (j ≫ f))) (m : ℕ) :
    moduleSheafTensorPower (R := V.sheaf) m G ⟶
      (Modules.pushforward j).obj
        (Modules.restrict (moduleSheafTensorPower (R := Y.sheaf) m F) (j ≫ f)) :=
  (moduleSheafTensorPowerHomEquiv m _ _).symm
    ((((moduleSheafTensorPowerMultilinear m F).restrict (j ≫ f)).pushforward j).precompHom β)

theorem tensorPowerRestrictPushforwardMap_tprod (f : V ⟶ Y) (j : W ⟶ V)
    [IsOpenImmersion (j ≫ f)] (β : G ⟶ (Modules.pushforward j).obj (F.restrict (j ≫ f)))
    (m : ℕ) (U : V.Opensᵒᵖ) (y : Fin m → G.val.obj U) :
    (tensorPowerRestrictPushforwardMap f j β m).val.app U
        ((moduleSheafTensorPowerMultilinear m G).app U y) =
      (moduleSheafTensorPowerMultilinear m F).app (op ((j ≫ f) ''ᵁ (j ⁻¹ᵁ U.unop)))
        (fun i => β.val.app U (y i)) :=
  moduleSheafTensorPowerHomEquiv_symm_app _ U y

end Lifts

section Compatible

variable {Y V W : Scheme.{u}} {F : Y.Modules} {G : V.Modules}

/-- If `β ∘ α` is the restriction of `F` to the open subscheme `V`, the same holds for the induced
maps on exterior powers. -/
theorem exteriorPowerPushforwardMap_comp_restrictMap (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g)
    (h : α ≫ (Modules.pushforward g).map β = (Modules.restrictAdjunction g).unit.app F)
    (n : ℕ) :
    exteriorPowerPushforwardMap g α n ≫
        (Modules.pushforward g).map (exteriorPowerRestrictMap g β n) =
      (Modules.restrictAdjunction g).unit.app (moduleSheafExteriorPower (R := Y.sheaf) n F) := by
  apply moduleSheafExteriorPower_hom_ext
  intro U m
  have hαβ : ∀ x : F.val.obj U, β.val.app (op (g ⁻¹ᵁ U.unop)) (α.val.app U x) =
      F.val.map (homOfLE (g.image_preimage_le U.unop)).op x :=
    fun x => congrArg (fun φ => φ.val.app U x) h
  change (exteriorPowerRestrictMap g β n).val.app (op (g ⁻¹ᵁ U.unop))
      ((exteriorPowerPushforwardMap g α n).val.app U
        ((moduleSheafExteriorPowerMultilinear n F).app U m)) =
    (moduleSheafExteriorPower (R := Y.sheaf) n F).val.map
      (homOfLE (g.image_preimage_le U.unop)).op
      ((moduleSheafExteriorPowerMultilinear n F).app U m)
  rw [exteriorPowerPushforwardMap_wedge]
  refine (exteriorPowerRestrictMap_wedge g β n _ _).trans ?_
  refine Eq.trans ?_ ((moduleSheafExteriorPowerMultilinear n F).naturality _ m).symm
  exact congrArg _ (funext fun i => hαβ (m i))

/-- If `β ∘ α` is the restriction of `F` to the open subscheme `V`, the same holds for the induced
maps on tensor powers. -/
theorem tensorPowerPushforwardMap_comp_restrictMap (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g)
    (h : α ≫ (Modules.pushforward g).map β = (Modules.restrictAdjunction g).unit.app F)
    (m : ℕ) :
    tensorPowerPushforwardMap g α m ≫
        (Modules.pushforward g).map (tensorPowerRestrictMap g β m) =
      (Modules.restrictAdjunction g).unit.app (moduleSheafTensorPower (R := Y.sheaf) m F) := by
  apply moduleSheafTensorPower_hom_ext
  intro U x
  have hαβ : ∀ y : F.val.obj U, β.val.app (op (g ⁻¹ᵁ U.unop)) (α.val.app U y) =
      F.val.map (homOfLE (g.image_preimage_le U.unop)).op y :=
    fun y => congrArg (fun φ => φ.val.app U y) h
  change (tensorPowerRestrictMap g β m).val.app (op (g ⁻¹ᵁ U.unop))
      ((tensorPowerPushforwardMap g α m).val.app U
        ((moduleSheafTensorPowerMultilinear m F).app U x)) =
    (moduleSheafTensorPower (R := Y.sheaf) m F).val.map
      (homOfLE (g.image_preimage_le U.unop)).op
      ((moduleSheafTensorPowerMultilinear m F).app U x)
  rw [tensorPowerPushforwardMap_tprod]
  refine (tensorPowerRestrictMap_tprod g β m _ _).trans ?_
  refine Eq.trans ?_ ((moduleSheafTensorPowerMultilinear m F).naturality _ x).symm
  exact congrArg _ (funext fun i => hαβ (x i))

/-- If `f_*β ∘ α` is the restriction of `F` to `W` (along the open immersion `j ≫ f`), the same
holds for the induced maps on tensor powers. -/
theorem tensorPowerPushforwardMap_comp_restrictPushforwardMap (f : V ⟶ Y) (j : W ⟶ V)
    [IsOpenImmersion (j ≫ f)] (α : F ⟶ (Modules.pushforward f).obj G)
    (β : G ⟶ (Modules.pushforward j).obj (F.restrict (j ≫ f)))
    (h : α ≫ (Modules.pushforward f).map β =
      (Modules.restrictAdjunction (j ≫ f)).unit.app F ≫ (Modules.pushforwardComp j f).inv.app _)
    (m : ℕ) :
    tensorPowerPushforwardMap f α m ≫
        (Modules.pushforward f).map (tensorPowerRestrictPushforwardMap f j β m) =
      (Modules.restrictAdjunction (j ≫ f)).unit.app
          (moduleSheafTensorPower (R := Y.sheaf) m F) ≫
        (Modules.pushforwardComp j f).inv.app _ := by
  apply moduleSheafTensorPower_hom_ext
  intro U x
  have hαβ : ∀ y : F.val.obj U, β.val.app (op (f ⁻¹ᵁ U.unop)) (α.val.app U y) =
      F.val.map (homOfLE ((j ≫ f).image_preimage_le U.unop)).op y :=
    fun y => congrArg (fun φ => φ.val.app U y) h
  change (tensorPowerRestrictPushforwardMap f j β m).val.app (op (f ⁻¹ᵁ U.unop))
      ((tensorPowerPushforwardMap f α m).val.app U
        ((moduleSheafTensorPowerMultilinear m F).app U x)) =
    (moduleSheafTensorPower (R := Y.sheaf) m F).val.map
      (homOfLE ((j ≫ f).image_preimage_le U.unop)).op
      ((moduleSheafTensorPowerMultilinear m F).app U x)
  rw [tensorPowerPushforwardMap_tprod]
  refine (tensorPowerRestrictPushforwardMap_tprod f j β m _ _).trans ?_
  refine Eq.trans ?_ ((moduleSheafTensorPowerMultilinear m F).naturality _ x).symm
  exact congrArg _ (funext fun i => hαβ (x i))

end Compatible

section LeftInverse

variable {Y V : Scheme.{u}} {F : Y.Modules} {G : V.Modules}

/-- Restriction along an open immersion `g : V ⟶ Y` undoes `(g^♯)⁻¹`. -/
theorem presheaf_map_app_appIso_inv (g : V ⟶ Y) [IsOpenImmersion g] (U : V.Opens)
    (a : Γ(V, U)) :
    V.presheaf.map (homOfLE (g.preimage_image_eq U).ge).op
      (g.app (g ''ᵁ U) ((g.appIso U).inv a)) = a := by
  have h := ConcreteCategory.congr_hom (Scheme.Hom.appIso_inv_app g U) a
  refine (congrArg (V.presheaf.map (homOfLE (g.preimage_image_eq U).ge).op) h).trans ?_
  have hc : (eqToHom (g.preimage_image_eq U)).op ≫ (homOfLE (g.preimage_image_eq U).ge).op =
      𝟙 (op U) := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have := ConcreteCategory.congr_hom
    ((V.presheaf.map_comp (eqToHom (g.preimage_image_eq U)).op
      (homOfLE (g.preimage_image_eq U).ge).op).symm.trans
        ((congrArg V.presheaf.map hc).trans (V.presheaf.map_id _))) a
  exact this

/-- The component over `U ⊆ V` of `restrictLeftComposite`: `z ↦ α(β z)|_U`, where `α(β z)` lives
over `g⁻¹(g(U)) = U`. -/
def restrictLeftCompositeApp (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g) (U : V.Opensᵒᵖ) :
    G.val.obj U ⟶ G.val.obj U :=
  ModuleCat.ofHom
    { toFun z := G.val.map (homOfLE (g.preimage_image_eq U.unop).ge).op
        (α.val.app (op (g ''ᵁ U.unop)) (β.val.app U z))
      map_add' x y := by
        refine (congrArg _ ((congrArg _ (map_add (β.val.app U).hom x y)).trans
          (map_add _ _ _))).trans (map_add _ _ _)
      map_smul' c z := by
        change G.val.map _ (α.val.app _ (β.val.app U (c • z))) = c • _
        refine (congrArg _ ((congrArg _ ((β.val.app U).hom.map_smul c z)).trans
          ((α.val.app (op (g ''ᵁ U.unop))).hom.map_smul ((g.appIso U.unop).inv c) _))).trans ?_
        refine (PresheafOfModules.map_smul G.val _ _ _).trans ?_
        exact congrArg (· • _) (presheaf_map_app_appIso_inv g U.unop c) }

theorem restrictLeftCompositeApp_apply (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g) (U : V.Opensᵒᵖ)
    (z : G.val.obj U) :
    restrictLeftCompositeApp g α β U z = G.val.map (homOfLE (g.preimage_image_eq U.unop).ge).op
      (α.val.app (op (g ''ᵁ U.unop)) (β.val.app U z)) :=
  rfl

theorem restrictLeftCompositeApp_naturality (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g) {U U' : V.Opensᵒᵖ}
    (i : U ⟶ U') (z : G.val.obj U) :
    restrictLeftCompositeApp g α β U' (G.val.map i z) =
      G.val.map i (restrictLeftCompositeApp g α β U z) := by
  refine (restrictLeftCompositeApp_apply g α β U' _).trans (Eq.trans ?_
    (congrArg (G.val.map i) (restrictLeftCompositeApp_apply g α β U z)).symm)
  have h1 : β.val.app U' (G.val.map i z) =
      F.val.map (g.opensFunctor.op.map i) (β.val.app U z) :=
    PresheafOfModules.naturality_apply β.val i z
  have h2 : α.val.app (op (g ''ᵁ U'.unop)) (F.val.map (g.opensFunctor.op.map i) (β.val.app U z)) =
      G.val.map ((TopologicalSpace.Opens.map g.base).op.map (g.opensFunctor.op.map i))
        (α.val.app (op (g ''ᵁ U.unop)) (β.val.app U z)) :=
    PresheafOfModules.naturality_apply α.val (g.opensFunctor.op.map i) (β.val.app U z)
  have h3 : ∀ y : G.val.obj (op (g ⁻¹ᵁ g ''ᵁ U.unop)),
      G.val.map (homOfLE (g.preimage_image_eq U'.unop).ge).op
        (G.val.map ((TopologicalSpace.Opens.map g.base).op.map (g.opensFunctor.op.map i)) y) =
      G.val.map i (G.val.map (homOfLE (g.preimage_image_eq U.unop).ge).op y) := fun y => by
    let a : op (g ⁻¹ᵁ g ''ᵁ U.unop) ⟶ op (g ⁻¹ᵁ g ''ᵁ U'.unop) :=
      (TopologicalSpace.Opens.map g.base).op.map (g.opensFunctor.op.map i)
    let b' : op (g ⁻¹ᵁ g ''ᵁ U'.unop) ⟶ U' := (homOfLE (g.preimage_image_eq U'.unop).ge).op
    let b : op (g ⁻¹ᵁ g ''ᵁ U.unop) ⟶ U := (homOfLE (g.preimage_image_eq U.unop).ge).op
    have hc : a ≫ b' = b ≫ i := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    refine (PresheafOfModules.map_comp_apply G.val a b' y).symm.trans ?_
    refine Eq.trans ?_ (PresheafOfModules.map_comp_apply G.val b i y)
    exact congrArg (fun c : op (g ⁻¹ᵁ g ''ᵁ U.unop) ⟶ U' => G.val.map c y) hc
  refine (congrArg (fun y => G.val.map (homOfLE (g.preimage_image_eq U'.unop).ge).op
    (α.val.app (op (g ''ᵁ U'.unop)) y)) h1).trans ?_
  refine (congrArg (G.val.map (homOfLE (g.preimage_image_eq U'.unop).ge).op) h2).trans ?_
  exact h3 _

/-- For an open immersion `g : V ⟶ Y`, `α : F ⟶ g_*G` and `β : G ⟶ F|_V`, the endomorphism
`z ↦ α(β z)|_U` of `G`. -/
def restrictLeftComposite (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g) : G ⟶ G :=
  ⟨{ app U := restrictLeftCompositeApp g α β U
     naturality {_ _} i := by
      ext z
      exact restrictLeftCompositeApp_naturality g α β i z }⟩

theorem restrictLeftComposite_app (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g) (U : V.Opensᵒᵖ)
    (z : G.val.obj U) :
    (restrictLeftComposite g α β).val.app U z =
      G.val.map (homOfLE (g.preimage_image_eq U.unop).ge).op
        (α.val.app (op (g ''ᵁ U.unop)) (β.val.app U z)) :=
  rfl

/-- If `z ↦ α(β z)|_U` is the identity of `G`, the same holds for the induced maps on exterior
powers. -/
theorem restrictLeftComposite_exteriorPower (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g)
    (h : restrictLeftComposite g α β = 𝟙 G) (n : ℕ) :
    restrictLeftComposite g (exteriorPowerPushforwardMap g α n)
      (exteriorPowerRestrictMap g β n) = 𝟙 _ := by
  apply moduleSheafExteriorPower_hom_ext
  intro U m
  have hp : ∀ z : G.val.obj U, G.val.map (homOfLE (g.preimage_image_eq U.unop).ge).op
      (α.val.app (op (g ''ᵁ U.unop)) (β.val.app U z)) = z :=
    fun z => congrArg (fun φ => φ.val.app U z) h
  change (moduleSheafExteriorPower (R := V.sheaf) n G).val.map
      (homOfLE (g.preimage_image_eq U.unop).ge).op
      ((exteriorPowerPushforwardMap g α n).val.app (op (g ''ᵁ U.unop))
        ((exteriorPowerRestrictMap g β n).val.app U
          ((moduleSheafExteriorPowerMultilinear n G).app U m))) =
    (moduleSheafExteriorPowerMultilinear n G).app U m
  rw [exteriorPowerRestrictMap_wedge]
  refine (congrArg _ (exteriorPowerPushforwardMap_wedge g α _ _ _)).trans ?_
  refine ((moduleSheafExteriorPowerMultilinear n G).naturality _ _).trans ?_
  exact congrArg _ (funext fun i => hp (m i))

/-- If `z ↦ α(β z)|_U` is the identity of `G`, the same holds for the induced maps on tensor
powers. -/
theorem restrictLeftComposite_tensorPower (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g)
    (h : restrictLeftComposite g α β = 𝟙 G) (m : ℕ) :
    restrictLeftComposite g (tensorPowerPushforwardMap g α m)
      (tensorPowerRestrictMap g β m) = 𝟙 _ := by
  apply moduleSheafTensorPower_hom_ext
  intro U x
  have hp : ∀ z : G.val.obj U, G.val.map (homOfLE (g.preimage_image_eq U.unop).ge).op
      (α.val.app (op (g ''ᵁ U.unop)) (β.val.app U z)) = z :=
    fun z => congrArg (fun φ => φ.val.app U z) h
  change (moduleSheafTensorPower (R := V.sheaf) m G).val.map
      (homOfLE (g.preimage_image_eq U.unop).ge).op
      ((tensorPowerPushforwardMap g α m).val.app (op (g ''ᵁ U.unop))
        ((tensorPowerRestrictMap g β m).val.app U
          ((moduleSheafTensorPowerMultilinear m G).app U x))) =
    (moduleSheafTensorPowerMultilinear m G).app U x
  rw [tensorPowerRestrictMap_tprod]
  refine (congrArg _ (tensorPowerPushforwardMap_tprod g α _ _ _)).trans ?_
  refine ((moduleSheafTensorPowerMultilinear m G).naturality _ _).trans ?_
  exact congrArg _ (funext fun i => hp (x i))

/-- If `β ∘ α` is the restriction of `F` to `V` and `z ↦ α(β z)|_U` is the identity, then `α` is
bijective on global sections as soon as restriction `Γ(Y, F) → Γ(g(V), F)` is. -/
theorem bijective_app_top_of_restrict (g : V ⟶ Y) [IsOpenImmersion g]
    (α : F ⟶ (Modules.pushforward g).obj G) (β : G ⟶ F.restrict g)
    (h₁ : α ≫ (Modules.pushforward g).map β = (Modules.restrictAdjunction g).unit.app F)
    (h₂ : restrictLeftComposite g α β = 𝟙 G)
    (hρ : Function.Bijective
      (F.val.map (homOfLE (g.image_preimage_le (⊤ : Y.Opens))).op)) :
    Function.Bijective (α.val.app (op ⊤)) := by
  have e₁ : ∀ x, β.val.app (op (g ⁻¹ᵁ ⊤)) (α.val.app (op ⊤) x) =
      F.val.map (homOfLE (g.image_preimage_le (⊤ : Y.Opens))).op x :=
    fun x => congrArg (fun φ => φ.val.app (op ⊤) x) h₁
  have e₂ : ∀ z, (restrictLeftComposite g α β).val.app (op (g ⁻¹ᵁ ⊤)) z = z :=
    fun z => congrArg (fun φ => φ.val.app (op (g ⁻¹ᵁ ⊤)) z) h₂
  have hβ : Function.Injective (β.val.app (op (g ⁻¹ᵁ ⊤))) := fun z z' hzz' =>
    (e₂ z).symm.trans ((congrArg (fun w => G.val.map
      (homOfLE (g.preimage_image_eq (g ⁻¹ᵁ ⊤)).ge).op
        (α.val.app (op (g ''ᵁ (g ⁻¹ᵁ ⊤))) w)) hzz').trans (e₂ z'))
  refine ⟨fun x y hxy => hρ.1 ((e₁ x).symm.trans ((congrArg _ hxy).trans (e₁ y))),
    fun z => ?_⟩
  obtain ⟨x, hx⟩ := hρ.2 (β.val.app (op (g ⁻¹ᵁ ⊤)) z)
  exact ⟨x, hβ ((e₁ x).trans hx)⟩

end LeftInverse

section OpenImmersionDifferentials

variable {V Y S : Scheme.{u}} (g : V ⟶ Y) [IsOpenImmersion g] (p : Y ⟶ S)

/-- For an open immersion `g : V ⟶ Y` over `S`, the morphism `Ω_{V/S} ⟶ Ω_{Y/S}|_V`,
`d a ↦ d((g^♯)⁻¹ a)`. -/
def openImmersionDifferentialsRestrictMap :
    relativeDifferentials (g ≫ p) ⟶ (relativeDifferentials p).restrict g :=
  (relativeDifferentialsHomEquiv (g ≫ p) _).symm
    (derivationToInverseImage (g ≫ p) (openImmersionDerivation g p))

theorem openImmersionDifferentialsRestrictMap_d (U : V.Opensᵒᵖ) (a : V.presheaf.obj U) :
    (openImmersionDifferentialsRestrictMap g p).val.app U
      ((relativeDifferentialsDerivation (g ≫ p)).d a) =
        (openImmersionDerivation g p).d a := by
  have h : (relativeDifferentialsDerivation (g ≫ p)).postcomp
      (openImmersionDifferentialsRestrictMap g p).val =
        derivationToInverseImage (g ≫ p) (openImmersionDerivation g p) := by
    rw [← relativeDifferentialsHomEquiv_apply]
    exact Equiv.apply_symm_apply _ _
  exact PresheafOfModules.Derivation.congr_d h a

/-- Pulling back `Ω_{Y/S}` to the open subscheme `V` and mapping back to `Ω_{Y/S}|_V` is the
restriction. -/
theorem relativeDifferentialsToPushforwardComp_comp_restrictMap :
    relativeDifferentialsToPushforwardComp g p ≫
        (Modules.pushforward g).map (openImmersionDifferentialsRestrictMap g p) =
      (Modules.restrictAdjunction g).unit.app (relativeDifferentials p) := by
  apply (relativeDifferentialsHomEquiv p _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext U b
  change (openImmersionDifferentialsRestrictMap g p).val.app (op (g ⁻¹ᵁ U.unop))
      ((relativeDifferentialsToPushforwardComp g p).val.app U
        ((relativeDifferentialsDerivation p).d b)) =
    (relativeDifferentials p).val.map (homOfLE (g.image_preimage_le U.unop)).op
      ((relativeDifferentialsDerivation p).d b)
  refine (congrArg ((openImmersionDifferentialsRestrictMap g p).val.app (op (g ⁻¹ᵁ U.unop)))
    (relativeDifferentialsToPushforwardComp_d g p U b)).trans ?_
  refine (openImmersionDifferentialsRestrictMap_d g p _ _).trans ?_
  refine (congrArg (relativeDifferentialsDerivation p).d
    (ConcreteCategory.congr_hom (Scheme.Hom.app_appIso_inv g U.unop) b)).trans ?_
  exact (relativeDifferentialsDerivation p).d_map _ _

/-- Mapping `Ω_{V/S}` to `Ω_{Y/S}|_V` and pulling back to `V` is the identity. -/
theorem restrictLeftComposite_differentials :
    restrictLeftComposite g (relativeDifferentialsToPushforwardComp g p)
      (openImmersionDifferentialsRestrictMap g p) = 𝟙 _ := by
  apply (relativeDifferentialsHomEquiv (g ≫ p) _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext U a
  change (relativeDifferentials (g ≫ p)).val.map (homOfLE (g.preimage_image_eq U.unop).ge).op
      ((relativeDifferentialsToPushforwardComp g p).val.app (op (g ''ᵁ U.unop))
        ((openImmersionDifferentialsRestrictMap g p).val.app U
          ((relativeDifferentialsDerivation (g ≫ p)).d a))) =
    (relativeDifferentialsDerivation (g ≫ p)).d a
  refine (congrArg _ ((congrArg _ (openImmersionDifferentialsRestrictMap_d g p U a)).trans
    (relativeDifferentialsToPushforwardComp_d g p _ _))).trans ?_
  refine ((relativeDifferentialsDerivation (g ≫ p)).d_map _ _).symm.trans ?_
  exact congrArg _ (presheaf_map_app_appIso_inv g U.unop a)

end OpenImmersionDifferentials

section Plurigenus

variable {k : Type u} [Field k]

/-- **Plurigenera (Hartshorne, Exercise II.8.8).** The `m`-th plurigenus
`P_m(X) = dim_k Γ(X, ω_X^{⊗m})` of a scheme `X` over `k`, where `ω_X^{⊗m}` is the `m`-th tensor
power of the canonical sheaf and `Γ(X, ω_X^{⊗m})` is a `k`-vector space through the structure
morphism. Hartshorne defines it for a nonsingular projective variety and `m > 0`. -/
def plurigenus {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (m : ℕ) : ℕ :=
  Module.finrank k
    (GlobalSectionsOver f (moduleSheafTensorPower (R := X.sheaf) m (canonicalSheaf f)))

/-- A morphism `M ⟶ h_*N` of modules, for `h : V ⟶ X` over `k`, is `k`-linear on global
sections. -/
def globalSectionsLinearMap {X V : Scheme.{u}} (h : V ⟶ X) (q : X ⟶ Spec (.of k))
    {M : X.Modules} {N : V.Modules} (φ : M ⟶ (Modules.pushforward h).obj N) :
    GlobalSectionsOver q M →ₗ[k] GlobalSectionsOver (h ≫ q) N where
  toFun s := φ.val.app (op ⊤) s
  map_add' x y := map_add (φ.val.app (op ⊤)).hom x y
  map_smul' a s := (φ.val.app (op ⊤)).hom.map_smul (structureRingHom q a) s

theorem globalSectionsLinearMap_apply {X V : Scheme.{u}} (h : V ⟶ X) (q : X ⟶ Spec (.of k))
    {M : X.Modules} {N : V.Modules} (φ : M ⟶ (Modules.pushforward h).obj N)
    (s : GlobalSectionsOver q M) :
    globalSectionsLinearMap h q φ s = φ.val.app (op ⊤) s :=
  rfl

/-- An integral scheme of finite type over a field has finite dimension. -/
theorem exists_topologicalKrullDim_eq_nat {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsIntegral X]
    (hp : FiniteType p) : ∃ n : ℕ, topologicalKrullDim X = n := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have : Nonempty U := ⟨⟨x, X.affineCover.covers x⟩⟩
  obtain ⟨N, -, hN⟩ := DimensionCodimension.exists_ringKrullDim_eq p hp U hU
  exact ⟨N, hN⟩

/-- Birationally equivalent integral schemes of finite type over `k` have the same dimension. -/
theorem topologicalKrullDim_eq_of_partialIso {X X' : Scheme.{u}} (pX : X ⟶ Spec (.of k))
    (pX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X'] (hpX : FiniteType pX)
    (hpX' : FiniteType pX') (e : X.PartialIso X') {n : ℕ} (hn : topologicalKrullDim X = n) :
    topologicalKrullDim X' = n := by
  obtain ⟨n', hn'⟩ := exists_topologicalKrullDim_eq_nat pX' hpX'
  have : Nonempty e.source := e.dense_source.nonempty.to_subtype
  have : Nonempty e.target := e.dense_target.nonempty.to_subtype
  have : IsIntegral e.source := isIntegral_of_isOpenImmersion e.source.ι
  have : IsIntegral e.target := isIntegral_of_isOpenImmersion e.target.ι
  have h1 := topologicalKrullDim_opens_eq pX hpX hn e.source
  have h2 := topologicalKrullDim_opens_eq pX' hpX' hn' e.target
  have h3 := IsHomeomorph.topologicalKrullDim_eq _ e.iso.hom.homeomorph.isHomeomorph
  rw [hn']
  exact h2.symm.trans (h3.symm.trans h1)

/-- **One half of the birational invariance of plurigenera.** For nonsingular varieties `X`, `X'`
of dimension `n`, proper over an algebraically closed field `k` and birational over `k`,
`dim_k Γ(X', ω_{X'}^{⊗m}) ≤ dim_k Γ(X, ω_X^{⊗m})` (as cardinals). -/
theorem rank_globalSections_le_of_partialIso [IsAlgClosed k] {X X' : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X']
    [IsProper pX] [IsProper pX'] (hX : X.IsRegular) (hX' : X'.IsRegular) (e : X.PartialIso X')
    (he : e.IsOver pX pX') {n : ℕ} (hnX : topologicalKrullDim X = n)
    (hnX' : topologicalKrullDim X' = n) (m : ℕ) :
    Module.rank k (GlobalSectionsOver pX' (moduleSheafTensorPower (R := X'.sheaf) m
      (moduleSheafExteriorPower (R := X'.sheaf) n (relativeDifferentials pX')))) ≤
    Module.rank k (GlobalSectionsOver pX (moduleSheafTensorPower (R := X.sheaf) m
      (moduleSheafExteriorPower (R := X.sheaf) n (relativeDifferentials pX)))) := by
  let : X.Over (Spec (.of k)) := ⟨pX⟩
  let : X'.Over (Spec (.of k)) := ⟨pX'⟩
  have hpX : FiniteType pX := ⟨inferInstance, inferInstance⟩
  have hpX' : FiniteType pX' := ⟨inferInstance, inferInstance⟩
  have : X'.IsSeparated := ⟨by
    rw [show Limits.terminal.from X' = pX' ≫ Limits.terminal.from _ from
      Limits.terminal.hom_ext _ _]
    infer_instance⟩
  -- The birational map `T` and its domain `V`, whose complement has codimension `≥ 2`.
  let T : X ⤏ X' := e.toRationalMap
  have hcodim : 2 ≤ codim ((T.domain : Set X)ᶜ) :=
    (Scheme.RationalMap.codim_compl_domain_birational (k := k)
      ⟨inferInstance, (inferInstance : IsSeparated pX), (inferInstance : LocallyOfFiniteType pX),
        (inferInstance : QuasiCompact pX)⟩ hX
      ⟨inferInstance, (inferInstance : IsProper pX')⟩ T ⟨e, he, rfl⟩).2
  have : e.toPartialMap.IsOver (Spec (.of k)) := ⟨(Category.assoc _ _ _).trans he⟩
  let φ : X.PartialMap X' := T.toPartialMap
  have : φ.IsOver (Spec (.of k)) := inferInstance
  have hφ : φ.hom ≫ pX' = φ.domain.ι ≫ pX := HomIsOver.comp_over (f := φ.hom) (S := Spec (.of k))
  let V : X.Opens := φ.domain
  -- Pullback along `φ` is injective on `Γ(X', ω^{⊗m})`.
  obtain ⟨W, hWl, hW, hj⟩ := φ.exists_isOpenImmersion e (T.toRationalMap_toPartialMap).symm
  have hL := canonicalSheaf_isInvertible pX' hpX' hX' n hnX'
  rw [canonicalSheaf_eq pX' hnX'] at hL
  have hinj := injective_app_top_of_comp_eq_unit φ.hom (X.homOfLE hWl)
    (isInvertible_moduleSheafTensorPower hL m) _ _
    (tensorPowerPushforwardMap_comp_restrictPushforwardMap φ.hom (X.homOfLE hWl) _ _
      (exteriorPowerPullback_comp_openImmersionExteriorPowerMap φ.hom (X.homOfLE hWl) pX' n) m)
  -- Pullback along `V ⟶ X` is bijective on `Γ(X, ω^{⊗m})`.
  have : IsNoetherian X := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pX
    exact {}
  have : IsNormal X := isNormal_of_isRegular hX
  have hLX := canonicalSheaf_isInvertible pX hpX hX n hnX
  rw [canonicalSheaf_eq pX hnX] at hLX
  have himg : V.ι ''ᵁ V.ι ⁻¹ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  have hρ := Scheme.Modules.bijective_presheaf_map_top_of_two_le_codim (V.ι ''ᵁ V.ι ⁻¹ᵁ ⊤)
    (by rw [himg]; exact hcodim) _ (isInvertible_moduleSheafTensorPower hLX m)
  have hbij := bijective_app_top_of_restrict V.ι _ _
    (tensorPowerPushforwardMap_comp_restrictMap V.ι _ _
      (exteriorPowerPushforwardMap_comp_restrictMap V.ι _ _
        (relativeDifferentialsToPushforwardComp_comp_restrictMap V.ι pX) n) m)
    (restrictLeftComposite_tensorPower V.ι _ _
      (restrictLeftComposite_exteriorPower V.ι _ _
        (restrictLeftComposite_differentials V.ι pX) n) m) hρ
  -- Compare ranks.
  have h1 := LinearMap.rank_le_of_injective (globalSectionsLinearMap φ.hom pX'
    (tensorPowerPushforwardMap φ.hom (exteriorPowerPullback φ.hom pX' n) m)) hinj
  have h2 := (LinearEquiv.ofBijective (globalSectionsLinearMap V.ι pX
    (tensorPowerPushforwardMap V.ι
      (exteriorPowerPushforwardMap V.ι (relativeDifferentialsToPushforwardComp V.ι pX) n) m))
    hbij).rank_eq
  refine h1.trans (le_of_eq (Eq.trans ?_ h2.symm))
  rw [hφ]

/-- **Hartshorne, Exercise II.8.8: birational invariance of plurigenera.** If `X` and `X'` are
nonsingular varieties, proper over an algebraically closed field `k` and birationally equivalent
over `k` (a partial isomorphism `X ⤏ X'` over `k`), then `P_m(X) = P_m(X')` for every `m`.
Hartshorne states it for projective varieties and `m > 0`; here `X`, `X'` are integral regular
schemes proper over `k`, and `m = 0` is allowed. -/
theorem plurigenus_eq_of_birational [IsAlgClosed k] {X X' : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X']
    [IsProper pX] [IsProper pX'] (hX : X.IsRegular) (hX' : X'.IsRegular)
    (hbir : ∃ e : X.PartialIso X', e.IsOver pX pX') (m : ℕ) :
    plurigenus pX m = plurigenus pX' m := by
  obtain ⟨e, he⟩ := hbir
  have hpX : FiniteType pX := ⟨inferInstance, inferInstance⟩
  have hpX' : FiniteType pX' := ⟨inferInstance, inferInstance⟩
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_nat pX hpX
  have hn' := topologicalKrullDim_eq_of_partialIso pX pX' hpX hpX' e hn
  unfold plurigenus
  rw [canonicalSheaf_eq pX hn, canonicalSheaf_eq pX' hn']
  exact congrArg Cardinal.toNat (le_antisymm
    (rank_globalSections_le_of_partialIso pX' pX hX' hX e.symm he.symm hn' hn m)
    (rank_globalSections_le_of_partialIso pX pX' hX hX' e he hn hn' m))

end Plurigenus

section GeometricGenus

variable {k : Type u} [Field k]

/-- On a nonsingular variety `X` of dimension `n` over an algebraically closed field,
`⋀^q Ω_{X/k}` is locally free of rank `n choose q`. -/
theorem isLocallyFreeOfRank_exteriorPower_relativeDifferentials [IsAlgClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IrreducibleSpace X] (hp : FiniteType p) (hX : X.IsRegular) {n : ℕ}
    (hn : topologicalKrullDim X = n) (q : ℕ) :
    Modules.IsLocallyFreeOfRank
      (moduleSheafExteriorPower (R := X.sheaf) q (relativeDifferentials p)) (n.choose q) := by
  have h := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank p hp n hn).mp hX
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at h
  exact (Scheme.Modules.isLocallyFreeOfRank_iff_ringed _ _).mpr (h.moduleSheafExteriorPower q)

/-- **One half of the birational invariance of regular `q`-forms.** For nonsingular varieties
`X`, `X'` of dimension `n`, proper over an algebraically closed field `k` and birational over `k`,
`dim_k Γ(X', ⋀^q Ω_{X'/k}) ≤ dim_k Γ(X, ⋀^q Ω_{X/k})` (as cardinals). -/
theorem rank_globalSections_exteriorPower_le_of_partialIso [IsAlgClosed k] {X X' : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X']
    [IsProper pX] [IsProper pX'] (hX : X.IsRegular) (hX' : X'.IsRegular) (e : X.PartialIso X')
    (he : e.IsOver pX pX') {n : ℕ} (hnX : topologicalKrullDim X = n)
    (hnX' : topologicalKrullDim X' = n) (q : ℕ) :
    Module.rank k (GlobalSectionsOver pX'
      (moduleSheafExteriorPower (R := X'.sheaf) q (relativeDifferentials pX'))) ≤
    Module.rank k (GlobalSectionsOver pX
      (moduleSheafExteriorPower (R := X.sheaf) q (relativeDifferentials pX))) := by
  let : X.Over (Spec (.of k)) := ⟨pX⟩
  let : X'.Over (Spec (.of k)) := ⟨pX'⟩
  have hpX : FiniteType pX := ⟨inferInstance, inferInstance⟩
  have hpX' : FiniteType pX' := ⟨inferInstance, inferInstance⟩
  have : X'.IsSeparated := ⟨by
    rw [show Limits.terminal.from X' = pX' ≫ Limits.terminal.from _ from
      Limits.terminal.hom_ext _ _]
    infer_instance⟩
  -- The birational map `T` and its domain `V`, whose complement has codimension `≥ 2`.
  let T : X ⤏ X' := e.toRationalMap
  have hcodim : 2 ≤ codim ((T.domain : Set X)ᶜ) :=
    (Scheme.RationalMap.codim_compl_domain_birational (k := k)
      ⟨inferInstance, (inferInstance : IsSeparated pX), (inferInstance : LocallyOfFiniteType pX),
        (inferInstance : QuasiCompact pX)⟩ hX
      ⟨inferInstance, (inferInstance : IsProper pX')⟩ T ⟨e, he, rfl⟩).2
  have : e.toPartialMap.IsOver (Spec (.of k)) := ⟨(Category.assoc _ _ _).trans he⟩
  let φ : X.PartialMap X' := T.toPartialMap
  have : φ.IsOver (Spec (.of k)) := inferInstance
  have hφ : φ.hom ≫ pX' = φ.domain.ι ≫ pX := HomIsOver.comp_over (f := φ.hom) (S := Spec (.of k))
  let V : X.Opens := φ.domain
  -- Pullback along `φ` is injective on `Γ(X', ⋀^q Ω_{X'/k})`.
  obtain ⟨W, hWl, hW, hj⟩ := φ.exists_isOpenImmersion e (T.toRationalMap_toPartialMap).symm
  have hinj := injective_app_top_of_comp_eq_unit φ.hom (X.homOfLE hWl)
    (isLocallyFreeOfRank_exteriorPower_relativeDifferentials pX' hpX' hX' hnX' q) _ _
    (exteriorPowerPullback_comp_openImmersionExteriorPowerMap φ.hom (X.homOfLE hWl) pX' q)
  -- Pullback along `V ⟶ X` is bijective on `Γ(X, ⋀^q Ω_{X/k})`.
  have : IsNoetherian X := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pX
    exact {}
  have : IsNormal X := isNormal_of_isRegular hX
  have himg : V.ι ''ᵁ V.ι ⁻¹ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  have hρ := Scheme.Modules.bijective_presheaf_map_top_of_two_le_codim (V.ι ''ᵁ V.ι ⁻¹ᵁ ⊤)
    (by rw [himg]; exact hcodim) _
    (isLocallyFreeOfRank_exteriorPower_relativeDifferentials pX hpX hX hnX q)
  have hbij := bijective_app_top_of_restrict V.ι _ _
    (exteriorPowerPushforwardMap_comp_restrictMap V.ι _ _
      (relativeDifferentialsToPushforwardComp_comp_restrictMap V.ι pX) q)
    (restrictLeftComposite_exteriorPower V.ι _ _
      (restrictLeftComposite_differentials V.ι pX) q) hρ
  -- Compare ranks.
  have h1 := LinearMap.rank_le_of_injective (globalSectionsLinearMap φ.hom pX'
    (exteriorPowerPullback φ.hom pX' q)) hinj
  have h2 := (LinearEquiv.ofBijective (globalSectionsLinearMap V.ι pX
    (exteriorPowerPushforwardMap V.ι (relativeDifferentialsToPushforwardComp V.ι pX) q))
    hbij).rank_eq
  refine h1.trans (le_of_eq (Eq.trans ?_ h2.symm))
  rw [hφ]

/-- **Hartshorne, Theorem II.8.19: birational invariance of the geometric genus.** If `X` and `X'`
are nonsingular varieties, proper over an algebraically closed field `k` and birationally
equivalent over `k` (a partial isomorphism `X ⤏ X'` over `k`), then `p_g(X) = p_g(X')`.
Hartshorne states it for projective varieties; here `X`, `X'` are integral regular schemes proper
over `k`. -/
theorem geometricGenus_eq_of_birational [IsAlgClosed k] {X X' : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X']
    [IsProper pX] [IsProper pX'] (hX : X.IsRegular) (hX' : X'.IsRegular)
    (hbir : ∃ e : X.PartialIso X', e.IsOver pX pX') :
    geometricGenus pX = geometricGenus pX' := by
  obtain ⟨e, he⟩ := hbir
  have hpX : FiniteType pX := ⟨inferInstance, inferInstance⟩
  have hpX' : FiniteType pX' := ⟨inferInstance, inferInstance⟩
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_nat pX hpX
  have hn' := topologicalKrullDim_eq_of_partialIso pX pX' hpX hpX' e hn
  unfold geometricGenus
  rw [canonicalSheaf_eq pX hn, canonicalSheaf_eq pX' hn']
  exact congrArg Cardinal.toNat (le_antisymm
    (rank_globalSections_exteriorPower_le_of_partialIso pX' pX hX' hX e.symm he.symm hn' hn n)
    (rank_globalSections_exteriorPower_le_of_partialIso pX pX' hX hX' e he hn hn' n))

/-- **The Hodge number h^{q,0}, the dimension of the space of regular q-forms (Hartshorne,
Exercise II.8.8).**
`h^{q,0}(X) = dim_k Γ(X, ⋀^q Ω_{X/k})` for a scheme `X` over `k`, where `Γ(X, ⋀^q Ω_{X/k})` is a
`k`-vector space through the structure morphism. Hartshorne defines it for a nonsingular
projective variety and `0 ≤ q ≤ dim X`. -/
def regularFormDimension {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (q : ℕ) : ℕ :=
  Module.finrank k
    (GlobalSectionsOver f (moduleSheafExteriorPower (R := X.sheaf) q (relativeDifferentials f)))

/-- **Hartshorne, Exercise II.8.8: birational invariance of `h^{q,0}`.** Let `k` be an
algebraically closed field (Hartshorne's convention for varieties in Chapter II). If `X` and `X'`
are nonsingular varieties, proper over `k` and birationally equivalent over `k` (a partial
isomorphism `X ⤏ X'` over `k`), then `h^{q,0}(X) = h^{q,0}(X')` for every `q`. Hartshorne states
it for projective varieties and `0 ≤ q ≤ dim X`; here `X`, `X'` are integral regular schemes
proper over `k`, and every `q` is allowed. -/
theorem regularFormDimension_eq_of_birational [IsAlgClosed k] {X X' : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X']
    [IsProper pX] [IsProper pX'] (hX : X.IsRegular) (hX' : X'.IsRegular)
    (hbir : ∃ e : X.PartialIso X', e.IsOver pX pX') (q : ℕ) :
    regularFormDimension pX q = regularFormDimension pX' q := by
  obtain ⟨e, he⟩ := hbir
  have hpX : FiniteType pX := ⟨inferInstance, inferInstance⟩
  have hpX' : FiniteType pX' := ⟨inferInstance, inferInstance⟩
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_nat pX hpX
  have hn' := topologicalKrullDim_eq_of_partialIso pX pX' hpX hpX' e hn
  exact congrArg Cardinal.toNat (le_antisymm
    (rank_globalSections_exteriorPower_le_of_partialIso pX' pX hX' hX e.symm he.symm hn' hn q)
    (rank_globalSections_exteriorPower_le_of_partialIso pX pX' hX hX' e he hn hn' q))

end GeometricGenus

end Hartshorne
