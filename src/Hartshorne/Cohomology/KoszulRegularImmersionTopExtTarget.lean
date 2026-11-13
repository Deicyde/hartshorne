/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulRegularImmersionTopExtCharts
import Hartshorne.RingedSpace.ModuleSheafHomEvalAt

/-!
# The target of the top-Ext isomorphism of a Koszul-regular immersion: evaluation at frames

Let `i : X ⟶ Y` be a morphism of schemes and `L`, `N` modules on `X`. For a section `ω` of `L`
over `i⁻¹ V`, evaluation at `ω` is a morphism `(i_* ℋom(L, N))|_V ⟶ (i_* N)|_V`
(`Hartshorne.KoszulTarget.frameEval`, `ψ ↦ ψ(ω|_{i⁻¹ U})` on sections over `U ⊆ V`, built from
sections by `Hartshorne.Ringed.RestrictGlue.localHomMk`). It is an isomorphism when `ω` is a
one-element frame of `L` over `i⁻¹ V` (`isIso_frameEval`), it is compatible with restriction of
`ω` (`localApp_frameEval_restrict`), and evaluation at `a ω` is evaluation at `ω` followed by
multiplication by `a` (`frameEval_smul`).

Consequently (`nonempty_sheafExt_iso_of_frames`): for a closed immersion `i`, a quasi-coherent
`M` and frames `ω_c` of an invertible `L` over `i⁻¹ V` for the Koszul charts `c` covering `Y`,
compatible with restriction to basic opens and satisfying `ω_{f Q} = det Q · ω_f`, there is an
isomorphism `ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_* ℋom(L, i^* M)`. For `L = ⋀^r(i^* I)` the frame of a chart is
`[f₁] ∧ ⋯ ∧ [f_r]`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Ringed

namespace RestrictGlue

/-- Restriction maps of a presheaf of rings compose. -/
lemma ring_map_map_apply {Z : TopCat.{u}} (P : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u}) {a b d : (Opens Z)ᵒᵖ}
    (f : a ⟶ b) (g : b ⟶ d) (k : a ⟶ d) (r : P.obj a) : P.map g (P.map f r) = P.map k r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {E T : SheafOfModules.{u} (ringCatSheafOf R)} {V : Opens X}

/-- Morphisms of modules on the open subspace `V` agreeing on the sections over the opens of `X`
contained in `V` are equal. -/
lemma localApp_ext {φ ψ : (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T}
    (h : ∀ (U : Opens X) (hU : U ≤ V) (x : E.val.obj (op U)),
      localApp φ hU x = localApp ψ hU x) : φ = ψ := by
  apply SheafOfModules.hom_ext
  ext W x : 3
  rw [← localApp_eq_app φ W.unop x, ← localApp_eq_app ψ W.unop x]
  exact h _ _ x

/-- The morphism `E|_V ⟶ T|_V` given by linear maps on the sections over the opens `U ⊆ V` of
`X`, compatible with restriction. -/
noncomputable def localHomMk
    (f : ∀ (U : Opens X) (_ : U ≤ V), E.val.obj (op U) →ₗ[R.obj.obj (op U)] T.val.obj (op U))
    (hf : ∀ (U U' : Opens X) (h : U ≤ V) (h' : U' ≤ U) (x : E.val.obj (op U)),
      f U' (h'.trans h) (E.val.map (homOfLE h').op x) = T.val.map (homOfLE h').op (f U h x)) :
    (moduleRestrict V).obj E ⟶ (moduleRestrict V).obj T :=
  modulesHomMk (fun W => f _ (functor_obj_le W)) fun W _ i x =>
    hf _ _ (functor_obj_le W) (V.isOpenEmbedding.isOpenMap.functor.monotone i) x

variable (f : ∀ (U : Opens X) (_ : U ≤ V), E.val.obj (op U) →ₗ[R.obj.obj (op U)] T.val.obj (op U))
  (hf : ∀ (U U' : Opens X) (h : U ≤ V) (h' : U' ≤ U) (x : E.val.obj (op U)),
      f U' (h'.trans h) (E.val.map (homOfLE h').op x) = T.val.map (homOfLE h').op (f U h x))

/-- `localHomMk` on sections over an open `U ⊆ V` of `X`. -/
lemma localApp_localHomMk {U : Opens X} (h : U ≤ V) (x : E.val.obj (op U)) :
    localApp (localHomMk f hf) h x = f U h x := by
  have hle : V.isOpenEmbedding.functor.obj (subOpen V U) ≤ U := (functor_obj_subOpen h).le
  have h1 := hf U _ h hle x
  change T.val.map (homOfLE (functor_obj_subOpen h).ge).op
    (f _ (functor_obj_le (subOpen V U)) (E.val.map (homOfLE hle).op x)) = _
  rw [h1, map_map, map_self]

/-- `localHomMk` is an isomorphism if all the linear maps are bijective. -/
lemma isIso_localHomMk (hb : ∀ (U : Opens X) (h : U ≤ V), Function.Bijective (f U h)) :
    IsIso (localHomMk f hf) :=
  ModuleGluing.isIso_of_bijective _ fun A => hb _ (functor_obj_le A.unop)

/-- Multiplication by a section of `𝒪_V`, on sections over an open `U ⊆ V` of `X`. -/
lemma localApp_scalarHom (c : (restrictRingSheaf R V).obj.obj (op ⊤)) {U : Opens X} (h : U ≤ V)
    (x : T.val.obj (op U)) :
    localApp (KoszulSheaf.scalarHom c ((moduleRestrict V).obj T)) h x =
      R.obj.map (homOfLE (h.trans (Opens.isOpenEmbedding_obj_top V).ge)).op c • x := by
  simp only [localApp]
  erw [KoszulSheaf.scalarHom_app, T.val.map_smul, map_map, map_self]
  congr 1
  exact ring_map_map_apply R.obj _ _ _ c

end RestrictGlue

end Ringed

namespace KoszulTarget

open AlgebraicGeometry Ringed Ringed.RestrictGlue

variable {Y X : Scheme.{u}} (i : X ⟶ Y) (L N : X.Modules)

/-- Evaluation at the restriction of a section `ω` of `L` over `i⁻¹ V`, on the sections over an
open `U ⊆ V` of `i_* ℋom(L, N)`. -/
noncomputable def frameEvalLinear {V : Y.Opens} (ω : L.val.presheaf.obj (op (i ⁻¹ᵁ V)))
    (U : Y.Opens) (h : U ≤ V) :
    ((Scheme.Modules.pushforward i).obj (moduleSheafHom (R := X.sheaf) L N)).val.obj (op U)
      →ₗ[Y.sheaf.obj.obj (op U)] ((Scheme.Modules.pushforward i).obj N).val.obj (op U) where
  toFun ψ := moduleSheafHomEval (R := X.sheaf) ψ (le_refl _)
    (L.val.presheaf.map (homOfLE (i.preimage_mono h)).op ω)
  map_add' _ _ := rfl
  map_smul' a ψ := by
    refine (moduleSheafHomEval_smul (R := X.sheaf) (i.app U a) ψ (le_refl _) _).trans ?_
    congr 1
    change X.sheaf.obj.map (𝟙 _) _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl

/-- `frameEvalLinear` commutes with restriction. -/
lemma frameEvalLinear_naturality {V : Y.Opens} (ω : L.val.presheaf.obj (op (i ⁻¹ᵁ V)))
    (U U' : Y.Opens) (h : U ≤ V) (h' : U' ≤ U)
    (x : ((Scheme.Modules.pushforward i).obj (moduleSheafHom (R := X.sheaf) L N)).val.obj
      (op U)) :
    frameEvalLinear i L N ω U' (h'.trans h)
        (((Scheme.Modules.pushforward i).obj (moduleSheafHom (R := X.sheaf) L N)).val.map
          (homOfLE h').op x) =
      ((Scheme.Modules.pushforward i).obj N).val.map (homOfLE h').op
        (frameEvalLinear i L N ω U h x) := by
  change moduleSheafHomEval (R := X.sheaf) x ((le_refl _).trans (i.preimage_mono h'))
      (L.val.presheaf.map (homOfLE (i.preimage_mono (h'.trans h))).op ω) =
    N.val.presheaf.map (homOfLE (i.preimage_mono h')).op
      (moduleSheafHomEval (R := X.sheaf) x (le_refl _)
        (L.val.presheaf.map (homOfLE (i.preimage_mono h)).op ω))
  rw [← moduleSheafHomEval_natural (R := X.sheaf) x (le_refl _) (i.preimage_mono h')]
  congr 1
  exact (presheaf_map_map_apply L _ _ _ ω).symm

/-- **Evaluation at a frame.** For a section `ω` of `L` over `i⁻¹ V`, the morphism
`(i_* ℋom(L, N))|_V ⟶ (i_* N)|_V`, `ψ ↦ ψ(ω|_{i⁻¹ U})` on sections over `U ⊆ V`. -/
noncomputable def frameEval {V : Y.Opens} (ω : L.val.presheaf.obj (op (i ⁻¹ᵁ V))) :
    (moduleRestrict V).obj ((Scheme.Modules.pushforward i).obj (moduleSheafHom (R := X.sheaf) L N))
      ⟶ (moduleRestrict V).obj ((Scheme.Modules.pushforward i).obj N) :=
  localHomMk (frameEvalLinear i L N ω) (frameEvalLinear_naturality i L N ω)

/-- `frameEval` on sections over an open `U ⊆ V`. -/
lemma localApp_frameEval {V : Y.Opens} (ω : L.val.presheaf.obj (op (i ⁻¹ᵁ V))) {U : Y.Opens}
    (h : U ≤ V)
    (x : ((Scheme.Modules.pushforward i).obj (moduleSheafHom (R := X.sheaf) L N)).val.obj
      (op U)) :
    localApp (frameEval i L N ω) h x = frameEvalLinear i L N ω U h x :=
  localApp_localHomMk _ _ h x

/-- Evaluation at a one-element frame is an isomorphism. -/
lemma isIso_frameEval {V : Y.Opens} (ω : L.val.presheaf.obj (op (i ⁻¹ᵁ V)))
    (hω : IsLocalFrame (R := X.sheaf) L (i ⁻¹ᵁ V) (fun _ : PUnit.{u + 1} => ω)) :
    IsIso (frameEval i L N ω) :=
  isIso_localHomMk _ _ fun _ h =>
    (Equiv.funUnique PUnit.{u + 1} _).bijective.comp
      (hω.localFrameEval_bijective (G := N) (i.preimage_mono h))

/-- Evaluation at a frame is compatible with restriction of the frame. -/
lemma localApp_frameEval_restrict {V W : Y.Opens} (hWV : W ≤ V)
    (ω : L.val.presheaf.obj (op (i ⁻¹ᵁ V))) (ω' : L.val.presheaf.obj (op (i ⁻¹ᵁ W)))
    (hω : L.val.presheaf.map (homOfLE (i.preimage_mono hWV)).op ω = ω')
    {U : Y.Opens} (hU : U ≤ W)
    (x : ((Scheme.Modules.pushforward i).obj (moduleSheafHom (R := X.sheaf) L N)).val.obj
      (op U)) :
    localApp (frameEval i L N ω) (hU.trans hWV) x = localApp (frameEval i L N ω') hU x := by
  rw [localApp_frameEval, localApp_frameEval, ← hω]
  change moduleSheafHomEval (R := X.sheaf) x (le_refl _) _ =
    moduleSheafHomEval (R := X.sheaf) x (le_refl _) _
  erw [map_map]
  rfl

/-- Evaluation at `a ω` is evaluation at `ω` followed by multiplication by `a`. -/
lemma frameEval_smul {V : Y.Opens} (a : Γ(Y, V)) (ω : L.val.presheaf.obj (op (i ⁻¹ᵁ V))) :
    frameEval i L N (i.app V a • (show Γ(L, i ⁻¹ᵁ V) from ω)) =
      frameEval i L N ω ≫ KoszulSheaf.scalarHom (KoszulImmersion.restrictPhi V a)
        ((moduleRestrict V).obj ((Scheme.Modules.pushforward i).obj N)) := by
  refine localApp_ext fun U h x => ?_
  rw [localApp_comp, localApp_scalarHom, localApp_frameEval, localApp_frameEval]
  change moduleSheafHomEval (R := X.sheaf) x (le_refl _)
      (L.val.presheaf.map (homOfLE (i.preimage_mono h)).op
        (i.app V a • (show Γ(L, i ⁻¹ᵁ V) from ω))) =
    i.app U (Y.sheaf.obj.map _ (KoszulImmersion.restrictPhi V a)) •
      (show Γ(N, i ⁻¹ᵁ U) from moduleSheafHomEval (R := X.sheaf) x (le_refl _)
        (L.val.presheaf.map (homOfLE (i.preimage_mono h)).op ω))
  erw [L.val.map_smul, LinearMap.map_smul]
  congr 1
  have e := ConcreteCategory.congr_hom (i.naturality (homOfLE h).op) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at e
  refine e.symm.trans (congrArg (fun z => i.app U z) ?_)
  exact (ring_map_map_apply Y.presheaf _ _ _ a).symm

section Frames

open Koszul KoszulImmersion KoszulSheaf

variable {Y X : Scheme.{u}} {i : X ⟶ Y} (M : Y.Modules) {s : ℕ} (L : X.Modules)
  (ω : ∀ (V : Y.Opens) (_ : KoszulChart i (s + 1) V), L.val.presheaf.obj (op (i ⁻¹ᵁ V)))
  (hω : ∀ (V : Y.Opens) (c : KoszulChart i (s + 1) V),
    IsLocalFrame (R := X.sheaf) L (i ⁻¹ᵁ V) (fun _ : PUnit.{u + 1} => ω V c))

/-- Evaluation at the frame `ω_c` of a chart, as an isomorphism
`(i_* ℋom(L, i^* M))|_V ≅ (i_* i^* M)|_V`. -/
noncomputable def frameEvalIso {V : Y.Opens} (c : KoszulChart i (s + 1) V) :
    (moduleRestrict V).obj ((Scheme.Modules.pushforward i).obj
      (moduleSheafHom (R := X.sheaf) L ((Scheme.Modules.pullback i).obj M))) ≅
      pullbackRestrict i M V :=
  haveI := isIso_frameEval i L ((Scheme.Modules.pullback i).obj M) (ω V c) (hω V c)
  asIso (frameEval i L ((Scheme.Modules.pullback i).obj M) (ω V c))

/-- Unfolding `frameEvalIso`. -/
lemma frameEvalIso_hom {V : Y.Opens} (c : KoszulChart i (s + 1) V) :
    (frameEvalIso M L ω hω c).hom = frameEval i L ((Scheme.Modules.pullback i).obj M) (ω V c) :=
  rfl

include hω in
/-- **The top-Ext isomorphism from frames.** Frames `ω_c` of `L` over `i⁻¹ V` for the Koszul
charts `c` of `i`, compatible with restriction to basic opens and transforming by
`ω_{f Q} = det Q · ω_f` under a change of generators, give an isomorphism
`ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_* ℋom(L, i^* M)` when the charts cover `Y`. -/
theorem nonempty_sheafExt_iso_of_frames [IsClosedImmersion i] [M.IsQuasicoherent]
    (hres : ∀ (V : Y.Opens) (c : KoszulChart i (s + 1) V) (W : Y.Opens) (b : Γ(Y, V))
      (hb : Y.basicOpen b = W),
      L.val.presheaf.map (homOfLE (i.preimage_mono (le_of_basicOpen_eq b hb))).op (ω V c) =
        ω W (c.restrict W b hb))
    (hdet : ∀ (V : Y.Opens) (c : KoszulChart i (s + 1) V) (g : Fin (s + 1) → Γ(Y, V))
      (hIg : i.ker.ideal ⟨V, c.hV⟩ = Ideal.span (Set.range g))
      (hfg : IsKoszulRegular g (ModuleCat.of Γ(Y, V) Γ(Y, V)))
      (Q : Matrix (Fin (s + 1)) (Fin (s + 1)) Γ(Y, V)) (_ : g = Matrix.vecMul c.f Q),
      ω V ⟨c.hV, g, hIg, hfg⟩ = i.app V Q.det • (show Γ(L, i ⁻¹ᵁ V) from ω V c))
    (hcover : ∀ y : Y, ∃ (V : Y.Opens) (_ : KoszulChart i (s + 1) V), y ∈ V) :
    Nonempty ((Ringed.sheafExt (R := Y.sheaf) ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)) (s + 1)).obj M ≅
        (Scheme.Modules.pushforward i).obj
          (moduleSheafHom (R := X.sheaf) L ((Scheme.Modules.pullback i).obj M))) := by
  refine nonempty_sheafExt_iso_of_localIso M _ (fun V c => frameEvalIso M L ω hω c)
    (fun V c W b hb U hU x => ?_) (fun V c g hIg hfg Q hg => ?_) hcover
  · rw [frameEvalIso_hom, frameEvalIso_hom]
    exact localApp_frameEval_restrict i L _ (le_of_basicOpen_eq b hb) _ _ (hres V c W b hb) hU x
  · rw [frameEvalIso_hom, frameEvalIso_hom, hdet V c g hIg hfg Q hg]
    exact frameEval_smul i L _ Q.det (ω V c)

end Frames

end KoszulTarget

end Hartshorne
