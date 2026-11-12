/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SectionAlgebraSheafComparison

/-!
# Multiplicativity of the section-algebra model

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.17, Steps 1–3 (pp. 166–167).

-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open CategoryTheory Opposite TopologicalSpace

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {F : SheafOfModules.{u} (ringCatSheafOf R)}

/-! ### Elementary tensors in tensor powers -/

/-- `T^{n+1} F ≅ T^n F ⊗ F` sends `f₁ ⊗ ⋯ ⊗ f_{n+1}` to `(f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f_{n+1}`. -/
theorem moduleSheafTensorPowerSuccIso_hom_tprod (n : ℕ) (U : Opens X)
    (m : Fin (n + 1) → F.val.obj (op U)) :
    sectionsMap (moduleSheafTensorPowerSuccIso F n).hom U
        ((moduleSheafTensorPowerMultilinear (n + 1) F).app (op U) m) =
      (moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op U)
        ((moduleSheafTensorPowerMultilinear n F).app (op U) (Fin.init m)) (m (Fin.last n)) :=
  moduleSheafTensorPowerHomEquiv_symm_tprod _ U m

/-- `T^n F ⊗ F ≅ T^{n+1} F` sends `(f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f` to `f₁ ⊗ ⋯ ⊗ fₙ ⊗ f`. -/
theorem moduleSheafTensorPowerSuccIso_inv_tmul (n : ℕ) (U : Opens X)
    (m : Fin n → F.val.obj (op U)) (x : F.val.obj (op U)) :
    sectionsMap (moduleSheafTensorPowerSuccIso F n).inv U
        ((moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op U)
          ((moduleSheafTensorPowerMultilinear n F).app (op U) m) x) =
      (moduleSheafTensorPowerMultilinear (n + 1) F).app (op U) (Fin.snoc m x) :=
  tensorPowerSnocDesc_tmul _ m x

private theorem sectionsMap_comp_apply {A B C : SheafOfModules.{u} (ringCatSheafOf R)}
    (f : A ⟶ B) (g : B ⟶ C) (U : Opens X) (x : A.val.obj (op U)) :
    sectionsMap (f ≫ g) U x = sectionsMap g U (sectionsMap f U x) :=
  rfl

/-- `T^{a+b} F ≅ T^a F ⊗ T^b F` sends `f₁ ⊗ ⋯ ⊗ f_{a+b}` to
`(f₁ ⊗ ⋯ ⊗ f_a) ⊗ (f_{a+1} ⊗ ⋯ ⊗ f_{a+b})`. -/
theorem moduleSheafTensorPowerAddIso_hom_tprod_append (a : ℕ) : ∀ (b : ℕ) (U : Opens X)
    (m : Fin a → F.val.obj (op U)) (m' : Fin b → F.val.obj (op U)),
    sectionsMap (moduleSheafTensorPowerAddIso F a b).hom U
        ((moduleSheafTensorPowerMultilinear (a + b) F).app (op U) (Fin.append m m')) =
      (moduleSheafTensorBilinear (moduleSheafTensorPower a F) (moduleSheafTensorPower b F)).app
        (op U) ((moduleSheafTensorPowerMultilinear a F).app (op U) m)
        ((moduleSheafTensorPowerMultilinear b F).app (op U) m')
  | 0, U, m, m' => by
    have hm : Fin.append m m' = m := by
      funext k
      exact Fin.append_left m m' k
    have hm' : tensorPowerZeroSection F U =
        (moduleSheafTensorPowerMultilinear 0 F).app (op U) m' :=
      congrArg ((moduleSheafTensorPowerMultilinear 0 F).app (op U)) (funext fun k => k.elim0)
    rw [hm]
    have e : (moduleSheafTensorPowerAddIso F a 0).hom =
      (moduleSheafUnitTensor _).inv ≫ (moduleSheafTensorComm _ _).hom ≫
        modulesTensorMap (𝟙 _) (tensorPowerZeroInv F) := rfl
    rw [e, sectionsMap_comp_apply, sectionsMap_comp_apply]
    have h1 : ∀ (G : SheafOfModules.{u} (ringCatSheafOf R)) y,
        sectionsMap (moduleSheafUnitTensor G).inv U y =
        (moduleSheafTensorBilinear (structureModule R) G).app (op U)
          (show (structureModule R).val.obj (op U) from (1 : R.obj.obj (op U))) y :=
      fun _ _ => rfl
    have h2 : sectionsMap (tensorPowerZeroInv F) U
        (show (structureModule R).val.obj (op U) from (1 : R.obj.obj (op U))) =
        tensorPowerZeroSection F U := by
      change ((1 : (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) •
        tensorPowerZeroSection F U) = _
      exact one_smul _ _
    rw [h1, show ∀ E G : SheafOfModules.{u} (ringCatSheafOf R),
      (moduleSheafTensorComm E G).hom = moduleSheafTensorFlip E G from fun _ _ => rfl,
      moduleSheafTensorFlip_tmul, modulesTensorMap_tmul, h2, ← hm']
    rfl
  | b + 1, U, m, m' => by
    obtain ⟨m'', x, rfl⟩ : ∃ m'' x, m' = Fin.snoc m'' x :=
      ⟨Fin.init m', m' (Fin.last b), (Fin.snoc_init_self m').symm⟩
    have e : (moduleSheafTensorPowerAddIso F a (b + 1)).hom =
      (moduleSheafTensorPowerSuccIso F (a + b)).hom ≫
        modulesTensorMap (moduleSheafTensorPowerAddIso F a b).hom (𝟙 F) ≫
        (moduleSheafTensorAssoc _ _ _).hom ≫
        modulesTensorMap (𝟙 _) (moduleSheafTensorPowerSuccIso F b).inv := rfl
    rw [Fin.append_snoc, e, sectionsMap_comp_apply, sectionsMap_comp_apply,
      sectionsMap_comp_apply]
    have h3 := moduleSheafTensorPowerSuccIso_hom_tprod (F := F) (a + b) U
      (Fin.snoc (Fin.append m m'') x)
    rw [Fin.init_snoc, Fin.snoc_last] at h3
    refine (congrArg (fun y => sectionsMap (modulesTensorMap (𝟙 (moduleSheafTensorPower a F))
      (moduleSheafTensorPowerSuccIso F b).inv) U
        (sectionsMap (moduleSheafTensorAssoc (moduleSheafTensorPower a F)
          (moduleSheafTensorPower b F) F).hom U
          (sectionsMap (modulesTensorMap (moduleSheafTensorPowerAddIso F a b).hom (𝟙 F)) U y)))
      h3).trans ?_
    dsimp only
    rw [modulesTensorMap_tmul, moduleSheafTensorPowerAddIso_hom_tprod_append a b U m m'']
    rw [show (moduleSheafTensorAssoc (moduleSheafTensorPower a F) (moduleSheafTensorPower b F)
      F).hom = (assocTrilinear _ _ _).tensorDesc from rfl, ModuleSheafTrilinear.tensorDesc_tmul]
    have h4 : ∀ (A B C : SheafOfModules.{u} (ringCatSheafOf R)) (l : A.val.obj (op U))
        (l' : B.val.obj (op U)) (l'' : C.val.obj (op U)),
        (assocTrilinear A B C).app U l l' l'' = (moduleSheafTensorBilinear A _).app (op U) l
          ((moduleSheafTensorBilinear B C).app (op U) l' l'') := fun _ _ _ _ _ _ => rfl
    have h5 : ∀ (A : SheafOfModules.{u} (ringCatSheafOf R)) (l : A.val.obj (op U)),
        sectionsMap (𝟙 A) U l = l := fun _ _ => rfl
    rw [h4, modulesTensorMap_tmul, h5, h5, moduleSheafTensorPowerSuccIso_inv_tmul]

/-! ### The product of sections of tensor powers -/

/-- The product `T^p F(U) × T^q F(U) → T^{p+q} F(U)`, `(s, t) ↦ s ⊗ t`, induced by the
isomorphism `T^p F ⊗ T^q F ≅ T^{p+q} F`. -/
noncomputable def moduleSheafTensorPowerMulSection {p q : ℕ} {U : Opens X}
    (s : (moduleSheafTensorPower p F).val.obj (op U))
    (t : (moduleSheafTensorPower q F).val.obj (op U)) :
    (moduleSheafTensorPower (p + q) F).val.obj (op U) :=
  sectionsMap (moduleSheafTensorPowerAddIso F p q).inv U
    ((moduleSheafTensorBilinear (moduleSheafTensorPower p F) (moduleSheafTensorPower q F)).app
      (op U) s t)

/-- The product of `f₁ ⊗ ⋯ ⊗ f_p` and `g₁ ⊗ ⋯ ⊗ g_q` is `f₁ ⊗ ⋯ ⊗ f_p ⊗ g₁ ⊗ ⋯ ⊗ g_q`. -/
theorem moduleSheafTensorPowerMulSection_tprod {p q : ℕ} {U : Opens X}
    (m : Fin p → F.val.obj (op U)) (m' : Fin q → F.val.obj (op U)) :
    moduleSheafTensorPowerMulSection ((moduleSheafTensorPowerMultilinear p F).app (op U) m)
        ((moduleSheafTensorPowerMultilinear q F).app (op U) m') =
      (moduleSheafTensorPowerMultilinear (p + q) F).app (op U) (Fin.append m m') := by
  rw [moduleSheafTensorPowerMulSection, ← moduleSheafTensorPowerAddIso_hom_tprod_append,
    ← sectionsMap_comp_apply, Iso.hom_inv_id]
  rfl

theorem moduleSheafTensorPowerMulSection_smul_left {p q : ℕ} {U : Opens X}
    (c : (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
    (s : (moduleSheafTensorPower p F).val.obj (op U))
    (t : (moduleSheafTensorPower q F).val.obj (op U)) :
    moduleSheafTensorPowerMulSection (c • s) t = c • moduleSheafTensorPowerMulSection s t := by
  rw [moduleSheafTensorPowerMulSection, LinearMap.map_smul₂]
  exact ((moduleSheafTensorPowerAddIso F p q).inv.val.app (op U)).hom.map_smul c _

theorem moduleSheafTensorPowerMulSection_smul_right {p q : ℕ} {U : Opens X}
    (c : (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
    (s : (moduleSheafTensorPower p F).val.obj (op U))
    (t : (moduleSheafTensorPower q F).val.obj (op U)) :
    moduleSheafTensorPowerMulSection s (c • t) = c • moduleSheafTensorPowerMulSection s t := by
  rw [moduleSheafTensorPowerMulSection, LinearMap.map_smul]
  exact ((moduleSheafTensorPowerAddIso F p q).inv.val.app (op U)).hom.map_smul c _

theorem moduleSheafTensorPowerMulSection_add_left {p q : ℕ} {U : Opens X}
    (s s' : (moduleSheafTensorPower p F).val.obj (op U))
    (t : (moduleSheafTensorPower q F).val.obj (op U)) :
    moduleSheafTensorPowerMulSection (s + s') t =
      moduleSheafTensorPowerMulSection s t + moduleSheafTensorPowerMulSection s' t := by
  rw [moduleSheafTensorPowerMulSection, LinearMap.map_add₂]
  exact ((moduleSheafTensorPowerAddIso F p q).inv.val.app (op U)).hom.map_add _ _

theorem moduleSheafTensorPowerMulSection_add_right {p q : ℕ} {U : Opens X}
    (s : (moduleSheafTensorPower p F).val.obj (op U))
    (t t' : (moduleSheafTensorPower q F).val.obj (op U)) :
    moduleSheafTensorPowerMulSection s (t + t') =
      moduleSheafTensorPowerMulSection s t + moduleSheafTensorPowerMulSection s t' := by
  rw [moduleSheafTensorPowerMulSection, LinearMap.map_add]
  exact ((moduleSheafTensorPowerAddIso F p q).inv.val.app (op U)).hom.map_add _ _

theorem moduleSheafTensorPowerMulSection_zero_left {p q : ℕ} {U : Opens X}
    (t : (moduleSheafTensorPower q F).val.obj (op U)) :
    moduleSheafTensorPowerMulSection (0 : (moduleSheafTensorPower p F).val.obj (op U)) t = 0 := by
  rw [moduleSheafTensorPowerMulSection, LinearMap.map_zero₂]
  exact ((moduleSheafTensorPowerAddIso F p q).inv.val.app (op U)).hom.map_zero

theorem moduleSheafTensorPowerMulSection_zero_right {p q : ℕ} {U : Opens X}
    (s : (moduleSheafTensorPower p F).val.obj (op U)) :
    moduleSheafTensorPowerMulSection s (0 : (moduleSheafTensorPower q F).val.obj (op U)) = 0 := by
  rw [moduleSheafTensorPowerMulSection, LinearMap.map_zero]
  exact ((moduleSheafTensorPowerAddIso F p q).inv.val.app (op U)).hom.map_zero

/-- The product is compatible with restriction. -/
theorem moduleSheafTensorPowerMulSection_restrict {p q : ℕ} {U V : Opens X} (h : V ≤ U)
    (s : (moduleSheafTensorPower p F).val.obj (op U))
    (t : (moduleSheafTensorPower q F).val.obj (op U)) :
    (moduleSheafTensorPower (p + q) F).val.map (homOfLE h).op
        (moduleSheafTensorPowerMulSection s t) =
      moduleSheafTensorPowerMulSection ((moduleSheafTensorPower p F).val.map (homOfLE h).op s)
        ((moduleSheafTensorPower q F).val.map (homOfLE h).op t) := by
  rw [moduleSheafTensorPowerMulSection, moduleSheafTensorPowerMulSection,
    ← (moduleSheafTensorBilinear _ _).naturality]
  exact (ConcreteCategory.congr_hom
    ((moduleSheafTensorPowerAddIso F p q).inv.val.naturality (homOfLE h).op) _).symm

end Ringed

end Hartshorne

namespace Hartshorne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite GradedGlobalSections
open MonoidalCategory

namespace SectionAlgebraModel

/-! ### Elementary tensors of pulled-back degree-one sections -/

section TensorPowerTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤)
  {Z : Scheme.{u}} (ψ : Z ⟶ Proj 𝒜) {L : Z.Modules}
  (α : L ≅ (Scheme.Modules.pullback ψ).obj (projTwistingSheaf 𝒜 1))

/-- `F ≅ F'` and `G ≅ G'` act on `f ⊗ g` factorwise. -/
private theorem tensorIsoOfIso_hom_bilinear {F F' G G' : Z.Modules} (φ : F ≅ F') (φ' : G ≅ G')
    {U : Z.Opens} (f : Γ(F, U)) (g : Γ(G, U)) :
    Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafTensorIsoTensor F G ≪≫
        MonoidalCategory.tensorIso φ φ' ≪≫ (Ringed.moduleSheafTensorIsoTensor F' G').symm).hom U
        ((moduleSheafTensorBilinear F G).app (op U) f g) =
      (moduleSheafTensorBilinear F' G').app (op U) (φ.hom.app U f) (φ'.hom.app U g) := by
  refine (congrArg (fun y => (Ringed.moduleSheafTensorIsoTensor F' G').inv.val.app (op U)
    ((MonoidalCategory.tensorIso φ φ').hom.val.app (op U) y))
    (Ringed.moduleSheafTensorIsoTensor_hom_bilinear F G f g)).trans ?_
  refine (congrArg (fun y => (Ringed.moduleSheafTensorIsoTensor F' G').inv.val.app (op U) y)
    (Ringed.tensorHom_tmulSection φ.hom φ'.hom f g)).trans ?_
  exact ProjTwist.moduleSheafTensorIsoTensor_inv_tmulSection _ _ _ _

/-- `f^*(M ⊗ N) ≅ f^* M ⊗ f^* N` identifies `f^*(a ⊗ b)` with `f^* a ⊗ f^* b`. -/
theorem pullbackTensorIso_inv_bilinear {Y : Scheme.{u}} (f : Z ⟶ Y) {M N : Y.Modules}
    (hM : Ringed.IsInvertible (R := Y.sheaf) M) (hN : Ringed.IsInvertible (R := Y.sheaf) N)
    (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) :
    (pullbackTensorIso f hM hN).inv.app ⊤
        ((moduleSheafTensorBilinear _ _).app (op ⊤) (pullbackGlobalSection f a)
          (pullbackGlobalSection f b)) =
      pullbackGlobalSection (N := moduleSheafTensor M N) f
        ((moduleSheafTensorBilinear M N).app (op ⊤) a b) := by
  have key : (pullbackTensorIso f hM hN).hom.app ⊤
      (pullbackGlobalSection (N := moduleSheafTensor M N) f
        ((moduleSheafTensorBilinear M N).app (op ⊤) a b)) =
      (moduleSheafTensorBilinear _ _).app (op ⊤) (pullbackGlobalSection f a)
        (pullbackGlobalSection f b) := by
    rw [pullbackGlobalSection, hom_app_map]
    erw [pullbackTensorMap_app_unit]
    exact (moduleSheafTensorBilinear _ _).naturality _ _ _
  rw [← key, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
  rfl

/-- The global section of `L` corresponding to `u / 1`, for `u ∈ S₁`. -/
def degreeOneLineSection (u : 𝒜 1) : Γ(L, ⊤) :=
  α.inv.app ⊤ (pullbackGlobalSection (N := projTwistingSheaf 𝒜 1) ψ (twistSection 1 u (op ⊤)))

theorem prod_mem_degree {n : ℕ} (u : Fin n → 𝒜 1) : (∏ k, (u k : A)) ∈ 𝒜 n := by
  simpa using SetLike.prod_mem_graded 𝒜 (fun _ => 1) (fun k => (u k : A)) (F := Finset.univ)
    (fun k _ => (u k).2)

private theorem iso_hom_inv_app {M N : Z.Modules} (e : M ≅ N) {U : Z.Opens} (y : Γ(N, U)) :
    e.hom.app U (e.inv.app U y) = y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
  rfl

private theorem iso_inv_hom_app {M N : Z.Modules} (e : M ≅ N) {U : Z.Opens} (y : Γ(M, U)) :
    e.inv.app U (e.hom.app U y) = y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
  rfl

/-- **Elementary tensors of degree-one sections** (Proposition 5.12(b), on sections). For
`L ≅ ψ^* 𝒪(1)` and `u₁, …, u_{N+1} ∈ S₁`, the isomorphism `L^{N+1} ≅ ψ^* 𝒪(N + 1)` sends
`ψ^*(u₁ / 1) ⊗ ⋯ ⊗ ψ^*(u_{N+1} / 1)` to `ψ^*(u₁ ⋯ u_{N+1} / 1)`. -/
theorem tensorPowerPullbackTwistIso_hom_tprod : ∀ (N : ℕ) (u : Fin (N + 1) → 𝒜 1),
    Scheme.Modules.Hom.app (X := Z) (tensorPowerPullbackTwistIso hgen ψ α N).hom ⊤
        ((moduleSheafTensorPowerMultilinear (N + 1) L).app (op ⊤)
          fun k => degreeOneLineSection ψ α (u k)) =
      pullbackGlobalSection (N := projTwistingSheaf 𝒜 ((N + 1 : ℕ) : ℤ)) ψ
        (twistSection (N + 1) ⟨∏ k, (u k : A), prod_mem_degree u⟩ (op ⊤))
  | 0, u => by
    have e : tensorPowerPullbackTwistIso hgen ψ α 0 =
        Ringed.moduleSheafTensorPowerSuccIso _ 0 ≪≫
          (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫
            MonoidalCategory.tensorIso (Ringed.moduleSheafTensorPowerZeroIso _) (Iso.refl _) ≪≫
            (Ringed.moduleSheafTensorIsoTensor _ _).symm) ≪≫
          Ringed.moduleSheafUnitTensor _ ≪≫ α := rfl
    rw [e]
    have s1 := Ringed.moduleSheafTensorPowerSuccIso_hom_tprod (F := L) 0 ⊤
      (fun k => degreeOneLineSection ψ α (u k))
    have s2 := tensorIsoOfIso_hom_bilinear (Ringed.moduleSheafTensorPowerZeroIso L) (Iso.refl L)
      ((moduleSheafTensorPowerMultilinear 0 L).app (op ⊤)
        (Fin.init fun k => degreeOneLineSection ψ α (u k)))
      (degreeOneLineSection ψ α (u (Fin.last 0)))
    have s3 := Ringed.moduleSheafTensorPowerHomEquiv_symm_tprod
      (Ringed.tensorPowerZeroMultilinear L) ⊤ (Fin.init fun k => degreeOneLineSection ψ α (u k))
    have s4 := Ringed.moduleSheafTensorHomEquiv_symm_tmul (Ringed.unitSMulBilinear L)
      (U := ⊤) (show (Ringed.structureModule Z.sheaf).val.obj (op ⊤) from
        (1 : (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤)))
      (degreeOneLineSection ψ α (u (Fin.last 0)))
    refine (congrArg (fun y => α.hom.app ⊤ (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafUnitTensor L).hom ⊤
      (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫
        MonoidalCategory.tensorIso (Ringed.moduleSheafTensorPowerZeroIso _) (Iso.refl _) ≪≫
        (Ringed.moduleSheafTensorIsoTensor _ _).symm).hom ⊤ y))) s1).trans ?_
    refine (congrArg (fun y => α.hom.app ⊤ (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafUnitTensor L).hom ⊤ y))
      s2).trans ?_
    refine (congrArg (fun y => α.hom.app ⊤ (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafUnitTensor L).hom ⊤
      ((moduleSheafTensorBilinear _ _).app (op ⊤) y
        (degreeOneLineSection ψ α (u (Fin.last 0)))))) s3).trans ?_
    refine (congrArg (fun y => α.hom.app ⊤ y) (s4.trans
      (one_smul ((Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤)) _))).trans ?_
    refine (iso_hom_inv_app α _).trans ?_
    congr 2
    exact Subtype.ext (Fin.prod_univ_one (fun k => (u k : A))).symm
  | N + 1, u => by
    have hL := (Scheme.Modules.isInvertible_iff_ringed _).1
      (ProjTwistingSheaf.isInvertible hgen ((N + 1 : ℕ) : ℤ))
    have hO := (Scheme.Modules.isInvertible_iff_ringed _).1 (ProjTwistingSheaf.isInvertible hgen 1)
    have hdeg : projTwistingSheaf 𝒜 (((N + 1 : ℕ) : ℤ) + 1) =
        projTwistingSheaf 𝒜 ((N + 1 + 1 : ℕ) : ℤ) :=
      congrArg (projTwistingSheaf 𝒜) (by push_cast; ring)
    have e : tensorPowerPullbackTwistIso hgen ψ α (N + 1) =
        Ringed.moduleSheafTensorPowerSuccIso _ (N + 1) ≪≫
          (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫
            MonoidalCategory.tensorIso (tensorPowerPullbackTwistIso hgen ψ α N) α ≪≫
            (Ringed.moduleSheafTensorIsoTensor _ _).symm) ≪≫
          (pullbackTensorIso ψ hL hO).symm ≪≫
          (Scheme.Modules.pullback ψ).mapIso
            (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫ twistMulIso 𝒜 hgen _ 1 ≪≫ eqToIso hdeg) :=
      rfl
    rw [e]
    have s1 := Ringed.moduleSheafTensorPowerSuccIso_hom_tprod (F := L) (N + 1) ⊤
      (fun k => degreeOneLineSection ψ α (u k))
    have s2 := tensorIsoOfIso_hom_bilinear (tensorPowerPullbackTwistIso hgen ψ α N) α
      ((moduleSheafTensorPowerMultilinear (N + 1) L).app (op ⊤)
        (Fin.init fun k => degreeOneLineSection ψ α (u k)))
      (degreeOneLineSection ψ α (u (Fin.last (N + 1))))
    have s3 := tensorPowerPullbackTwistIso_hom_tprod N (Fin.init u)
    have s4 := iso_hom_inv_app α
      (pullbackGlobalSection (N := projTwistingSheaf 𝒜 1) ψ
        (twistSection 1 (u (Fin.last (N + 1))) (op ⊤)))
    refine (congrArg (fun y => Scheme.Modules.Hom.app (X := Z)
      ((Scheme.Modules.pullback ψ).mapIso
        (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫ twistMulIso 𝒜 hgen _ 1 ≪≫ eqToIso hdeg)).hom ⊤
      (Scheme.Modules.Hom.app (X := Z) (pullbackTensorIso ψ hL hO).symm.hom ⊤
        (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫
            MonoidalCategory.tensorIso (tensorPowerPullbackTwistIso hgen ψ α N) α ≪≫
            (Ringed.moduleSheafTensorIsoTensor _ _).symm).hom ⊤ y))) s1).trans ?_
    refine (congrArg (fun y => Scheme.Modules.Hom.app (X := Z)
      ((Scheme.Modules.pullback ψ).mapIso
        (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫ twistMulIso 𝒜 hgen _ 1 ≪≫ eqToIso hdeg)).hom ⊤
      (Scheme.Modules.Hom.app (X := Z) (pullbackTensorIso ψ hL hO).symm.hom ⊤ y)) s2).trans ?_
    refine (congrArg (fun y => Scheme.Modules.Hom.app (X := Z)
      ((Scheme.Modules.pullback ψ).mapIso
        (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫ twistMulIso 𝒜 hgen _ 1 ≪≫ eqToIso hdeg)).hom ⊤
      (Scheme.Modules.Hom.app (X := Z) (pullbackTensorIso ψ hL hO).symm.hom ⊤
        ((moduleSheafTensorBilinear _ _).app (op ⊤) y
          (α.hom.app ⊤ (degreeOneLineSection ψ α (u (Fin.last (N + 1))))))))
      s3).trans ?_
    refine (congrArg (fun y => Scheme.Modules.Hom.app (X := Z)
      ((Scheme.Modules.pullback ψ).mapIso
        (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫ twistMulIso 𝒜 hgen _ 1 ≪≫ eqToIso hdeg)).hom ⊤
      (Scheme.Modules.Hom.app (X := Z) (pullbackTensorIso ψ hL hO).symm.hom ⊤
        ((moduleSheafTensorBilinear _ _).app (op ⊤) _ y))) s4).trans ?_
    refine (congrArg (fun y => Scheme.Modules.Hom.app (X := Z)
      ((Scheme.Modules.pullback ψ).mapIso
        (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫ twistMulIso 𝒜 hgen _ 1 ≪≫ eqToIso hdeg)).hom ⊤
      y) (pullbackTensorIso_inv_bilinear ψ hL hO _ _)).trans ?_
    refine (pullback_map_pullbackGlobalSection ψ _ _).trans ?_
    congr 1
    refine (congrArg (fun y => Scheme.Modules.Hom.app (X := Proj 𝒜) (eqToHom hdeg) ⊤
      ((twistMulHom 𝒜 ((N + 1 : ℕ) : ℤ) 1).val.app (op ⊤) y))
      (Ringed.moduleSheafTensorIsoTensor_hom_bilinear _ _ _ _)).trans ?_
    refine (congrArg (fun y => Scheme.Modules.Hom.app (X := Proj 𝒜) (eqToHom hdeg) ⊤ y)
      (GammaStarReconstruction.twistMulHom_twistSection (N + 1) 1 _ (u (Fin.last (N + 1))) (op ⊤))).trans ?_
    refine congrArg (fun x => twistSection (N + 1 + 1) x (op ⊤)) (Subtype.ext ?_)
    exact (Fin.prod_univ_castSucc (fun k => (u k : A))).symm

end TensorPowerTwist

/-! ### Products of pulled-back monomials -/

section Monomials

attribute [local instance] MvPolynomial.gradedAlgebra

variable {r : ℕ} {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X)

/-- The global section `f^*(u / 1)` of `L = i^* 𝒪(1)` for `u ∈ ℤ[x₀, …, xᵣ]₁`. -/
abbrev lineSection (u : GeneratedProj.intGrading.{u} r 1) :
    Γ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf r X 1), ⊤) :=
  degreeOneLineSection (𝒜 := GeneratedProj.intGrading.{u} r) (toIntProj i)
    ((Scheme.Modules.pullbackComp _ _).app _) u

/-- `L^{N+1} ≅ 𝒪(N + 1)|_Z` sends `f^*(u₁ / 1) ⊗ ⋯ ⊗ f^*(u_{N+1} / 1)` to `f^*(u₁ ⋯ u_{N+1} / 1)`. -/
theorem tensorPowerTwistOnZIso_hom_tprod (N : ℕ) (hN : 0 < N + 1)
    (u : Fin (N + 1) → GeneratedProj.intGrading.{u} r 1) :
    (tensorPowerTwistOnZIso i (N + 1) hN).hom.app ⊤
        ((moduleSheafTensorPowerMultilinear (N + 1) _).app (op ⊤) fun k => lineSection i (u k)) =
      pullbackGlobalSection
        (N := projTwistingSheaf (GeneratedProj.intGrading.{u} r) ((N + 1 : ℕ) : ℤ)) (toIntProj i)
        (twistSection (N + 1) ⟨∏ k, (u k : MvPolynomial (Fin (r + 1)) (ULift.{u} ℤ)),
          prod_mem_degree u⟩ (op ⊤)) := by
  rw [← tensorPowerPullbackTwistIso_hom_tprod (adjoin_intGrading_one_eq_top r) (toIntProj i)
    ((Scheme.Modules.pullbackComp _ _).app _) N u]
  have key := iso_hom_inv_app ((Scheme.Modules.pullbackComp i
    (pullback.fst (projectiveSpaceOverIntegersMap r) (schemeToSpecZ X))).app
      (projTwistingSheaf (GeneratedProj.intGrading.{u} r) ((N + 1 : ℕ) : ℤ)))
    (Scheme.Modules.Hom.app (X := Z) (tensorPowerPullbackTwistIso (adjoin_intGrading_one_eq_top r)
      (toIntProj i) ((Scheme.Modules.pullbackComp _ _).app _) N).hom ⊤
      ((moduleSheafTensorPowerMultilinear (N + 1) _).app (op ⊤) fun k => lineSection i (u k)))
  exact key

/-- A monomial of degree `n` is a product of `n` elements of degree one. -/
theorem exists_prod_eq_monomial : ∀ (n : ℕ) (β : Fin (r + 1) →₀ ℕ), β.degree = n →
    ∃ u : Fin n → GeneratedProj.intGrading.{u} r 1,
      ∏ k, (u k : MvPolynomial (Fin (r + 1)) (ULift.{u} ℤ)) = MvPolynomial.monomial β 1
  | 0, β, h => ⟨Fin.elim0, by simp [(Finsupp.degree_eq_zero_iff β).mp h]⟩
  | n + 1, β, h => by
    obtain ⟨j, hj⟩ : ∃ j, β j ≠ 0 := by
      by_contra hc
      push Not at hc
      have : β = 0 := Finsupp.ext hc
      simp [this] at h
    have hle : Finsupp.single j 1 ≤ β := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj)
    have hdeg : (β - Finsupp.single j 1).degree = n := by
      have := map_add Finsupp.degree (β - Finsupp.single j 1) (Finsupp.single j 1)
      rw [tsub_add_cancel_of_le hle, h, Finsupp.degree_single] at this
      omega
    obtain ⟨u, hu⟩ := exists_prod_eq_monomial n _ hdeg
    refine ⟨Fin.snoc u ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X _ j⟩, ?_⟩
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hu, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, tsub_add_cancel_of_le hle]

/-- `L^{n} ≅ 𝒪(n)|_Z` sends `f^*(u₁ / 1) ⊗ ⋯ ⊗ f^*(uₙ / 1)` to the pulled-back monomial
`x^β = u₁ ⋯ uₙ`. -/
theorem tensorPowerTwistOnZIso_hom_tprod_eq_monomialSection {n : ℕ} (hn : 0 < n)
    {β : Fin (r + 1) →₀ ℕ} (hβ : β.degree = n) (u : Fin n → GeneratedProj.intGrading.{u} r 1)
    (hu : ∏ k, (u k : MvPolynomial (Fin (r + 1)) (ULift.{u} ℤ)) = MvPolynomial.monomial β 1) :
    (tensorPowerTwistOnZIso i n hn).hom.app ⊤
        ((moduleSheafTensorPowerMultilinear n _).app (op ⊤) fun k => lineSection i (u k)) =
      monomialSection i n β := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [tensorPowerTwistOnZIso_hom_tprod, monomialSection, dif_pos hβ]
  congr 2
  exact Subtype.ext hu

/-- The product of sections of tensor powers of `L = i^* 𝒪(1)`,
`Γ(W, L^{p}) × Γ(W, L^{q}) → Γ(W, L^{p+q})`, induced by `L^{p} ⊗ L^{q} ≅ L^{p+q}`. -/
noncomputable def tensorPowerMulSection {p q : ℕ} {W : Z.Opens} (s : Γ(tensorPowerL i p, W))
    (t : Γ(tensorPowerL i q, W)) : Γ(tensorPowerL i (p + q), W) :=
  Ringed.moduleSheafTensorPowerMulSection (R := Z.sheaf) s t

/-- **Products of pulled-back monomials.** Under `L^{n} ≅ 𝒪(n)|_Z`, the product
`L^{p} × L^{q} → L^{p+q}` sends the pulled-back monomials `x^β` and `x^γ` to `x^{β+γ}`. -/
theorem tensorPowerMulSection_monomialSection {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {β γ : Fin (r + 1) →₀ ℕ} (hβ : β.degree = p) (hγ : γ.degree = q) :
    tensorPowerMulSection i ((tensorPowerTwistOnZIso i p hp).inv.app ⊤ (monomialSection i p β))
        ((tensorPowerTwistOnZIso i q hq).inv.app ⊤ (monomialSection i q γ)) =
      (tensorPowerTwistOnZIso i (p + q) (by omega)).inv.app ⊤
        (monomialSection i (p + q) (β + γ)) := by
  obtain ⟨u, hu⟩ := exists_prod_eq_monomial p β hβ
  obtain ⟨v, hv⟩ := exists_prod_eq_monomial q γ hγ
  have e3 := tensorPowerTwistOnZIso_hom_tprod_eq_monomialSection i (n := p + q) (by omega)
    (show (β + γ).degree = p + q by rw [map_add, hβ, hγ]) (Fin.append u v) (by
      rw [Fin.prod_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hu, hv, MvPolynomial.monomial_mul, one_mul])
  rw [← tensorPowerTwistOnZIso_hom_tprod_eq_monomialSection i hp hβ u hu,
    ← tensorPowerTwistOnZIso_hom_tprod_eq_monomialSection i hq hγ v hv, ← e3,
    iso_inv_hom_app, iso_inv_hom_app, iso_inv_hom_app, tensorPowerMulSection,
    Ringed.moduleSheafTensorPowerMulSection_tprod]
  congr 1
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

end Monomials

end SectionAlgebraModel

end Hartshorne
