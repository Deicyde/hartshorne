/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SectionAlgebraSheafComparison

/-!
# Multiplicativity of the section-algebra model

Hartshorne, *Algebraic Geometry*, II, proof of Theorem 7.17, Steps 1–3 (pp. 166–167).

Let `i : Z ⟶ ℙʳ_X` be a closed immersion of an integral scheme, `f = π ∘ i`, `L = i^* 𝒪(1)` and
`T(U) = Γ(X, U)[x₀, …, xᵣ] / I_U` the relative homogeneous coordinate algebra. The comparison
`T(U)_n ≅ Γ(f⁻¹(U), L^{n})` of `SectionAlgebraSheafComparison` turns the multiplication of `T(U)`
into the product `L^{p} ⊗ L^{q} → L^{p+q}`; this file proves this, together with the algebra of
these products (bilinearity, compatibility with restriction).

* `Ringed.moduleSheafTensorPowerAddIso_hom_tprod_append`: `T^{a+b} F ≅ T^a F ⊗ T^b F` on
  elementary tensors; `Ringed.moduleSheafTensorPowerMulSection`, the induced product of sections.
* `SectionAlgebraModel.tensorPowerPullbackTwistIso_hom_tprod`: for `L ≅ ψ^* 𝒪(1)` on `Proj S`,
  `L^{N+1} ≅ ψ^* 𝒪(N + 1)` sends `ψ^*(u₁ / 1) ⊗ ⋯ ⊗ ψ^*(u_{N+1} / 1)` to `ψ^*(u₁ ⋯ u_{N+1} / 1)`
  (Proposition 5.12(b) on sections).
* `SectionAlgebraModel.tensorPowerMulSection_monomialSection`: the pulled-back monomials multiply,
  `x^β · x^γ = x^{β+γ}`; `tensorPowerMulSection_polyTwistSection_monomial`: so do the comparison
  sections `f^*(a) x^α` over `f⁻¹(U)`, and `tensorPowerMulSection_polyTwistSection`: so do those
  of arbitrary polynomials.
* `SectionAlgebraModel.tensorPowerMulSection_coordTwistSection`,
  `SectionAlgebraModel.veroneseTwistSection_mul`: the comparisons `T(U)_n ≅ Γ(f⁻¹(U), L^{n})` and
  `T(U)^{(d)}_m ≅ Γ(f⁻¹(U), L^{md})` are multiplicative.
* `SectionAlgebraModel.exists_sectionAlgebraModel_multiplicative`: the section-algebra model of
  Theorem 7.17, Steps 1–3, with comparison isomorphisms that are natural, linear and
  multiplicative.

The route to multiplicativity (reduction to pulled-back monomials on `Z`) is this formalization's
own and is not taken from Hartshorne.
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

/-- The associator `(A ⊗ B) ⊗ C ≅ A ⊗ (B ⊗ C)` on elementary tensors, for arbitrary modules (checked
once here; unfolding the associator inside the proof below made the kernel compare the two
presentations of its forward map for every use, about ten seconds). -/
private theorem moduleSheafTensorAssoc_hom_tmul (A B C : SheafOfModules.{u} (ringCatSheafOf R))
    {U : Opens X} (a : A.val.obj (op U)) (b : B.val.obj (op U)) (c : C.val.obj (op U)) :
    sectionsMap (moduleSheafTensorAssoc A B C).hom U
        ((moduleSheafTensorBilinear (moduleSheafTensor A B) C).app (op U)
          ((moduleSheafTensorBilinear A B).app (op U) a b) c) =
      (moduleSheafTensorBilinear A (moduleSheafTensor B C)).app (op U) a
        ((moduleSheafTensorBilinear B C).app (op U) b c) :=
  (assocTrilinear A B C).tensorDesc_tmul a b c

/-- The case `b = 0` of `moduleSheafTensorPowerAddIso_hom_tprod_append`. -/
private theorem tensorPowerAddIso_hom_tprod_append_zero (a : ℕ) (U : Opens X)
    (m : Fin a → F.val.obj (op U)) (m' : Fin 0 → F.val.obj (op U)) :
    sectionsMap (moduleSheafTensorPowerAddIso F a 0).hom U
        ((moduleSheafTensorPowerMultilinear (a + 0) F).app (op U) (Fin.append m m')) =
      (moduleSheafTensorBilinear (moduleSheafTensorPower a F) (moduleSheafTensorPower 0 F)).app
        (op U) ((moduleSheafTensorPowerMultilinear a F).app (op U) m)
        ((moduleSheafTensorPowerMultilinear 0 F).app (op U) m') := by
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

/-- The inductive step of `moduleSheafTensorPowerAddIso_hom_tprod_append`. It is stated separately
and used through `induction` rather than structural recursion: checking the structurally recursive
proof made the kernel compare the recursive call with the unfolded recursor (about a minute). -/
private theorem tensorPowerAddIso_hom_tprod_append_succ (a b : ℕ)
    (ih : ∀ (U : Opens X) (m : Fin a → F.val.obj (op U)) (m' : Fin b → F.val.obj (op U)),
      sectionsMap (moduleSheafTensorPowerAddIso F a b).hom U
          ((moduleSheafTensorPowerMultilinear (a + b) F).app (op U) (Fin.append m m')) =
        (moduleSheafTensorBilinear (moduleSheafTensorPower a F) (moduleSheafTensorPower b F)).app
          (op U) ((moduleSheafTensorPowerMultilinear a F).app (op U) m)
          ((moduleSheafTensorPowerMultilinear b F).app (op U) m'))
    (U : Opens X) (m : Fin a → F.val.obj (op U)) (m' : Fin (b + 1) → F.val.obj (op U)) :
    sectionsMap (moduleSheafTensorPowerAddIso F a (b + 1)).hom U
        ((moduleSheafTensorPowerMultilinear (a + (b + 1)) F).app (op U) (Fin.append m m')) =
      (moduleSheafTensorBilinear (moduleSheafTensorPower a F)
          (moduleSheafTensorPower (b + 1) F)).app (op U)
        ((moduleSheafTensorPowerMultilinear a F).app (op U) m)
        ((moduleSheafTensorPowerMultilinear (b + 1) F).app (op U) m') := by
  obtain ⟨m'', x, rfl⟩ : ∃ m'' x, m' = Fin.snoc m'' x :=
    ⟨Fin.init m', m' (Fin.last b), (Fin.snoc_init_self m').symm⟩
  have e : (moduleSheafTensorPowerAddIso F a (b + 1)).hom =
    (moduleSheafTensorPowerSuccIso F (a + b)).hom ≫
      modulesTensorMap (moduleSheafTensorPowerAddIso F a b).hom (𝟙 F) ≫
      (moduleSheafTensorAssoc _ _ _).hom ≫
      modulesTensorMap (𝟙 _) (moduleSheafTensorPowerSuccIso F b).inv := by
    rw [moduleSheafTensorPowerAddIso.eq_2]
    rfl
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
  rw [modulesTensorMap_tmul, ih U m m'', moduleSheafTensorAssoc_hom_tmul]
  have h5 : ∀ (A : SheafOfModules.{u} (ringCatSheafOf R)) (l : A.val.obj (op U)),
      sectionsMap (𝟙 A) U l = l := fun _ _ => rfl
  rw [modulesTensorMap_tmul, h5, h5, moduleSheafTensorPowerSuccIso_inv_tmul]

/-- `T^{a+b} F ≅ T^a F ⊗ T^b F` sends `f₁ ⊗ ⋯ ⊗ f_{a+b}` to
`(f₁ ⊗ ⋯ ⊗ f_a) ⊗ (f_{a+1} ⊗ ⋯ ⊗ f_{a+b})`. -/
theorem moduleSheafTensorPowerAddIso_hom_tprod_append (a : ℕ) : ∀ (b : ℕ) (U : Opens X)
    (m : Fin a → F.val.obj (op U)) (m' : Fin b → F.val.obj (op U)),
    sectionsMap (moduleSheafTensorPowerAddIso F a b).hom U
        ((moduleSheafTensorPowerMultilinear (a + b) F).app (op U) (Fin.append m m')) =
      (moduleSheafTensorBilinear (moduleSheafTensorPower a F) (moduleSheafTensorPower b F)).app
        (op U) ((moduleSheafTensorPowerMultilinear a F).app (op U) m)
        ((moduleSheafTensorPowerMultilinear b F).app (op U) m') := by
  intro b
  induction b with
  | zero => exact tensorPowerAddIso_hom_tprod_append_zero a
  | succ b ih => exact tensorPowerAddIso_hom_tprod_append_succ a b ih

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
    refine (congrArg (fun y => α.hom.app ⊤
      (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafUnitTensor L).hom ⊤
      (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafTensorIsoTensor _ _ ≪≫
        MonoidalCategory.tensorIso (Ringed.moduleSheafTensorPowerZeroIso _) (Iso.refl _) ≪≫
        (Ringed.moduleSheafTensorIsoTensor _ _).symm).hom ⊤ y))) s1).trans ?_
    refine (congrArg (fun y => α.hom.app ⊤
      (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafUnitTensor L).hom ⊤ y))
      s2).trans ?_
    refine (congrArg (fun y => α.hom.app ⊤
      (Scheme.Modules.Hom.app (X := Z) (Ringed.moduleSheafUnitTensor L).hom ⊤
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
      (GammaStarReconstruction.twistMulHom_twistSection (N + 1) 1 _ (u (Fin.last (N + 1)))
        (op ⊤))).trans ?_
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

/-- `L^{N+1} ≅ 𝒪(N + 1)|_Z` sends `f^*(u₁ / 1) ⊗ ⋯ ⊗ f^*(u_{N+1} / 1)` to
`f^*(u₁ ⋯ u_{N+1} / 1)`. -/
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

/-- `0 < p + q` whenever `0 < p`. -/
theorem pos_add_of_pos {p : ℕ} (hp : 0 < p) (q : ℕ) : 0 < p + q := by omega

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
      (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app ⊤
        (monomialSection i (p + q) (β + γ)) := by
  obtain ⟨u, hu⟩ := exists_prod_eq_monomial p β hβ
  obtain ⟨v, hv⟩ := exists_prod_eq_monomial q γ hγ
  have e3 := tensorPowerTwistOnZIso_hom_tprod_eq_monomialSection i (pos_add_of_pos hp q)
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

/-! ### Multiplicativity of the comparison -/

section Local

attribute [local instance] MvPolynomial.gradedAlgebra

variable {r : ℕ} {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X)

theorem tensorPowerMulSection_restrict {p q : ℕ} {W W' : Z.Opens} (h : W' ≤ W)
    (s : Γ(tensorPowerL i p, W)) (t : Γ(tensorPowerL i q, W)) :
    (tensorPowerL i (p + q)).presheaf.map (homOfLE h).op (tensorPowerMulSection i s t) =
      tensorPowerMulSection i ((tensorPowerL i p).presheaf.map (homOfLE h).op s)
        ((tensorPowerL i q).presheaf.map (homOfLE h).op t) :=
  Ringed.moduleSheafTensorPowerMulSection_restrict h s t

theorem tensorPowerMulSection_smul_smul {p q : ℕ} {W : Z.Opens} (c c' : Γ(Z, W))
    (s : Γ(tensorPowerL i p, W)) (t : Γ(tensorPowerL i q, W)) :
    tensorPowerMulSection i (c • s) (c' • t) = (c * c') • tensorPowerMulSection i s t :=
  (Ringed.moduleSheafTensorPowerMulSection_smul_left (R := Z.sheaf)
    (show (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op W) from c) s (c' • t)).trans
    ((congrArg (c • ·) (Ringed.moduleSheafTensorPowerMulSection_smul_right (R := Z.sheaf)
      (show (Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op W) from c') s t)).trans
      (smul_smul c c' _))

theorem tensorPowerMulSection_add_left {p q : ℕ} {W : Z.Opens} (s s' : Γ(tensorPowerL i p, W))
    (t : Γ(tensorPowerL i q, W)) :
    tensorPowerMulSection i (s + s') t =
      tensorPowerMulSection i s t + tensorPowerMulSection i s' t :=
  Ringed.moduleSheafTensorPowerMulSection_add_left s s' t

theorem tensorPowerMulSection_add_right {p q : ℕ} {W : Z.Opens} (s : Γ(tensorPowerL i p, W))
    (t t' : Γ(tensorPowerL i q, W)) :
    tensorPowerMulSection i s (t + t') =
      tensorPowerMulSection i s t + tensorPowerMulSection i s t' :=
  Ringed.moduleSheafTensorPowerMulSection_add_right s t t'

theorem tensorPowerMulSection_zero_left {p q : ℕ} {W : Z.Opens} (t : Γ(tensorPowerL i q, W)) :
    tensorPowerMulSection i (0 : Γ(tensorPowerL i p, W)) t = 0 :=
  Ringed.moduleSheafTensorPowerMulSection_zero_left t

theorem tensorPowerMulSection_zero_right {p q : ℕ} {W : Z.Opens} (s : Γ(tensorPowerL i p, W)) :
    tensorPowerMulSection i s (0 : Γ(tensorPowerL i q, W)) = 0 :=
  Ringed.moduleSheafTensorPowerMulSection_zero_right s

theorem polyTwistSection_monomial_eq_zero (U : X.Opens) {n : ℕ} {α : Fin (r + 1) →₀ ℕ}
    (hα : ¬ α.degree = n) (a : Γ(X, U)) :
    polyTwistSection i U n (MvPolynomial.monomial α a) = 0 := by
  rw [polyTwistSection_monomial, monomialSection, dif_neg hα, map_zero, smul_zero]

/-- An isomorphism of `𝒪_Z`-modules is `Γ(Z, W)`-linear and commutes with restriction from `Z`.
(Stated for arbitrary modules so that instances are checked once.) -/
theorem iso_inv_app_smul_map {M N : Z.Modules} (e : M ≅ N) {W : Z.Opens} (c : Γ(Z, W))
    (x : Γ(N, ⊤)) :
    e.inv.app W (c • N.presheaf.map (homOfLE le_top).op x) =
      c • M.presheaf.map (homOfLE le_top).op (e.inv.app ⊤ x) := by
  rw [Scheme.Modules.Hom.app_smul, hom_app_map]

/-- An isomorphism of `𝒪_Z`-modules is additive on sections. -/
theorem iso_inv_app_add {M N : Z.Modules} (e : M ≅ N) {W : Z.Opens} (x y : Γ(N, W)) :
    e.inv.app W (x + y) = e.inv.app W x + e.inv.app W y :=
  map_add _ x y

/-- An isomorphism of `𝒪_Z`-modules sends `0` to `0`. -/
theorem iso_inv_app_zero {M N : Z.Modules} (e : M ≅ N) {W : Z.Opens} :
    e.inv.app W (0 : Γ(N, W)) = 0 :=
  map_zero _

/-- `L^{p} ≅ 𝒪(p)|_Z` on a monomial section: `f^*(a) x^α ↦ f^*(a) · (x^α)|`. -/
theorem invApp_polyTwistSection_monomial (U : X.Opens) {p : ℕ} (hp : 0 < p)
    (α : Fin (r + 1) →₀ ℕ) (a : Γ(X, U)) :
    (tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p (MvPolynomial.monomial α a)) =
      (i ≫ projectiveSpaceOverSchemeProjection r X).app U a •
        (tensorPowerL i p).presheaf.map (homOfLE le_top).op
          ((tensorPowerTwistOnZIso i p hp).inv.app ⊤ (monomialSection i p α)) := by
  rw [polyTwistSection_monomial]
  exact iso_inv_app_smul_map _ _ _

/-- The comparison sections of two monomials multiply to that of their product. -/
theorem tensorPowerMulSection_polyTwistSection_monomial (U : X.Opens) {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) {α β : Fin (r + 1) →₀ ℕ} (hα : α.degree = p) (hβ : β.degree = q)
    (a b : Γ(X, U)) :
    tensorPowerMulSection i ((tensorPowerTwistOnZIso i p hp).inv.app _
        (polyTwistSection i U p (MvPolynomial.monomial α a)))
        ((tensorPowerTwistOnZIso i q hq).inv.app _
          (polyTwistSection i U q (MvPolynomial.monomial β b))) =
      (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q) (MvPolynomial.monomial (α + β) (a * b))) := by
  rw [invApp_polyTwistSection_monomial, invApp_polyTwistSection_monomial,
    invApp_polyTwistSection_monomial, tensorPowerMulSection_smul_smul,
    ← tensorPowerMulSection_restrict, tensorPowerMulSection_monomialSection i hp hq hα hβ,
    map_mul]

/-- An isomorphism of `𝒪_Z`-modules composed with an additive map is additive. -/
theorem iso_inv_app_comp_add {M N : Z.Modules} (e : M ≅ N) {W : Z.Opens} {A : Type*} [Add A]
    (f : A → Γ(N, W)) (hf : ∀ a b, f (a + b) = f a + f b) (a b : A) :
    e.inv.app W (f (a + b)) = e.inv.app W (f a) + e.inv.app W (f b) := by
  rw [hf, map_add]

/-- An isomorphism of `𝒪_Z`-modules composed with a map sending `0` to `0` sends `0` to `0`. -/
theorem iso_inv_app_comp_zero {M N : Z.Modules} (e : M ≅ N) {W : Z.Opens} {A : Type*} [Zero A]
    (f : A → Γ(N, W)) (hf : f 0 = 0) :
    e.inv.app W (f 0) = 0 := by
  rw [hf, map_zero]

/-- The product of the homogeneous components of degrees `p` and `q` of two monomials. -/
theorem homogeneousComponent_monomial_mul {σ R : Type*} [CommSemiring R] {p q : ℕ}
    (α β : σ →₀ ℕ) (a b : R) :
    MvPolynomial.homogeneousComponent p (MvPolynomial.monomial α a) *
        MvPolynomial.homogeneousComponent q (MvPolynomial.monomial β b) =
      if α.degree = p ∧ β.degree = q then MvPolynomial.monomial (α + β) (a * b) else 0 := by
  rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial a rfl),
    MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial b rfl)]
  by_cases hα : α.degree = p
  · subst hα
    by_cases hβ : β.degree = q
    · subst hβ
      simp [MvPolynomial.monomial_mul]
    · simp [hβ, Ne.symm hβ]
  · simp [hα, Ne.symm hα]

/-- `L^{n} ≅ 𝒪(n)|_Z` on the comparison section of a monomial of the wrong degree. -/
theorem invApp_polyTwistSection_monomial_eq_zero (U : X.Opens) {n : ℕ} (hn : 0 < n)
    {α : Fin (r + 1) →₀ ℕ} (hα : ¬ α.degree = n) (a : Γ(X, U)) :
    (tensorPowerTwistOnZIso i n hn).inv.app _ (polyTwistSection i U n (MvPolynomial.monomial α a))
      = 0 :=
  (congrArg (fun z => (tensorPowerTwistOnZIso i n hn).inv.app _ z)
    (polyTwistSection_monomial_eq_zero i U hα a)).trans (iso_inv_app_zero _)

section PolyMul

/-! The steps of `tensorPowerMulSection_polyTwistSection`, stated separately (and composed with
explicit `Eq.trans`) so that the kernel compares syntactically equal terms only. -/

variable (U : X.Opens) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)

private theorem polyMul_add_left (x x' y : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p (x + x')))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q y)) =
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p x))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q y)) +
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p x'))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q y)) :=
  Eq.trans (congrArg (fun z => tensorPowerMulSection i z _)
      (iso_inv_app_comp_add _ _ (polyTwistSection_add i U p) x x'))
    (tensorPowerMulSection_add_left i _ _ _)

private theorem polyMul_add_right (x y y' : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p x))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q (y + y'))) =
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p x))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q y)) +
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p x))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q y')) :=
  Eq.trans (congrArg (fun z => tensorPowerMulSection i _ z)
      (iso_inv_app_comp_add _ _ (polyTwistSection_add i U q) y y'))
    (tensorPowerMulSection_add_right i _ _ _)

private theorem polyMulComp_add_left (x x' y : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p (x + x') * MvPolynomial.homogeneousComponent q y)) =
    (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p x * MvPolynomial.homogeneousComponent q y)) +
    (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p x' * MvPolynomial.homogeneousComponent q y)) :=
  Eq.trans (congrArg (fun z => (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
      (polyTwistSection i U (p + q) z)) (by rw [map_add, add_mul]))
    (iso_inv_app_comp_add _ _ (polyTwistSection_add i U (p + q)) _ _)

private theorem polyMulComp_add_right (x y y' : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p x * MvPolynomial.homogeneousComponent q (y + y'))) =
    (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p x * MvPolynomial.homogeneousComponent q y)) +
    (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p x * MvPolynomial.homogeneousComponent q y')) :=
  Eq.trans (congrArg (fun z => (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
      (polyTwistSection i U (p + q) z)) (by rw [map_add, mul_add]))
    (iso_inv_app_comp_add _ _ (polyTwistSection_add i U (p + q)) _ _)

private theorem polyMul_monomial_eq_zero_left {α : Fin (r + 1) →₀ ℕ} (hα : ¬ α.degree = p)
    (a : Γ(X, U)) (β : Fin (r + 1) →₀ ℕ) (b : Γ(X, U)) :
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p
        (MvPolynomial.monomial α a)))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q
        (MvPolynomial.monomial β b))) = 0 :=
  Eq.trans (congrArg (fun z => tensorPowerMulSection i z _)
      (invApp_polyTwistSection_monomial_eq_zero i U hp hα a))
    (tensorPowerMulSection_zero_left i _)

private theorem polyMul_monomial_eq_zero_right (α : Fin (r + 1) →₀ ℕ) (a : Γ(X, U))
    {β : Fin (r + 1) →₀ ℕ} (hβ : ¬ β.degree = q) (b : Γ(X, U)) :
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p
        (MvPolynomial.monomial α a)))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q
        (MvPolynomial.monomial β b))) = 0 :=
  Eq.trans (congrArg (fun z => tensorPowerMulSection i _ z)
      (invApp_polyTwistSection_monomial_eq_zero i U hq hβ b))
    (tensorPowerMulSection_zero_right i _)

private theorem polyMulComp_monomial_eq_zero (α : Fin (r + 1) →₀ ℕ) (a : Γ(X, U))
    (β : Fin (r + 1) →₀ ℕ) (b : Γ(X, U)) (h : ¬ (α.degree = p ∧ β.degree = q)) :
    (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p (MvPolynomial.monomial α a) *
            MvPolynomial.homogeneousComponent q (MvPolynomial.monomial β b))) = 0 :=
  Eq.trans (congrArg (fun z => (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
      (polyTwistSection i U (p + q) z))
      (Eq.trans (homogeneousComponent_monomial_mul α β a b) (if_neg h)))
    (iso_inv_app_comp_zero _ _ (polyTwistSection_zero i U (p + q)))

private theorem polyMul_monomial (α : Fin (r + 1) →₀ ℕ) (a : Γ(X, U)) (β : Fin (r + 1) →₀ ℕ)
    (b : Γ(X, U)) :
    tensorPowerMulSection i
      ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p
        (MvPolynomial.monomial α a)))
      ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q
        (MvPolynomial.monomial β b))) =
    (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p (MvPolynomial.monomial α a) *
            MvPolynomial.homogeneousComponent q (MvPolynomial.monomial β b))) := by
  by_cases hα : α.degree = p
  · by_cases hβ : β.degree = q
    · exact Eq.trans (tensorPowerMulSection_polyTwistSection_monomial i U hp hq hα hβ a b)
        (congrArg (fun z => (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
          (polyTwistSection i U (p + q) z))
          (Eq.symm (Eq.trans (homogeneousComponent_monomial_mul α β a b) (if_pos ⟨hα, hβ⟩))))
    · exact Eq.trans (polyMul_monomial_eq_zero_right i U hp hq α a hβ b)
        (Eq.symm (polyMulComp_monomial_eq_zero i U hp α a β b fun h => hβ h.2))
  · exact Eq.trans (polyMul_monomial_eq_zero_left i U hp hq hα a β b)
      (Eq.symm (polyMulComp_monomial_eq_zero i U hp α a β b fun h => hα h.1))

end PolyMul

/-- The monomial case, for polynomials only known to be equal to monomials (so that the
monomials coming from `MvPolynomial.induction_on'` are compared at the level of polynomials). -/
private theorem polyMul_of_eq_monomial (U : X.Opens) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (α : Fin (r + 1) →₀ ℕ) (a : Γ(X, U)) (β : Fin (r + 1) →₀ ℕ) (b : Γ(X, U))
    (P Q : MvPolynomial (Fin (r + 1)) Γ(X, U)) (hP : P = MvPolynomial.monomial α a)
    (hQ : Q = MvPolynomial.monomial β b) :
    tensorPowerMulSection i ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p P))
        ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q Q)) =
      (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p P * MvPolynomial.homogeneousComponent q Q)) := by
  subst hP hQ
  exact polyMul_monomial i U hp hq α a β b

/-- **Multiplicativity of the comparison over `f⁻¹(U)`.** For polynomials `P`, `Q` over `Γ(X, U)`,
the comparison sections of `P` in degree `p` and of `Q` in degree `q` multiply, under
`L^{p} × L^{q} → L^{p+q}`, to the comparison section of `P_p Q_q` in degree `p + q`. -/
theorem tensorPowerMulSection_polyTwistSection (U : X.Opens) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (P Q : MvPolynomial (Fin (r + 1)) Γ(X, U)) :
    tensorPowerMulSection i ((tensorPowerTwistOnZIso i p hp).inv.app _ (polyTwistSection i U p P))
        ((tensorPowerTwistOnZIso i q hq).inv.app _ (polyTwistSection i U q Q)) =
      (tensorPowerTwistOnZIso i (p + q) (pos_add_of_pos hp q)).inv.app _
        (polyTwistSection i U (p + q)
          (MvPolynomial.homogeneousComponent p P * MvPolynomial.homogeneousComponent q Q)) :=
  MvPolynomial.induction_on' P
    (fun α a => MvPolynomial.induction_on' Q
      (fun β b => polyMul_of_eq_monomial i U hp hq α a β b _ _ rfl rfl)
      (fun y y' hy hy' => Eq.trans (polyMul_add_right i U hp hq _ y y')
        (Eq.trans (congrArg₂ (· + ·) hy hy') (Eq.symm (polyMulComp_add_right i U hp _ y y')))))
    (fun x x' hx hx' => Eq.trans (polyMul_add_left i U hp hq x x' Q)
      (Eq.trans (congrArg₂ (· + ·) hx hx') (Eq.symm (polyMulComp_add_left i U hp x x' Q))))

variable [IsClosedImmersion i] [IsIntegral Z]

omit [IsClosedImmersion i] [IsIntegral Z] in
private theorem eqToHom_app_self {M : Z.Modules} (e : M = M) {W : Z.Opens} (y : Γ(M, W)) :
    Scheme.Modules.Hom.app (eqToHom e) W y = y := by
  rw [eqToHom_refl, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]

/-- Transport of the comparison along an equality of degrees. -/
theorem eqToHom_app_coordTwistSection (U : X.AffineZariskiSite) {n n' : ℕ} (h : n = n')
    (hn : 0 < n) (hn' : 0 < n') (e : tensorPowerL i n = tensorPowerL i n')
    (z : (coordinateAlgebra i).obj.obj (op U)) (hz : z ∈ (coordinateAlgebra i).grading U n)
    (hz' : z ∈ (coordinateAlgebra i).grading U n') :
    Scheme.Modules.Hom.app (eqToHom e) _
        ((tensorPowerTwistOnZIso i n hn).inv.app _ (coordTwistSection i U n ⟨z, hz⟩)) =
      (tensorPowerTwistOnZIso i n' hn').inv.app _ (coordTwistSection i U n' ⟨z, hz'⟩) := by
  subst h
  exact (eqToHom_app_self e _).trans (congrArg₂ (fun (h₁ : 0 < n)
    (h₂ : z ∈ (coordinateAlgebra i).grading U n) =>
      (tensorPowerTwistOnZIso i n h₁).inv.app _ (coordTwistSection i U n ⟨z, h₂⟩))
    (Subsingleton.elim hn hn') (Subsingleton.elim hz hz'))

/-! ### The comparison `T(U)_n ≅ Γ(f⁻¹(U), L^{n})` is multiplicative

The statements below are spelled out in full (with local notation) and every step of a proof is
stated with its type: the kernel then only compares syntactically equal terms, whereas comparing
two presentations of the same section under `tensorPowerTwistOnZIso` unfolds the isomorphism. -/

set_option hygiene false in
local notation "Φ⁻¹[" n ", " h "]" => (tensorPowerTwistOnZIso i n h).inv.app _

set_option hygiene false in
local notation "𝒯" => (coordinateAlgebra i).obj.obj (op U)

set_option hygiene false in
local notation "𝒢" => (coordinateAlgebra i).grading U

/-- The comparison `T(U)_n → Γ(f⁻¹(U), 𝒪(n)|_Z)` on the chosen homogeneous lift. -/
theorem coordTwistSection_apply (U : X.AffineZariskiSite) {n : ℕ} (x : 𝒢 n) :
    coordTwistSection i U n x = polyTwistSection i U.1 n (coordLift i U x) :=
  congrFun (AddMonoidHom.mk'_apply _ _) x

omit [IsClosedImmersion i] in
private theorem coordLift_mul_mem (U : X.AffineZariskiSite) {p q : ℕ} (x : 𝒢 p) (y : 𝒢 q) :
    coordLift i U x * coordLift i U y ∈
      MvPolynomial.homogeneousSubmodule (Fin (r + 1)) Γ(X, U.1) (p + q) :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).2
    (((MvPolynomial.mem_homogeneousSubmodule _ _).1 (coordLift_mem i U x)).mul
      ((MvPolynomial.mem_homogeneousSubmodule _ _).1 (coordLift_mem i U y)))

omit [IsClosedImmersion i] in
private theorem homogeneousComponent_coordLift_mul (U : X.AffineZariskiSite) {p q : ℕ} (x : 𝒢 p)
    (y : 𝒢 q) :
    MvPolynomial.homogeneousComponent p (coordLift i U x) *
        MvPolynomial.homogeneousComponent q (coordLift i U y) =
      coordLift i U x * coordLift i U y :=
  congrArg₂ (· * ·)
    ((MvPolynomial.homogeneousComponent_of_mem (coordLift_mem i U x)).trans (if_pos rfl))
    ((MvPolynomial.homogeneousComponent_of_mem (coordLift_mem i U y)).trans (if_pos rfl))

omit [IsClosedImmersion i] in
private theorem mk_coordLift_mul (U : X.AffineZariskiSite) {p q : ℕ} (x : 𝒢 p) (y : 𝒢 q) :
    (⟨_, mk_mem_gradedQuotient (I := chartIdeal i U.1 U.2) (coordLift_mul_mem i U x y)⟩ :
        𝒢 (p + q)) = ⟨(x : 𝒯) * (y : 𝒯), SetLike.mul_mem_graded x.2 y.2⟩ :=
  Subtype.ext ((map_mul _ _ _).trans (congrArg₂ (· * ·) (mk_coordLift i U x) (mk_coordLift i U y)))

section CoordMul

variable (U : X.AffineZariskiSite) {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (x : 𝒢 p) (y : 𝒢 q)

private theorem coordMul_step1 :
    tensorPowerMulSection i (Φ⁻¹[p, hp] (coordTwistSection i U p x))
        (Φ⁻¹[q, hq] (coordTwistSection i U q y)) =
      tensorPowerMulSection i (Φ⁻¹[p, hp] (polyTwistSection i U.1 p (coordLift i U x)))
        (Φ⁻¹[q, hq] (polyTwistSection i U.1 q (coordLift i U y))) :=
  congrArg₂ (fun u v => tensorPowerMulSection i (Φ⁻¹[p, hp] u) (Φ⁻¹[q, hq] v))
    (coordTwistSection_apply i U x) (coordTwistSection_apply i U y)

omit [IsClosedImmersion i] in
private theorem coordMul_step3 :
    Φ⁻¹[p + q, pos_add_of_pos hp q] (polyTwistSection i U.1 (p + q)
        (MvPolynomial.homogeneousComponent p (coordLift i U x) *
          MvPolynomial.homogeneousComponent q (coordLift i U y))) =
      Φ⁻¹[p + q, pos_add_of_pos hp q]
        (polyTwistSection i U.1 (p + q) (coordLift i U x * coordLift i U y)) :=
  congrArg (fun z => Φ⁻¹[p + q, pos_add_of_pos hp q] (polyTwistSection i U.1 (p + q) z))
    (homogeneousComponent_coordLift_mul i U x y)

private theorem coordMul_step4 :
    Φ⁻¹[p + q, pos_add_of_pos hp q]
        (polyTwistSection i U.1 (p + q) (coordLift i U x * coordLift i U y)) =
      Φ⁻¹[p + q, pos_add_of_pos hp q] (coordTwistSection i U (p + q)
        ⟨_, mk_mem_gradedQuotient (I := chartIdeal i U.1 U.2) (coordLift_mul_mem i U x y)⟩) :=
  congrArg (fun z => Φ⁻¹[p + q, pos_add_of_pos hp q] z)
    (coordTwistSection_mk i U (coordLift_mul_mem i U x y)).symm

private theorem coordMul_step5 :
    Φ⁻¹[p + q, pos_add_of_pos hp q] (coordTwistSection i U (p + q)
        ⟨_, mk_mem_gradedQuotient (I := chartIdeal i U.1 U.2) (coordLift_mul_mem i U x y)⟩) =
      Φ⁻¹[p + q, pos_add_of_pos hp q] (coordTwistSection i U (p + q)
        ⟨(x : 𝒯) * (y : 𝒯), SetLike.mul_mem_graded x.2 y.2⟩) :=
  congrArg (fun z => Φ⁻¹[p + q, pos_add_of_pos hp q] (coordTwistSection i U (p + q) z))
    (mk_coordLift_mul i U x y)

/-- **Multiplicativity of the comparison** `T(U)_n ≅ Γ(f⁻¹(U), L^{n})`: the sections of `L^{p}`
and `L^{q}` attached to `x ∈ T(U)_p` and `y ∈ T(U)_q` multiply, under `L^{p} × L^{q} → L^{p+q}`,
to the section attached to `xy`. -/
theorem tensorPowerMulSection_coordTwistSection :
    tensorPowerMulSection i (Φ⁻¹[p, hp] (coordTwistSection i U p x))
        (Φ⁻¹[q, hq] (coordTwistSection i U q y)) =
      Φ⁻¹[p + q, pos_add_of_pos hp q] (coordTwistSection i U (p + q)
        ⟨(x : 𝒯) * (y : 𝒯), SetLike.mul_mem_graded x.2 y.2⟩) := by
  have h₁ : tensorPowerMulSection i (Φ⁻¹[p, hp] (coordTwistSection i U p x))
        (Φ⁻¹[q, hq] (coordTwistSection i U q y)) =
      tensorPowerMulSection i (Φ⁻¹[p, hp] (polyTwistSection i U.1 p (coordLift i U x)))
        (Φ⁻¹[q, hq] (polyTwistSection i U.1 q (coordLift i U y))) :=
    coordMul_step1 i U hp hq x y
  have h₂ : tensorPowerMulSection i (Φ⁻¹[p, hp] (polyTwistSection i U.1 p (coordLift i U x)))
        (Φ⁻¹[q, hq] (polyTwistSection i U.1 q (coordLift i U y))) =
      Φ⁻¹[p + q, pos_add_of_pos hp q] (polyTwistSection i U.1 (p + q)
        (MvPolynomial.homogeneousComponent p (coordLift i U x) *
          MvPolynomial.homogeneousComponent q (coordLift i U y))) :=
    tensorPowerMulSection_polyTwistSection i U.1 hp hq _ _
  have h₃ : Φ⁻¹[p + q, pos_add_of_pos hp q] (polyTwistSection i U.1 (p + q)
        (MvPolynomial.homogeneousComponent p (coordLift i U x) *
          MvPolynomial.homogeneousComponent q (coordLift i U y))) =
      Φ⁻¹[p + q, pos_add_of_pos hp q]
        (polyTwistSection i U.1 (p + q) (coordLift i U x * coordLift i U y)) :=
    coordMul_step3 i U hp x y
  have h₄ : Φ⁻¹[p + q, pos_add_of_pos hp q]
        (polyTwistSection i U.1 (p + q) (coordLift i U x * coordLift i U y)) =
      Φ⁻¹[p + q, pos_add_of_pos hp q] (coordTwistSection i U (p + q)
        ⟨_, mk_mem_gradedQuotient (I := chartIdeal i U.1 U.2) (coordLift_mul_mem i U x y)⟩) :=
    coordMul_step4 i U hp x y
  have h₅ : Φ⁻¹[p + q, pos_add_of_pos hp q] (coordTwistSection i U (p + q)
        ⟨_, mk_mem_gradedQuotient (I := chartIdeal i U.1 U.2) (coordLift_mul_mem i U x y)⟩) =
      Φ⁻¹[p + q, pos_add_of_pos hp q] (coordTwistSection i U (p + q)
        ⟨(x : 𝒯) * (y : 𝒯), SetLike.mul_mem_graded x.2 y.2⟩) :=
    coordMul_step5 i U hp x y
  exact Eq.trans h₁ (Eq.trans h₂ (Eq.trans h₃ (Eq.trans h₄ h₅)))

end CoordMul

/-! ### The Veronese comparison `T(U)^{(d)}_m ≅ Γ(f⁻¹(U), L^{md})` is multiplicative -/

set_option hygiene false in
local notation "𝒱" => ((coordinateAlgebra i).veronese d).obj.obj (op U)

set_option hygiene false in
local notation "𝒢ᵈ" => ((coordinateAlgebra i).veronese d).grading U

set_option hygiene false in
local notation "ϖ" => veronesePieceEquiv ((coordinateAlgebra i).grading U) d

set_option hygiene false in
local notation "Γᴸ[" n "]" =>
  Γ(tensorPowerL i n, (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)

omit [IsClosedImmersion i] [IsIntegral Z] in
private theorem ab_hom_apply {A B : Ab.{u}} (f : A ⟶ B) (x : A) : f.hom x = f x := rfl

omit [IsClosedImmersion i] [IsIntegral Z] in
/-- `md > 0` for `m > 0` and `d ≠ 0`. -/
theorem pos_mul_neZero (d : ℕ) [NeZero d] {m : ℕ} (hm : 0 < m) : 0 < m * d :=
  Nat.mul_pos hm (Nat.pos_of_ne_zero (NeZero.ne d))

/-- The comparison `T(U)^{(d)}_m → Γ(f⁻¹(U), L^{md})` unfolded: `y ↦ Φ⁻¹(c(y))` for the comparison
`c : T(U)_{md} → Γ(f⁻¹(U), 𝒪(md)|_Z)` and `Φ : L^{md} ≅ 𝒪(md)|_Z`. -/
theorem veroneseTwistSection_apply (d : ℕ) [NeZero d] (U : X.AffineZariskiSite) {m : ℕ}
    (hm : 0 < m) (h : 0 < m * d) (y : 𝒢ᵈ m) :
    veroneseTwistSection i d U hm y = Φ⁻¹[m * d, h] (coordTwistSection i U (m * d) (ϖ m y)) := by
  obtain ⟨h₀, e₁⟩ : ∃ h₀ : 0 < m * d, veroneseTwistSection i d U hm =
      ((Φ⁻¹[m * d, h₀]).hom.comp ((coordTwistSection i U (m * d)).comp (ϖ m).toAddMonoidHom) :
        𝒢ᵈ m →+ Γᴸ[m * d]) :=
    ⟨_, veroneseTwistSection.eq_1 i d U hm⟩
  have e₂ : veroneseTwistSection i d U hm y =
      ((Φ⁻¹[m * d, h₀]).hom.comp ((coordTwistSection i U (m * d)).comp (ϖ m).toAddMonoidHom) :
        𝒢ᵈ m →+ Γᴸ[m * d]) y :=
    DFunLike.congr_fun e₁ y
  have e₃ : ((Φ⁻¹[m * d, h₀]).hom.comp ((coordTwistSection i U (m * d)).comp (ϖ m).toAddMonoidHom) :
        𝒢ᵈ m →+ Γᴸ[m * d]) y =
      (Φ⁻¹[m * d, h₀]).hom (((coordTwistSection i U (m * d)).comp (ϖ m).toAddMonoidHom :
        𝒢ᵈ m →+ Γ(twistOnZ i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)) y) :=
    AddMonoidHom.comp_apply _ _ y
  have e₄ : ((coordTwistSection i U (m * d)).comp (ϖ m).toAddMonoidHom :
        𝒢ᵈ m →+ Γ(twistOnZ i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)) y =
      coordTwistSection i U (m * d) (((ϖ m).toAddMonoidHom : 𝒢ᵈ m →+ 𝒢 (m * d)) y) :=
    AddMonoidHom.comp_apply _ _ y
  have e₅ : ((ϖ m).toAddMonoidHom : 𝒢ᵈ m →+ 𝒢 (m * d)) y = ϖ m y := rfl
  have e₆ : (Φ⁻¹[m * d, h₀]).hom (((coordTwistSection i U (m * d)).comp (ϖ m).toAddMonoidHom :
        𝒢ᵈ m →+ Γ(twistOnZ i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)) y) =
      (Φ⁻¹[m * d, h₀]).hom (coordTwistSection i U (m * d) (ϖ m y)) :=
    congrArg (fun z => (Φ⁻¹[m * d, h₀]).hom z)
      (Eq.trans e₄ (congrArg (fun z => coordTwistSection i U (m * d) z) e₅))
  have e₇ : (Φ⁻¹[m * d, h₀]).hom (coordTwistSection i U (m * d) (ϖ m y)) =
      Φ⁻¹[m * d, h₀] (coordTwistSection i U (m * d) (ϖ m y)) :=
    ab_hom_apply _ _
  have e₈ : Φ⁻¹[m * d, h₀] (coordTwistSection i U (m * d) (ϖ m y)) =
      Φ⁻¹[m * d, h] (coordTwistSection i U (m * d) (ϖ m y)) :=
    congrArg (fun h' => Φ⁻¹[m * d, h'] (coordTwistSection i U (m * d) (ϖ m y)))
      (Subsingleton.elim h₀ h)
  exact Eq.trans e₂ (Eq.trans e₃ (Eq.trans e₆ (Eq.trans e₇ e₈)))

section VeroneseMul

variable (d : ℕ) [NeZero d] (U : X.AffineZariskiSite) {a b : ℕ} (x : 𝒢ᵈ a) (y : 𝒢ᵈ b)

omit [IsClosedImmersion i] in
private theorem veronesePieceEquiv_mul
    (hz : ((ϖ a x : 𝒢 (a * d)) : 𝒯) * ((ϖ b y : 𝒢 (b * d)) : 𝒯) ∈ 𝒢 ((a + b) * d)) :
    ϖ (a + b) (⟨(x : 𝒱) * (y : 𝒱), SetLike.mul_mem_graded x.2 y.2⟩ : 𝒢ᵈ (a + b)) =
      ⟨((ϖ a x : 𝒢 (a * d)) : 𝒯) * ((ϖ b y : 𝒢 (b * d)) : 𝒯), hz⟩ :=
  Subtype.ext rfl

set_option hygiene false in
local notation "τ" =>
  Scheme.Modules.Hom.app (eqToHom (congrArg (tensorPowerL i) (Nat.add_mul a b d).symm)) _

set_option hygiene false in
local notation "𝔵𝔶" => (⟨(x : 𝒱) * (y : 𝒱), SetLike.mul_mem_graded x.2 y.2⟩ : 𝒢ᵈ (a + b))

set_option hygiene false in
local notation "𝔛𝔜" => ((ϖ a x : 𝒢 (a * d)) : 𝒯) * ((ϖ b y : 𝒢 (b * d)) : 𝒯)

/-- **Multiplicativity of the comparison** `T(U)^{(d)}_m ≅ Γ(f⁻¹(U), L^{md})`: for `x` of degree
`a` and `y` of degree `b`, the product of the sections of `L^{ad}` and `L^{bd}` attached to `x` and
`y`, transported along `L^{ad+bd} = L^{(a+b)d}`, is the section attached to `xy`. -/
theorem veroneseTwistSection_mul (ha : 0 < a) (hb : 0 < b) :
    τ (tensorPowerMulSection i (veroneseTwistSection i d U ha x)
        (veroneseTwistSection i d U hb y)) =
      veroneseTwistSection i d U (pos_add_of_pos ha b) 𝔵𝔶 := by
  have hz : 𝔛𝔜 ∈ 𝒢 ((a + b) * d) := (ϖ (a + b) 𝔵𝔶).2
  have h₁ : veroneseTwistSection i d U ha x =
      Φ⁻¹[a * d, pos_mul_neZero d ha] (coordTwistSection i U (a * d) (ϖ a x)) :=
    veroneseTwistSection_apply i d U ha _ x
  have h₂ : veroneseTwistSection i d U hb y =
      Φ⁻¹[b * d, pos_mul_neZero d hb] (coordTwistSection i U (b * d) (ϖ b y)) :=
    veroneseTwistSection_apply i d U hb _ y
  have h₃ : tensorPowerMulSection i (veroneseTwistSection i d U ha x)
        (veroneseTwistSection i d U hb y) =
      tensorPowerMulSection i
        (Φ⁻¹[a * d, pos_mul_neZero d ha] (coordTwistSection i U (a * d) (ϖ a x)))
        (Φ⁻¹[b * d, pos_mul_neZero d hb] (coordTwistSection i U (b * d) (ϖ b y))) :=
    congrArg₂ (tensorPowerMulSection i) h₁ h₂
  have h₄ : tensorPowerMulSection i
        (Φ⁻¹[a * d, pos_mul_neZero d ha] (coordTwistSection i U (a * d) (ϖ a x)))
        (Φ⁻¹[b * d, pos_mul_neZero d hb] (coordTwistSection i U (b * d) (ϖ b y))) =
      Φ⁻¹[a * d + b * d, pos_add_of_pos (pos_mul_neZero d ha) (b * d)]
        (coordTwistSection i U (a * d + b * d)
          ⟨𝔛𝔜, SetLike.mul_mem_graded (ϖ a x).2 (ϖ b y).2⟩) :=
    tensorPowerMulSection_coordTwistSection i U (pos_mul_neZero d ha) (pos_mul_neZero d hb) _ _
  have h₅ : τ (tensorPowerMulSection i (veroneseTwistSection i d U ha x)
        (veroneseTwistSection i d U hb y)) =
      τ (Φ⁻¹[a * d + b * d, pos_add_of_pos (pos_mul_neZero d ha) (b * d)]
        (coordTwistSection i U (a * d + b * d)
          ⟨𝔛𝔜, SetLike.mul_mem_graded (ϖ a x).2 (ϖ b y).2⟩)) :=
    congrArg (fun z => τ z) (Eq.trans h₃ h₄)
  have h₆ : τ (Φ⁻¹[a * d + b * d, pos_add_of_pos (pos_mul_neZero d ha) (b * d)]
        (coordTwistSection i U (a * d + b * d)
          ⟨𝔛𝔜, SetLike.mul_mem_graded (ϖ a x).2 (ϖ b y).2⟩)) =
      Φ⁻¹[(a + b) * d, pos_mul_neZero d (pos_add_of_pos ha b)]
        (coordTwistSection i U ((a + b) * d) ⟨𝔛𝔜, hz⟩) :=
    eqToHom_app_coordTwistSection i U (Nat.add_mul a b d).symm _ _ _ _ _ _
  have h₇ : veroneseTwistSection i d U (pos_add_of_pos ha b) 𝔵𝔶 =
      Φ⁻¹[(a + b) * d, pos_mul_neZero d (pos_add_of_pos ha b)]
        (coordTwistSection i U ((a + b) * d) (ϖ (a + b) 𝔵𝔶)) :=
    veroneseTwistSection_apply i d U _ _ _
  have h₈ : Φ⁻¹[(a + b) * d, pos_mul_neZero d (pos_add_of_pos ha b)]
        (coordTwistSection i U ((a + b) * d) (ϖ (a + b) 𝔵𝔶)) =
      Φ⁻¹[(a + b) * d, pos_mul_neZero d (pos_add_of_pos ha b)]
        (coordTwistSection i U ((a + b) * d) ⟨𝔛𝔜, hz⟩) :=
    congrArg (fun z => Φ⁻¹[(a + b) * d, pos_mul_neZero d (pos_add_of_pos ha b)]
      (coordTwistSection i U ((a + b) * d) z)) (veronesePieceEquiv_mul i d U x y hz)
  exact Eq.trans h₅ (Eq.trans h₆ (Eq.symm (Eq.trans h₇ h₈)))

end VeroneseMul

/-! ### The section-algebra model, multiplicative form -/

section Model

open Scheme.AffineZariskiSite

variable [IsNoetherian X] [IsIntegral X]
  (hf : (i ≫ projectiveSpaceOverSchemeProjection r X) (genericPoint Z) = genericPoint X)
  (d : ℕ) [NeZero d]
  (E : ∀ (U : X.AffineZariskiSite) {m : ℕ}, 0 < m →
    Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) ≃+
      (sectionAlgebraRelativeProjData i hf d).algebra.grading U m)
  (hE : ∀ (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m)
    (s : Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)),
    veroneseTwistSection i d U hm (E U hm s) = s)
  (hV : ∀ (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m),
    Function.Injective (veroneseTwistSection i d U hm))

include hE hV

/-- A right inverse `E` of the injective comparison maps commutes with restriction. -/
theorem sectionAlgebraModel_restrict (U V : X.AffineZariskiSite) (h : V ⟶ U) {m : ℕ} (hm : 0 < m)
    (s : Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)) :
    (E V hm ((tensorPowerL i (m * d)).presheaf.map
        (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
          (toOpens_mono h.le))).op s) :
        (sectionAlgebraRelativeProjData i hf d).algebra.obj.obj (op V)) =
      (sectionAlgebraRelativeProjData i hf d).algebra.obj.map h.op (E U hm s) := by
  have key := veroneseTwistSection_restrict i d h hm (E U hm s)
  have := hV V hm ((hE V hm _).trans ((congrArg (fun t => (tensorPowerL i (m * d)).presheaf.map
      (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
        (toOpens_mono h.le))).op t) (hE U hm s).symm).trans key))
  exact congrArg Subtype.val this

/-- A right inverse `E` of the injective comparison maps is `Γ(X, U)`-linear. -/
theorem sectionAlgebraModel_structureMap_mul (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m)
    (a : Γ(X, U.1))
    (s : Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)) :
    (E U hm ((i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a • s) :
        (sectionAlgebraRelativeProjData i hf d).algebra.obj.obj (op U)) =
      (sectionAlgebraRelativeProjData i hf d).algebra.structureMap.app (op U) a * E U hm s := by
  have key := veroneseTwistSection_structureMap_mul i d U hm a (E U hm s)
  have := hV U hm ((hE U hm _).trans ((congrArg (fun t =>
    (i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a • t) (hE U hm s).symm).trans key.symm))
  exact congrArg Subtype.val this

/-- A right inverse `E` of the injective comparison maps is multiplicative: it sends the product
`L^{ad} × L^{bd} → L^{ad+bd} = L^{(a+b)d}` to the multiplication of `T^{(d)}(U)`. -/
theorem sectionAlgebraModel_mul (U : X.AffineZariskiSite) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (s : Γ(tensorPowerL i (a * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1))
    (t : Γ(tensorPowerL i (b * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)) :
    (E U (pos_add_of_pos ha b) (Scheme.Modules.Hom.app
        (eqToHom (congrArg (tensorPowerL i) (Nat.add_mul a b d).symm)) _
        (tensorPowerMulSection i s t)) :
        (sectionAlgebraRelativeProjData i hf d).algebra.obj.obj (op U)) =
      (E U ha s : (sectionAlgebraRelativeProjData i hf d).algebra.obj.obj (op U)) * E U hb t := by
  have key := veroneseTwistSection_mul i d U (E U ha s) (E U hb t) ha hb
  have h₁ := congrArg₂ (fun s t => Scheme.Modules.Hom.app
    (eqToHom (congrArg (tensorPowerL i) (Nat.add_mul a b d).symm)) _
    (tensorPowerMulSection i s t)) (hE U ha s) (hE U hb t)
  have := hV U (pos_add_of_pos ha b) ((hE U _ _).trans (h₁.symm.trans key))
  exact congrArg Subtype.val this

omit hE hV

end Model

/-! ### The comparison isomorphisms of the model -/

/-- `f x = n` from `x = y` and `f y = n`. Used with `y` given explicitly: the kernel then compares
`x` with `y` directly, whereas comparing `f x` with `f y` makes it unfold `f` first. -/
private theorem apply_eq_of_eq {M N : Type*} (f : M → N) {x y : M} {n : N} (h : x = y)
    (hy : f y = n) : f x = n :=
  h ▸ hy

section ModelEquiv

variable [IsNoetherian X] [IsIntegral X]
  (hf : (i ≫ projectiveSpaceOverSchemeProjection r X) (genericPoint Z) = genericPoint X)
  (d : ℕ) [NeZero d]
  (hG : ∀ (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m),
    Function.Bijective (veroneseTwistSection i d U hm))

/-- The inverses `Γ(f⁻¹(U), L^{md}) ≅ T^{(d)}(U)_m` of bijective comparison maps, built with the
grading of `sectionAlgebraRelativeProjData` as domain. As a definition (rather than a `fun`), it
appears literally in the hypotheses of `sectionAlgebraModel_restrict` and its siblings; passing a
`fun` there made the kernel unfold the comparison maps to check each use (about a minute and a
half each). -/
private noncomputable def sectionAlgebraModelEquiv : ∀ (U : X.AffineZariskiSite) {m : ℕ}, 0 < m →
    Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) ≃+
      (sectionAlgebraRelativeProjData i hf d).algebra.grading U m :=
  fun U m hm => (AddEquiv.ofBijective
    (M := (sectionAlgebraRelativeProjData i hf d).algebra.grading U m)
    (F := (sectionAlgebraRelativeProjData i hf d).algebra.grading U m →+ Γᴸ[m * d])
    (veroneseTwistSection i d U hm) (hG U hm)).symm

/-- `sectionAlgebraModelEquiv` is a right inverse of the comparison maps. -/
private theorem veroneseTwistSection_sectionAlgebraModelEquiv (U : X.AffineZariskiSite) {m : ℕ}
    (hm : 0 < m)
    (s : Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)) :
    veroneseTwistSection i d U hm (sectionAlgebraModelEquiv i hf d hG U hm s) = s :=
  apply_eq_of_eq (veroneseTwistSection i d U hm)
    (y := (AddEquiv.ofBijective (M := (sectionAlgebraRelativeProjData i hf d).algebra.grading U m)
      (F := (sectionAlgebraRelativeProjData i hf d).algebra.grading U m →+ Γᴸ[m * d])
      (veroneseTwistSection i d U hm) (hG U hm)).symm s) rfl
    ((AddEquiv.ofBijective (M := (sectionAlgebraRelativeProjData i hf d).algebra.grading U m)
      (F := (sectionAlgebraRelativeProjData i hf d).algebra.grading U m →+ Γᴸ[m * d])
      (veroneseTwistSection i d U hm) (hG U hm)).apply_symm_apply s)

end ModelEquiv

open Scheme.AffineZariskiSite in
/-- **The section-algebra model of a projective birational morphism** (Hartshorne II, proof of
Theorem 7.17, Steps 1–3). Let `X` be an integral quasi-compact scheme locally of finite type over a
field `k`, `i : Z ⟶ ℙʳ_X` a closed immersion of an integral scheme, `f = π ∘ i` sending the generic
point of `Z` to that of `X` (only this dominance is used, not birationality), and `L = i^* 𝒪(1)`.
There is a `d₀` such that for every `d ≥ d₀` there is a quasi-coherent graded `𝒪_X`-algebra `S`
satisfying the hypotheses for relative Proj (`S₀ = 𝒪_X`, `S₁` coherent, generated by `S₁`) with
`Proj_X S ≅ Z` over `X`, together with isomorphisms `E : Γ(f⁻¹(U), L^{md}) ≅ S(U)_m` (`U` affine,
`m ≥ 1`) that are compatible with restriction, `Γ(X, U)`-linear, and multiplicative: `E` sends the
product `L^{ad} × L^{bd} → L^{(a+b)d}` (from `L^{ad} ⊗ L^{bd} ≅ L^{ad+bd}`) to the multiplication of
`S(U)`. Thus `𝒪_X ⊕ ⨁_{m ≥ 1} f_* L^{md} ≅ S` as graded `𝒪_X`-algebras on the affine opens. -/
theorem exists_sectionAlgebraModel_multiplicative (k : Type u) [Field k] [IsIntegral X]
    [CompactSpace X] (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    (hf : (i ≫ projectiveSpaceOverSchemeProjection r X) (genericPoint Z) = genericPoint X) :
    letI : IsNoetherian X :=
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian pX }
    ∃ d₀ : ℕ, ∀ (d : ℕ) [NeZero d], d₀ ≤ d → ∃ D : RelativeProjData X,
      ∃ E : ∀ (U : X.AffineZariskiSite) {m : ℕ}, 0 < m →
        Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1) ≃+
          D.algebra.grading U m,
      (∀ (U V : X.AffineZariskiSite) (h : V ⟶ U) {m : ℕ} (hm : 0 < m)
          (s : Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)),
        (E V hm ((tensorPowerL i (m * d)).presheaf.map
            (homOfLE ((i ≫ projectiveSpaceOverSchemeProjection r X).preimage_mono
              (toOpens_mono h.le))).op s) : D.algebra.obj.obj (op V)) =
          D.algebra.obj.map h.op (E U hm s)) ∧
      (∀ (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m) (a : Γ(X, U.1))
          (s : Γ(tensorPowerL i (m * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)),
        (E U hm ((i ≫ projectiveSpaceOverSchemeProjection r X).app U.1 a • s) :
            D.algebra.obj.obj (op U)) =
          D.algebra.structureMap.app (op U) a * E U hm s) ∧
      (∀ (U : X.AffineZariskiSite) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
          (s : Γ(tensorPowerL i (a * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1))
          (t : Γ(tensorPowerL i (b * d), (i ≫ projectiveSpaceOverSchemeProjection r X) ⁻¹ᵁ U.1)),
        (E U (pos_add_of_pos ha b) (Scheme.Modules.Hom.app
            (eqToHom (congrArg (tensorPowerL i) (Nat.add_mul a b d).symm)) _
            (tensorPowerMulSection i s t)) : D.algebra.obj.obj (op U)) =
          (E U ha s : D.algebra.obj.obj (op U)) * E U hb t) ∧
      ∃ e : D.relativeProj ≅ Z, e.hom ≫ (i ≫ projectiveSpaceOverSchemeProjection r X) =
        D.projection := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian pX }
  obtain ⟨d₀, hd₀⟩ := exists_bound_bijective_twistSection i k pX
  refine ⟨d₀, fun d _ hd => ?_⟩
  have hG : ∀ (U : X.AffineZariskiSite) {m : ℕ} (hm : 0 < m),
      Function.Bijective (veroneseTwistSection i d U hm) := fun U m hm =>
    veroneseTwistSection_bijective i d U hm
      (hd₀ U (m * d) (hd.trans (Nat.le_mul_of_pos_left d hm)))
  exact ⟨sectionAlgebraRelativeProjData i hf d, sectionAlgebraModelEquiv i hf d hG,
    sectionAlgebraModel_restrict i hf d _ (veroneseTwistSection_sectionAlgebraModelEquiv i hf d hG)
      (fun U m hm => (hG U hm).1),
    sectionAlgebraModel_structureMap_mul i hf d _
      (veroneseTwistSection_sectionAlgebraModelEquiv i hf d hG) (fun U m hm => (hG U hm).1),
    sectionAlgebraModel_mul i hf d _ (veroneseTwistSection_sectionAlgebraModelEquiv i hf d hG)
      (fun U m hm => (hG U hm).1),
    sectionAlgebraRelativeProjIso i hf d, sectionAlgebraRelativeProjIso_hom_comp i hf d⟩

end Local

end SectionAlgebraModel

end Hartshorne
