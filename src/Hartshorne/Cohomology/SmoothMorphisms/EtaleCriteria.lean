/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeDifferentials
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Étale, flat-unramified, and differential criteria

Hartshorne, *Algebraic Geometry*, III Exercise 10.3 (p. 275).

For a morphism `f : X → Y` of schemes of finite type over a field, the following are
equivalent: `f` is étale (equivalently smooth of relative dimension zero); `f` is flat and the
relative differential sheaf `Ω_{X/Y}` vanishes; `f` is flat and unramified in Hartshorne's
pointwise sense (`m_y 𝒪_{X,x} = m_x` and `k(x)/k(y)` separable algebraic).

The bridge between the sheaf `Ω_{X/Y}`, constructed by sheafifying Kähler differentials, and
formal unramifiedness goes through the universal property of `Ω_{X/Y}`: it vanishes exactly
when every relative derivation into every module sheaf vanishes. A formally unramified
morphism kills derivations on affine opens, hence everywhere. Conversely, the universal
derivation of the stalk `𝒪_{X,x}` over `𝒪_{Y,f(x)}`, placed in a skyscraper module sheaf at
`x`, is a relative derivation, so vanishing of `Ω_{X/Y}` forces every stalk map to be formally
unramified.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

namespace Hartshorne

open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace EtaleCriteria

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit of the inverse-image adjunction. -/
noncomputable abbrev inverseImageUnit :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj (inverseImageStructureSheaf f) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app Y.sheaf

/-- The unit of the inverse-image adjunction followed by the structural map `f⁻¹𝒪_Y → 𝒪_X`
is the comorphism of `f`. -/
lemma inverseImageUnit_comp (U : Y.Opens) :
    (inverseImageUnit f).hom.app (op U) ≫
      (inverseImageStructureSheafMap f).hom.app (op (f ⁻¹ᵁ U)) = f.c.app (op U) := by
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv_unit
    (X := Y.sheaf) (Y := X.sheaf) (f := inverseImageStructureSheafMap f)
  simp only [inverseImageStructureSheafMap] at h
  erw [Equiv.apply_symm_apply] at h
  exact (congrArg (fun g => g.hom.app (op U)) h).symm

/-- A relative derivation kills the image of sections of `𝒪_Y` over any open. -/
lemma derivation_d_appLE (M : X.Modules)
    (D : M.val.Derivation' (inverseImageStructureSheafMap f).hom)
    (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (a : Γ(Y, U)) :
    D.d (X := op V) (f.appLE U V e a) = 0 := by
  have h1 : f.appLE U V e a = X.presheaf.map (homOfLE e).op (f.app U a) := by
    rw [Scheme.Hom.appLE]; rfl
  have h2 : f.app U a = (inverseImageStructureSheafMap f).hom.app (op (f ⁻¹ᵁ U))
      ((inverseImageUnit f).hom.app (op U) a) := by
    exact (ConcreteCategory.congr_hom (inverseImageUnit_comp f U) a).symm
  rw [h1, h2]
  erw [D.d_map, D.d_app]
  exact map_zero _

/-- On affine opens, a formally unramified morphism kills every relative derivation. -/
lemma derivation_d_eq_zero_of_affine [FormallyUnramified f] (M : X.Modules)
    (D : M.val.Derivation' (inverseImageStructureSheafMap f).hom)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (b : Γ(X, V)) : D.d (X := op V) b = 0 := by
  let g := f.appLE U V e
  let D' : ModuleCat.Derivation (M.val.obj (op V)) g :=
    ModuleCat.Derivation.mk (fun b => D.d (X := op V) b) (fun b b' => by simp)
      (fun b b' => D.d_mul b b') (fun a => derivation_d_appLE f M D U V e a)
  have hfu := f.formallyUnramified_appLE hU hV e
  have hsub : Subsingleton (CommRingCat.KaehlerDifferential g) := by
    let := g.hom.toAlgebra
    exact hfu.subsingleton_kaehlerDifferential
  have := D'.desc_d b
  have h0 : CommRingCat.KaehlerDifferential.d (f := g) b = 0 := Subsingleton.elim _ _
  erw [h0, map_zero] at this
  exact this.symm

/-- A formally unramified morphism kills every relative derivation into a module sheaf. -/
lemma derivation_d_eq_zero [FormallyUnramified f] (M : X.Modules)
    (D : M.val.Derivation' (inverseImageStructureSheafMap f).hom)
    (W : X.Opens) (a : Γ(X, W)) : D.d (X := op W) a = 0 := by
  let F : TopCat.Sheaf Ab.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
  have hx : ∀ x : W, ∃ V : X.Opens, IsAffineOpen V ∧ (x : X) ∈ V ∧ V ≤ W ∧
      ∃ U : Y.Opens, IsAffineOpen U ∧ V ≤ f ⁻¹ᵁ U := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show (x : X) ∈ (W ⊓ f ⁻¹ᵁ U : X.Opens)
        from ⟨x.2, hxU⟩) (W ⊓ f ⁻¹ᵁ U).isOpen
    exact ⟨V, hV, hxV, fun y hy => (hVW hy).1, U, hU, fun y hy => (hVW hy).2⟩
  choose V hV hxV hVW U hU hVU using hx
  refine F.eq_of_locally_eq' V W (fun x => homOfLE (hVW x)) ?_ (D.d a) 0 ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩
  · intro x
    have h := D.d_map (homOfLE (hVW x)).op a
    have h0 := derivation_d_eq_zero_of_affine f M D (hU x) (hV x) (hVU x)
      (X.presheaf.map (homOfLE (hVW x)).op a)
    erw [h0] at h
    erw [map_zero, ← h]
    rfl

/-- The relative differential sheaf vanishes exactly when every relative derivation into every
module sheaf vanishes. -/
lemma isZero_relativeDifferentials_iff :
    IsZero (relativeDifferentials f) ↔ ∀ (M : X.Modules)
      (D : M.val.Derivation' (inverseImageStructureSheafMap f).hom)
      (W : X.Opens) (a : Γ(X, W)), D.d (X := op W) a = 0 := by
  constructor
  · intro hz M D W a
    let α := (relativeDifferentialsHomEquiv f M).symm D
    have hα : α = 0 := hz.eq_of_src _ _
    have hD : D = (relativeDifferentialsDerivation f).postcomp α.val := by
      rw [← relativeDifferentialsHomEquiv_apply, Equiv.apply_symm_apply]
    rw [hD, hα]
    rfl
  · intro h
    rw [IsZero.iff_id_eq_zero]
    apply (relativeDifferentialsHomEquiv f (relativeDifferentials f)).injective
    ext W a
    rw [h _ _ W.unop a, h _ _ W.unop a]

/-- An element whose two images in the tensor square agree has zero differential. -/
lemma kaehlerD_eq_zero_of_tmul {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (b : S)
    (h : b ⊗ₜ[R] (1 : S) = 1 ⊗ₜ b) : KaehlerDifferential.D R S b = 0 := by
  rw [KaehlerDifferential.D_apply]
  have : (⟨1 ⊗ₜ b - b ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R b⟩ :
      KaehlerDifferential.ideal R S) = 0 := Subtype.ext (by simp [h])
  rw [this]
  exact map_zero _

/-- Postcomposition preserves an equality of values. -/
lemma comp_apply_congr {A B C : CommRingCat.{u}} (g₁ g₂ : A ⟶ B) (k : B ⟶ C) (a : A)
    (H : g₁ a = g₂ a) : (g₁ ≫ k) a = (g₂ ≫ k) a := by
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, H]

section Stalk

variable (x : X)

/-- The stalk of the source as an algebra over the stalk of the target. -/
@[instance_reducible]
noncomputable def stalkAlgebra : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

attribute [local instance] stalkAlgebra

/-- The first inclusion of the stalk into its tensor square over the stalk of the target. -/
noncomputable abbrev stalkTensorLeft :
    X.presheaf.stalk x ⟶ CommRingCat.of (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
      X.presheaf.stalk x) :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
    X.presheaf.stalk x →+* X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] X.presheaf.stalk x)

/-- The second inclusion of the stalk into its tensor square. -/
noncomputable abbrev stalkTensorRight :
    X.presheaf.stalk x ⟶ CommRingCat.of (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
      X.presheaf.stalk x) :=
  CommRingCat.ofHom ((Algebra.TensorProduct.includeRight :
    X.presheaf.stalk x →ₐ[Y.presheaf.stalk (f x)]
      X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] X.presheaf.stalk x) :
    X.presheaf.stalk x →+* X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)] X.presheaf.stalk x)

/-- The two inclusions agree on the image of the stalk of the target. -/
lemma stalkTensorLeft_stalkMap (a : Y.presheaf.stalk (f x)) :
    stalkTensorLeft f x (f.stalkMap x a) = stalkTensorRight f x (f.stalkMap x a) := by
  change (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) a) ⊗ₜ (1 : X.presheaf.stalk x)
    = (1 : X.presheaf.stalk x) ⊗ₜ (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) a)
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]

open StalkSkyscraperPresheafAdjunctionAuxs in
/-- The morphism to a skyscraper sheaf induced by a map out of the stalk. -/
noncomputable def toSky {T : CommRingCat.{u}} (σ : X.presheaf.stalk x ⟶ T) :
    X.sheaf ⟶ (by classical exact skyscraperSheaf x T) := by
  classical
  exact ObjectProperty.homMk (toSkyscraperPresheaf x σ)

/-- Over an open containing `x`, the morphism to the skyscraper is the germ followed by `σ`. -/
lemma toSky_app_of_mem {T : CommRingCat.{u}} (σ : X.presheaf.stalk x ⟶ T) (W : X.Opens)
    (h : x ∈ W) : (toSky x σ).hom.app (op W) =
      X.presheaf.germ W x h ≫ σ ≫ eqToHom (by classical exact (if_pos h).symm) := by
  classical
  exact dif_pos h

/-- Two morphisms to a skyscraper that agree over an open containing `x` agree on germs. -/
lemma toSky_cancel {T : CommRingCat.{u}} (σ₁ σ₂ : X.presheaf.stalk x ⟶ T) (W : X.Opens)
    (h : x ∈ W) {Z : CommRingCat.{u}} (u : Z ⟶ X.presheaf.obj (op W))
    (H : u ≫ (toSky x σ₁).hom.app (op W) = u ≫ (toSky x σ₂).hom.app (op W)) :
    u ≫ X.presheaf.germ W x h ≫ σ₁ = u ≫ X.presheaf.germ W x h ≫ σ₂ := by
  classical
  rw [toSky_app_of_mem x σ₁ W h, toSky_app_of_mem x σ₂ W h] at H
  ext z
  exact (ConcreteCategory.bijective_of_isIso (eqToHom _)).1 (ConcreteCategory.congr_hom H z)

/-- Germs of sections of `f⁻¹𝒪_Y` have equal images under the two inclusions of the stalk
into its tensor square over the stalk of the target. -/
lemma germ_inverseImage_tensor (W : X.Opens) (h : x ∈ W)
    (t : (inverseImageStructureSheaf f).obj.obj (op W)) :
    stalkTensorLeft f x (X.presheaf.germ W x h ((inverseImageStructureSheafMap f).hom.app (op W) t))
      = stalkTensorRight f x
        (X.presheaf.germ W x h ((inverseImageStructureSheafMap f).hom.app (op W) t)) := by
  classical
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base
  have key : inverseImageStructureSheafMap f ≫ toSky x (stalkTensorLeft f x) =
      inverseImageStructureSheafMap f ≫ toSky x (stalkTensorRight f x) := by
    apply (adj.homEquiv _ _).injective
    erw [adj.homEquiv_unit, adj.homEquiv_unit]
    apply Sheaf.hom_ext
    ext ⟨U⟩ : 2
    change ((inverseImageUnit f).hom.app (op U) ≫
        (inverseImageStructureSheafMap f).hom.app (op (f ⁻¹ᵁ U))) ≫
          (toSky x (stalkTensorLeft f x)).hom.app (op (f ⁻¹ᵁ U)) =
      ((inverseImageUnit f).hom.app (op U) ≫
        (inverseImageStructureSheafMap f).hom.app (op (f ⁻¹ᵁ U))) ≫
          (toSky x (stalkTensorRight f x)).hom.app (op (f ⁻¹ᵁ U))
    erw [inverseImageUnit_comp]
    by_cases hU : x ∈ f ⁻¹ᵁ U
    · rw [toSky_app_of_mem x _ _ hU, toSky_app_of_mem x _ _ hU]
      ext s
      have hs : stalkTensorLeft f x (X.presheaf.germ (f ⁻¹ᵁ U) x hU (f.app U s)) =
          stalkTensorRight f x (X.presheaf.germ (f ⁻¹ᵁ U) x hU (f.app U s)) := by
        erw [← Scheme.Hom.germ_stalkMap_apply]
        exact stalkTensorLeft_stalkMap f x _
      exact comp_apply_congr (f.c.app (op U) ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hU ≫
        stalkTensorLeft f x) (f.c.app (op U) ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hU ≫
          stalkTensorRight f x) (eqToHom _) s hs
    · exact (isTerminalSkyscraperSheafObjObjOfNotMem (U := op (f ⁻¹ᵁ U)) hU).hom_ext _ _
  have := toSky_cancel x _ _ W h _ (congrArg (fun g => g.hom.app (op W)) key)
  exact ConcreteCategory.congr_hom this t

end Stalk

section SkyscraperModule

variable (x : X) (N : Type u) [AddCommGroup N]

/-- The abelian presheaf `W ↦ (x ∈ W → N)`: a skyscraper at `x` with value `N`. -/
noncomputable def skyAb : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u} where
  obj W := AddCommGrpCat.of (PLift (x ∈ W.unop) → N)
  map i := AddCommGrpCat.ofHom
    { toFun := fun φ h => φ ⟨i.unop.le h.down⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }

/-- The skyscraper abelian presheaf is a sheaf. -/
lemma skyAb_isSheaf : TopCat.Presheaf.IsSheaf (skyAb x N) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hc : ∀ i j (hi : x ∈ U i) (hj : x ∈ U j), sf i ⟨hi⟩ = sf j ⟨hj⟩ := fun i j hi hj =>
    congrFun (hsf i j) ⟨⟨hi, hj⟩⟩
  refine ⟨fun h => sf (Opens.mem_iSup.mp h.down).choose ⟨(Opens.mem_iSup.mp h.down).choose_spec⟩,
    ?_, ?_⟩
  · intro i
    funext hi
    exact hc _ _ _ _
  · intro s hs
    funext h
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp h.down
    exact (congrFun (hs i) ⟨hi⟩).trans (hc _ _ _ _)

variable [Module (X.presheaf.stalk x) N]

/-- Sections of the skyscraper over `W` are a module over `Γ(X, W)` through the germ at `x`. -/
@[instance_reducible]
noncomputable def skyModule (W : (TopologicalSpace.Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj W) ((skyAb x N).obj W) where
  smul a φ := fun h => X.presheaf.germ W.unop x h.down a • φ h
  one_smul φ := funext fun h => by
    change X.presheaf.germ W.unop x h.down 1 • φ h = φ h
    rw [map_one, one_smul]
  mul_smul a b φ := funext fun h => by
    change X.presheaf.germ W.unop x h.down (a * b) • φ h =
      X.presheaf.germ W.unop x h.down a • X.presheaf.germ W.unop x h.down b • φ h
    erw [map_mul, mul_smul]
  smul_zero a := funext fun h => smul_zero (X.presheaf.germ W.unop x h.down a)
  smul_add a φ ψ := funext fun h => smul_add (X.presheaf.germ W.unop x h.down a) (φ h) (ψ h)
  add_smul a b φ := funext fun h => by
    change X.presheaf.germ W.unop x h.down (a + b) • φ h =
      X.presheaf.germ W.unop x h.down a • φ h + X.presheaf.germ W.unop x h.down b • φ h
    erw [map_add, add_smul]
  zero_smul φ := funext fun h => by
    change X.presheaf.germ W.unop x h.down 0 • φ h = 0
    rw [map_zero, zero_smul]

attribute [local instance] skyModule

/-- The skyscraper sheaf of `𝒪_X`-modules at `x` with value the `𝒪_{X,x}`-module `N`. -/
noncomputable def skyMod : X.Modules where
  val := PresheafOfModules.ofPresheaf (skyAb x N) (fun W W' i a φ => funext fun h => by
    change X.presheaf.germ W.unop x (i.unop.le h.down) a • φ ⟨i.unop.le h.down⟩ =
      X.presheaf.germ W'.unop x h.down (X.presheaf.map i a) • φ ⟨i.unop.le h.down⟩
    erw [TopCat.Presheaf.germ_res_apply'])
  isSheaf := skyAb_isSheaf x N

end SkyscraperModule

section Converse

variable (x : X)

attribute [local instance] stalkAlgebra skyModule

/-- The relative derivation into the skyscraper at `x` of the stalk-level Kähler differentials. -/
noncomputable def skyDer :
    (skyMod x (Ω[X.presheaf.stalk x⁄Y.presheaf.stalk (f x)])).val.Derivation'
      (inverseImageStructureSheafMap f).hom where
  d {W} := AddMonoidHom.mk'
    (fun a h => KaehlerDifferential.D (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (X.presheaf.germ W.unop x h.down a)) (fun a b => funext fun h => by
        change KaehlerDifferential.D _ _ (X.presheaf.germ W.unop x h.down (a + b)) =
          KaehlerDifferential.D _ _ (X.presheaf.germ W.unop x h.down a) +
            KaehlerDifferential.D _ _ (X.presheaf.germ W.unop x h.down b)
        erw [map_add, map_add])
  d_mul {W} a b := funext fun h => by
    change KaehlerDifferential.D _ _ (X.presheaf.germ W.unop x h.down (a * b)) =
      X.presheaf.germ W.unop x h.down a •
          KaehlerDifferential.D _ _ (X.presheaf.germ W.unop x h.down b) +
        X.presheaf.germ W.unop x h.down b •
          KaehlerDifferential.D _ _ (X.presheaf.germ W.unop x h.down a)
    erw [map_mul, Derivation.leibniz]
  d_map {W W'} i a := funext fun h => by
    change KaehlerDifferential.D _ _ (X.presheaf.germ W'.unop x h.down (X.presheaf.map i a)) =
      KaehlerDifferential.D _ _ (X.presheaf.germ W.unop x (i.unop.le h.down) a)
    erw [TopCat.Presheaf.germ_res_apply']
  d_app {W} t := funext fun h => by
    change KaehlerDifferential.D _ _
      (X.presheaf.germ W.unop x h.down ((inverseImageStructureSheafMap f).hom.app W t)) = 0
    exact kaehlerD_eq_zero_of_tmul _ (germ_inverseImage_tensor f x W.unop h.down t)

/-- If the relative differential sheaf vanishes, the morphism is formally unramified. -/
lemma formallyUnramified_of_isZero (h : IsZero (relativeDifferentials f)) :
    FormallyUnramified f := by
  have hD := (isZero_relativeDifferentials_iff f).1 h
  apply HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime
  intro x
  change Algebra.FormallyUnramified (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
  constructor
  have hz : ∀ z : X.presheaf.stalk x,
      KaehlerDifferential.D (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) z = 0 := by
    intro z
    obtain ⟨W, hxW, a, rfl⟩ := X.presheaf.exists_germ_eq z
    exact congrFun (hD _ (skyDer f x) W a) ⟨hxW⟩
  refine subsingleton_of_forall_eq 0 fun ω => ?_
  have hω : ω ∈ (⊤ : Submodule (X.presheaf.stalk x) _) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation] at hω
  induction hω using Submodule.span_induction with
  | mem y hy => obtain ⟨z, rfl⟩ := hy; exact hz z
  | zero => rfl
  | add y z _ _ hy hz => rw [hy, hz, add_zero]
  | smul a y _ hy => rw [hy, smul_zero]

end Converse

end EtaleCriteria

open EtaleCriteria

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The relative differential sheaf vanishes exactly for formally unramified morphisms. -/
theorem isZero_relativeDifferentials_iff_formallyUnramified :
    IsZero (relativeDifferentials f) ↔ FormallyUnramified f := by
  refine ⟨formallyUnramified_of_isZero f, fun _ => ?_⟩
  rw [isZero_relativeDifferentials_iff]
  exact fun M D W a => derivation_d_eq_zero f M D W a

/-- Hartshorne's pointwise notion of an unramified morphism (III Exercise 10.3): for every
`x ∈ X`, with `y = f x`, the maximal ideal of `𝒪_{Y,y}` generates the maximal ideal of
`𝒪_{X,x}`, and the residue field extension `k(x)/k(y)` is separable algebraic. -/
def HartshorneUnramified {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x : X,
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
      letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) ∧
        Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)

/-- For a morphism locally of finite type, Hartshorne's pointwise condition at `x` is formal
unramifiedness of the stalk map at `x`. -/
lemma formallyUnramified_stalkMap_iff [LocallyOfFiniteType f] (x : X) :
    (f.stalkMap x).hom.FormallyUnramified ↔
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        letI := (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) ∧
          Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  let := (f.residueFieldMap x).hom.toAlgebra
  have hA : (inferInstance : Algebra (Y.residueField (f x)) (X.residueField x)) =
      (inferInstance : Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
    refine Algebra.algebra_ext _ _ fun z ↦ ?_
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z
    rfl
  change Algebra.FormallyUnramified _ _ ↔ _
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq]
  constructor
  · rintro ⟨hs, hm⟩
    refine ⟨hm, ?_⟩
    have hs' : Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x) := by
      convert! hs
    exact ⟨Algebra.IsSeparable.isAlgebraic _ _, hs'⟩
  · rintro ⟨hm, -, hs⟩
    refine ⟨?_, hm⟩
    convert! hs
    exact hA.symm

/-- Hartshorne's pointwise unramifiedness is formal unramifiedness, for morphisms locally of
finite type. -/
lemma hartshorneUnramified_iff_formallyUnramified [LocallyOfFiniteType f] :
    HartshorneUnramified f ↔ FormallyUnramified f := by
  constructor
  · intro h
    exact HasRingHomProperty.of_stalkMap RingHom.FormallyUnramified.ofLocalizationPrime
      fun x => (formallyUnramified_stalkMap_iff f x).2 (h x)
  · intro _ x
    exact (formallyUnramified_stalkMap_iff f x).1 (FormallyUnramified.stalkMap f x)

/-- The étale criteria of Hartshorne III Exercise 10.3, for an arbitrary morphism locally of
finite presentation. -/
theorem etale_tfae_of_locallyOfFinitePresentation [LocallyOfFinitePresentation f] :
    List.TFAE [Etale f, SmoothOfRelativeDimension 0 f,
      Flat f ∧ IsZero (relativeDifferentials f), Flat f ∧ HartshorneUnramified f] := by
  tfae_have 1 ↔ 2 := Etale.iff_smoothOfRelativeDimension_zero f
  tfae_have 1 ↔ 3 := by
    rw [Etale.iff_flat_and_formallyUnramified, isZero_relativeDifferentials_iff_formallyUnramified]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, inferInstance⟩⟩
  tfae_have 3 ↔ 4 := by
    rw [isZero_relativeDifferentials_iff_formallyUnramified,
      hartshorneUnramified_iff_formallyUnramified]
  tfae_finish

/-- **Hartshorne III Exercise 10.3.** Let `f : X → Y` be a morphism of schemes of finite type
over a field `k`. The following are equivalent: `f` is étale; `f` is smooth of relative
dimension zero; `f` is flat and `Ω_{X/Y} = 0`; `f` is flat and unramified in Hartshorne's
pointwise sense. -/
theorem etale_tfae_finiteTypeOverField {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}
    (hX : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (hY : LocallyOfFiniteType Y.hom ∧ QuasiCompact Y.hom) (f : X ⟶ Y) :
    List.TFAE [Etale f.left, SmoothOfRelativeDimension 0 f.left,
      Flat f.left ∧ IsZero (relativeDifferentials f.left),
      Flat f.left ∧ HartshorneUnramified f.left] := by
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w f]; exact hX.1
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : LocallyOfFiniteType Y.hom := hY.1
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  exact etale_tfae_of_locallyOfFinitePresentation f.left

end Hartshorne
