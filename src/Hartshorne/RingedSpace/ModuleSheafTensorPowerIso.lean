/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.PicardGroup
import Hartshorne.Scheme.SheafTensorOperations

/-!
# Arithmetic of tensor powers of module sheaves

Let `(X, 𝒪_X)` be a ringed space, given by a topological space `X` and a sheaf `R` of commutative
rings on `X`, and let `T^r F` be the `r`-th tensor power `Hartshorne.moduleSheafTensorPower r F`
of an `𝒪_X`-module `F` (the sheafification of `U ↦ ⨂^r F(U)`). We compare tensor powers with
iterated tensor products `Hartshorne.moduleSheafTensor`:

* `moduleSheafTensorPowerZeroIso`: `T^0 F ≅ 𝒪_X`;
* `moduleSheafTensorPowerSuccIso`: `T^{n+1} F ≅ T^n F ⊗ F`, `f₁ ⊗ ⋯ ⊗ f_{n+1} ↦
  (f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f_{n+1}`;
* `moduleSheafTensorPowerAddIso`: `T^{a+b} F ≅ T^a F ⊗ T^b F`;
* `moduleSheafTensorPowerMulIso`: `T^n (T^m F) ≅ T^{mn} F`;
* `isInvertible_moduleSheafTensorPower`: tensor powers of an invertible sheaf are invertible.

Morphisms out of `T^n F ⊗ F` are built from `(n+1)`-multilinear maps `β` by currying the last
variable into `ℋom(F, H)` (`tensorPowerSnocDesc`), and are determined by their values on the
elements `(f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f` (`tensorPowerSnoc_hom_ext`).
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

private lemma tp_map_map (A : 𝓜) {U V W : Opens X} (i : V ≤ U) (j : W ≤ V)
    (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE j).op (A.val.presheaf.map (homOfLE i).op x) =
      A.val.presheaf.map (homOfLE (j.trans i)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

private lemma tp_map_id (A : 𝓜) {U : Opens X} (x : Γ(A, U)) :
    A.val.presheaf.map (homOfLE (le_refl U)).op x = x := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

private lemma tp_modules_hom_ext {A B : 𝓜} {f g : A ⟶ B}
    (h : ∀ U : Opens X, sectionsMap f U = sectionsMap g U) : f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact ConcreteCategory.congr_hom (h U.unop) x

section TensorPowerIso

variable {F H : 𝓜}

/-- Two morphisms out of a tensor power `T^r F` agreeing on all elements `f₁ ⊗ ⋯ ⊗ fᵣ` are
equal. -/
lemma moduleSheafTensorPower_hom_ext {r : ℕ} {φ ψ : moduleSheafTensorPower r F ⟶ H}
    (h : ∀ (U : Opens X) (m : Fin r → Γ(F, U)),
      sectionsMap φ U ((moduleSheafTensorPowerMultilinear r F).app (op U) m) =
        sectionsMap ψ U ((moduleSheafTensorPowerMultilinear r F).app (op U) m)) : φ = ψ := by
  apply (moduleSheafTensorPowerHomEquiv r F H).injective
  rw [moduleSheafTensorPowerHomEquiv_apply, moduleSheafTensorPowerHomEquiv_apply]
  ext U m
  exact h U.unop m

/-- The morphism out of `T^r F` attached to a multilinear map sends `f₁ ⊗ ⋯ ⊗ fᵣ` to
`β(f₁, …, fᵣ)`. -/
lemma moduleSheafTensorPowerHomEquiv_symm_tprod {r : ℕ} (β : ModuleSheafMultilinear r F H)
    (U : Opens X) (m : Fin r → Γ(F, U)) :
    sectionsMap ((moduleSheafTensorPowerHomEquiv r F H).symm β) U
        ((moduleSheafTensorPowerMultilinear r F).app (op U) m) = β.app (op U) m := by
  have := congrArg (fun γ : ModuleSheafMultilinear r F H => γ.app (op U) m)
    ((moduleSheafTensorPowerHomEquiv_apply
      ((moduleSheafTensorPowerHomEquiv r F H).symm β)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorPowerHomEquiv r F H) β))
  exact this

variable {n : ℕ}

/-- For an `(n+1)`-multilinear `β` and sections `m₁, …, mₙ` of `F` over `U`, the local morphism
`f ↦ β(m₁, …, mₙ, f)` of `ℋom(F, H)` over `U`. -/
noncomputable def snocHomSection (β : ModuleSheafMultilinear (n + 1) F H) {U : Opens X}
    (m : Fin n → Γ(F, U)) : Γ(moduleSheafHom F H, U) :=
  moduleSheafHomMk
    (fun V h => (β.app (op V)).curryRight (fun k => F.val.presheaf.map (homOfLE h).op (m k)))
    (fun V V' hV i x => by
      change β.app (op V') (Fin.snoc (fun k => F.val.presheaf.map (homOfLE (i.trans hV)).op (m k))
          (F.val.presheaf.map (homOfLE i).op x)) =
        H.val.map (homOfLE i).op (β.app (op V)
          (Fin.snoc (fun k => F.val.presheaf.map (homOfLE hV).op (m k)) x))
      rw [β.naturality]
      have hq : (fun k => F.val.presheaf.map (homOfLE (i.trans hV)).op (m k)) =
          (⇑(F.val.map (homOfLE i).op)) ∘
            (fun k => F.val.presheaf.map (homOfLE hV).op (m k)) :=
        funext fun k => (tp_map_map F hV i (m k)).symm
      rw [hq]
      exact congrArg _ (Fin.comp_snoc _ _ x).symm)

lemma snocHomSection_eval (β : ModuleSheafMultilinear (n + 1) F H) {U : Opens X}
    (m : Fin n → Γ(F, U)) {V : Opens X} (h : V ≤ U) (x : Γ(F, V)) :
    moduleSheafHomEval (snocHomSection β m) h x =
      β.app (op V) (Fin.snoc (fun k => F.val.presheaf.map (homOfLE h).op (m k)) x) := rfl

/-- The `n`-multilinear morphism `F^n → ℋom(F, H)` obtained from an `(n+1)`-multilinear morphism
by currying the last variable. -/
noncomputable def snocHomMultilinear (β : ModuleSheafMultilinear (n + 1) F H) :
    ModuleSheafMultilinear n F (moduleSheafHom F H) where
  app U :=
    { toFun := fun m => snocHomSection β (U := U.unop) m
      map_update_add' := fun (m : Fin n → Γ(F, U.unop)) j (a b : Γ(F, U.unop)) =>
        moduleSheafHomEval_ext fun V h => LinearMap.ext fun x => by
        change β.app (op V) (Fin.snoc (fun k => F.val.presheaf.map (homOfLE h).op
            (Function.update m j (a + b) k)) x) =
          β.app (op V) (Fin.snoc (fun k => F.val.presheaf.map (homOfLE h).op
            (Function.update m j a k)) x) +
          β.app (op V) (Fin.snoc (fun k => F.val.presheaf.map (homOfLE h).op
            (Function.update m j b k)) x)
        have e : ∀ c : Γ(F, U.unop), (fun k => F.val.presheaf.map (homOfLE h).op
            (Function.update m j c k)) = Function.update
              (fun k => F.val.presheaf.map (homOfLE h).op (m k)) j
              (F.val.presheaf.map (homOfLE h).op c) := fun c => by
          funext k
          exact Function.apply_update (fun _ => F.val.presheaf.map (homOfLE h).op) m j c k
        rw [e, e, e, map_add]
        exact (β.app (op V)).curryRight.map_update_add _ j _ _ |> fun h' =>
          LinearMap.congr_fun h' x
      map_update_smul' := fun (m : Fin n → Γ(F, U.unop)) j r (a : Γ(F, U.unop)) =>
        moduleSheafHomEval_ext fun V h =>
          LinearMap.ext fun x => by
        change β.app (op V) (Fin.snoc (fun k => F.val.presheaf.map (homOfLE h).op
            (Function.update m j (r • a) k)) x) =
          R.obj.map (homOfLE h).op r • β.app (op V) (Fin.snoc (fun k =>
            F.val.presheaf.map (homOfLE h).op (Function.update m j a k)) x)
        have e : ∀ c : Γ(F, U.unop), (fun k => F.val.presheaf.map (homOfLE h).op
            (Function.update m j c k)) = Function.update
              (fun k => F.val.presheaf.map (homOfLE h).op (m k)) j
              (F.val.presheaf.map (homOfLE h).op c) := fun c => by
          funext k
          exact Function.apply_update (fun _ => F.val.presheaf.map (homOfLE h).op) m j c k
        rw [e, e]
        have hs : F.val.presheaf.map (homOfLE h).op (r • a) =
            R.obj.map (homOfLE h).op r • F.val.presheaf.map (homOfLE h).op a :=
          F.val.map_smul (homOfLE h).op r a
        rw [hs]
        exact LinearMap.congr_fun ((β.app (op V)).curryRight.map_update_smul _ j _ _) x }
  naturality {U V} i m := moduleSheafHomEval_ext fun W h => LinearMap.ext fun x => by
    change β.app (op W) (Fin.snoc (fun k => F.val.presheaf.map (homOfLE (h.trans
        (leOfHom i.unop))).op (m k)) x) =
      β.app (op W) (Fin.snoc (fun k => F.val.presheaf.map (homOfLE h).op
        (F.val.presheaf.map (homOfLE (leOfHom i.unop)).op (m k))) x)
    congr 2
    funext k
    exact (tp_map_map F _ h (m k)).symm

/-- The morphism `T^n F ⊗ F ⟶ H`, `(f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f ↦ β(f₁, …, fₙ, f)`, attached to an
`(n+1)`-multilinear morphism `β`. -/
noncomputable def tensorPowerSnocDesc (β : ModuleSheafMultilinear (n + 1) F H) :
    @Quiver.Hom 𝓜 _ (moduleSheafTensor (moduleSheafTensorPower n F) F) H :=
  (moduleSheafTensorHomEquiv _ _ _).symm
    { app U := (homUncurry ((moduleSheafTensorPowerHomEquiv n F _).symm
        (snocHomMultilinear β))).app U |>.flip
      naturality i t c := (homUncurry ((moduleSheafTensorPowerHomEquiv n F _).symm
        (snocHomMultilinear β))).naturality i c t }

/-- The morphism `tensorPowerSnocDesc β` sends `(f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f` to `β(f₁, …, fₙ, f)`. -/
lemma tensorPowerSnocDesc_tmul (β : ModuleSheafMultilinear (n + 1) F H) {U : Opens X}
    (m : Fin n → Γ(F, U)) (x : Γ(F, U)) :
    sectionsMap (tensorPowerSnocDesc β) U
      ((moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op U)
        ((moduleSheafTensorPowerMultilinear n F).app (op U) m) x) =
      β.app (op U) (Fin.snoc m x) := by
  refine (moduleSheafTensorHomEquiv_symm_tmul _ _ x).trans ?_
  change moduleSheafHomEval (sectionsMap ((moduleSheafTensorPowerHomEquiv n F _).symm
    (snocHomMultilinear β)) U ((moduleSheafTensorPowerMultilinear n F).app (op U) m))
      (le_refl U) x = _
  rw [moduleSheafTensorPowerHomEquiv_symm_tprod]
  change β.app (op U) (Fin.snoc (fun k => F.val.presheaf.map (homOfLE (le_refl U)).op (m k)) x) = _
  simp_rw [tp_map_id]

/-- Two morphisms out of `T^n F ⊗ F` agreeing on all elements `(f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f` are equal. -/
lemma tensorPowerSnoc_hom_ext
    {φ ψ : @Quiver.Hom 𝓜 _ (moduleSheafTensor (moduleSheafTensorPower n F) F) H}
    (h : ∀ (U : Opens X) (m : Fin n → Γ(F, U)) (x : Γ(F, U)),
      sectionsMap φ U ((moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op U)
        ((moduleSheafTensorPowerMultilinear n F).app (op U) m) x) =
      sectionsMap ψ U ((moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op U)
        ((moduleSheafTensorPowerMultilinear n F).app (op U) m) x)) : φ = ψ := by
  let flipB : ∀ (χ : @Quiver.Hom 𝓜 _ (moduleSheafTensor (moduleSheafTensorPower n F) F) H),
      ModuleSheafBilinear F (moduleSheafTensorPower n F) H := fun χ =>
    { app U := (moduleSheafTensorHomEquiv _ _ H χ).app U |>.flip
      naturality i c t := (moduleSheafTensorHomEquiv _ _ H χ).naturality i t c }
  have hcurry : bilinearCurry (flipB φ) = bilinearCurry (flipB ψ) := by
    refine moduleSheafTensorPower_hom_ext fun U m => moduleSheafHomEval_ext fun V hV =>
      LinearMap.ext fun x => ?_
    change sectionsMap φ V ((moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op V)
        ((moduleSheafTensorPower n F).val.map (homOfLE hV).op
          ((moduleSheafTensorPowerMultilinear n F).app (op U) m)) x) =
      sectionsMap ψ V ((moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op V)
        ((moduleSheafTensorPower n F).val.map (homOfLE hV).op
          ((moduleSheafTensorPowerMultilinear n F).app (op U) m)) x)
    have hn : (moduleSheafTensorPower n F).val.map (homOfLE hV).op
        ((moduleSheafTensorPowerMultilinear n F).app (op U) m) =
        (moduleSheafTensorPowerMultilinear n F).app (op V)
          (fun k => F.val.map (homOfLE hV).op (m k)) :=
      (moduleSheafTensorPowerMultilinear n F).naturality _ m
    erw [hn]
    exact h V _ x
  have hflip : flipB φ = flipB ψ := bilinearCurryEquiv.injective hcurry
  apply (moduleSheafTensorHomEquiv _ _ H).injective
  ext U t c
  exact congrArg (fun β : ModuleSheafBilinear F (moduleSheafTensorPower n F) H => β.app U c t) hflip

variable (n F) in
/-- The `(n+1)`-multilinear map `(f₁, …, f_{n+1}) ↦ (f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f_{n+1}`. -/
noncomputable def tensorPowerSuccMultilinear :
    ModuleSheafMultilinear (n + 1) F (moduleSheafTensor (moduleSheafTensorPower n F) F) where
  app U := MultilinearMap.uncurryRight
    (((moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app U).compMultilinearMap
      ((moduleSheafTensorPowerMultilinear n F).app U))
  naturality i m := by
    simp only [MultilinearMap.uncurryRight_apply, LinearMap.compMultilinearMap_apply]
    rw [(moduleSheafTensorBilinear _ F).naturality i,
      (moduleSheafTensorPowerMultilinear n F).naturality i]
    rfl

variable (n F) in
/-- **Successor tensor powers.** `T^{n+1} F ≅ T^n F ⊗ F`, `f₁ ⊗ ⋯ ⊗ f_{n+1} ↦
(f₁ ⊗ ⋯ ⊗ fₙ) ⊗ f_{n+1}`. -/
noncomputable def moduleSheafTensorPowerSuccIso :
    @Iso 𝓜 _ (moduleSheafTensorPower (n + 1) F)
      (moduleSheafTensor (moduleSheafTensorPower n F) F) where
  hom := (moduleSheafTensorPowerHomEquiv _ _ _).symm (tensorPowerSuccMultilinear F n)
  inv := tensorPowerSnocDesc (moduleSheafTensorPowerMultilinear (n + 1) F)
  hom_inv_id := by
    refine moduleSheafTensorPower_hom_ext fun U m => ?_
    change sectionsMap (tensorPowerSnocDesc (moduleSheafTensorPowerMultilinear (n + 1) F)) U
      (sectionsMap ((moduleSheafTensorPowerHomEquiv _ _ _).symm
        (tensorPowerSuccMultilinear F n)) U _) = _
    rw [moduleSheafTensorPowerHomEquiv_symm_tprod]
    change sectionsMap (tensorPowerSnocDesc (moduleSheafTensorPowerMultilinear (n + 1) F)) U
      ((moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op U)
        ((moduleSheafTensorPowerMultilinear n F).app (op U) (Fin.init m)) (m (Fin.last n))) = _
    rw [tensorPowerSnocDesc_tmul]
    exact congrArg _ (Fin.snoc_init_self m)
  inv_hom_id := by
    refine tensorPowerSnoc_hom_ext fun U m x => ?_
    change sectionsMap ((moduleSheafTensorPowerHomEquiv _ _ _).symm
        (tensorPowerSuccMultilinear F n)) U
      (sectionsMap (tensorPowerSnocDesc (moduleSheafTensorPowerMultilinear (n + 1) F)) U _) = _
    rw [tensorPowerSnocDesc_tmul]
    refine (moduleSheafTensorPowerHomEquiv_symm_tprod _ U _).trans ?_
    change (moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op U)
        ((moduleSheafTensorPowerMultilinear n F).app (op U)
          (Fin.init (Fin.snoc (α := fun _ => Γ(F, U)) m x)))
          (Fin.snoc (α := fun _ => Γ(F, U)) m x (Fin.last n)) =
      (moduleSheafTensorBilinear (moduleSheafTensorPower n F) F).app (op U)
        ((moduleSheafTensorPowerMultilinear n F).app (op U) m) x
    rw [Fin.init_snoc, Fin.snoc_last]

variable (F) in
/-- The `0`-multilinear map `F^0 → 𝒪_X` with value `1`. -/
noncomputable def tensorPowerZeroMultilinear : ModuleSheafMultilinear 0 F (structureModule R) where
  app U := MultilinearMap.constOfIsEmpty _ _ (1 : (R.obj ⋙ forget₂ CommRingCat RingCat).obj U)
  naturality i _ := map_one ((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom

variable (F) in
/-- The empty tensor `1 ∈ T^0 F` over `U`. -/
noncomputable abbrev tensorPowerZeroSection (U : Opens X) : Γ(moduleSheafTensorPower 0 F, U) :=
  (moduleSheafTensorPowerMultilinear 0 F).app (op U) (fun k => k.elim0)

lemma tensorPowerZeroSection_restrict {U V : Opens X} (i : V ≤ U) :
    (moduleSheafTensorPower 0 F).val.presheaf.map (homOfLE i).op (tensorPowerZeroSection F U) =
      tensorPowerZeroSection F V := by
  refine ((moduleSheafTensorPowerMultilinear 0 F).naturality (homOfLE i).op _).trans ?_
  congr 1
  funext k
  exact k.elim0

variable (F) in
/-- The map `𝒪_X ⟶ T^0 F`, `r ↦ r · 1`. -/
noncomputable def tensorPowerZeroInv : structureModule R ⟶ moduleSheafTensorPower 0 F :=
  modulesHomMk (fun U => LinearMap.toSpanSingleton 𝒪(U) _ (tensorPowerZeroSection F U))
    (fun U V i r => by
      change (show 𝒪(V) from R.obj.map (homOfLE i).op (show 𝒪(U) from r)) •
          tensorPowerZeroSection F V =
        (moduleSheafTensorPower 0 F).val.presheaf.map (homOfLE i).op
          ((show 𝒪(U) from r) • tensorPowerZeroSection F U)
      refine Eq.trans ?_ ((moduleSheafTensorPower 0 F).val.map_smul (homOfLE i).op
        (show 𝒪(U) from r) _).symm
      exact congrArg _ (tensorPowerZeroSection_restrict i).symm)

variable (F) in
/-- **The zeroth tensor power.** `T^0 F ≅ 𝒪_X`. -/
noncomputable def moduleSheafTensorPowerZeroIso :
    @Iso 𝓜 _ (moduleSheafTensorPower 0 F) (structureModule R) where
  hom := (moduleSheafTensorPowerHomEquiv _ _ _).symm (tensorPowerZeroMultilinear F)
  inv := tensorPowerZeroInv F
  hom_inv_id := by
    refine moduleSheafTensorPower_hom_ext fun U m => ?_
    change sectionsMap (tensorPowerZeroInv F) U
      (sectionsMap ((moduleSheafTensorPowerHomEquiv _ _ _).symm
        (tensorPowerZeroMultilinear F)) U _) = _
    rw [moduleSheafTensorPowerHomEquiv_symm_tprod]
    change (1 : 𝒪(U)) • tensorPowerZeroSection F U =
      (moduleSheafTensorPowerMultilinear 0 F).app (op U) m
    rw [one_smul]
    exact congrArg ((moduleSheafTensorPowerMultilinear 0 F).app (op U)) (funext fun k => k.elim0)
  inv_hom_id := by
    refine tp_modules_hom_ext fun U => ?_
    ext r
    change sectionsMap ((moduleSheafTensorPowerHomEquiv _ _ _).symm
        (tensorPowerZeroMultilinear F)) U ((show 𝒪(U) from r) • tensorPowerZeroSection F U) = r
    have hs := (((moduleSheafTensorPowerHomEquiv _ _ _).symm
        (tensorPowerZeroMultilinear F)).val.app (op U)).hom.map_smul (show 𝒪(U) from r)
        (tensorPowerZeroSection F U)
    refine hs.trans ?_
    have h1 := moduleSheafTensorPowerHomEquiv_symm_tprod (tensorPowerZeroMultilinear F) U
      (fun k => k.elim0)
    refine (congrArg (fun y => (show 𝒪(U) from r) • y) h1).trans ?_
    exact mul_one (show 𝒪(U) from r)

variable (F) in
/-- **Sums of exponents.** `T^{a+b} F ≅ T^a F ⊗ T^b F`. -/
noncomputable def moduleSheafTensorPowerAddIso (a : ℕ) : ∀ b : ℕ,
    @Iso 𝓜 _ (moduleSheafTensorPower (a + b) F)
      (moduleSheafTensor (moduleSheafTensorPower a F) (moduleSheafTensorPower b F))
  | 0 => (moduleSheafUnitTensor (moduleSheafTensorPower a F)).symm ≪≫
      moduleSheafTensorComm _ _ ≪≫
      moduleSheafTensorIsoOfIso (Iso.refl _) (moduleSheafTensorPowerZeroIso F).symm
  | b + 1 => moduleSheafTensorPowerSuccIso F (a + b) ≪≫
      moduleSheafTensorIsoOfIso (moduleSheafTensorPowerAddIso a b) (Iso.refl F) ≪≫
      moduleSheafTensorAssoc _ _ _ ≪≫
      moduleSheafTensorIsoOfIso (Iso.refl _) (moduleSheafTensorPowerSuccIso F b).symm

variable (F) in
/-- **Products of exponents.** `T^n (T^m F) ≅ T^{mn} F`. -/
noncomputable def moduleSheafTensorPowerMulIso (m : ℕ) : ∀ n : ℕ,
    @Iso 𝓜 _ (moduleSheafTensorPower n (moduleSheafTensorPower m F))
      (moduleSheafTensorPower (m * n) F)
  | 0 => moduleSheafTensorPowerZeroIso _ ≪≫ (moduleSheafTensorPowerZeroIso F).symm
  | n + 1 => moduleSheafTensorPowerSuccIso _ n ≪≫
      moduleSheafTensorIsoOfIso (moduleSheafTensorPowerMulIso m n) (Iso.refl _) ≪≫
      (moduleSheafTensorPowerAddIso F (m * n) m).symm

/-- Invertibility is invariant under isomorphism. -/
lemma IsInvertible.of_iso {L L' : 𝓜} (hL : IsInvertible L) (α : L ≅ L') : IsInvertible L' :=
  isLocallyFreeOfRank_of_isLocalFrame fun x => by
    obtain ⟨U, e, hx, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hL x
    exact ⟨U, _, hx, he.of_iso α⟩

/-- **Tensor powers of an invertible sheaf are invertible.** -/
theorem isInvertible_moduleSheafTensorPower {L : 𝓜} (hL : IsInvertible L) :
    ∀ n : ℕ, IsInvertible (moduleSheafTensorPower n L)
  | 0 => structureModule_isInvertible.of_iso (moduleSheafTensorPowerZeroIso L).symm
  | n + 1 => (isInvertible_moduleSheafTensor (isInvertible_moduleSheafTensorPower hL n) hL).of_iso
      (moduleSheafTensorPowerSuccIso L n).symm

end TensorPowerIso

end Ringed

end Hartshorne
