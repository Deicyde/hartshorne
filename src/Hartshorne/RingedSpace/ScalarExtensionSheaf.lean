/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SheafTensorOperations
import Hartshorne.RingedSpace.PicardGroup
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The module sheaf `𝒪_X ⊗_A N`

Let `(X, 𝒪_X)` be a ringed space, given by a sheaf `R` of commutative rings on `X`, and let
`φ : A → 𝒪_X(X)` be a ring map. For an `A`-module `N` the presheaf of `𝒪_X`-modules
`V ↦ 𝒪_X(V) ⊗_A N` (`Hartshorne.Ringed.ScalarExtension.presheaf`) is functorial in `N`. When `N`
is finite free it is a sheaf (`Hartshorne.Ringed.ScalarExtension.sheaf`): a basis `b` of `N`
identifies its sections over `V` with `ι`-tuples of sections of `𝒪_X` over `V`, naturally in `V`.
It is then locally free of finite rank
(`Hartshorne.Ringed.ScalarExtension.isFiniteLocallyFree_sheaf`), the sections `1 ⊗ bᵢ` being a
global frame.

Morphisms `(𝒪_X ⊗_A N)|_W ⟶ G|_W` correspond to `A`-linear maps `N → G(W)` by evaluation at
`1 ⊗ n` (`Hartshorne.Ringed.ScalarExtension.overHomEquiv`), compatibly with precomposition
(`Hartshorne.Ringed.ScalarExtension.overHomEquiv_comp`); globally, an `A`-linear map
`N → G(X)` gives a morphism `𝒪_X ⊗_A N ⟶ G` (`Hartshorne.Ringed.ScalarExtension.homOfLinear`).
These are the tools for sheafifying a complex of finite free `A`-modules, such as a Koszul
complex, and computing `ℋom` out of it on sections.
-/

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Ringed

namespace ScalarExtension

section Linear

variable {A S T : Type u} [CommRing A] [CommRing S] [CommRing T] (φ : A →+* S) (ψ : A →+* T)
  (ρ : S →+* T) (h : ρ.comp φ = ψ)
include h

/-- A ring map `ρ : S → T` under `A`, as an `A`-linear map. -/
noncomputable def ringHomLinear :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) →ₗ[A]
      (ModuleCat.restrictScalars ψ).obj (ModuleCat.of T T) where
  toFun s := ρ s
  map_add' := map_add ρ
  map_smul' a s := by
    change ρ (@HMul.hMul S S S _ (φ a) s) = @HMul.hMul T T T _ (ψ a) (ρ s)
    rw [map_mul, ← h]; rfl

variable (N : ModuleCat.{u} A)

/-- The `ρ`-semilinear map `S ⊗_A N → T ⊗_A N`, `s ⊗ n ↦ ρ s ⊗ n`. -/
noncomputable def semilinear :
    (ModuleCat.extendScalars φ).obj N →ₛₗ[ρ] (ModuleCat.extendScalars ψ).obj N where
  toFun := TensorProduct.map (ringHomLinear φ ψ ρ h) LinearMap.id
  map_add' := map_add _
  map_smul' s t := by
    induction t using TensorProduct.induction_on with
    | zero => exact (congrArg _ (smul_zero s)).trans ((map_zero _).trans (smul_zero _).symm)
    | tmul a m =>
      change ρ (@HMul.hMul S S S _ s a) ⊗ₜ[A, ψ] m = ρ s • (ρ a ⊗ₜ[A, ψ] m)
      rw [ModuleCat.ExtendScalars.smul_tmul, map_mul]
    | add t t' ht ht' =>
      exact (congrArg _ (smul_add s t t')).trans ((map_add _ _ _).trans
        ((congrArg₂ (· + ·) ht ht').trans ((smul_add _ _ _).symm.trans
          (congrArg _ (map_add _ t t').symm))))

/-- `semilinear` on elementary tensors. -/
lemma semilinear_tmul (s : S) (m : N) :
    semilinear φ ψ ρ h N (s ⊗ₜ[A, φ] m) = ρ s ⊗ₜ[A, ψ] m := rfl

end Linear

/-- The extension-of-scalars adjunction on elementary tensors: the adjoint of `k` sends
`s ⊗ m` to `s • k m`. -/
lemma homEquiv_symm_tmul {A S : Type u} [CommRing A] [CommRing S]
    (φ : A →+* S) {M : ModuleCat.{u} A} {N : ModuleCat.{u} S}
    (k : M ⟶ (ModuleCat.restrictScalars φ).obj N) (s : S) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm k (s ⊗ₜ[A, φ] m) =
      s • (show N from k m) := by
  have h1 : ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm k ((1 : S) ⊗ₜ[A, φ] m) =
      k m := by
    have := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
      (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm k) m
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have e : s ⊗ₜ[A, φ] m = s • ((1 : S) ⊗ₜ[A, φ] m : (ModuleCat.extendScalars φ).obj M) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [e, map_smul, h1]

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {A : Type u} [CommRing A] (φ : A →+* R.obj.obj (op ⊤))

/-- The ring map `A → 𝒪_X(V)`: the structure map `A → 𝒪_X(X)` followed by restriction. -/
noncomputable def baseMap (V : Opens X) : A →+* R.obj.obj (op V) :=
  (R.obj.map (homOfLE le_top : V ⟶ ⊤).op).hom.comp φ

/-- The structure maps `A → 𝒪_X(V)` are compatible with restriction. -/
lemma baseMap_comp {U V : Opens X} (i : op U ⟶ op V) :
    (R.obj.map i).hom.comp (baseMap φ U) = baseMap φ V := by
  ext a
  change (R.obj.map (homOfLE le_top : U ⟶ ⊤).op ≫ R.obj.map i) (φ a) =
    R.obj.map (homOfLE le_top : V ⟶ ⊤).op (φ a)
  rw [← Functor.map_comp]
  rfl

variable (N : ModuleCat.{u} A)

/-- The presheaf of `𝒪_X`-modules `V ↦ 𝒪_X(V) ⊗_A N`. -/
noncomputable def presheaf : PresheafOfModules.{u} (ringCatSheafOf R).obj :=
  SheafTensorOperations.presheafOfSemilinear (R := R)
    (fun V => (ModuleCat.extendScalars (baseMap φ V.unop)).obj N)
    (fun {U V} i => semilinear _ _ (R.obj.map i).hom (baseMap_comp φ i) N)
    (fun U t => by
      induction t using TensorProduct.induction_on with
      | zero => exact map_zero _
      | tmul a m =>
        change (R.obj.map (𝟙 U) a) ⊗ₜ[A, (baseMap φ U.unop)] m = _
        rw [R.obj.map_id]; rfl
      | add t t' ht ht' => exact (map_add _ _ _).trans (congrArg₂ (· + ·) ht ht'))
    (fun i j t => by
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a m =>
        change (R.obj.map (i ≫ j) a) ⊗ₜ[A, _] m = (R.obj.map j (R.obj.map i a)) ⊗ₜ[A, _] m
        rw [R.obj.map_comp]; rfl
      | add t t' ht ht' => simp only [map_add, ht, ht'])

/-- Restriction in `𝒪_X(-) ⊗_A N` on elementary tensors. -/
lemma presheaf_map_tmul {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (a : R.obj.obj U) (m : N) :
    (presheaf φ N).map i (a ⊗ₜ[A, baseMap φ U.unop] m) =
      (R.obj.map i a) ⊗ₜ[A, baseMap φ V.unop] m :=
  rfl

variable {N} in
/-- Functoriality of `N ↦ 𝒪_X(-) ⊗_A N`. -/
noncomputable def presheafMap {N' : ModuleCat.{u} A} (g : N ⟶ N') :
    presheaf φ N ⟶ presheaf φ N' where
  app U := (ModuleCat.extendScalars (baseMap φ U.unop)).map g
  naturality {U V} i := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul a m => rfl
    | add t t' ht ht' =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ht ht').trans (map_add _ _ _).symm)

/-- `presheafMap` on elementary tensors. -/
lemma presheafMap_app_tmul {N' : ModuleCat.{u} A} (g : N ⟶ N') (U : (Opens X)ᵒᵖ) (a : R.obj.obj U)
    (m : N) :
    (presheafMap φ g).app U (a ⊗ₜ[A, baseMap φ U.unop] m) = a ⊗ₜ[A, baseMap φ U.unop] g m :=
  rfl

/-- The functor `N ↦ (V ↦ 𝒪_X(V) ⊗_A N)`. -/
noncomputable def functor : ModuleCat.{u} A ⥤ PresheafOfModules.{u} (ringCatSheafOf R).obj where
  obj N := presheaf φ N
  map g := presheafMap φ g
  map_id N := by
    ext U t
    exact congrArg (fun k => k.hom t) ((ModuleCat.extendScalars (baseMap φ U.unop)).map_id N)
  map_comp g g' := by
    ext U t
    exact congrArg (fun k => k.hom t)
      ((ModuleCat.extendScalars (baseMap φ U.unop)).map_comp g g')

/-- A presheaf of abelian groups whose sections are naturally in bijection with `ι`-tuples of
sections of `𝒪_X` is a sheaf. -/
theorem isSheaf_of_pi_bijection {F : TopCat.Presheaf AddCommGrpCat.{u} X} {ι : Type u}
    (e : ∀ V : Opens X, (ι → R.obj.obj (op V)) → F.obj (op V))
    (he : ∀ V, Function.Bijective (e V))
    (hnat : ∀ {U V : Opens X} (i : U ⟶ V) (a : ι → R.obj.obj (op V)),
      F.map i.op (e V a) = e U (fun j => R.obj.map i.op (a j))) :
    F.IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ U sf hsf
  let a : ∀ k, ι → R.obj.obj (op (U k)) := fun k => (Equiv.ofBijective _ (he _)).symm (sf k)
  have ha : ∀ k, e _ (a k) = sf k := fun k => (Equiv.ofBijective _ (he _)).apply_symm_apply _
  have hcomp : ∀ j, TopCat.Presheaf.IsCompatible R.obj U (fun k => a k j) := by
    intro j k l
    have := hsf k l
    rw [← ha k, ← ha l, hnat, hnat] at this
    exact congrFun ((he _).1 this) j
  choose s hs hsu using fun j => TopCat.Sheaf.existsUnique_gluing R U _ (hcomp j)
  refine ⟨e _ s, fun k => ?_, fun t ht => ?_⟩
  · rw [hnat, ← ha k]
    congr 1
    funext j
    exact hs j k
  · obtain ⟨t', rfl⟩ := (he _).2 t
    congr 1
    funext j
    apply hsu j
    intro k
    have := ht k
    change F.map _ (e _ t') = sf k at this
    rw [hnat, ← ha k] at this
    exact congrFun ((he _).1 this) j

section Basis

variable {ι : Type u} [Fintype ι] (b : Module.Basis ι A N)

/-- The map `(a_i) ↦ ∑ a_i ⊗ b_i` from `ι`-tuples of sections of `𝒪_X` over `V` to
`𝒪_X(V) ⊗_A N`, for a basis `b` of `N`. -/
noncomputable def basisMap (V : Opens X) (a : ι → R.obj.obj (op V)) : (presheaf φ N).obj (op V) :=
  ∑ i, a i ⊗ₜ[A, baseMap φ V] b i

omit [Fintype ι] in
/-- For a basis `b` of `N` indexed by a finite type, `(a_i) ↦ ∑ a_i ⊗ b_i` is a bijection
`M^ι → M ⊗_A N`. -/
lemma sum_tmul_bijective [Finite ι] {M : Type u} [AddCommGroup M] [Module A M] :
    Function.Bijective (fun a : ι → M => ∑ᶠ i, a i ⊗ₜ[A] b i) := by
  classical
  have := Fintype.ofFinite ι
  have h : (fun a : ι → M => ∑ᶠ i, a i ⊗ₜ[A] b i) =
      (TensorProduct.equivFinsuppOfBasisRight (M := M) b).symm ∘
        (Finsupp.equivFunOnFinite (α := ι) (M := M)).symm := by
    funext a
    rw [Function.comp_apply, TensorProduct.equivFinsuppOfBasisRight_symm_apply,
      Finsupp.sum_fintype, finsum_eq_sum_of_fintype]
    · rfl
    · intro i
      exact TensorProduct.zero_tmul _ _
  rw [h]
  exact (TensorProduct.equivFinsuppOfBasisRight (M := M) b).symm.bijective.comp
    (Finsupp.equivFunOnFinite (α := ι) (M := M)).symm.bijective

/-- For a basis `b` of `N`, `(a_i) ↦ ∑ a_i ⊗ b_i` is bijective. -/
lemma basisMap_bijective (V : Opens X) : Function.Bijective (basisMap φ N b V) := by
  have h := sum_tmul_bijective N b (M := (ModuleCat.restrictScalars (baseMap φ V)).obj
    (ModuleCat.of (R.obj.obj (op V)) (R.obj.obj (op V))))
  simp only [finsum_eq_sum_of_fintype] at h
  exact h

/-- `basisMap` commutes with restriction. -/
lemma presheaf_map_basisMap {U V : Opens X} (i : U ⟶ V) (a : ι → R.obj.obj (op V)) :
    (presheaf φ N).map i.op (basisMap φ N b V a) =
      basisMap φ N b U (fun j => R.obj.map i.op (a j)) := by
  simp only [basisMap, map_sum]
  rfl

include b in
/-- `𝒪_X(-) ⊗_A N` is a sheaf when `N` has a finite basis. -/
lemma isSheaf_of_basis : TopCat.Presheaf.IsSheaf (presheaf φ N).presheaf :=
  isSheaf_of_pi_bijection (basisMap φ N b) (basisMap_bijective φ N b)
    (fun i a => presheaf_map_basisMap φ N b i a)

end Basis

/-- The `𝒪_X`-module `𝒪_X ⊗_A N` for a finite free `A`-module `N`. -/
noncomputable def sheaf [Module.Free A N] [Module.Finite A N] :
    SheafOfModules.{u} (ringCatSheafOf R) where
  val := presheaf φ N
  isSheaf := isSheaf_of_basis φ N (Module.Free.chooseBasis A N)

variable {N} in
/-- Functoriality of `N ↦ 𝒪_X ⊗_A N` on finite free modules. -/
noncomputable def sheafMap [Module.Free A N] [Module.Finite A N] {N' : ModuleCat.{u} A}
    [Module.Free A N'] [Module.Finite A N'] (g : N ⟶ N') : sheaf φ N ⟶ sheaf φ N' :=
  ⟨presheafMap φ g⟩

variable {N} in
/-- `sheafMap` is functorial. -/
lemma sheafMap_comp [Module.Free A N] [Module.Finite A N] {N' N'' : ModuleCat.{u} A}
    [Module.Free A N'] [Module.Finite A N'] [Module.Free A N''] [Module.Finite A N'']
    (g : N ⟶ N') (g' : N' ⟶ N'') :
    sheafMap φ (g ≫ g') = sheafMap φ g ≫ sheafMap φ g' :=
  SheafOfModules.hom_ext ((functor φ).map_comp g g')

variable {N} in
/-- `sheafMap` of the zero map is zero. -/
lemma sheafMap_zero [Module.Free A N] [Module.Finite A N] {N' : ModuleCat.{u} A}
    [Module.Free A N'] [Module.Finite A N'] : sheafMap φ (0 : N ⟶ N') = 0 := by
  apply SheafOfModules.hom_ext
  ext V t
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul a m =>
    exact TensorProduct.tmul_zero (M := (ModuleCat.restrictScalars (baseMap φ V.unop)).obj
      (ModuleCat.of (R.obj.obj V) (R.obj.obj V))) _ _
  | add t t' ht ht' => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ht ht').trans (add_zero _))

/-- The sheaf `𝒪_X ⊗_A N` of a finite free `A`-module `N` is locally free of finite rank. -/
theorem isFiniteLocallyFree_sheaf [Module.Free A N] [Module.Finite A N] :
    IsFiniteLocallyFree (sheaf φ N) := by
  classical
  let b := (Module.Free.chooseBasis A N).reindex
    ((Fintype.equivFin _).trans Equiv.ulift.symm)
  let e : ULift.{u} (Fin (Fintype.card (Module.Free.ChooseBasisIndex A N))) →
      (sheaf φ N).val.presheaf.obj (op ⊤) :=
    fun i => show (presheaf φ N).obj (op ⊤) from (1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] b i
  have hframe : IsLocalFrame (sheaf φ N) ⊤ e := by
    intro V h
    have : ⇑(localFrameMap (sheaf φ N) e h) = basisMap φ N b V := by
      funext a
      rw [localFrameMap_apply]
      simp only [basisMap]
      refine Finset.sum_congr rfl fun i _ => ?_
      change a i • ((R.obj.map (homOfLE h).op 1) ⊗ₜ[A, baseMap φ V] b i) = _
      rw [map_one, ModuleCat.ExtendScalars.smul_tmul, mul_one]
    rw [this]
    exact basisMap_bijective φ N b V
  intro x
  exact ⟨⊤, trivial, _, nonempty_over_iso_free_of_isLocalFrame hframe⟩

section Hom

variable {N}

/-- Restriction `G(W) → G(V)` along `V ≤ W`, as an `A`-linear map. -/
noncomputable def resLinear (G : PresheafOfModules.{u} (ringCatSheafOf R).obj) {V W : Opens X}
    (h : V ≤ W) :
    (ModuleCat.restrictScalars (baseMap φ W)).obj (G.obj (op W)) ⟶
      (ModuleCat.restrictScalars (baseMap φ V)).obj (G.obj (op V)) :=
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars (baseMap φ W)).obj (G.obj (op W)))
      (Y := (ModuleCat.restrictScalars (baseMap φ V)).obj (G.obj (op V)))
    { toFun x := G.map (homOfLE h).op x
      map_add' := map_add _
      map_smul' a x := by
        change G.map _ (@HSMul.hSMul ((ringCatSheafOf R).obj.obj (op W)) (G.obj (op W))
            (G.obj (op W)) _ (baseMap φ W a) x) =
          @HSMul.hSMul ((ringCatSheafOf R).obj.obj (op V)) (G.obj (op V)) (G.obj (op V)) _
            (baseMap φ V a) (G.map (homOfLE h).op x)
        rw [PresheafOfModules.map_smul]
        congr 1
        exact congrArg (fun k => k a) (baseMap_comp φ (homOfLE h).op) }

/-- `resLinear` is restriction. -/
lemma resLinear_apply (G : PresheafOfModules.{u} (ringCatSheafOf R).obj) {V W : Opens X}
    (h : V ≤ W) (x : (ModuleCat.restrictScalars (baseMap φ W)).obj (G.obj (op W))) :
    resLinear φ G h x = G.map (homOfLE h).op x := rfl

/-- The morphism `𝒪_X(-) ⊗_A N ⟶ G` determined by an `A`-linear map `N → G(X)`. -/
noncomputable def homOfLinear (G : PresheafOfModules.{u} (ringCatSheafOf R).obj)
    (g : N ⟶ (ModuleCat.restrictScalars (baseMap φ ⊤)).obj (G.obj (op ⊤))) :
    presheaf φ N ⟶ G where
  app V := ((ModuleCat.extendRestrictScalarsAdj (baseMap φ V.unop)).homEquiv _ _).symm
    (g ≫ resLinear φ G (le_top : V.unop ≤ ⊤))
  naturality {V V'} i := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a m =>
      change ((ModuleCat.extendRestrictScalarsAdj (baseMap φ V'.unop)).homEquiv _ _).symm _
          ((R.obj.map i a) ⊗ₜ[A, baseMap φ V'.unop] m) =
        G.map i (((ModuleCat.extendRestrictScalarsAdj (baseMap φ V.unop)).homEquiv _ _).symm _
          (a ⊗ₜ[A, baseMap φ V.unop] m))
      erw [homEquiv_symm_tmul, homEquiv_symm_tmul, PresheafOfModules.map_smul]
      congr 1
      show resLinear φ G _ (g m) = G.map i (resLinear φ G _ (g m))
      rw [resLinear_apply, resLinear_apply, ← PresheafOfModules.map_comp_apply]
      rfl
    | add t t' ht ht' => simp only [map_add, ht, ht']

/-- `homOfLinear` on elementary tensors. -/
lemma homOfLinear_app_tmul (G : PresheafOfModules.{u} (ringCatSheafOf R).obj)
    (g : N ⟶ (ModuleCat.restrictScalars (baseMap φ ⊤)).obj (G.obj (op ⊤))) (V : (Opens X)ᵒᵖ)
    (a : R.obj.obj V) (m : N) :
    (homOfLinear φ G g).app V (a ⊗ₜ[A, baseMap φ V.unop] m) =
      a • (show G.obj V from G.map (homOfLE (le_top : V.unop ≤ ⊤)).op
        (show G.obj (op ⊤) from g m)) :=
  homEquiv_symm_tmul _ _ _ _

/-- Precomposing `homOfLinear` with `𝒪_X(-) ⊗_A g` corresponds to precomposing with `g`. -/
lemma presheafMap_comp_homOfLinear {N' : ModuleCat.{u} A}
    (G : PresheafOfModules.{u} (ringCatSheafOf R).obj) (g : N' ⟶ N)
    (c : N ⟶ (ModuleCat.restrictScalars (baseMap φ ⊤)).obj (G.obj (op ⊤))) :
    presheafMap φ g ≫ homOfLinear φ G c = homOfLinear φ G (g ≫ c) := by
  ext V t
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a m =>
    exact (homOfLinear_app_tmul φ G c V a (g m)).trans
      (homOfLinear_app_tmul φ G (g ≫ c) V a m).symm
  | add t t' ht ht' =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ht ht').trans (map_add _ _ _).symm)

/-- `homOfLinear` of the zero map is zero. -/
lemma homOfLinear_zero (G : PresheafOfModules.{u} (ringCatSheafOf R).obj) :
    homOfLinear φ G (0 : N ⟶ (ModuleCat.restrictScalars (baseMap φ ⊤)).obj (G.obj (op ⊤))) =
      0 := by
  ext V t
  induction t using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul a m =>
    refine (homOfLinear_app_tmul φ G 0 V a m).trans ?_
    change a • G.map _ (0 : G.obj (op ⊤)) = 0
    rw [map_zero, smul_zero]
  | add t t' ht ht' => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ht ht').trans (add_zero _))

variable [Module.Free A N] [Module.Finite A N] (G : SheafOfModules.{u} (ringCatSheafOf R))

/-- The morphism `(𝒪_X ⊗_A N)|_W ⟶ G|_W` determined by an `A`-linear map `N → G(W)`. -/
noncomputable def overHom (W : Opens X)
    (g : N ⟶ (ModuleCat.restrictScalars (baseMap φ W)).obj (G.val.obj (op W))) :
    (sheaf φ N).over W ⟶ G.over W where
  val :=
    { app B := ((ModuleCat.extendRestrictScalarsAdj (baseMap φ B.unop.left)).homEquiv _ _).symm
        (g ≫ resLinear φ G.val (leOfHom B.unop.hom))
      naturality {B B'} i := by
        ext t
        induction t using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul a m =>
          change ((ModuleCat.extendRestrictScalarsAdj (baseMap φ B'.unop.left)).homEquiv _ _).symm _
              ((R.obj.map i.unop.left.op a) ⊗ₜ[A, baseMap φ B'.unop.left] m) =
            G.val.map i.unop.left.op
              (((ModuleCat.extendRestrictScalarsAdj (baseMap φ B.unop.left)).homEquiv _ _).symm _
                (a ⊗ₜ[A, baseMap φ B.unop.left] m))
          erw [homEquiv_symm_tmul, homEquiv_symm_tmul, PresheafOfModules.map_smul]
          congr 1
          show resLinear φ G.val _ (g m) = G.val.map _ (resLinear φ G.val _ (g m))
          rw [resLinear_apply, resLinear_apply, ← PresheafOfModules.map_comp_apply]
          rfl
        | add t t' ht ht' => simp only [map_add, ht, ht'] }

/-- **Local morphisms out of `𝒪_X ⊗_A N`**: morphisms `(𝒪_X ⊗_A N)|_W ⟶ G|_W` correspond to
`A`-linear maps `N → G(W)`, by evaluation at `1 ⊗ n`. -/
noncomputable def overHomEquiv (W : Opens X) :
    ((sheaf φ N).over W ⟶ G.over W) ≃
      (N ⟶ (ModuleCat.restrictScalars (baseMap φ W)).obj (G.val.obj (op W))) where
  toFun σ := (ModuleCat.extendRestrictScalarsAdj (baseMap φ W)).homEquiv _ _
    (σ.val.app (op (Over.mk (𝟙 W))))
  invFun g := overHom φ G W g
  left_inv σ := by
    apply SheafOfModules.hom_ext
    ext B t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a m =>
      have h := PresheafOfModules.naturality_apply σ.val
        (Over.homMk B.unop.hom : B.unop ⟶ Over.mk (𝟙 W)).op
        ((1 : R.obj.obj (op W)) ⊗ₜ[A, baseMap φ W] m)
      show ((ModuleCat.extendRestrictScalarsAdj (baseMap φ B.unop.left)).homEquiv _ _).symm
          (((ModuleCat.extendRestrictScalarsAdj (baseMap φ W)).homEquiv _ _
            (σ.val.app (op (Over.mk (𝟙 W))))) ≫ resLinear φ G.val (leOfHom B.unop.hom))
          (a ⊗ₜ[A, baseMap φ B.unop.left] m) = _
      erw [homEquiv_symm_tmul]
      show a • (show G.val.obj (op B.unop.left) from resLinear φ G.val (leOfHom B.unop.hom)
        (((ModuleCat.extendRestrictScalarsAdj (baseMap φ W)).homEquiv _ _
          (σ.val.app (op (Over.mk (𝟙 W))))) m)) = _
      erw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, resLinear_apply]
      erw [← h]
      change a • σ.val.app B ((R.obj.map (B.unop.hom).op (1 : R.obj.obj (op W))) ⊗ₜ[A,
        baseMap φ B.unop.left] m) = _
      rw [map_one]
      erw [← map_smul]
      congr 1
      refine (ModuleCat.ExtendScalars.smul_tmul (f := baseMap φ B.unop.left)
        (show R.obj.obj (op B.unop.left) from a) 1 m).trans ?_
      exact congrArg (fun x : R.obj.obj (op B.unop.left) => x ⊗ₜ[A, baseMap φ B.unop.left] m)
        (mul_one _)
    | add t t' ht ht' => simp only [map_add, ht, ht']
  right_inv g := by
    ext m
    erw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, homEquiv_symm_tmul, one_smul]
    show G.val.map (homOfLE (le_refl W)).op (g m) = g m
    rw [show (homOfLE (le_refl W)).op = 𝟙 (op W) from rfl, PresheafOfModules.map_id]
    rfl

/-- `overHomEquiv` evaluates at `1 ⊗ n`. -/
lemma overHomEquiv_apply (W : Opens X) (σ : (sheaf φ N).over W ⟶ G.over W) (m : N) :
    overHomEquiv φ G W σ m =
      σ.val.app (op (Over.mk (𝟙 W))) ((1 : R.obj.obj (op W)) ⊗ₜ[A, baseMap φ W] m) :=
  ModuleCat.extendRestrictScalarsAdj_homEquiv_apply _ _

/-- Under `overHomEquiv`, precomposition with `𝒪_X ⊗_A g` is precomposition with `g`. -/
lemma overHomEquiv_comp {N' : ModuleCat.{u} A} [Module.Free A N'] [Module.Finite A N']
    (g : N' ⟶ N) (W : Opens X) (σ : (sheaf φ N).over W ⟶ G.over W) :
    overHomEquiv φ G W (SheafOfModules.Hom.over (sheafMap φ g) W ≫ σ) =
      g ≫ overHomEquiv φ G W σ := by
  ext m
  rw [overHomEquiv_apply]
  exact (overHomEquiv_apply φ G W σ (g m)).symm

end Hom

end ScalarExtension

end Ringed

end Hartshorne
