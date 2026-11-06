/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SheafTensorOperations
import Hartshorne.Cohomology.Flatness.ModuleSheafFlatOverBase
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Hartshorne.Scheme.CoherentAffineLocalCriterion
import Hartshorne.Scheme.ProjectiveSpaceOverScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived


/-!
# Cohomology after tensoring is a δ-functor

Hartshorne, *Algebraic Geometry*, III.12, the statement before Proposition 12.2 (p. 282).

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a projective morphism and `F` a coherent
`𝒪_X`-module which is flat over `Spec A`. For an `A`-module `M` put `F ⊗_A M := F ⊗_{𝒪_X} f^*(M̃)`
(`Hartshorne.tensorPullbackTilde`, landing in sheaves of abelian groups) and
`Tⁱ(M) = Hⁱ(X, F ⊗_A M)` (`Hartshorne.cohomologyTensor`), where `Hⁱ(X, -)` is the `i`-th right
derived functor of global sections on sheaves of abelian groups. The main result
`Hartshorne.cohomologyTensor_isCovariantDeltaFunctor` says that every `Tⁱ` is an additive functor
and that, with the connecting morphisms `Hartshorne.cohomologyTensorδ` of the long exact cohomology
sequences, `(Tⁱ)` is a covariant δ-functor (`Hartshorne.IsCovariantDeltaFunctor`: long exact
sequences, natural in morphisms of short exact sequences); in particular every `Tⁱ` is exact in the
middle. The values of `Tⁱ` are taken in abelian groups, as for Hartshorne's `Hⁱ(X, -)`.

Only the flatness of `F` is used: the Noetherian, projectivity and coherence hypotheses are kept as
in the source.

## Proof

Everything reduces to the exactness of `M ↦ F ⊗_{𝒪_X} f^*(M̃)` for `F` flat over `Spec A`
(`Hartshorne.tensorPullbackTilde_shortExact`); the δ-functor structure is then the long exact
sequence of right derived functors (`Hartshorne.rightDerivedδ` and its exactness and naturality).

* `f^*(M̃)` is identified with the sheafification `P(M)` of the presheaf `U ↦ 𝒪_X(U) ⊗_A M`
  (`CohomologyTensorDelta.sheafFunctorIso`): both functors are left adjoint to
  `G ↦ Γ(X, G)`, viewed as an `A`-module (for `P` this is an explicit adjunction on presheaves,
  `CohomologyTensorDelta.preAdjunction`, composed with sheafification).
* Stalks: `(𝒪_X(-) ⊗_A M)ₓ ≅ 𝒪_{X,x} ⊗_A M` (`CohomologyTensorDelta.preStalkIso`), sheafification
  does not change stalks, `(F ⊗ G)ₓ ≅ Fₓ ⊗_{𝒪_{X,x}} Gₓ` (`Hartshorne.moduleSheafTensorStalkIso`),
  and `Fₓ ⊗_{𝒪_{X,x}} (𝒪_{X,x} ⊗_A M) ≅ Fₓ ⊗_A M` (`CohomologyTensorDelta.cancelEquiv`). Together,
  `(F ⊗ P(M))ₓ ≅ Fₓ ⊗_A M` naturally in `M` (`CohomologyTensorDelta.tensorSheafStalkEquiv`).
* `Fₓ` is flat over `𝒪_{Spec A, f(x)} ≅ A_𝔭` by hypothesis, hence flat over `A`
  (`CohomologyTensorDelta.stalkA_flat`), so `Fₓ ⊗_A -` is exact; exactness of a sequence of
  sheaves of abelian groups is checked on stalks.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe u

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace CohomologyTensorDelta

section ExtendScalars

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : R →+* T)
  (ρ : S →+* T) (h : ρ.comp φ = ψ)
include h

/-- A ring map `ρ : S → T` under `R`, as an `R`-linear map. -/
noncomputable def ringHomRestrictLinear :
    (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) →ₗ[R]
      (ModuleCat.restrictScalars ψ).obj (ModuleCat.of T T) where
  toFun s := ρ s
  map_add' := map_add ρ
  map_smul' r s := by
    change ρ (@HMul.hMul S S S _ (φ r) s) = @HMul.hMul T T T _ (ψ r) (ρ s)
    rw [map_mul, ← h]; rfl

variable (M : ModuleCat.{u} R)

/-- The `ρ`-semilinear map `S ⊗_R M → T ⊗_R M`, `s ⊗ m ↦ ρ s ⊗ m`. -/
noncomputable def extendScalarsSemilinear :
    (ModuleCat.extendScalars φ).obj M →ₛₗ[ρ] (ModuleCat.extendScalars ψ).obj M where
  toFun := TensorProduct.map (ringHomRestrictLinear φ ψ ρ h) LinearMap.id
  map_add' := map_add _
  map_smul' s t := by
    induction t using TensorProduct.induction_on with
    | zero => exact (congrArg _ (smul_zero s)).trans ((map_zero _).trans (smul_zero _).symm)
    | tmul a m =>
      change ρ (@HMul.hMul S S S _ s a) ⊗ₜ[R, ψ] m = ρ s • (ρ a ⊗ₜ[R, ψ] m)
      rw [ModuleCat.ExtendScalars.smul_tmul, map_mul]
    | add t t' ht ht' =>
      exact (congrArg _ (smul_add s t t')).trans ((map_add _ _ _).trans
        ((congrArg₂ (· + ·) ht ht').trans ((smul_add _ _ _).symm.trans
          (congrArg _ (map_add _ t t').symm))))

lemma extendScalarsSemilinear_tmul (s : S) (m : M) :
    extendScalarsSemilinear φ ψ ρ h M (s ⊗ₜ[R, φ] m) = ρ s ⊗ₜ[R, ψ] m := rfl

end ExtendScalars

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- The ring map `A → Γ(X, U)` induced by `f : X ⟶ Spec A`. -/
noncomputable def baseMap (U : X.Opens) : A ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U (show U ≤ f ⁻¹ᵁ ⊤ from le_top)

lemma baseMap_map {U V : X.Opens} (i : op U ⟶ op V) :
    baseMap f U ≫ X.presheaf.map i = baseMap f V := by
  rw [baseMap, Category.assoc, Scheme.Hom.appLE_map]
  rfl

lemma baseMap_map_hom {U V : X.Opens} (i : op U ⟶ op V) :
    (X.presheaf.map i).hom.comp (baseMap f U).hom = (baseMap f V).hom := by
  rw [← baseMap_map f i]; rfl

lemma baseMap_top : baseMap f ⊤ = (Scheme.ΓSpecIso A).inv ≫ f.app ⊤ := by
  rw [baseMap, Scheme.Hom.appLE]
  simp

variable (M : ModuleCat.{u} A)

/-- The presheaf of `𝒪_X`-modules `U ↦ 𝒪_X(U) ⊗_A M`. -/
noncomputable def prePresheaf : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) :=
  SheafTensorOperations.presheafOfSemilinear (R := X.sheaf)
    (fun U => (ModuleCat.extendScalars (baseMap f U.unop).hom).obj M)
    (fun {U V} i => extendScalarsSemilinear _ _ (X.presheaf.map i).hom (baseMap_map_hom f i) M)
    (fun U t => by
      induction t using TensorProduct.induction_on with
      | zero => exact map_zero _
      | tmul a m =>
        change (X.presheaf.map (𝟙 U) a) ⊗ₜ[A, (baseMap f U.unop).hom] m = _
        rw [X.presheaf.map_id]; rfl
      | add t t' ht ht' => exact (map_add _ _ _).trans (congrArg₂ (· + ·) ht ht'))
    (fun i j t => by
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a m =>
        change (X.presheaf.map (i ≫ j) a) ⊗ₜ[A, _] m =
          (X.presheaf.map j (X.presheaf.map i a)) ⊗ₜ[A, _] m
        rw [X.presheaf.map_comp]; rfl
      | add t t' ht ht' => simp only [map_add, ht, ht'])

lemma prePresheaf_map_tmul {U V : (X.Opens)ᵒᵖ} (i : U ⟶ V) (a : Γ(X, U.unop)) (m : M) :
    (prePresheaf f M).map i (a ⊗ₜ[A, (baseMap f U.unop).hom] m) =
      (X.presheaf.map i a) ⊗ₜ[A, (baseMap f V.unop).hom] m :=
  rfl

variable {M} in
/-- Functoriality of `M ↦ 𝒪_X(-) ⊗_A M`. -/
noncomputable def prePresheafMap {N : ModuleCat.{u} A} (g : M ⟶ N) :
    prePresheaf f M ⟶ prePresheaf f N where
  app U := (ModuleCat.extendScalars (baseMap f U.unop).hom).map g
  naturality {U V} i := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul a m => rfl
    | add t t' ht ht' =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) ht ht').trans (map_add _ _ _).symm)

/-- The functor `M ↦ (U ↦ 𝒪_X(U) ⊗_A M)`. -/
noncomputable def preFunctor :
    ModuleCat.{u} A ⥤ PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) where
  obj M := prePresheaf f M
  map g := prePresheafMap f g
  map_id M := by
    ext U t
    exact congrArg (fun k => k.hom t) ((ModuleCat.extendScalars (baseMap f U.unop).hom).map_id M)
  map_comp g g' := by
    ext U t
    exact congrArg (fun k => k.hom t)
      ((ModuleCat.extendScalars (baseMap f U.unop).hom).map_comp g g')

section PresheafAdjunction


/-- Global sections of a presheaf of `𝒪_X`-modules, as an `A`-module. -/
noncomputable def preGlobal :
    PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) ⥤ ModuleCat.{u} A :=
  PresheafOfModules.evaluation (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat) (op ⊤) ⋙
    ModuleCat.restrictScalars (baseMap f ⊤).hom

lemma extendScalars_homEquiv_symm_one_tmul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (k : M ⟶ (ModuleCat.restrictScalars φ).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm k ((1 : S) ⊗ₜ[R, φ] m) = k m := by
  have := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
    (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm k) m
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

lemma extendScalars_homEquiv_symm_tmul {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {M : ModuleCat.{u} R} {N : ModuleCat.{u} S}
    (k : M ⟶ (ModuleCat.restrictScalars φ).obj N) (s : S) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm k (s ⊗ₜ[R, φ] m) =
      s • (show N from k m) := by
  have e : s ⊗ₜ[R, φ] m = s • ((1 : S) ⊗ₜ[R, φ] m : (ModuleCat.extendScalars φ).obj M) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [e, map_smul, extendScalars_homEquiv_symm_one_tmul]

/-- Restriction from global sections to `U`, as an `A`-linear map. -/
noncomputable def resFromTop
    (G : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) (U : (X.Opens)ᵒᵖ) :
    (preGlobal f).obj G ⟶ (ModuleCat.restrictScalars (baseMap f U.unop).hom).obj (G.obj U) :=
  ModuleCat.ofHom (X := (preGlobal f).obj G)
      (Y := (ModuleCat.restrictScalars (baseMap f U.unop).hom).obj (G.obj U))
    { toFun s := G.map (homOfLE le_top : U.unop ⟶ ⊤).op s
      map_add' := map_add _
      map_smul' a s := by
        change G.map _ (@HSMul.hSMul ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤))
            (G.obj (op ⊤)) (G.obj (op ⊤)) _
            (baseMap f ⊤ a) s) =
          @HSMul.hSMul ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) (G.obj U) (G.obj U) _
            (baseMap f U.unop a)
            (G.map (homOfLE le_top : U.unop ⟶ ⊤).op s)
        rw [PresheafOfModules.map_smul]
        congr 1
        exact congrArg (fun k => k.hom a) (baseMap_map f (homOfLE le_top : U.unop ⟶ ⊤).op) }

lemma resFromTop_apply (G : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
    (U : (X.Opens)ᵒᵖ) (s : G.obj (op ⊤)) :
    resFromTop f G U s = G.map (homOfLE le_top : U.unop ⟶ ⊤).op s := rfl

/-- Morphisms out of `𝒪_X(-) ⊗_A M` are `A`-linear maps from `M` to global sections. -/
noncomputable def preHomEquiv (M : ModuleCat.{u} A)
    (G : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :
    (prePresheaf f M ⟶ G) ≃ (M ⟶ (preGlobal f).obj G) where
  toFun φ := (ModuleCat.extendRestrictScalarsAdj (baseMap f ⊤).hom).homEquiv _ _ (φ.app (op ⊤))
  invFun g :=
    { app U := ((ModuleCat.extendRestrictScalarsAdj (baseMap f U.unop).hom).homEquiv _ _).symm
        (g ≫ resFromTop f G U)
      naturality {U V} i := by
        ext t
        induction t using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul a m =>
          change ((ModuleCat.extendRestrictScalarsAdj (baseMap f V.unop).hom).homEquiv _ _).symm
              (g ≫ resFromTop f G V) ((X.presheaf.map i a) ⊗ₜ[A, (baseMap f V.unop).hom] m) =
            G.map i (((ModuleCat.extendRestrictScalarsAdj (baseMap f U.unop).hom).homEquiv _ _).symm
              (g ≫ resFromTop f G U) (a ⊗ₜ[A, (baseMap f U.unop).hom] m))
          erw [extendScalars_homEquiv_symm_tmul, extendScalars_homEquiv_symm_tmul,
            PresheafOfModules.map_smul]
          congr 1
          change G.map (homOfLE le_top : V.unop ⟶ ⊤).op (g m) =
            G.map i (G.map (homOfLE le_top : U.unop ⟶ ⊤).op (g m))
          rw [← PresheafOfModules.map_comp_apply]
          rfl
        | add t t' ht ht' => simp only [map_add, ht, ht'] }
  left_inv φ := by
    ext U t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a m =>
      change ((ModuleCat.extendRestrictScalarsAdj (baseMap f U.unop).hom).homEquiv _ _).symm
          (_ ≫ resFromTop f G U) (a ⊗ₜ[A, (baseMap f U.unop).hom] m) = φ.app U (a ⊗ₜ m)
      erw [extendScalars_homEquiv_symm_tmul]
      change a • G.map _ ((ModuleCat.extendRestrictScalarsAdj (baseMap f ⊤).hom).homEquiv _ _
        (φ.app (op ⊤)) m) = _
      erw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, ← PresheafOfModules.naturality_apply]
      have e : a ⊗ₜ[A, (baseMap f U.unop).hom] m =
          (show Γ(X, U.unop) from a) • ((1 : Γ(X, U.unop)) ⊗ₜ[A, (baseMap f U.unop).hom] m :
            (ModuleCat.extendScalars (baseMap f U.unop).hom).obj M) := by
        rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
      rw [e, map_smul]
      congr 2
      change (X.presheaf.map _ 1) ⊗ₜ[A, (baseMap f U.unop).hom] m = _
      rw [map_one]
    | add t t' ht ht' => simp only [map_add, ht, ht']
  right_inv g := by
    ext m
    erw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, extendScalars_homEquiv_symm_one_tmul]
    change G.map _ (g m) = g m
    rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op = 𝟙 _ from rfl]
    simp only [PresheafOfModules.map_id]
    rfl

lemma preHomEquiv_symm_apply_tmul (M : ModuleCat.{u} A)
    (G : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
    (g : M ⟶ (preGlobal f).obj G) (U : (X.Opens)ᵒᵖ) (a : Γ(X, U.unop)) (m : M) :
    ((preHomEquiv f M G).symm g).app U (a ⊗ₜ[A, (baseMap f U.unop).hom] m) =
      a • (show G.obj U from G.map (homOfLE le_top : U.unop ⟶ ⊤).op (g m)) :=
  extendScalars_homEquiv_symm_tmul _ _ _ _

/-- The adjunction between `M ↦ 𝒪_X(-) ⊗_A M` and global sections. -/
noncomputable def preAdjunction : preFunctor f ⊣ preGlobal f :=
  Adjunction.mkOfHomEquiv
    { homEquiv := preHomEquiv f
      homEquiv_naturality_left_symm := by
        intro M' M G h g
        ext U t
        induction t using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul a m =>
          erw [preHomEquiv_symm_apply_tmul]
        | add t t' ht ht' => simp only [map_add, ht, ht']
      homEquiv_naturality_right := by
        intro M G G' φ ψ
        ext m
        rfl }

end PresheafAdjunction

section SheafAdjunction

/-- The `𝒪_X`-module `P(M)`, the sheafification of `U ↦ 𝒪_X(U) ⊗_A M`. -/
noncomputable def sheafFunctor : ModuleCat.{u} A ⥤ X.Modules :=
  preFunctor f ⋙ PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)

/-- The adjunction for `P`, with right adjoint written through presheaves. -/
noncomputable def sheafAdjunction' : sheafFunctor f ⊣
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 (ringCatSheafOf X.sheaf).obj))
      ⋙ preGlobal f :=
  (preAdjunction f).comp (PresheafOfModules.sheafificationAdjunction _)

/-- The two descriptions of global sections of an `𝒪_X`-module as an `A`-module agree. -/
noncomputable def globalIso :
    (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 (ringCatSheafOf X.sheaf).obj))
      ⋙ preGlobal f ≅ Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor :=
  NatIso.ofComponents (fun G =>
    let e : (((SheafOfModules.forget _ ⋙
        PresheafOfModules.restrictScalars (𝟙 (ringCatSheafOf X.sheaf).obj)) ⋙ preGlobal f).obj G :
          ModuleCat.{u} A) ≃ₗ[A]
        ((Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor).obj G : ModuleCat.{u} A) :=
      { toFun := fun s => s
        invFun := fun s => s
        map_add' := fun _ _ => rfl
        map_smul' := fun a s => by
          change @HSMul.hSMul ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤))
              (G.val.obj (op ⊤)) (G.val.obj (op ⊤)) _ (baseMap f ⊤ a) s =
            @HSMul.hSMul ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤))
              (G.val.obj (op ⊤)) (G.val.obj (op ⊤)) _ (((Scheme.ΓSpecIso A).inv ≫ f.app ⊤) a) s
          rw [baseMap_top]
          rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    e.toModuleIso) (fun φ => rfl)

/-- `P` is left adjoint to global sections, viewed as `A`-modules. -/
noncomputable def sheafAdjunction :
    sheafFunctor f ⊣ Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor :=
  (sheafAdjunction' f).ofNatIsoRight (globalIso f)

/-- `M ↦ f^*(M̃)` is left adjoint to global sections, viewed as `A`-modules. -/
noncomputable def tildePullbackAdjunction :
    tilde.functor A ⋙ Scheme.Modules.pullback f ⊣
      Scheme.Modules.pushforward f ⋙ moduleSpecΓFunctor :=
  tilde.adjunction.comp (Scheme.Modules.pullbackPushforwardAdjunction f)

/-- `f^*(M̃)` is the sheafification of `U ↦ 𝒪_X(U) ⊗_A M`, naturally in `M`. -/
noncomputable def sheafFunctorIso : sheafFunctor f ≅ tilde.functor A ⋙ Scheme.Modules.pullback f :=
  (sheafAdjunction f).leftAdjointUniq (tildePullbackAdjunction f)

end SheafAdjunction

section PreStalk

open ModuleSheafTensor

variable (x : X)

/-- The ring map `A → 𝒪_{X,x}`. -/
noncomputable def stalkBaseMap : A ⟶ X.presheaf.stalk x :=
  baseMap f ⊤ ≫ X.presheaf.germ ⊤ x trivial

lemma baseMap_germ (U : X.Opens) (hU : x ∈ U) :
    baseMap f U ≫ X.presheaf.germ U x hU = stalkBaseMap f x := by
  rw [stalkBaseMap, ← baseMap_map f (homOfLE le_top : U ⟶ ⊤).op, Category.assoc,
    TopCat.Presheaf.germ_res]

lemma baseMap_germ_hom (U : X.Opens) (hU : x ∈ U) :
    (X.presheaf.germ U x hU).hom.comp (baseMap f U).hom = (stalkBaseMap f x).hom := by
  rw [← baseMap_germ f x U hU]; rfl

/-- `𝒪_{X,x} ⊗_A M`. -/
noncomputable abbrev stalkExt : ModuleCat.{u} (X.presheaf.stalk x) :=
  (ModuleCat.extendScalars (stalkBaseMap f x).hom).obj M

/-- The map `(𝒪_X(-) ⊗_A M)ₓ → 𝒪_{X,x} ⊗_A M`. -/
noncomputable def preStalkToExt :
    moduleStalk (R := X.sheaf) (prePresheaf f M) x ⟶ AddCommGrpCat.of (stalkExt f M x) :=
  stalkDesc (fun U hU => AddCommGrpCat.ofHom
      (extendScalarsSemilinear (baseMap f U).hom (stalkBaseMap f x).hom
        (X.presheaf.germ U x hU).hom (baseMap_germ_hom f x U hU) M).toAddMonoidHom)
    (fun U V i hV => by
      ext t
      change (prePresheaf f M).obj (op U) at t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a m =>
        change (X.presheaf.germ V x hV (X.presheaf.map i.op a)) ⊗ₜ[A, _] m =
          (X.presheaf.germ U x (i.le hV) a) ⊗ₜ[A, _] m
        rw [TopCat.Presheaf.germ_res_apply]
      | add t t' ht ht' => simp only [map_add, ht, ht'])

lemma preStalkToExt_germ (U : X.Opens) (hU : x ∈ U) (a : Γ(X, U)) (m : M) :
    preStalkToExt f M x (sectionGerm (prePresheaf f M) x U hU
      (a ⊗ₜ[A, (baseMap f U).hom] m)) =
      (X.presheaf.germ U x hU a) ⊗ₜ[A, (stalkBaseMap f x).hom] m :=
  stalkDesc_germ (P := (prePresheaf f M).presheaf) _ _ U hU _

/-- The stalk `(𝒪_X(-) ⊗_A M)ₓ` as an `𝒪_{X,x}`-module. -/
noncomputable abbrev preStalkMod : ModuleCat.{u} (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x) (moduleStalk (R := X.sheaf) (prePresheaf f M) x)

/-- The `A`-linear map `M → (𝒪_X(-) ⊗_A M)ₓ`, `m ↦ (1 ⊗ m)ₓ`. -/
noncomputable def oneTmulGerm :
    M ⟶ (ModuleCat.restrictScalars (stalkBaseMap f x).hom).obj (preStalkMod f M x) :=
  ModuleCat.ofHom (X := M)
      (Y := (ModuleCat.restrictScalars (stalkBaseMap f x).hom).obj (preStalkMod f M x))
    { toFun m := sectionGerm (prePresheaf f M) x ⊤ trivial
        ((1 : Γ(X, ⊤)) ⊗ₜ[A, (baseMap f ⊤).hom] m)
      map_add' m m' := by
        rw [TensorProduct.tmul_add, map_add]
      map_smul' a m := by
        have e : (1 : Γ(X, ⊤)) ⊗ₜ[A, (baseMap f ⊤).hom] (a • m) =
            (baseMap f ⊤ a : Γ(X, ⊤)) • ((1 : Γ(X, ⊤)) ⊗ₜ[A, (baseMap f ⊤).hom] m :
              (ModuleCat.extendScalars (baseMap f ⊤).hom).obj M) := by
          rw [ModuleCat.ExtendScalars.smul_tmul]
          exact (TensorProduct.smul_tmul (M := (ModuleCat.restrictScalars (baseMap f ⊤).hom).obj
            (ModuleCat.of _ Γ(X, ⊤))) a (1 : Γ(X, ⊤)) m).symm
        rw [e]
        erw [sectionGerm_smul]
        rfl }

/-- The map `𝒪_{X,x} ⊗_A M → (𝒪_X(-) ⊗_A M)ₓ`. -/
noncomputable def extToPreStalk : stalkExt f M x ⟶ preStalkMod f M x :=
  ((ModuleCat.extendRestrictScalarsAdj (stalkBaseMap f x).hom).homEquiv _ _).symm
    (oneTmulGerm f M x)

lemma extToPreStalk_tmul (s : X.presheaf.stalk x) (m : M) :
    extToPreStalk f M x (s ⊗ₜ[A, (stalkBaseMap f x).hom] m) =
      s • sectionGerm (prePresheaf f M) x ⊤ trivial ((1 : Γ(X, ⊤)) ⊗ₜ[A, (baseMap f ⊤).hom] m) :=
  extendScalars_homEquiv_symm_tmul _ (oneTmulGerm f M x) s m

lemma sectionGerm_one_tmul (U : X.Opens) (hU : x ∈ U) (m : M) :
    sectionGerm (prePresheaf f M) x ⊤ trivial ((1 : Γ(X, ⊤)) ⊗ₜ[A, (baseMap f ⊤).hom] m) =
      sectionGerm (prePresheaf f M) x U hU ((1 : Γ(X, U)) ⊗ₜ[A, (baseMap f U).hom] m) := by
  rw [← sectionGerm_res (prePresheaf f M) x (homOfLE le_top : U ⟶ ⊤) hU]
  congr 1
  change (X.presheaf.map _ (1 : Γ(X, ⊤))) ⊗ₜ[A, (baseMap f U).hom] m = _
  rw [map_one]

lemma extToPreStalk_germ_tmul (U : X.Opens) (hU : x ∈ U) (a : Γ(X, U)) (m : M) :
    extToPreStalk f M x ((X.presheaf.germ U x hU a) ⊗ₜ[A, (stalkBaseMap f x).hom] m) =
      sectionGerm (prePresheaf f M) x U hU (a ⊗ₜ[A, (baseMap f U).hom] m) := by
  rw [extToPreStalk_tmul, sectionGerm_one_tmul f M x U hU]
  refine (sectionGerm_smul (prePresheaf f M) x U hU a _).symm.trans ?_
  congr 1
  change (a * 1) ⊗ₜ[A, (baseMap f U).hom] m = _
  rw [mul_one]

/-- **Stalks of `𝒪_X(-) ⊗_A M`.** `(𝒪_X(-) ⊗_A M)ₓ ≅ 𝒪_{X,x} ⊗_A M`. -/
noncomputable def preStalkIso : stalkExt f M x ≃ₗ[X.presheaf.stalk x] preStalkMod f M x where
  toFun := extToPreStalk f M x
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := preStalkToExt f M x
  left_inv t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul s m =>
      obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq s
      rw [extToPreStalk_germ_tmul]
      exact preStalkToExt_germ f M x U hU a m
    | add t t' ht ht' => simp only [map_add, ht, ht']
  right_inv y := by
    obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm (prePresheaf f M) x y
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul a m =>
      erw [preStalkToExt_germ]
      exact extToPreStalk_germ_tmul f M x U hU a m
    | add t t' ht ht' => simp only [map_add, ht, ht']

end PreStalk

section StalkMaps

open ModuleSheafTensor

variable (x : X)

/-- The additive map on stalks induced by a morphism of presheaves of modules. -/
noncomputable def pStalkMap
    {P Q : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)}
    (φ : P ⟶ Q) : moduleStalk (R := X.sheaf) P x →+ moduleStalk (R := X.sheaf) Q x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map φ)).hom

lemma pStalkMap_germ {P Q : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)}
    (φ : P ⟶ Q) (U : X.Opens) (hU : x ∈ U) (t : P.obj (op U)) :
    pStalkMap x φ (sectionGerm P x U hU t) = sectionGerm Q x U hU (φ.app (op U) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) U x hU
    ((PresheafOfModules.toPresheaf _).map φ) t

lemma preStalkToExt_naturality {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (y : moduleStalk (R := X.sheaf) (prePresheaf f M) x) :
    preStalkToExt f N x (pStalkMap x (prePresheafMap f g) y) =
      (ModuleCat.extendScalars (stalkBaseMap f x).hom).map g (preStalkToExt f M x y) := by
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm (prePresheaf f M) x y
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m =>
    rw [pStalkMap_germ]
    exact (preStalkToExt_germ f N x U hU a (g m)).trans
      (congrArg ((ModuleCat.extendScalars (stalkBaseMap f x).hom).map g)
        (preStalkToExt_germ f M x U hU a m)).symm
  | add t t' ht ht' => simp only [map_add, ht, ht']

variable (P : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))

/-- The sheafification of a presheaf of `𝒪_X`-modules. -/
noncomputable abbrev sh : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)).obj P

/-- The unit of sheafification. -/
noncomputable abbrev shUnit : P ⟶ (sh P).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf X.sheaf).obj)).unit.app P

/-- The stalk map of the sheafification unit. -/
noncomputable def shUnitStalk :
    moduleStalk (R := X.sheaf) P x →+ moduleStalk (R := X.sheaf) (sh P).val x :=
  ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)).hom

lemma shUnitStalk_bijective : Function.Bijective (shUnitStalk x P) := by
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} P.presheaf
  exact ConcreteCategory.bijective_of_isIso _

lemma shUnitStalk_germ (W : X.Opens) (hW : x ∈ W) (t : P.obj (op W)) :
    shUnitStalk x P (sectionGerm P x W hW t) =
      sectionGerm (sh P).val x W hW ((shUnit P).app (op W) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) W x hW
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf) t

lemma shUnitStalk_smul (r : X.presheaf.stalk x) (s : moduleStalk (R := X.sheaf) P x) :
    shUnitStalk x P (r • s) = r • shUnitStalk x P s := by
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm P x s
  obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm (R := X.sheaf) x r hU
  rw [← sectionGerm_res P x (homOfLE hWU) hW t, ← sectionGerm_smul, shUnitStalk_germ,
    shUnitStalk_germ, ← sectionGerm_smul]
  exact congrArg (sectionGerm (sh P).val x W hW) (((shUnit P).app (op W)).hom.map_smul c _)

/-- The stalk map of the sheafification unit, as an `𝒪_{X,x}`-linear equivalence. -/
noncomputable def shUnitStalkEquiv :
    moduleStalk (R := X.sheaf) P x ≃ₗ[X.presheaf.stalk x] moduleStalk (R := X.sheaf) (sh P).val x :=
  LinearEquiv.ofBijective
    { toFun := shUnitStalk x P
      map_add' := map_add _
      map_smul' := shUnitStalk_smul x P }
    (shUnitStalk_bijective x P)

lemma shUnitStalk_naturality
    {P Q : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)}
    (φ : P ⟶ Q) (s : moduleStalk (R := X.sheaf) P x) :
    shUnitStalk x Q (pStalkMap x φ s) =
      pStalkMap x ((PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)).map φ).val
        (shUnitStalk x P s) := by
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm P x s
  rw [pStalkMap_germ, shUnitStalk_germ, shUnitStalk_germ, pStalkMap_germ]
  congr 1
  exact (congrArg (fun k => (k.app (op U)).hom t)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheafOf X.sheaf).obj)).unit.naturality
      φ))

end StalkMaps

section TensorStalk

open ModuleSheafTensor MonoidalCategory

variable (x : X)

/-- The stalk map of a morphism of presheaves of modules, as an `𝒪_{X,x}`-linear map. -/
noncomputable def pStalkLinear
    {P Q : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)}
    (φ : P ⟶ Q) :
    moduleStalk (R := X.sheaf) P x →ₗ[X.presheaf.stalk x] moduleStalk (R := X.sheaf) Q x where
  toFun := pStalkMap x φ
  map_add' := map_add _
  map_smul' r s := by
    obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm P x s
    obtain ⟨W, hWU, hW, c, rfl⟩ := exists_le_ringGerm (R := X.sheaf) x r hU
    rw [← sectionGerm_res P x (homOfLE hWU) hW t, ← sectionGerm_smul, RingHom.id_apply,
      pStalkMap_germ, pStalkMap_germ, ← sectionGerm_smul]
    exact congrArg (sectionGerm Q x W hW) ((φ.app (op W)).hom.map_smul c _)

variable (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

/-- The functor `G ↦ F ⊗_{𝒪_X} G` on `𝒪_X`-modules. -/
noncomputable def tensorFunctor :
    SheafOfModules.{u} (ringCatSheafOf X.sheaf) ⥤ SheafOfModules.{u} (ringCatSheafOf X.sheaf) :=
  SheafOfModules.forget _ ⋙ tensorLeft F.val ⋙
    PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)

lemma tensorStalkIso_naturality {G G' : SheafOfModules.{u} (ringCatSheafOf X.sheaf)} (b : G ⟶ G')
    (y : moduleStalk (R := X.sheaf) (moduleSheafTensor F G).val x) :
    moduleSheafTensorStalkIso F G' x (pStalkMap x ((tensorFunctor F).map b).val y) =
      TensorProduct.map LinearMap.id (pStalkLinear x b.val)
        (moduleSheafTensorStalkIso F G x y) := by
  obtain ⟨z, rfl⟩ := (shUnitStalk_bijective x (F.val ⊗ G.val)).2 y
  erw [← shUnitStalk_naturality x (F.val ◁ b.val) z]
  obtain ⟨U, hU, t, rfl⟩ := exists_sectionGerm (F.val ⊗ G.val) x z
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a c =>
    rw [pStalkMap_germ, shUnitStalk_germ, shUnitStalk_germ]
    erw [moduleSheafTensorStalkIso_germ F G' x U hU a (b.val.app (op U) c),
      moduleSheafTensorStalkIso_germ F G x U hU a c]
    erw [TensorProduct.map_tmul]
    congr 1
    exact (pStalkMap_germ x b.val U hU c).symm
  | add t t' ht ht' => simp only [map_add, ht, ht']

end TensorStalk

section Cancel

variable (x : X) (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf)) (M : ModuleCat.{u} A)

/-- The stalk `Fₓ` as an `A`-module. -/
noncomputable abbrev stalkA : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (stalkBaseMap f x).hom).obj
    (ModuleCat.of (X.presheaf.stalk x) (moduleStalk (R := X.sheaf) F.val x))

lemma stalkA_smul (a : A) (v : moduleStalk (R := X.sheaf) F.val x) :
    (a • (show stalkA f x F from v) : stalkA f x F) =
      (show moduleStalk (R := X.sheaf) F.val x from (stalkBaseMap f x a • v)) := rfl

/-- For `v ∈ Fₓ`, the map `𝒪_{X,x} ⊗_A M → Fₓ ⊗_A M`, `s ⊗ m ↦ s v ⊗ m`. -/
noncomputable def cancelInner (v : moduleStalk (R := X.sheaf) F.val x) :
    stalkExt f M x →+ (stalkA f x F) ⊗[A] M :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun s => (TensorProduct.mk A (stalkA f x F) M
        (show stalkA f x F from ((show X.presheaf.stalk x from s) • v))).toAddMonoidHom)
      (fun s s' => by
        ext m
        change (show stalkA f x F from ((show X.presheaf.stalk x from s + s') • v)) ⊗ₜ[A] m =
          (show stalkA f x F from ((show X.presheaf.stalk x from s) • v)) ⊗ₜ[A] m +
          (show stalkA f x F from ((show X.presheaf.stalk x from s') • v)) ⊗ₜ[A] m
        rw [← TensorProduct.add_tmul, add_smul]))
    (fun a s m => by
      change (show stalkA f x F from ((stalkBaseMap f x a * (show X.presheaf.stalk x from s)) • v))
          ⊗ₜ[A] m = (show stalkA f x F from ((show X.presheaf.stalk x from s) • v)) ⊗ₜ[A] (a • m)
      rw [← TensorProduct.smul_tmul, mul_smul]
      rfl)

lemma cancelInner_tmul (v : moduleStalk (R := X.sheaf) F.val x) (s : X.presheaf.stalk x) (m : M) :
    cancelInner f x F M v (s ⊗ₜ[A, (stalkBaseMap f x).hom] m) =
      (show stalkA f x F from (s • v)) ⊗ₜ[A] m := rfl

/-- The map `Fₓ ⊗_{𝒪_{X,x}} (𝒪_{X,x} ⊗_A M) → Fₓ ⊗_A M`. -/
noncomputable def cancelHom :
    (moduleStalk (R := X.sheaf) F.val x) ⊗[X.presheaf.stalk x] (stalkExt f M x) →+
      (stalkA f x F) ⊗[A] M :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun v => cancelInner f x F M v) (fun v v' => by
      ext t
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul s m =>
        rw [AddMonoidHom.add_apply, cancelInner_tmul, cancelInner_tmul, cancelInner_tmul,
          ← TensorProduct.add_tmul, smul_add]
      | add t t' ht ht' => simp only [map_add, ht, ht']))
    (fun r v t => by
      induction t using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul s m =>
        change cancelInner f x F M (r • v) (s ⊗ₜ[A, (stalkBaseMap f x).hom] m) =
          cancelInner f x F M v
            ((r * (show X.presheaf.stalk x from s)) ⊗ₜ[A, (stalkBaseMap f x).hom] m)
        rw [cancelInner_tmul, cancelInner_tmul, smul_smul, mul_comm]
      | add t t' ht ht' =>
        rw [smul_add, map_add, map_add, ht, ht'])

lemma cancelHom_tmul (v : moduleStalk (R := X.sheaf) F.val x) (s : X.presheaf.stalk x) (m : M) :
    cancelHom f x F M (v ⊗ₜ (s ⊗ₜ[A, (stalkBaseMap f x).hom] m)) =
      (show stalkA f x F from (s • v)) ⊗ₜ[A] m := rfl

/-- The map `Fₓ ⊗_A M → Fₓ ⊗_{𝒪_{X,x}} (𝒪_{X,x} ⊗_A M)`. -/
noncomputable def uncancelHom :
    (stalkA f x F) ⊗[A] M →+
      (moduleStalk (R := X.sheaf) F.val x) ⊗[X.presheaf.stalk x] (stalkExt f M x) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun m =>
        (show moduleStalk (R := X.sheaf) F.val x from v) ⊗ₜ[X.presheaf.stalk x]
          ((1 : X.presheaf.stalk x) ⊗ₜ[A, (stalkBaseMap f x).hom] m : stalkExt f M x))
        (fun m m' => by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]))
      (fun v v' => by
        ext m
        exact TensorProduct.add_tmul _ _ _))
    (fun a v m => by
      change (stalkBaseMap f x a • (show moduleStalk (R := X.sheaf) F.val x from v)) ⊗ₜ
          ((1 : X.presheaf.stalk x) ⊗ₜ[A, (stalkBaseMap f x).hom] m : stalkExt f M x) =
        (show moduleStalk (R := X.sheaf) F.val x from v) ⊗ₜ
          ((1 : X.presheaf.stalk x) ⊗ₜ[A, (stalkBaseMap f x).hom] (a • m) : stalkExt f M x)
      rw [TensorProduct.smul_tmul, ModuleCat.ExtendScalars.smul_tmul]
      congr 1
      exact TensorProduct.smul_tmul (M := (ModuleCat.restrictScalars (stalkBaseMap f x).hom).obj
        (ModuleCat.of _ (X.presheaf.stalk x))) a (1 : X.presheaf.stalk x) m)

/-- `Fₓ ⊗_{𝒪_{X,x}} (𝒪_{X,x} ⊗_A M) ≃ Fₓ ⊗_A M`. -/
noncomputable def cancelEquiv :
    (moduleStalk (R := X.sheaf) F.val x) ⊗[X.presheaf.stalk x] (stalkExt f M x) ≃+
      (stalkA f x F) ⊗[A] M where
  toFun := cancelHom f x F M
  invFun := uncancelHom f x F M
  map_add' := map_add _
  left_inv y := by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v t =>
      induction t using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | tmul s m =>
        rw [cancelHom_tmul]
        change ((show X.presheaf.stalk x from s) • v) ⊗ₜ
          ((1 : X.presheaf.stalk x) ⊗ₜ[A, (stalkBaseMap f x).hom] m :
          stalkExt f M x) = v ⊗ₜ (s ⊗ₜ[A, (stalkBaseMap f x).hom] m)
        rw [TensorProduct.smul_tmul, ModuleCat.ExtendScalars.smul_tmul, mul_one]
      | add t t' ht ht' => rw [TensorProduct.tmul_add, map_add, map_add, ht, ht']
    | add y y' hy hy' => simp only [map_add, hy, hy']
  right_inv y := by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v m =>
      change cancelHom f x F M (v ⊗ₜ ((1 : X.presheaf.stalk x) ⊗ₜ[A, (stalkBaseMap f x).hom] m)) = _
      rw [cancelHom_tmul, one_smul]
    | add y y' hy hy' => simp only [map_add, hy, hy']

lemma cancelEquiv_naturality {N : ModuleCat.{u} A} (g : M ⟶ N)
    (y : (moduleStalk (R := X.sheaf) F.val x) ⊗[X.presheaf.stalk x] (stalkExt f M x)) :
    cancelEquiv f x F N
        (TensorProduct.map LinearMap.id
          ((ModuleCat.extendScalars (stalkBaseMap f x).hom).map g).hom y) =
      TensorProduct.map LinearMap.id g.hom (cancelEquiv f x F M y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul s m => rfl
    | add t t' ht ht' => simp only [TensorProduct.tmul_add, map_add, ht, ht']
  | add y y' hy hy' => simp only [map_add, hy, hy']

end Cancel

section Assemble

open ModuleSheafTensor

variable (x : X) (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

/-- `P(M)ₓ ≅ 𝒪_{X,x} ⊗_A M`. -/
noncomputable def sheafStalkEquiv (M : ModuleCat.{u} A) :
    moduleStalk (R := X.sheaf) (sh (prePresheaf f M)).val x ≃ₗ[X.presheaf.stalk x] stalkExt f M x :=
  (shUnitStalkEquiv x (prePresheaf f M)).symm.trans (preStalkIso f M x).symm

lemma sheafStalkEquiv_naturality {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (w : moduleStalk (R := X.sheaf) (sh (prePresheaf f M)).val x) :
    sheafStalkEquiv f x N (pStalkLinear x ((sheafFunctor f).map g).val w) =
      (ModuleCat.extendScalars (stalkBaseMap f x).hom).map g (sheafStalkEquiv f x M w) := by
  obtain ⟨z, rfl⟩ := (shUnitStalk_bijective x (prePresheaf f M)).2 w
  have h1 : pStalkLinear x ((sheafFunctor f).map g).val (shUnitStalk x (prePresheaf f M) z) =
      shUnitStalk x (prePresheaf f N) (pStalkMap x (prePresheafMap f g) z) :=
    (shUnitStalk_naturality x (prePresheafMap f g) z).symm
  have h2 : ∀ {P : PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)}
      (z : moduleStalk (R := X.sheaf) P x),
      (shUnitStalkEquiv x P).symm (shUnitStalk x P z) = z := fun z =>
    (shUnitStalkEquiv x _).symm_apply_apply z
  simp only [sheafStalkEquiv, LinearEquiv.trans_apply]
  rw [h1, h2, h2]
  exact preStalkToExt_naturality f x g z

/-- **Stalks of `F ⊗ P(M)`.** `(F ⊗_{𝒪_X} P(M))ₓ ≃ Fₓ ⊗_A M`. -/
noncomputable def tensorSheafStalkEquiv (M : ModuleCat.{u} A) :
    moduleStalk (R := X.sheaf) (moduleSheafTensor F (sh (prePresheaf f M))).val x ≃+
      (stalkA f x F) ⊗[A] M :=
  (moduleSheafTensorStalkIso F (sh (prePresheaf f M)) x).toAddEquiv.trans
    ((LinearEquiv.lTensor (moduleStalk (R := X.sheaf) F.val x)
      (sheafStalkEquiv f x M)).toAddEquiv.trans (cancelEquiv f x F M))

lemma tensorSheafStalkEquiv_naturality_aux {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (z : (moduleStalk (R := X.sheaf) F.val x) ⊗[X.presheaf.stalk x]
      (moduleStalk (R := X.sheaf) (sh (prePresheaf f M)).val x)) :
    cancelEquiv f x F N (LinearEquiv.lTensor (moduleStalk (R := X.sheaf) F.val x)
        (sheafStalkEquiv f x N)
        (TensorProduct.map LinearMap.id (pStalkLinear x ((sheafFunctor f).map g).val) z)) =
      TensorProduct.map LinearMap.id g.hom (cancelEquiv f x F M
        (LinearEquiv.lTensor (moduleStalk (R := X.sheaf) F.val x) (sheafStalkEquiv f x M) z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v w =>
    rw [TensorProduct.map_tmul, LinearEquiv.lTensor_tmul, LinearEquiv.lTensor_tmul,
      LinearMap.id_apply, sheafStalkEquiv_naturality f x g w]
    exact cancelEquiv_naturality f x F M g (v ⊗ₜ sheafStalkEquiv f x M w)
  | add z z' hz hz' => simp only [map_add, hz, hz']

lemma tensorSheafStalkEquiv_naturality {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (y : moduleStalk (R := X.sheaf) (moduleSheafTensor F (sh (prePresheaf f M))).val x) :
    tensorSheafStalkEquiv f x F N
        (pStalkMap x ((tensorFunctor F).map ((sheafFunctor f).map g)).val y) =
      TensorProduct.map LinearMap.id g.hom (tensorSheafStalkEquiv f x F M y) := by
  simp only [tensorSheafStalkEquiv, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
  erw [tensorStalkIso_naturality]
  exact tensorSheafStalkEquiv_naturality_aux f x F g _

end Assemble

section Flatness

open ModuleSheafTensor

variable (x : X) (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

lemma stalkBaseMap_eq :
    stalkBaseMap f x =
      ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ (f x) trivial) ≫ f.stalkMap x := by
  rw [Category.assoc, Scheme.Hom.germ_stalkMap, stalkBaseMap, baseMap_top, Category.assoc]
  rfl

lemma flat_specStalk (y : Spec A) :
    ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ y trivial).hom.Flat := by
  rw [← Spec.algebraMap_stalkIso_inv]
  exact RingHom.Flat.comp
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ y.asIdeal.primeCompl))
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Spec.stalkIso A y).inv))

theorem stalkA_flat (hF : Scheme.Modules.FlatOverAt f F x) : Module.Flat A (stalkA f x F) := by
  let Ys := (Spec A).presheaf.stalk (f x)
  let Fx := moduleStalk (R := X.sheaf) F.val x
  let _ : Algebra A Ys :=
    ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.germ ⊤ (f x) trivial).hom.toAlgebra
  let _ : Module Ys Fx := Module.compHom Fx (f.stalkMap x).hom
  have : Module.Flat Ys Fx := hF
  have : Module.Flat A Ys := flat_specStalk (f x)
  let _ : Module A Fx := (stalkA f x F).isModule
  have : IsScalarTower A Ys Fx := IsScalarTower.of_algebraMap_smul fun a v => by
    change (f.stalkMap x).hom (((Scheme.ΓSpecIso A).inv ≫
      (Spec A).presheaf.germ ⊤ (f x) trivial).hom a) • v = (stalkBaseMap f x).hom a • v
    rw [stalkBaseMap_eq]
    rfl
  exact Module.Flat.trans A Ys Fx

end Flatness

section Exactness

variable (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

instance : (sheafFunctor f).IsLeftAdjoint := (sheafAdjunction f).isLeftAdjoint

instance : (tensorFunctor F).PreservesZeroMorphisms where
  map_zero G G' := by
    change (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)).map
      (F.val ◁ (0 : G ⟶ G').val) = 0
    have : F.val ◁ (0 : G ⟶ G').val = 0 := by
      ext U : 1
      exact MonoidalPreadditive.whiskerLeft_zero (C := ModuleCat _)
    rw [this, Functor.map_zero]

/-- The functor `M ↦ F ⊗_{𝒪_X} P(M)`, to sheaves of abelian groups. -/
noncomputable def sheafModel : ModuleCat.{u} A ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafFunctor f ⋙ tensorFunctor F ⋙ SheafOfModules.toSheaf (ringCatSheafOf X.sheaf)

instance : (sheafModel f F).PreservesZeroMorphisms := by
  have : (sheafFunctor f).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : (SheafOfModules.toSheaf (ringCatSheafOf X.sheaf)).PreservesZeroMorphisms := inferInstance
  have : (tensorFunctor F ⋙
      SheafOfModules.toSheaf (ringCatSheafOf X.sheaf)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_comp _ _
  exact Functor.preservesZeroMorphisms_comp _ _

variable (x : X) {S : ShortComplex (ModuleCat.{u} A)}

/-- The short complex `Fₓ ⊗_A S` of abelian groups. -/
noncomputable def stalkTensorComplex (S : ShortComplex (ModuleCat.{u} A)) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    (AddCommGrpCat.ofHom (TensorProduct.map LinearMap.id S.f.hom :
      (stalkA f x F) ⊗[A] S.X₁ →ₗ[A] (stalkA f x F) ⊗[A] S.X₂).toAddMonoidHom)
    (AddCommGrpCat.ofHom (TensorProduct.map LinearMap.id S.g.hom :
      (stalkA f x F) ⊗[A] S.X₂ →ₗ[A] (stalkA f x F) ⊗[A] S.X₃).toAddMonoidHom)
    (by
      ext y
      change (TensorProduct.map LinearMap.id S.g.hom) (TensorProduct.map LinearMap.id S.f.hom y) = 0
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp,
        ← ModuleCat.hom_comp, S.zero, ModuleCat.hom_zero, TensorProduct.map_zero_right,
        LinearMap.zero_apply])

lemma stalkTensorComplex_shortExact (hflat : Module.Flat A (stalkA f x F)) (hS : S.ShortExact) :
    (stalkTensorComplex f F x S).ShortExact := by
  have hf : Function.Injective S.f.hom := hS.moduleCat_injective_f
  have hg : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  have hfg : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff_function_exact]
    exact Module.Flat.lTensor_exact (stalkA f x F) hfg
  · rw [AddCommGrpCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom hf
  · rw [AddCommGrpCat.epi_iff_surjective]
    exact LinearMap.lTensor_surjective (stalkA f x F) hg

/-- The stalks of `F ⊗ P(S)` form the short complex `Fₓ ⊗_A S`. -/
noncomputable def stalkComplexIso (S : ShortComplex (ModuleCat.{u} A)) :
    S.map (sheafModel f F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) ≅ stalkTensorComplex f F x S :=
  ShortComplex.isoMk (tensorSheafStalkEquiv f x F S.X₁).toAddCommGrpIso
    (tensorSheafStalkEquiv f x F S.X₂).toAddCommGrpIso
    (tensorSheafStalkEquiv f x F S.X₃).toAddCommGrpIso
    (by
      ext y
      exact (tensorSheafStalkEquiv_naturality f x F S.f y).symm)
    (by
      ext y
      exact (tensorSheafStalkEquiv_naturality f x F S.g y).symm)

open Limits ZeroObject in
theorem sheafModel_shortExact (hF : Scheme.Modules.FlatOver f F) (hS : S.ShortExact) :
    (S.map (sheafModel f F)).ShortExact := by
  have hx : ∀ x : X, (S.map (sheafModel f F ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).ShortExact := fun x =>
    ShortComplex.shortExact_of_iso (stalkComplexIso f F x S).symm
      (stalkTensorComplex_shortExact f F x (stalkA_flat f x F (hF x)) hS)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    exact fun x => (hx x).exact
  · rw [TopCat.Presheaf.mono_iff_stalk_mono]
    exact fun x => (hx x).mono_f
  · let T := ShortComplex.mk (S.map (sheafModel f F)).g
      (0 : (S.map (sheafModel f F)).X₃ ⟶ (0 : TopCat.Sheaf AddCommGrpCat.{u} X)) Limits.comp_zero
    have hT : T.Exact := by
      rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
      intro x
      rw [ShortComplex.exact_iff_epi _ (Functor.map_zero (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) _ _)]
      exact (hx x).epi_g
    exact (ShortComplex.exact_iff_epi T rfl).mp hT

end Exactness

lemma tensorFunctor_additive (F : SheafOfModules.{u} (ringCatSheafOf X.sheaf)) :
    (tensorFunctor F).Additive where
  map_add {G G' b b'} := by
    have : Limits.PreservesColimitsOfSize.{0, 0}
        (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)) :=
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringCatSheafOf X.sheaf).obj)).leftAdjoint_preservesColimits
    have : Limits.PreservesBinaryBiproducts
        (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)) :=
      Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    have : (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)).Additive :=
      Functor.additive_of_preservesBinaryBiproducts _
    change (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf X.sheaf).obj)).map
      (F.val ◁ (b + b').val) = (PresheafOfModules.sheafification _).map (F.val ◁ b.val) +
        (PresheafOfModules.sheafification _).map (F.val ◁ b'.val)
    have : F.val ◁ (b + b').val = F.val ◁ b.val + F.val ◁ b'.val := by
      ext U : 1
      exact MonoidalPreadditive.whiskerLeft_add (C := ModuleCat _) (X := F.val.obj U)
        (b.val.app U) (b'.val.app U)
    rw [this, Functor.map_add]

end CohomologyTensorDelta

open CohomologyTensorDelta

section DeltaFunctor

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]

/-- **Covariant δ-functors** (Hartshorne III.1, p. 205). A family of functors `Tⁱ : C ⥤ D`
(`i ≥ 0`) with, for every short exact sequence `0 ⟶ A' ⟶ A ⟶ A'' ⟶ 0`, morphisms
`δⁱ : Tⁱ(A'') ⟶ Tⁱ⁺¹(A')` such that the sequence
`0 ⟶ T⁰(A') ⟶ T⁰(A) ⟶ T⁰(A'') ⟶ T¹(A') ⟶ ⋯ ⟶ Tⁱ(A) ⟶ Tⁱ(A'') ⟶ Tⁱ⁺¹(A') ⟶ Tⁱ⁺¹(A) ⟶ ⋯`
is exact (a complex which is exact at every term), and the `δⁱ` commute with the maps induced
by a morphism of short exact sequences. -/
structure IsCovariantDeltaFunctor (T : ℕ → C ⥤ D)
    (δ : ∀ S : ShortComplex C, S.ShortExact → ∀ i : ℕ, (T i).obj S.X₃ ⟶ (T (i + 1)).obj S.X₁) :
    Prop where
  /-- `0 ⟶ T⁰(A') ⟶ T⁰(A)` is exact. -/
  mono_map_f : ∀ (S : ShortComplex C) (_ : S.ShortExact), Mono ((T 0).map S.f)
  /-- `Tⁱ(A') ⟶ Tⁱ(A) ⟶ Tⁱ(A'')` is a complex. -/
  map_f_comp_map_g : ∀ (S : ShortComplex C) (_ : S.ShortExact) (i : ℕ),
    (T i).map S.f ≫ (T i).map S.g = 0
  /-- Exactness at `Tⁱ(A)`. -/
  exact_map_f_map_g : ∀ (S : ShortComplex C) (hS : S.ShortExact) (i : ℕ),
    (ShortComplex.mk _ _ (map_f_comp_map_g S hS i)).Exact
  /-- `Tⁱ(A) ⟶ Tⁱ(A'') ⟶ Tⁱ⁺¹(A')` is a complex. -/
  map_g_comp_δ : ∀ (S : ShortComplex C) (hS : S.ShortExact) (i : ℕ),
    (T i).map S.g ≫ δ S hS i = 0
  /-- Exactness at `Tⁱ(A'')`. -/
  exact_map_g_δ : ∀ (S : ShortComplex C) (hS : S.ShortExact) (i : ℕ),
    (ShortComplex.mk _ _ (map_g_comp_δ S hS i)).Exact
  /-- `Tⁱ(A'') ⟶ Tⁱ⁺¹(A') ⟶ Tⁱ⁺¹(A)` is a complex. -/
  δ_comp_map_f : ∀ (S : ShortComplex C) (hS : S.ShortExact) (i : ℕ),
    δ S hS i ≫ (T (i + 1)).map S.f = 0
  /-- Exactness at `Tⁱ⁺¹(A')`. -/
  exact_δ_map_f : ∀ (S : ShortComplex C) (hS : S.ShortExact) (i : ℕ),
    (ShortComplex.mk _ _ (δ_comp_map_f S hS i)).Exact
  /-- Naturality of `δ` in morphisms of short exact sequences. -/
  δ_naturality : ∀ (S₁ S₂ : ShortComplex C) (φ : S₁ ⟶ S₂) (h₁ : S₁.ShortExact)
    (h₂ : S₂.ShortExact) (i : ℕ), δ S₁ h₁ i ≫ (T (i + 1)).map φ.τ₁ = (T i).map φ.τ₃ ≫ δ S₂ h₂ i

end DeltaFunctor

/-- Global sections `Γ(X, -)` of sheaves of abelian groups. -/
noncomputable def abelianSheafGlobalSections (X : TopCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ (evaluation _ _).obj (op ⊤)

instance (X : TopCat.{u}) : Limits.PreservesFiniteLimits (abelianSheafGlobalSections X) := by
  have h₁ : Limits.PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X) := inferInstance
  have h₂ : Limits.PreservesFiniteLimits
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)) := inferInstance
  exact @Limits.comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂

instance (X : TopCat.{u}) : (abelianSheafGlobalSections X).Additive :=
  Functor.additive_of_preserves_binary_products _

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) (F : X.Modules)

/-- The functor `M ↦ F ⊗_A M := F ⊗_{𝒪_X} f^*(M̃)` from `A`-modules to sheaves of abelian groups
on `X`. -/
noncomputable def tensorPullbackTilde : ModuleCat.{u} A ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  tilde.functor A ⋙ Scheme.Modules.pullback f ⋙ tensorFunctor F ⋙
    SheafOfModules.toSheaf (ringCatSheafOf X.sheaf)

instance : (tensorPullbackTilde f F).PreservesZeroMorphisms := by
  have : (tensorFunctor F ⋙
      SheafOfModules.toSheaf (ringCatSheafOf X.sheaf)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_comp _ _
  have : (Scheme.Modules.pullback f ⋙ tensorFunctor F ⋙
      SheafOfModules.toSheaf (ringCatSheafOf X.sheaf)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_comp _ _
  exact Functor.preservesZeroMorphisms_comp _ _

/-- `Tⁱ(M) = Hⁱ(X, F ⊗_A M)`, the `i`-th right derived functor of `Γ(X, -)` evaluated at
`F ⊗_{𝒪_X} f^*(M̃)`. -/
noncomputable def cohomologyTensor (i : ℕ) : ModuleCat.{u} A ⥤ AddCommGrpCat.{u} :=
  tensorPullbackTilde f F ⋙ (abelianSheafGlobalSections X).rightDerived i

instance (i : ℕ) : (cohomologyTensor f F i).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_comp _ _

/-- If `F` is flat over `Spec A`, then `M ↦ F ⊗_{𝒪_X} f^*(M̃)` is exact. -/
theorem tensorPullbackTilde_shortExact (hflat : F.FlatOver f)
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) :
    (S.map (tensorPullbackTilde f F)).ShortExact := by
  have : (tensorFunctor F).Additive := tensorFunctor_additive F
  let e : sheafModel f F ≅ tensorPullbackTilde f F :=
    Functor.isoWhiskerRight (sheafFunctorIso f) (tensorFunctor F ⋙ SheafOfModules.toSheaf _)
  exact ShortComplex.shortExact_of_iso (S.mapNatIso e) (sheafModel_shortExact f F hflat hS)

/-- The connecting morphisms `Tⁱ(M'') ⟶ Tⁱ⁺¹(M')` of a short exact sequence of `A`-modules. -/
noncomputable def cohomologyTensorδ (hflat : F.FlatOver f) (S : ShortComplex (ModuleCat.{u} A))
    (hS : S.ShortExact) (i : ℕ) :
    (cohomologyTensor f F i).obj S.X₃ ⟶ (cohomologyTensor f F (i + 1)).obj S.X₁ :=
  rightDerivedδ (abelianSheafGlobalSections X) (tensorPullbackTilde_shortExact f F hflat hS) i


/-- **Hartshorne III.12, before Proposition 12.2.** Let `A` be Noetherian, `f : X ⟶ Spec A`
projective and `F` a coherent `𝒪_X`-module flat over `Spec A`. Then the functors
`Tⁱ(M) = Hⁱ(X, F ⊗_A M)` are additive, and together with the connecting morphisms of the long exact
cohomology sequences they form a covariant δ-functor from `A`-modules to abelian groups; in
particular every `Tⁱ` is exact in the middle. -/
theorem cohomologyTensor_isCovariantDeltaFunctor [IsNoetherianRing A] (hf : Projective f)
    (hF : IsCoherent F) (hflat : F.FlatOver f) :
    (∀ i, (cohomologyTensor f F i).Additive) ∧
      IsCovariantDeltaFunctor (cohomologyTensor f F) (cohomologyTensorδ f F hflat) := by
  have : (tensorFunctor F).Additive := tensorFunctor_additive F
  refine ⟨fun i => ?_, ⟨fun S hS => ?_, fun S hS i => ?_, fun S hS i => ?_, fun S hS i => ?_,
    fun S hS i => ?_, fun S hS i => ?_, fun S hS i => ?_, fun S₁ S₂ φ h₁ h₂ i => ?_⟩⟩
  · have h : (SheafOfModules.toSheaf (ringCatSheafOf X.sheaf)).Additive := inferInstance
    have : (tensorPullbackTilde f F).Additive := ⟨fun {M N a b} => by
      simp only [tensorPullbackTilde, Functor.comp_map, Functor.map_add]
      exact h.map_add⟩
    exact ⟨fun {M N a b} => by simp only [cohomologyTensor, Functor.comp_map, Functor.map_add]⟩
  · exact rightDerived_mono_map_f _ (tensorPullbackTilde_shortExact f F hflat hS)
  · rw [← Functor.map_comp, S.zero, Functor.map_zero]
  · exact rightDerived_exact₂ _ (tensorPullbackTilde_shortExact f F hflat hS) i
  · exact RightDerivedLES.Horseshoe.map_g_comp_δ (abelianSheafGlobalSections X)
      (tensorPullbackTilde_shortExact f F hflat hS) _ _ i
  · exact rightDerived_exact₃ _ (tensorPullbackTilde_shortExact f F hflat hS) i
  · exact RightDerivedLES.Horseshoe.δ_comp_map_f (abelianSheafGlobalSections X)
      (tensorPullbackTilde_shortExact f F hflat hS) _ _ i
  · exact rightDerived_exact₁ _ (tensorPullbackTilde_shortExact f F hflat hS) i
  · exact rightDerivedδ_naturality _ ((tensorPullbackTilde f F).mapShortComplex.map φ)
      (tensorPullbackTilde_shortExact f F hflat h₁) (tensorPullbackTilde_shortExact f F hflat h₂) i

end Hartshorne
