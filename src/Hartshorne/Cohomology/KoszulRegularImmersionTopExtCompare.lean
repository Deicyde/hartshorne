/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulRegularImmersionTopExtRestrict
import Hartshorne.RingedSpace.SheafExtTopMap
import Hartshorne.RingedSpace.ModuleSheafHomEvalAt

/-!
# Comparing local top-Ext isomorphisms on smaller opens

Let `σ : A → B` be a ring map and `f₁, …, f_r ∈ A`. The Koszul complexes `K_•(f; A)` and
`K_•(σ f; B)` are related by the `σ`-semilinear chain map `x ⊗ a ↦ ⋀σ(x) ⊗ σ(a)`
(`Hartshorne.Koszul.koszulBaseChangeMap`), which sends the top generator `e₁ ∧ ⋯ ∧ e_r ⊗ 1` to the
top generator.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct ChangeOfRings

/- The terms of the Koszul complex and the sections of restricted and transported modules are only
definitionally (not reducibly) the underlying modules. -/
set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace Koszul

open SheafTensorOperations

variable {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B)

/-- The `σ`-semilinear map `A^r → B^r`, `v ↦ σ ∘ v`. -/
def piMapSemilinear (r : ℕ) : (Fin r → A) →ₛₗ[σ] (Fin r → B) where
  toFun v i := σ (v i)
  map_add' v w := by ext i; simp
  map_smul' a v := by ext i; simp

variable {r : ℕ} (f : Fin r → A)

/-- **Base change of the Koszul complex** in degree `p`: the `σ`-semilinear map
`⋀^p A^r ⊗_A A → ⋀^p B^r ⊗_B B`, `x ⊗ a ↦ ⋀σ(a x) ⊗ 1`. -/
noncomputable def koszulBaseChangeMap (p : ℕ) :
    (sequenceKoszulComplex f (ModuleCat.of A A)).X p →ₛₗ[σ]
      (sequenceKoszulComplex (fun j => σ (f j)) (ModuleCat.of B B)).X p :=
  ((TensorProduct.rid B (⋀[B]^p (Fin r → B))).symm.toLinearMap.comp
    (exteriorPowerMap p σ (piMapSemilinear σ r))).comp
      (TensorProduct.rid A (⋀[A]^p (Fin r → A))).toLinearMap

lemma koszulBaseChangeMap_tmul_ιMulti (p : ℕ) (v : Fin p → Fin r → A) (a : A) :
    koszulBaseChangeMap σ f p (exteriorPower.ιMulti A p v ⊗ₜ[A] a) =
      exteriorPower.ιMulti B p (fun i => piMapSemilinear σ r (v i)) ⊗ₜ[B] σ a := by
  change (TensorProduct.rid B _).symm (exteriorPowerMap p σ (piMapSemilinear σ r)
    (TensorProduct.rid A _ (exteriorPower.ιMulti A p v ⊗ₜ[A] a))) = _
  rw [TensorProduct.rid_tmul, map_smulₛₗ, exteriorPowerMap_ιMulti, LinearEquiv.map_smul,
    TensorProduct.rid_symm_apply, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
    smul_eq_mul, mul_one]

lemma koszulForm_piMapSemilinear (v : Fin r → A) :
    koszulForm (fun j => σ (f j)) (piMapSemilinear σ r v) = σ (koszulForm f v) := by
  rw [koszulForm_apply, koszulForm_apply, map_sum]
  simp [piMapSemilinear]

/-- The base change maps form a chain map. -/
lemma koszulBaseChangeMap_d (p : ℕ) (x : (sequenceKoszulComplex f (ModuleCat.of A A)).X (p + 1)) :
    ((sequenceKoszulComplex (fun j => σ (f j)) (ModuleCat.of B B)).d (p + 1) p).hom
        (koszulBaseChangeMap σ f (p + 1) x) =
      koszulBaseChangeMap σ f p
        (((sequenceKoszulComplex f (ModuleCat.of A A)).d (p + 1) p).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x a =>
    have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A (p + 1))) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [koszulBaseChangeMap_tmul_ιMulti, koszulComplex_d_tmul_ιMulti,
        koszulComplex_d_tmul_ιMulti]
      refine Eq.trans ?_ (map_sum (koszulBaseChangeMap σ f p) _ _).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smulₛₗ, koszulBaseChangeMap_tmul_ιMulti, map_pow, map_neg, map_one, smul_eq_mul,
        smul_eq_mul, map_mul, koszulForm_piMapSemilinear]
      rfl
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add y z _ _ hy hz => simp only [TensorProduct.add_tmul, map_add, hy, hz]
    | smul c y _ hy =>
      rw [← TensorProduct.smul_tmul', map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hy]
      rfl

lemma piMapSemilinear_basisFun (j : Fin r) :
    piMapSemilinear σ r (Pi.basisFun A (Fin r) j) = Pi.basisFun B (Fin r) j := by
  ext i
  simp only [piMapSemilinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.basisFun_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [Ne.symm h]

/-- The base change map sends `e₁ ∧ ⋯ ∧ e_r ⊗ 1` to `e₁ ∧ ⋯ ∧ e_r ⊗ 1`. -/
lemma koszulBaseChangeMap_topForm :
    koszulBaseChangeMap σ f r (topForm r ⊗ₜ[A] (1 : A)) = topForm r ⊗ₜ[B] (1 : B) := by
  rw [topForm, topForm, exteriorPower.ιMulti_family, exteriorPower.ιMulti_family,
    koszulBaseChangeMap_tmul_ιMulti, map_one]
  congr 2
  funext i
  exact piMapSemilinear_basisFun σ _

/-- The base change map sends the standard basis vector `e_I ⊗ 1` to `e_I ⊗ 1`. -/
lemma koszulBaseChangeMap_basis (p : ℕ) (I : Set.powersetCard (Fin r) p) :
    koszulBaseChangeMap σ f p (exteriorPower.ιMulti_family A p (Pi.basisFun A (Fin r)) I ⊗ₜ[A]
      (1 : A)) = exteriorPower.ιMulti_family B p (Pi.basisFun B (Fin r)) I ⊗ₜ[B] (1 : B) := by
  rw [exteriorPower.ιMulti_family, exteriorPower.ιMulti_family, koszulBaseChangeMap_tmul_ιMulti,
    map_one]
  congr 2
  funext i
  exact piMapSemilinear_basisFun σ _

/-- The standard basis `e_I ⊗ 1` of `K_p(f; A) = ⋀^p A^r ⊗_A A`. -/
noncomputable def koszulBasis (p : ℕ) :
    Module.Basis (ULift.{u} (Set.powersetCard (Fin r) p)) A
      ((sequenceKoszulComplex f (ModuleCat.of A A)).X p) :=
  (((Pi.basisFun A (Fin r)).exteriorPower (n := p)).map
    (TensorProduct.rid A (⋀[A]^p (Fin r → A))).symm).reindex Equiv.ulift.symm

lemma koszulBasis_apply (p : ℕ) (I : ULift.{u} (Set.powersetCard (Fin r) p)) :
    koszulBasis f p I =
      exteriorPower.ιMulti_family A p (Pi.basisFun A (Fin r)) I.down ⊗ₜ[A] (1 : A) := by
  have h := Module.Basis.reindex_apply (((Pi.basisFun A (Fin r)).exteriorPower (n := p)).map
    (TensorProduct.rid A (⋀[A]^p (Fin r → A))).symm) Equiv.ulift.symm I
  rw [Module.Basis.map_apply, exteriorPower.basis_apply, TensorProduct.rid_symm_apply] at h
  exact h

/-- In degree zero, the base change map is `σ` under `K_0 ≅ A`, `K_0 ≅ B`. -/
lemma degreeZeroEquiv_koszulBaseChangeMap (x : (sequenceKoszulComplex f (ModuleCat.of A A)).X 0) :
    degreeZeroEquiv (V := Fin r → B) B (koszulBaseChangeMap σ f 0 x) =
      σ (degreeZeroEquiv (V := Fin r → A) A x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, map_zero]
  | add x y hx hy => rw [map_add, LinearEquiv.map_add, hx, hy, LinearEquiv.map_add, map_add]
  | tmul x a =>
    have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 0)) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      rw [koszulBaseChangeMap_tmul_ιMulti, degreeZeroEquiv_tmul, degreeZeroEquiv_tmul,
        exteriorPower.zeroEquiv_ιMulti, exteriorPower.zeroEquiv_ιMulti, one_smul, one_smul]
    | zero =>
      rw [TensorProduct.zero_tmul, map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, map_zero]
    | add y z _ _ hy hz =>
      rw [TensorProduct.add_tmul, map_add, LinearEquiv.map_add, hy, hz, LinearEquiv.map_add,
        map_add]
    | smul c y _ hy =>
      rw [← TensorProduct.smul_tmul', map_smulₛₗ, LinearEquiv.map_smul, LinearEquiv.map_smul, hy,
        smul_eq_mul, smul_eq_mul, map_mul]

/-- The base change map sends `k₀` to `k₀`. -/
lemma koszulBaseChangeMap_k₀ :
    koszulBaseChangeMap σ f 0 (Ringed.KoszulSheaf.k₀ f) =
      Ringed.KoszulSheaf.k₀ (fun j => σ (f j)) := by
  apply (degreeZeroEquiv (V := Fin r → B) B).injective
  rw [degreeZeroEquiv_koszulBaseChangeMap, Ringed.KoszulSheaf.k₀, Ringed.KoszulSheaf.k₀,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_one]

end Koszul

namespace Ringed

namespace ScalarExtension

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {A : Type u} [CommRing A] (φ : A →+* R.obj.obj (op ⊤)) (N : ModuleCat.{u} A)
  [Module.Free A N] [Module.Finite A N]

/-- Morphisms out of `𝒪_X ⊗_A N` are determined by the images of the global sections `1 ⊗ n`. -/
lemma hom_ext_of_tmul_one {G : SheafOfModules.{u} (ringCatSheafOf R)} {p q : sheaf φ N ⟶ G}
    (h : ∀ n : N, p.val.app (op ⊤) ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] n) =
      q.val.app (op ⊤) ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] n)) : p = q := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ((ModuleCat.extendRestrictScalarsAdj (baseMap φ V.unop)).homEquiv _ _).injective
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  have e : ((1 : R.obj.obj V) ⊗ₜ[A, baseMap φ V.unop] m : (presheaf φ N).obj V) =
      (presheaf φ N).map (homOfLE (le_top : V.unop ≤ ⊤)).op
        ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] m) := by
    rw [presheaf_map_tmul, map_one]
  have hp := ConcreteCategory.congr_hom (p.val.naturality (homOfLE (le_top : V.unop ≤ ⊤)).op)
    ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] m)
  have hq := ConcreteCategory.congr_hom (q.val.naturality (homOfLE (le_top : V.unop ≤ ⊤)).op)
    ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] m)
  simp only [ConcreteCategory.comp_apply] at hp hq
  erw [e]
  exact hp.trans ((congrArg _ (h m)).trans hq.symm)

end ScalarExtension

/-- Local freeness of finite rank is invariant under isomorphism. -/
lemma isFiniteLocallyFree_of_iso {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X)
    CommRingCat.{u}} {F G : SheafOfModules.{u} (ringCatSheafOf R)} (e : F ≅ G)
    (hF : IsFiniteLocallyFree F) : IsFiniteLocallyFree G := fun x => by
  obtain ⟨U, hx, r, ⟨e'⟩⟩ := hF x
  exact ⟨U, hx, r, ⟨(SheafOfModules.overFunctor _ U).mapIso e.symm ≪≫ e'⟩⟩

namespace KoszulSheaf

open Koszul ScalarExtension

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {A : Type u} [CommRing A] (φ : A →+* R.obj.obj (op ⊤)) {s : ℕ} (f : Fin (s + 1) → A)

/-- Evaluation at the top generator is evaluation at the global section `topSection`. -/
lemma topEval_eq_homEvalAt (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    topEval φ f G = homEvalAt (topSection φ f ⊤) G := by
  apply SheafOfModules.hom_ext
  ext W σ
  change moduleSheafHomEval σ (le_refl _) (topSection φ f W.unop) =
    moduleSheafHomEval σ (le_refl _)
      (((complex φ f).X (s + 1)).val.presheaf.map (homOfLE le_top).op (topSection φ f ⊤))
  rw [topSection_restrict]

/-- The restriction of `topSection` to an open subspace `U`, pulled back to `𝒪_U ⊗_A K_r`, is
`topSection` of `U`. -/
lemma restrictComplexIso_inv_topSection (U : Opens X) :
    ((restrictComplexIso φ f U).inv.f (s + 1)).val.app (op ⊤)
        (restrictSection U (topSection φ f ⊤)) = topSection (restrictBase φ U) f ⊤ := by
  have h1 : restrictSection U (topSection φ f ⊤) =
      (restrictSheafHom φ U ((K f).X (s + 1))).val.app (op ⊤)
        (topSection (restrictBase φ U) f ⊤) := by
    rw [restrictSheafHom_topSection]
    exact topSection_restrict φ f le_top
  rw [h1]
  change ((restrictComplexIso φ f U).hom.f (s + 1) ≫
    (restrictComplexIso φ f U).inv.f (s + 1)).val.app (op ⊤) _ = _
  rw [← HomologicalComplex.comp_f, Iso.hom_inv_id]
  rfl

omit f in
/-- Morphisms out of `𝒪_X ⊗_A K_0` are determined by the image of `1 ⊗ k₀`. -/
lemma hom_ext_k₀ {r : ℕ} (g : Fin r → A) {G : SheafOfModules.{u} (ringCatSheafOf R)}
    {p q : (complex φ g).X 0 ⟶ G}
    (h : p.val.app (op ⊤) ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] k₀ g) =
      q.val.app (op ⊤) ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] k₀ g)) : p = q := by
  apply hom_ext_of_tmul_one
  intro n
  have e : ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] n :
        (ModuleCat.extendScalars (baseMap φ ⊤)).obj ((K g).X 0)) =
      baseMap φ ⊤ (degreeZeroEquiv (V := Fin r → A) A n) •
        ((1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] k₀ g :
          (ModuleCat.extendScalars (baseMap φ ⊤)).obj ((K g).X 0)) := by
    refine (congrArg (fun x => (1 : R.obj.obj (op ⊤)) ⊗ₜ[A, baseMap φ ⊤] x)
      (eq_smul_k₀ g n)).trans ?_
    refine (TensorProduct.smul_tmul (R := A) (M := (ModuleCat.restrictScalars (baseMap φ ⊤)).obj
      (ModuleCat.of _ (R.obj.obj (op ⊤)))) (degreeZeroEquiv (V := Fin r → A) A n)
        (1 : R.obj.obj (op ⊤)) (k₀ g)).symm.trans ?_
    exact (ModuleCat.ExtendScalars.smul_tmul (f := baseMap φ ⊤) _ 1 _).symm
  erw [e, map_smul, map_smul]
  exact congrArg _ h

end KoszulSheaf



end Ringed

end Hartshorne

namespace Hartshorne

namespace Ringed

namespace KoszulSheaf

section Compare

open Koszul ScalarExtension Transport RestrictCompose SheafExtRestrict

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (U : Opens X) (V' : Opens ((Opens.toTopCat X).obj U))
  {A B : Type u} [CommRing A] [CommRing B]
  (φA : A →+* (restrictRingSheaf R U).obj.obj (op ⊤))
  (φB : B →+* (restrictRingSheaf R ((incl U).obj V')).obj.obj (op ⊤)) (σ : A →+* B)
  (hσ : ∀ a, (ringTransport U V' R).φ.hom.app (op ⊤) (baseMap (restrictBase φA V') ⊤ a) =
    baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤) (σ a))
  {r : ℕ} (f : Fin r → A)

/-- The `A`-linear map `K_p(f; A) → τ(𝒪_V ⊗_B K_p(σ f; B))(V')`, `n ↦ 1 ⊗ σ_*(n)`. -/
noncomputable def compareLinear (p : ℕ) :
    (K f).X p ⟶ (ModuleCat.restrictScalars (baseMap (restrictBase φA V') ⊤)).obj
      (((transport (ringTransport U V' R)).obj
        ((complex φB (fun j => σ (f j))).X p)).val.obj (op ⊤)) :=
  ModuleCat.ofHom (X := (K f).X p)
    (Y := (ModuleCat.restrictScalars (baseMap (restrictBase φA V') ⊤)).obj
      (((transport (ringTransport U V' R)).obj
        ((complex φB (fun j => σ (f j))).X p)).val.obj (op ⊤)))
    { toFun n := (show ((complex φB (fun j => σ (f j))).X p).val.obj
          (op ((opensEquiv (homeo U V')).functor.obj ⊤)) from
        (1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
          (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
            baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)] koszulBaseChangeMap σ f p n)
      map_add' n n' := by rw [map_add]; exact TensorProduct.tmul_add _ _ _
      map_smul' a n := by
        refine (congrArg (fun x => (1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
          (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
            baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)] x)
              (map_smulₛₗ (koszulBaseChangeMap σ f p) a n)).trans ?_
        refine (TensorProduct.smul_tmul (R := B) (M := (ModuleCat.restrictScalars
          (baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤))).obj (ModuleCat.of _
            ((restrictRingSheaf R ((incl U).obj V')).obj.obj
              (op ((opensEquiv (homeo U V')).functor.obj ⊤))))) (σ a) _ _).symm.trans ?_
        refine Eq.trans ?_ (ModuleCat.ExtendScalars.smul_tmul
          (f := baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)) _ 1 _).symm
        congr 1
        simp only [RingHom.id_apply, mul_one]
        change baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤) (σ a) * 1 = _
        rw [mul_one, ← hσ a]
        rfl }

/-- **Comparison of Koszul sheaves along a restriction and a base change**: the morphism
`𝒪_{V'} ⊗_A K_p(f; A) ⟶ τ(𝒪_V ⊗_B K_p(σ f; B))`, `a ⊗ n ↦ a ⊗ σ_*(n)`, for `V'` open in `U` and
`V` the corresponding open of `X`. -/
noncomputable def compareHom (p : ℕ) :
    (complex (restrictBase φA V') f).X p ⟶
      (transport (ringTransport U V' R)).obj ((complex φB (fun j => σ (f j))).X p) :=
  ⟨homOfLinear (restrictBase φA V') _ (compareLinear U V' φA φB σ hσ f p)⟩

lemma compareHom_app_one (p : ℕ) (n : (K f).X p) :
    (compareHom U V' φA φB σ hσ f p).val.app (op ⊤)
        ((1 : (restrictRingSheaf (restrictRingSheaf R U) V').obj.obj (op ⊤)) ⊗ₜ[A,
          baseMap (restrictBase φA V') ⊤] n) =
      (show ((complex φB (fun j => σ (f j))).X p).val.obj
          (op ((opensEquiv (homeo U V')).functor.obj ⊤)) from
        (1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
          (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
            baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)] koszulBaseChangeMap σ f p n) := by
  refine (homOfLinear_app_tmul _ _ _ (op ⊤) 1 n).trans ?_
  rw [one_smul]
  erw [show (homOfLE (le_top : (⊤ : Opens ((Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V'))
    ≤ ⊤)).op = 𝟙 (op ⊤) from rfl, PresheafOfModules.map_id]
  rfl

/-- The comparison morphisms form a chain map. -/
noncomputable def compareComplex :
    complex (restrictBase φA V') f ⟶
      ((transport (ringTransport U V' R)).mapHomologicalComplex _).obj
        (complex φB (fun j => σ (f j))) where
  f p := compareHom U V' φA φB σ hσ f p
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    apply hom_ext_of_tmul_one
    intro n
    change ((complex φB (fun j => σ (f j))).d (j + 1) j).val.app
        (op ((opensEquiv (homeo U V')).functor.obj ⊤))
        ((compareHom U V' φA φB σ hσ f (j + 1)).val.app (op ⊤)
          ((1 : (restrictRingSheaf (restrictRingSheaf R U) V').obj.obj (op ⊤)) ⊗ₜ[A,
            baseMap (restrictBase φA V') ⊤] n)) =
      (compareHom U V' φA φB σ hσ f j).val.app (op ⊤)
        (((complex (restrictBase φA V') f).d (j + 1) j).val.app (op ⊤)
          ((1 : (restrictRingSheaf (restrictRingSheaf R U) V').obj.obj (op ⊤)) ⊗ₜ[A,
            baseMap (restrictBase φA V') ⊤] n))
    refine (congrArg (((complex φB (fun j => σ (f j))).d (j + 1) j).val.app
      (op ((opensEquiv (homeo U V')).functor.obj ⊤)))
        (compareHom_app_one U V' φA φB σ hσ f (j + 1) n)).trans ?_
    refine Eq.trans ?_
      (compareHom_app_one U V' φA φB σ hσ f j (((K f).d (j + 1) j).hom n)).symm
    show (1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
          (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
            baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)]
        ((K (fun j => σ (f j))).d (j + 1) j).hom (koszulBaseChangeMap σ f (j + 1) n) =
      (1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
          (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
            baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)]
        koszulBaseChangeMap σ f j (((K f).d (j + 1) j).hom n)
    rw [koszulBaseChangeMap_d]

lemma compareHom_topSection {s : ℕ} (g : Fin (s + 1) → A) :
    (compareHom U V' φA φB σ hσ g (s + 1)).val.app (op ⊤) (topSection (restrictBase φA V') g ⊤) =
      transportSection (ringTransport U V' R) (topSection φB (fun j => σ (g j)) ⊤) := by
  refine (compareHom_app_one U V' φA φB σ hσ g (s + 1) (topElt g)).trans ?_
  refine Eq.trans ?_ (topSection_restrict φB (fun j => σ (g j))
    (le_top : (opensEquiv (homeo U V')).functor.obj ⊤ ≤ ⊤)).symm
  show (1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
      (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
        baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)]
      koszulBaseChangeMap σ g (s + 1) (topForm (s + 1) ⊗ₜ[A] (1 : A)) =
    (1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
      (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
        baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)] (topForm (s + 1) ⊗ₜ[B] (1 : B))
  rw [koszulBaseChangeMap_topForm]

/-- The structure maps of the twice restricted and the once restricted ring sheaves are bijective
on sections. -/
lemma ringTransport_φ_bijective (O : Opens ((Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V')) :
    Function.Bijective ((ringTransport U V' R).φ.hom.app (op O)) := by
  let e : (ringCatSheafOf R).obj.obj (op (jA U V' O)) ≅
      (ringCatSheafOf R).obj.obj (op (jB U V' ((opensEquiv (homeo U V')).functor.obj O))) :=
    (ringCatSheafOf R).obj.mapIso
      (Iso.op ⟨homOfLE (jB_le_jA U V' O), homOfLE (jA_le_jB U V' O), rfl, rfl⟩)
  exact ConcreteCategory.bijective_of_isIso e.hom

-- Identifying the module structure of a transported sheaf with that of the original sheaf unfolds
-- the pushforward along the homeomorphism; this needs more than the default budget.
set_option maxHeartbeats 1000000 in
/-- **The comparison morphisms are isomorphisms.** -/
instance isIso_compareHom (p : ℕ) : IsIso (compareHom U V' φA φB σ hσ f p) := by
  refine ModuleGluing.isIso_of_bijective _ fun O => ?_
  let b := koszulBasis f p
  let b' := koszulBasis (fun j => σ (f j)) p
  have h : (compareHom U V' φA φB σ hσ f p).val.app O ∘ basisMap (restrictBase φA V') _ b O.unop =
      basisMap φB _ b' ((opensEquiv (homeo U V')).functor.obj O.unop) ∘
        (fun c => (ringTransport U V' R).φ.hom.app O ∘ c) := by
    funext c
    simp only [Function.comp_apply, basisMap, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (homOfLinear_app_tmul _ _ _ O (c j) (b j)).trans ?_
    have hb : koszulBaseChangeMap σ f p (b j) = b' j := by
      rw [koszulBasis_apply, koszulBasis_apply]
      exact koszulBaseChangeMap_basis σ f p j.down
    have hm : ((complex φB (fun j => σ (f j))).X p).val.map
          ((opensEquiv (homeo U V')).functor.map (homOfLE (le_top : O.unop ≤ ⊤))).op
          ((1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
            (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
              baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)] b' j) =
        ((1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
            (op ((opensEquiv (homeo U V')).functor.obj O.unop))) ⊗ₜ[B,
              baseMap φB ((opensEquiv (homeo U V')).functor.obj O.unop)] b' j) := by
      refine (presheaf_map_tmul φB _ _ _ _).trans ?_
      rw [map_one]
    change (ringTransport U V' R).φ.hom.app O (c j) •
        ((complex φB (fun j => σ (f j))).X p).val.map
          ((opensEquiv (homeo U V')).functor.map (homOfLE (le_top : O.unop ≤ ⊤))).op
          ((1 : (restrictRingSheaf R ((incl U).obj V')).obj.obj
            (op ((opensEquiv (homeo U V')).functor.obj ⊤))) ⊗ₜ[B,
              baseMap φB ((opensEquiv (homeo U V')).functor.obj ⊤)]
                koszulBaseChangeMap σ f p (b j)) = _
    rw [hb, hm]
    exact (ModuleCat.ExtendScalars.smul_tmul
      (f := baseMap φB ((opensEquiv (homeo U V')).functor.obj O.unop)) _ _ _).trans
        (by rw [mul_one])
  have h2 : Function.Bijective (basisMap φB _ b' ((opensEquiv (homeo U V')).functor.obj O.unop) ∘
      (fun c => (ringTransport U V' R).φ.hom.app O ∘ c)) :=
    (basisMap_bijective φB _ b' ((opensEquiv (homeo U V')).functor.obj O.unop)).comp
      (Function.Bijective.comp_left (ringTransport_φ_bijective U V' O.unop))
  rw [← h] at h2
  exact (Function.Bijective.of_comp_iff _
    (basisMap_bijective (restrictBase φA V') _ b O.unop)).1 h2

@[simp]
lemma compareComplex_f (p : ℕ) :
    (compareComplex U V' φA φB σ hσ f).f p = compareHom U V' φA φB σ hσ f p := rfl

end Compare

end KoszulSheaf

end Ringed

end Hartshorne

namespace Hartshorne

namespace KoszulImmersion

open AlgebraicGeometry Koszul Ringed.KoszulSheaf Ringed.ScalarExtension Ringed.Transport
  Ringed.RestrictCompose Ringed.SheafExtRestrict

section Compare

variable {Y : Scheme.{u}} {V₀ : Y.Opens} (W' : Opens ((Opens.toTopCat Y).obj V₀))

/-- An open of the subspace `V₀`, as an open of `Y`, is contained in `V₀`. -/
lemma incl_obj_le : (incl V₀).obj W' ≤ V₀ := incl_le W'

/-- The restriction map `Γ(Y, V₀) → Γ(Y, W')`. -/
noncomputable abbrev resRing : Γ(Y, V₀) →+* Γ(Y, (incl V₀).obj W') :=
  (Y.presheaf.map (homOfLE (incl_obj_le W')).op).hom

lemma resRing_compat (a : Γ(Y, V₀)) :
    (ringTransport V₀ W' Y.sheaf).φ.hom.app (op ⊤)
        (baseMap (restrictBase (restrictPhi V₀) W') ⊤ a) =
      baseMap (restrictPhi ((incl V₀).obj W')) ((opensEquiv (homeo V₀ W')).functor.obj ⊤)
        (resRing W' a) := by
  dsimp only [baseMap, restrictBase, restrictPhi, resRing, RingHom.comp_apply]
  change (Y.presheaf.map _ ≫ Y.presheaf.map _ ≫ Y.presheaf.map _ ≫ Y.presheaf.map _) a =
    (Y.presheaf.map _ ≫ Y.presheaf.map _ ≫ Y.presheaf.map _) a
  simp only [← Functor.map_comp]
  rfl

variable (hV₀ : IsAffineOpen V₀) {X : Scheme.{u}} (i : X ⟶ Y) {s : ℕ} (f : Fin (s + 1) → Γ(Y, V₀))

/-- The comparison chain map for the Koszul complexes of `f` on `V₀` and of `f|_{W'}` on `W'`. -/
noncomputable abbrev compareChain :=
  compareComplex V₀ W' (restrictPhi V₀) (restrictPhi ((incl V₀).obj W')) (resRing W')
    (resRing_compat W') f

-- Sections of transported and twice restricted modules are only definitionally sections of the
-- original modules; matching them unfolds the pushforwards and needs more than the default budget.
set_option maxHeartbeats 1000000 in
/-- **The comparison chain map is compatible with the augmentations** to `(i_* 𝒪_X)|_{W'}`. -/
lemma compareChain_augmentation [IsClosedImmersion i]
    (hI : i.ker.ideal ⟨V₀, hV₀⟩ = Ideal.span (Set.range f))
    (hW : IsAffineOpen ((incl V₀).obj W'))
    (hI' : i.ker.ideal ⟨_, hW⟩ = Ideal.span (Set.range (fun j => resRing W' (f j)))) :
    compareChain W' f ≫
        ((transport (ringTransport V₀ W' Y.sheaf)).mapHomologicalComplex _).map
          (augmentation (restrictPhi ((incl V₀).obj W')) _ (augHom i _)
            (d_comp_augHom hW i _ hI')) ≫
        (HomologicalComplex.singleMapHomologicalComplex (transport (ringTransport V₀ W' Y.sheaf)) _
          0).hom.app _ =
      restrictAugmentation (restrictPhi V₀) f W' (augHom i f) (d_comp_augHom hV₀ i f hI) ≫
        (ChainComplex.single₀ _).map ((restrictCompIso V₀ W' Y.sheaf).hom.app
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf))) := by
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  rw [ChainComplex.toSingle₀Equiv_apply_coe, ChainComplex.toSingle₀Equiv_apply_coe]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero, ChainComplex.single₀_map_f_zero]
  erw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.comp_id]
  apply hom_ext_k₀
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    compareChain, compareComplex_f]
  have h1 := compareHom_app_one V₀ W' (restrictPhi V₀) (restrictPhi ((incl V₀).obj W'))
    (resRing W') (resRing_compat W') f 0 (k₀ f)
  have h5 : (1 : (Ringed.restrictRingSheaf Y.sheaf ((incl V₀).obj W')).obj.obj
        (op ((opensEquiv (homeo V₀ W')).functor.obj ⊤))) ⊗ₜ[Γ(Y, (incl V₀).obj W'),
          baseMap (restrictPhi ((incl V₀).obj W')) ((opensEquiv (homeo V₀ W')).functor.obj ⊤)]
          koszulBaseChangeMap (resRing W') f 0 (k₀ f) =
      (1 : (Ringed.restrictRingSheaf Y.sheaf ((incl V₀).obj W')).obj.obj
        (op ((opensEquiv (homeo V₀ W')).functor.obj ⊤))) ⊗ₜ[Γ(Y, (incl V₀).obj W'),
          baseMap (restrictPhi ((incl V₀).obj W')) ((opensEquiv (homeo V₀ W')).functor.obj ⊤)]
          k₀ (fun j => resRing W' (f j)) := by
    rw [koszulBaseChangeMap_k₀]
  have h2 := augHom_app_tmul_k₀ (V₀ := (incl V₀).obj W') i (fun j => resRing W' (f j))
    ((opensEquiv (homeo V₀ W')).functor.obj ⊤) 1
  have h3 := augHom_app_tmul_k₀ (V₀ := V₀) i f (W'.isOpenEmbedding.functor.obj ⊤) 1
  have h4 := restrictSheafHom_app_tmul (restrictPhi V₀) W' ((K f).X 0) ⊤ 1 (k₀ f)
  refine (congrArg (((transport (ringTransport V₀ W' Y.sheaf)).map
    (augHom i (fun j => resRing W' (f j)))).val.app (op ⊤)) h1).trans ?_
  refine (congrArg ((augHom i (fun j => resRing W' (f j))).val.app
    (op ((opensEquiv (homeo V₀ W')).functor.obj ⊤))) h5).trans ?_
  refine h2.trans ?_
  refine Eq.trans ?_ (congrArg (fun x => ((restrictCompIso V₀ W' Y.sheaf).hom.app
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf))).val.app (op ⊤)
      (((Ringed.moduleRestrict W').map (augHom i f)).val.app (op ⊤) x)) h4).symm
  refine Eq.trans ?_ (congrArg (fun x => ((restrictCompIso V₀ W' Y.sheaf).hom.app
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf))).val.app (op ⊤) x)
      h3).symm
  rw [restrictCompIso_hom_app_val_app, map_one, map_one]
  exact (map_one (X.presheaf.map _).hom).symm

variable (M : Y.Modules)

/-- The local top-Ext map is evaluation at the global section `topSection`, followed by the unit. -/
lemma topHom_eq_homEvalAt :
    topHom i f M =
      Ringed.homEvalAt (topSection (restrictPhi V₀) f ⊤) ((Ringed.moduleRestrict V₀).obj M) ≫
      unitRestrict i M V₀ := by
  rw [topHom, topEval_eq_homEvalAt]

/-- **The local top-Ext isomorphism as a map induced by a top map** (`Ringed.extTopMap`). -/
lemma localTopExtIso_hom_eq [IsClosedImmersion i]
    (hI : i.ker.ideal ⟨V₀, hV₀⟩ = Ideal.span (Set.range f)) [M.IsQuasicoherent]
    (hf : IsKoszulRegular f (ModuleCat.of Γ(Y, V₀) Γ(Y, V₀))) :
    have := quasiIso_koszulAugmentation hV₀ i f hI hf
    (localTopExtIso hV₀ i f M hI hf).hom = (Ringed.sheafExtRestrictIso V₀ _ M (s + 1)).hom ≫
      Ringed.extTopMap _ (augmentation (restrictPhi V₀) f (augHom i f) (d_comp_augHom hV₀ i f hI))
        (isFiniteLocallyFree_complex (restrictPhi V₀) f) _ (topHom i f M)
        (d_comp_topHom hV₀ i f M hI) := by
  intro _
  rw [localTopExtIso_hom, Ringed.extTopMap]
  congr 2
  rw [← cancel_epi (HomologicalComplex.homologyπ _ (s + 1)), homologyπ_comp_topHomologyIso_hom,
    CochainTop.homologyπ_desc]

-- The terms of the restricted and transported complexes are only definitionally the restricted and
-- transported terms; matching them unfolds the pushforwards and needs more than the default budget.
set_option maxHeartbeats 1000000 in
/-- The top map on `W'` obtained by restricting the local top-Ext map of `V₀`. -/
lemma topMap_restrict_eq :
    ((Ringed.moduleSheafHomComplex (complex (restrictBase (restrictPhi V₀) W') f)).map
        (X := (Ringed.moduleRestrict W').obj ((Ringed.moduleRestrict V₀).obj M))
        (Y := (transport (ringTransport V₀ W' Y.sheaf)).obj
          ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M))
        ((restrictCompIso V₀ W' Y.sheaf).hom.app M)).f (s + 1) ≫
      Ringed.homEvalAt (topSection (restrictBase (restrictPhi V₀) W') f ⊤)
        ((transport (ringTransport V₀ W' Y.sheaf)).obj
          ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M)) ≫
        (transport (ringTransport V₀ W' Y.sheaf)).map (unitRestrict i M ((incl V₀).obj W')) =
    ((Ringed.moduleSheafHomComplexMap (restrictComplexIso (restrictPhi V₀) f W').inv).app _).f
        (s + 1) ≫
      (Ringed.homRestrictIso W' ((complex (restrictPhi V₀) f).X (s + 1))).inv.app
        ((Ringed.moduleRestrict V₀).obj M) ≫
      (Ringed.moduleRestrict W').map (topHom i f M) ≫
        (restrictCompIso V₀ W' Y.sheaf).hom.app
          ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj M)) := by
  change (Ringed.moduleSheafHomFunctor _).map ((restrictCompIso V₀ W' Y.sheaf).hom.app M) ≫ _ = _
  have hR := Ringed.homRestrict_homEvalAt W' (topSection (restrictPhi V₀) f ⊤)
    ((Ringed.moduleRestrict V₀).obj M)
  have hinv : (Ringed.homRestrictIso W' ((complex (restrictPhi V₀) f).X (s + 1))).inv.app
      ((Ringed.moduleRestrict V₀).obj M) ≫ Ringed.homRestrict (U := W')
        ((complex (restrictPhi V₀) f).X (s + 1)) ((Ringed.moduleRestrict V₀).obj M) = 𝟙 _ :=
    (Ringed.homRestrictIso W' ((complex (restrictPhi V₀) f).X (s + 1))).inv_hom_id_app _
  have key : (Ringed.homRestrictIso W' ((complex (restrictPhi V₀) f).X (s + 1))).inv.app
      ((Ringed.moduleRestrict V₀).obj M) ≫ (Ringed.moduleRestrict W').map
        (Ringed.homEvalAt (topSection (restrictPhi V₀) f ⊤) ((Ringed.moduleRestrict V₀).obj M)) =
      Ringed.homEvalAt (Ringed.restrictSection W' (topSection (restrictPhi V₀) f ⊤))
        ((Ringed.moduleRestrict W').obj ((Ringed.moduleRestrict V₀).obj M)) := by
    rw [← hR, ← Category.assoc, hinv, Category.id_comp]
  rw [← Category.assoc, Ringed.homEvalAt_comp, Category.assoc, topHom_eq_homEvalAt,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% key, Ringed.moduleSheafHomComplexMap_app_f,
    Ringed.moduleSheafHomPrecomp_homEvalAt_assoc]
  refine Eq.trans ?_ (congrArg (fun z => Ringed.homEvalAt z ((Ringed.moduleRestrict W').obj
    ((Ringed.moduleRestrict V₀).obj M)) ≫ (Ringed.moduleRestrict W').map (unitRestrict i M V₀) ≫
      (restrictCompIso V₀ W' Y.sheaf).hom.app ((Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj M)))
          (restrictComplexIso_inv_topSection (restrictPhi V₀) f W')).symm
  congr 1
  exact ((restrictCompIso V₀ W' Y.sheaf).hom.naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)).symm

-- The terms of the restricted and transported complexes are only definitionally the restricted and
-- transported terms; matching them unfolds the pushforwards and needs more than the default budget.
set_option maxHeartbeats 1000000 in
/-- The top map on `W'` obtained by transporting the local top-Ext map of `W`. -/
lemma topMap_transport_eq :
    ((Ringed.moduleSheafHomComplexMap (compareChain W' f)).app _).f (s + 1) ≫
      Ringed.homEvalAt (topSection (restrictBase (restrictPhi V₀) W') f ⊤) _ ≫
        (transport (ringTransport V₀ W' Y.sheaf)).map (unitRestrict i M ((incl V₀).obj W')) =
    (homTransportIso (ringTransport V₀ W' Y.sheaf)
        ((complex (restrictPhi ((incl V₀).obj W')) (fun j => resRing W' (f j))).X (s + 1))).inv.app
          ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M) ≫
      (transport (ringTransport V₀ W' Y.sheaf)).map (topHom i (fun j => resRing W' (f j)) M) ≫
        𝟙 _ := by
  have hT := Ringed.homTransport_homEvalAt (ringTransport V₀ W' Y.sheaf)
    (topSection (restrictPhi ((incl V₀).obj W')) (fun j => resRing W' (f j)) ⊤)
    ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M)
  have hinv : (homTransportIso (ringTransport V₀ W' Y.sheaf)
      ((complex (restrictPhi ((incl V₀).obj W')) (fun j => resRing W' (f j))).X (s + 1))).inv.app
        ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M) ≫
          homTransport (ringTransport V₀ W' Y.sheaf)
          ((complex (restrictPhi ((incl V₀).obj W')) (fun j => resRing W' (f j))).X (s + 1))
          ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M) = 𝟙 _ :=
    (homTransportIso (ringTransport V₀ W' Y.sheaf) _).inv_hom_id_app _
  have key : (homTransportIso (ringTransport V₀ W' Y.sheaf)
      ((complex (restrictPhi ((incl V₀).obj W')) (fun j => resRing W' (f j))).X (s + 1))).inv.app
        ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M) ≫
      (transport (ringTransport V₀ W' Y.sheaf)).map (Ringed.homEvalAt
        (topSection (restrictPhi ((incl V₀).obj W')) (fun j => resRing W' (f j)) ⊤)
        ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M)) =
      Ringed.homEvalAt (Ringed.transportSection (ringTransport V₀ W' Y.sheaf)
        (topSection (restrictPhi ((incl V₀).obj W')) (fun j => resRing W' (f j)) ⊤))
        ((transport (ringTransport V₀ W' Y.sheaf)).obj
          ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M)) := by
    rw [← hT, ← Category.assoc, hinv, Category.id_comp]
  rw [Category.comp_id, topHom_eq_homEvalAt, Functor.map_comp,
    Ringed.moduleSheafHomComplexMap_app_f (compareChain W' f),
    Ringed.moduleSheafHomPrecomp_homEvalAt_assoc]
  refine (congrArg (fun z => Ringed.homEvalAt z ((transport (ringTransport V₀ W' Y.sheaf)).obj
    ((Ringed.moduleRestrict ((incl V₀).obj W')).obj M)) ≫
      (transport (ringTransport V₀ W' Y.sheaf)).map (unitRestrict i M ((incl V₀).obj W')))
        (compareHom_topSection V₀ W' (restrictPhi V₀) (restrictPhi ((incl V₀).obj W'))
          (resRing W') (resRing_compat W') f)).trans ?_
  exact ((reassoc_of% key) _).symm

end Compare

end KoszulImmersion

end Hartshorne
