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
      koszulBaseChangeMap σ f p (((sequenceKoszulComplex f (ModuleCat.of A A)).d (p + 1) p).hom x) := by
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

@[simp]
lemma compareComplex_f (p : ℕ) :
    (compareComplex U V' φA φB σ hσ f).f p = compareHom U V' φA φB σ hσ f p := rfl

end Compare

end KoszulSheaf

end Ringed

end Hartshorne
