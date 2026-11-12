/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.AffineFormalModuleTensor
import Hartshorne.Scheme.SchemeCompletionExact
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Completion and the ordinary tensor product on a scheme

Hartshorne, *Algebraic Geometry*, II, Corollary 9.8 (p. 198), the tensor product statement: for a
Noetherian scheme `X`, a closed subscheme `Y` with ideal sheaf `I`, and a coherent `𝒪_X`-module
`F`, the completion is `F̂ ≅ F|_{|Y|} ⊗_{𝒪_X|_{|Y|}} 𝒪_X̂`, an ordinary tensor product of sheaves of
modules on `|Y| = |X̂|`.

As in `Hartshorne.Scheme.AffineFormalModuleTensor`, the tensor product is the module pullback
`f^* F = i⁻¹ F ⊗_{i⁻¹ 𝒪_X} 𝒪_X̂` along the morphism of ringed spaces `f : (|Y|, 𝒪_X̂) ⟶ (X, 𝒪_X)`,
and the isomorphism is the canonical map `f^* F ⟶ F̂`
(`Hartshorne.QuasicoherentIdealSubsheaf.pullbackToModuleCompletion`), adjoint to `F ⟶ i_* F̂`.

* `Hartshorne.QuasicoherentIdealSubsheaf.isIso_pullbackToModuleCompletion`: on a locally Noetherian
  scheme, the canonical map `f^* F ⟶ F̂` is an isomorphism for every coherent `F`.
* `Hartshorne.QuasicoherentIdealSubsheaf.pullbackIsoModuleCompletion`: the isomorphism
  `F|_{|Y|} ⊗_{𝒪_X|_{|Y|}} 𝒪_X̂ ≅ F̂`.

The proof constructs the inverse. Let `U` be an affine open of `X` with `A = Γ(U, 𝒪_X)`
Noetherian, `M = Γ(U, F)` finite, and `W = U ∩ |Y|`. Lifting the projections of a section of `F̂`
over `W` to the levels `M / I(U) ^ (n + 1) M` gives an injective map `Γ(W, F̂) ⟶ M̂` to the
`I(U)`-adic completion of `M`, semilinear over `Γ(W, 𝒪_X̂) ≅ Â`. Since `Â ⊗_A M ≅ M̂` for `A`
Noetherian and `M` finite, this yields an additive map `Γ(W, F̂) ⟶ Γ(W, f^* F)`, `a ⊗ s ↦ a · s`,
which is `Γ(W, 𝒪_X̂)`-linear and a right inverse of the canonical map on sections over `W`. These
maps are compatible with restriction (first between nested affine opens, then for any inclusion
of traces by covering with affine opens inside both), so they glue along the basis of `|Y|`
formed by the traces of the affine opens to a morphism of `𝒪_X̂`-modules `F̂ ⟶ f^* F`. It is
inverse to the canonical map: on one side because both composites agree on sections over the
basis, on the other by the adjunction `f^* ⊣ f_*`, since both composites agree on the images of
the sections of `F` over the affine opens.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace
open scoped TensorProduct

namespace Hartshorne

universe u

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X) (F : X.Modules)

set_option hygiene false in
local notation "χ" => I.structureSheafToFormalCompletionRingCat

set_option hygiene false in
local notation "hχ" => I.structureSheafToFormalCompletionRingCat_compat

set_option hygiene false in
local notation "𝒫" => SheafOfModules.pushforward.{u} I.structureSheafToFormalCompletionRingCat

section AffineSections

variable [F.IsQuasicoherent] (U : X.affineOpens)

/-- A section of `F` over the affine open `U` whose image at level `n` is the projection of a
given section of `F̂` over `U ∩ |Y|`. -/
private def liftSection (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens)))
    (n : ℕ) : Γ(F, (U : X.Opens)) :=
  Function.surjInv (I.moduleCompletionSectionsMap_surjective F n U)
    (((𝒫).map (I.moduleCompletionπ F n)).val.app (op (U : X.Opens)) x)

private lemma levelMap_liftSection
    (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens))) (n : ℕ) :
    (I.moduleCompletionLevelMap χ hχ F n).val.app (op (U : X.Opens)) (I.liftSection F U x n) =
      ((𝒫).map (I.moduleCompletionπ F n)).val.app (op (U : X.Opens)) x :=
  Function.surjInv_eq (I.moduleCompletionSectionsMap_surjective F n U) _

private lemma levelMap_liftSection_succ
    (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens))) (n : ℕ) :
    (I.moduleCompletionLevelMap χ hχ F n).val.app (op (U : X.Opens))
        (I.liftSection F U x (n + 1)) =
      ((𝒫).map (I.moduleCompletionπ F n)).val.app (op (U : X.Opens)) x := by
  rw [← I.moduleCompletionMap_val_app_moduleCompletionLevelMap χ hχ F n U,
    levelMap_liftSection, I.moduleCompletionMap_val_app_moduleCompletionπ χ F n U]

private lemma sub_liftSection_mem
    (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens))) (n : ℕ)
    (t : Γ(F, (U : X.Opens)))
    (ht : (I.moduleCompletionLevelMap χ hχ F n).val.app (op (U : X.Opens)) t =
      ((𝒫).map (I.moduleCompletionπ F n)).val.app (op (U : X.Opens)) x) :
    t - I.liftSection F U x n ∈
      I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))) :=
  (I.moduleCompletionSectionsMap_eq_zero_iff F n U _).1 ((map_sub _ _ _).trans
    (sub_eq_zero.2 (ht.trans (I.levelMap_liftSection F U x n).symm)))

omit [F.IsQuasicoherent] in
private lemma mem_pow_smul_of_mem_succ {n : ℕ} {s : Γ(F, (U : X.Opens))}
    (h : s ∈ I.ideal U ^ (n + 1) • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens)))) :
    s ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))) :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) h

/-- **Sections of the completion as adic completions**: the map from `Γ(U ∩ |Y|, F̂)` to the
`I(U)`-adic completion of `Γ(U, F)`, sending a section to the classes of lifts of its projections
to the levels `Γ(U ∩ |Y|, (F / I ^ (n + 1) F)|_Y) = Γ(U, F) / I(U) ^ (n + 1) Γ(U, F)`. -/
private def toAdic (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens))) :
    AdicCompletion (I.ideal U) Γ(F, (U : X.Opens)) :=
  AdicCompletion.mk _ _ (AdicCompletion.AdicCauchySequence.mk _ _ (I.liftSection F U x) fun n => by
    have h := I.sub_liftSection_mem F U x n _ (I.levelMap_liftSection_succ F U x n)
    rw [SModEq.sub_mem, ← neg_sub]
    exact neg_mem (I.mem_pow_smul_of_mem_succ F U h))

private lemma toAdic_val_eq (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens)))
    (t : ℕ → Γ(F, (U : X.Opens)))
    (ht : ∀ n, (I.moduleCompletionLevelMap χ hχ F n).val.app (op (U : X.Opens)) (t n) =
      ((𝒫).map (I.moduleCompletionπ F n)).val.app (op (U : X.Opens)) x) (m : ℕ) :
    (I.toAdic F U x).val m = Submodule.Quotient.mk (t m) := by
  change Submodule.Quotient.mk (I.liftSection F U x m) = _
  rw [Submodule.Quotient.eq, ← neg_sub]
  exact neg_mem (I.mem_pow_smul_of_mem_succ F U (I.sub_liftSection_mem F U x m (t m) (ht m)))

private lemma toAdic_add (x y : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens))) :
    I.toAdic F U (x + y) = I.toAdic F U x + I.toAdic F U y := by
  ext m
  rw [I.toAdic_val_eq F U (x + y) (fun n => I.liftSection F U x n + I.liftSection F U y n)
    (fun n => ((map_add _ _ _).trans (congrArg₂ (· + ·) (I.levelMap_liftSection F U x n)
      (I.levelMap_liftSection F U y n))).trans (map_add _ _ _).symm),
    AdicCompletion.val_add_apply, I.toAdic_val_eq F U x (I.liftSection F U x)
      (I.levelMap_liftSection F U x), I.toAdic_val_eq F U y (I.liftSection F U y)
      (I.levelMap_liftSection F U y)]
  rfl

private lemma toAdic_toModuleCompletionPushforward (s : Γ(F, (U : X.Opens))) :
    I.toAdic F U ((I.toModuleCompletionPushforward F).val.app (op (U : X.Opens)) s) =
      AdicCompletion.of _ _ s := by
  ext m
  rw [I.toAdic_val_eq F U _ (fun _ => s) (fun n => (sheafOfModules_val_app_apply_of_comp_eq
    (I.toModuleCompletionPushforward_π F n) (op (U : X.Opens)) s).symm)]
  rfl

private lemma toAdic_injective
    (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens)))
    (hx : I.toAdic F U x = 0) : x = 0 := by
  have hc := isLimitOfPreserves (𝒫) (limit.isLimit (I.moduleCompletionDiagram F))
  refine sections_isLimit_mapCone_ext hc (op (U : X.Opens)) x 0 (fun n => ?_)
  have h1 : (I.toAdic F U x).val (n + 1) = 0 := by rw [hx]; rfl
  change Submodule.Quotient.mk (I.liftSection F U x (n + 1)) = 0 at h1
  rw [Submodule.Quotient.mk_eq_zero] at h1
  have h2 := (I.moduleCompletionSectionsMap_eq_zero_iff F n U _).2 h1
  exact (I.levelMap_liftSection_succ F U x n).symm.trans (h2.trans (map_zero _).symm)

/-- Scalars with the same image under the ring map act equally on a pushforward. -/
private lemma pushforward_smul_congr' {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {G : C ⥤ D} [G.IsContinuous J K]
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (φ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S) (M : SheafOfModules.{u} S)
    (V : Cᵒᵖ) {r r' : R.obj.obj V} (h : φ.hom.app V r = φ.hom.app V r')
    (m : ((SheafOfModules.pushforward.{u} φ).obj M).val.obj V) : r • m = r' • m :=
  congrArg (fun (a : S.obj.obj (op (G.obj V.unop))) =>
    (a • (show M.val.obj (op (G.obj V.unop)) from m) : M.val.obj (op (G.obj V.unop)))) h

omit [F.IsQuasicoherent] in
/-- The projection to `𝒪_{Y_(n+1)}` of the image of a function under `𝒪_X ⟶ i_* 𝒪_X̂` is its
restriction to `Y_(n+1)`. -/
private lemma formalCompletionRingCatSheafπ_χ (n : ℕ) (a : Γ(X, (U : X.Opens))) :
    (I.formalCompletionRingCatSheafπ n).hom.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))
        ((χ).hom.app (op (U : X.Opens)) a) =
      I.formalCompletionSheafObjSectionsMap n U a :=
  congrArg (fun g => g.hom a) (I.formalCompletionSectionsMap_π U n)

/-- The map to the adic completion is semilinear over
`Γ(U ∩ |Y|, 𝒪_X̂) ≅ Γ(U, 𝒪_X)^`. -/
private lemma toAdic_smul
    (a : I.formalCompletionRingCatSheaf.obj.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))))
    (x : (I.moduleCompletion F).val.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    I.toAdic F U (a • x) = I.formalCompletionAffineSectionsIso U a • I.toAdic F U x := by
  obtain ⟨c, hc⟩ := AdicCompletion.mk_surjective (I.ideal U) Γ(X, (U : X.Opens))
    (I.formalCompletionAffineSectionsIso U a)
  have hcm : ∀ m, c.val (m + 1) - c.val m ∈ I.ideal U ^ m := by
    intro m
    have h := c.property (Nat.le_succ m)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
    rw [← neg_sub]
    exact neg_mem h
  ext m
  rw [I.toAdic_val_eq F U (a • x) (fun n => c.val (n + 1) • I.liftSection F U x n) ?_ m,
    AdicCompletion.smul_eval, ← hc, I.toAdic_val_eq F U x (I.liftSection F U x)
      (I.levelMap_liftSection F U x) m]
  · change _ = c.val m • Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← sub_smul]
    exact Submodule.smul_mem_smul (hcm m) Submodule.mem_top
  · intro n
    have h : (I.formalCompletionRingCatSheafπ n).hom.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))
        ((χ).hom.app (op (U : X.Opens)) (c.val (n + 1))) =
        (I.formalCompletionRingCatSheafπ n).hom.app
          (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) a := by
      rw [I.formalCompletionRingCatSheafπ_χ U n]
      refine Eq.symm ((formalCompletionSheafObjAffineEquiv_evalₐ_formalCompletionAffineSectionsIso
        I U n a).symm.trans ?_)
      rw [← hc, AdicCompletion.evalₐ_mk]
      rfl
    refine (map_smul ((I.moduleCompletionLevelMap χ hχ F n).val.app (op (U : X.Opens))).hom
      (show X.ringCatSheaf.obj.obj (op (U : X.Opens)) from c.val (n + 1))
      (show F.val.obj (op (U : X.Opens)) from I.liftSection F U x n)).trans ?_
    refine (congrArg _ (I.levelMap_liftSection F U x n)).trans ?_
    refine (pushforward_smul_congr' (I.formalCompletionRingCatSheafπ n)
      (I.moduleCompletionNeighborhood F n) _ h _).trans ?_
    exact (map_smul ((I.moduleCompletionπ F n).val.app
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))).hom a x).symm

/-- The map to the adic completion as an additive map. -/
private def toAdicHom :
    ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens)) →+
      AdicCompletion (I.ideal U) Γ(F, (U : X.Opens)) :=
  AddMonoidHom.mk' (I.toAdic F U) (I.toAdic_add F U)

end AffineSections

section AffineInverse

/-- `𝒪_X ⟶ i_* 𝒪_X̂` on sections over `V`, with values in `Γ(V ∩ |Y|, 𝒪_X̂)`. -/
private abbrev χApp (V : X.Opens) (r : Γ(X, V)) :
    I.formalCompletionRingCatSheaf.obj.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ V)) :=
  (χ).hom.app (op V) r

/-- `Γ(U, 𝒪_X)^ ≅ Γ(U ∩ |Y|, 𝒪_X̂)`, with values in the ring of sections acting on modules. -/
private def adicScalar (U : X.affineOpens) (b : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens))) :
    I.formalCompletionRingCatSheaf.obj.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) :=
  (I.formalCompletionAffineSectionsIso U).symm b

private lemma adicScalar_mul (U : X.affineOpens)
    (b b' : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens))) :
    I.adicScalar U (b * b') = I.adicScalar U b * I.adicScalar U b' :=
  map_mul (I.formalCompletionAffineSectionsIso U).symm b b'

private lemma adicScalar_one (U : X.affineOpens) : I.adicScalar U 1 = 1 :=
  map_one (I.formalCompletionAffineSectionsIso U).symm

private lemma adicScalar_add (U : X.affineOpens)
    (b b' : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens))) :
    I.adicScalar U (b + b') = I.adicScalar U b + I.adicScalar U b' :=
  map_add (I.formalCompletionAffineSectionsIso U).symm b b'

private lemma adicScalar_formalCompletionAffineSectionsIso (U : X.affineOpens)
    (a : I.formalCompletionRingCatSheaf.obj.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    I.adicScalar U (I.formalCompletionAffineSectionsIso U a) = a :=
  (I.formalCompletionAffineSectionsIso U).symm_apply_apply a

private lemma adicScalar_of (U : X.affineOpens) (r : Γ(X, (U : X.Opens))) :
    I.adicScalar U (AdicCompletion.of _ _ r) = I.χApp U r :=
  (RingEquiv.symm_apply_eq _).2
    (I.formalCompletionAffineSectionsIso_formalCompletionSectionsMap U r).symm

private lemma adicScalar_smul (U : X.affineOpens) (r : Γ(X, (U : X.Opens)))
    (b : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens))) :
    I.adicScalar U (r • b) = I.χApp U r * I.adicScalar U b := by
  rw [Algebra.smul_def, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    adicScalar_mul, adicScalar_of]

/-- Sections of `𝒪_X̂` commute. -/
private lemma formalCompletion_mul_comm (V : Opens (I.infinitesimalNeighborhood 1))
    (p q : I.formalCompletionRingCatSheaf.obj.obj (op V)) : p * q = q * p :=
  mul_comm (G := I.formalCompletionSheaf.presheaf.obj (op V)) p q

variable [F.IsQuasicoherent] (U : X.affineOpens)

/-- The unit `F ⟶ f_* f^* F` on sections over `U`. -/
private abbrev pullbackUnitApp (s : Γ(F, (U : X.Opens))) :
    ((SheafOfModules.pullback.{u} χ).obj F).val.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u} χ).unit.app F).val.app (op (U : X.Opens)) s

omit [F.IsQuasicoherent] in
private lemma pullbackUnitApp_smul (r : Γ(X, (U : X.Opens))) (s : Γ(F, (U : X.Opens))) :
    I.pullbackUnitApp F U (r • s) = I.χApp U r • I.pullbackUnitApp F U s :=
  map_smul (((SheafOfModules.pullbackPushforwardAdjunction.{u} χ).unit.app F).val.app
    (op (U : X.Opens))).hom (show X.ringCatSheaf.obj.obj (op (U : X.Opens)) from r)
    (show F.val.obj (op (U : X.Opens)) from s)

omit [F.IsQuasicoherent] in
private lemma pullbackUnitApp_add (s s' : Γ(F, (U : X.Opens))) :
    I.pullbackUnitApp F U (s + s') = I.pullbackUnitApp F U s + I.pullbackUnitApp F U s' :=
  map_add (((SheafOfModules.pullbackPushforwardAdjunction.{u} χ).unit.app F).val.app
    (op (U : X.Opens))).hom (show F.val.obj (op (U : X.Opens)) from s)
    (show F.val.obj (op (U : X.Opens)) from s')

/-- The map `Γ(U, 𝒪_X)^ ⊗ Γ(U, F) ⟶ Γ(U ∩ |Y|, f^* F)`, `b ⊗ s ↦ b · s`. -/
private def tensorToPullback :
    AdicCompletion (I.ideal U) Γ(X, (U : X.Opens)) ⊗[Γ(X, (U : X.Opens))] Γ(F, (U : X.Opens)) →+
      ((SheafOfModules.pullback.{u} χ).obj F).val.obj
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk'
      (fun s => I.adicScalar U b • I.pullbackUnitApp F U s)
      (fun s s' => by rw [pullbackUnitApp_add, smul_add]))
      (fun b b' => by
        ext s
        exact (congrArg (· • _) (I.adicScalar_add U b b')).trans (add_smul _ _ _)))
    (fun r b s => by
      change I.adicScalar U (r • b) • I.pullbackUnitApp F U s =
        I.adicScalar U b • I.pullbackUnitApp F U (r • s)
      rw [adicScalar_smul, pullbackUnitApp_smul, smul_smul, formalCompletion_mul_comm])

omit [F.IsQuasicoherent] in
private lemma tensorToPullback_tmul (b : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens)))
    (s : Γ(F, (U : X.Opens))) :
    I.tensorToPullback F U (b ⊗ₜ s) = I.adicScalar U b • I.pullbackUnitApp F U s :=
  rfl

omit [F.IsQuasicoherent] in
private lemma tensorToPullback_smul (b : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens)))
    (t : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens)) ⊗[Γ(X, (U : X.Opens))]
      Γ(F, (U : X.Opens))) :
    I.tensorToPullback F U (b • t) = I.adicScalar U b • I.tensorToPullback F U t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul b' s =>
    rw [TensorProduct.smul_tmul', tensorToPullback_tmul, tensorToPullback_tmul, smul_eq_mul,
      adicScalar_mul, mul_smul]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', smul_add]

omit [F.IsQuasicoherent] in
/-- The canonical map `f^* F ⟶ F̂` sends the image of `s ∈ Γ(U, F)` under the unit to the image of
`s` under `F ⟶ i_* F̂`. -/
private lemma pullbackToModuleCompletion_pullbackUnitApp (s : Γ(F, (U : X.Opens))) :
    (I.pullbackToModuleCompletion F).val.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.pullbackUnitApp F U s) =
      (I.toModuleCompletionPushforward F).val.app (op (U : X.Opens)) s := by
  have e : (SheafOfModules.pullbackPushforwardAdjunction.{u} χ).unit.app F ≫
      (𝒫).map (I.pullbackToModuleCompletion F) = I.toModuleCompletionPushforward F :=
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} χ).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  exact sheafOfModules_val_app_apply_of_comp_eq e (op (U : X.Opens)) s

omit [F.IsQuasicoherent] in
private lemma pullbackToModuleCompletion_tensorToPullback_tmul
    (b : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens))) (s : Γ(F, (U : X.Opens))) :
    (I.pullbackToModuleCompletion F).val.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.tensorToPullback F U (b ⊗ₜ s)) =
      I.adicScalar U b • (show (I.moduleCompletion F).val.obj
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) from
          (I.toModuleCompletionPushforward F).val.app (op (U : X.Opens)) s) :=
  (map_smul ((I.pullbackToModuleCompletion F).val.app
    (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))).hom (I.adicScalar U b)
      (I.pullbackUnitApp F U s)).trans
    (congrArg (I.adicScalar U b • ·) (I.pullbackToModuleCompletion_pullbackUnitApp F U s))

private lemma toAdic_zero : I.toAdic F U 0 = 0 := (I.toAdicHom F U).map_zero

private lemma toAdic_sub (x y : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens))) :
    I.toAdic F U (x - y) = I.toAdic F U x - I.toAdic F U y := (I.toAdicHom F U).map_sub x y

private lemma toAdic_pullbackToModuleCompletion_tensorToPullback
    (t : AdicCompletion (I.ideal U) Γ(X, (U : X.Opens)) ⊗[Γ(X, (U : X.Opens))]
      Γ(F, (U : X.Opens))) :
    I.toAdic F U ((I.pullbackToModuleCompletion F).val.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.tensorToPullback F U t)) =
      AdicCompletion.ofTensorProduct (I.ideal U) Γ(F, (U : X.Opens)) t := by
  induction t using TensorProduct.induction_on with
  | zero =>
    refine (congrArg (I.toAdic F U) ((congrArg _ (map_zero _)).trans (map_zero _))).trans ?_
    exact (I.toAdic_zero F U).trans (map_zero _).symm
  | tmul b s =>
    refine (congrArg (I.toAdic F U)
      (I.pullbackToModuleCompletion_tensorToPullback_tmul F U b s)).trans ?_
    refine (I.toAdic_smul F U _ _).trans ?_
    rw [AdicCompletion.ofTensorProduct_tmul]
    exact congrArg₂ (· • ·) ((I.formalCompletionAffineSectionsIso U).apply_symm_apply b)
      (I.toAdic_toModuleCompletionPushforward F U s)
  | add t t' ht ht' =>
    refine (congrArg (I.toAdic F U) ((congrArg _ (map_add _ _ _)).trans (map_add _ _ _))).trans ?_
    exact (I.toAdic_add F U _ _).trans ((congrArg₂ (· + ·) ht ht').trans (map_add _ _ _).symm)

variable [IsNoetherianRing Γ(X, (U : X.Opens))]
  [Module.Finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))]

/-- **The inverse on sections over `U ∩ |Y|`**: `Γ(U ∩ |Y|, F̂) ≅ Γ(U, 𝒪_X)^ ⊗ Γ(U, F)` (the
adic completion of the finite module `Γ(U, F)`), followed by `b ⊗ s ↦ b · s` into
`Γ(U ∩ |Y|, f^* F)`. -/
private def completionToPullback :
    ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens)) →+
      ((SheafOfModules.pullback.{u} χ).obj F).val.obj
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) :=
  (I.tensorToPullback F U).comp
    (((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I.ideal U)
      Γ(F, (U : X.Opens))).symm.toLinearMap.toAddMonoidHom).comp (I.toAdicHom F U))

private lemma completionToPullback_apply
    (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens))) :
    I.completionToPullback F U x = I.tensorToPullback F U
      ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I.ideal U)
        Γ(F, (U : X.Opens))).symm (I.toAdic F U x)) :=
  rfl

private lemma completionToPullback_toModuleCompletionPushforward (s : Γ(F, (U : X.Opens))) :
    I.completionToPullback F U ((I.toModuleCompletionPushforward F).val.app (op (U : X.Opens)) s) =
      I.pullbackUnitApp F U s := by
  rw [completionToPullback_apply, toAdic_toModuleCompletionPushforward]
  have h : (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I.ideal U)
      Γ(F, (U : X.Opens))).symm (AdicCompletion.of _ _ s) = 1 ⊗ₜ s := by
    rw [LinearEquiv.symm_apply_eq, AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
      AdicCompletion.ofTensorProduct_tmul, one_smul]
  rw [h, tensorToPullback_tmul, adicScalar_one, one_smul]

private lemma completionToPullback_smul
    (a : I.formalCompletionRingCatSheaf.obj.obj
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))))
    (x : (I.moduleCompletion F).val.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    I.completionToPullback F U (a • x) = a • I.completionToPullback F U x := by
  refine (I.completionToPullback_apply F U _).trans ?_
  refine (congrArg (fun y => I.tensorToPullback F U
    ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I.ideal U)
      Γ(F, (U : X.Opens))).symm y)) (I.toAdic_smul F U a x)).trans ?_
  rw [LinearEquiv.map_smul, tensorToPullback_smul, adicScalar_formalCompletionAffineSectionsIso]
  rfl

private lemma pullbackToModuleCompletion_completionToPullback
    (x : ((𝒫).obj (I.moduleCompletion F)).val.obj (op (U : X.Opens))) :
    (I.pullbackToModuleCompletion F).val.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.completionToPullback F U x) =
      x := by
  have h := I.toAdic_pullbackToModuleCompletion_tensorToPullback F U
    ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I.ideal U)
      Γ(F, (U : X.Opens))).symm (I.toAdic F U x))
  rw [← AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply, LinearEquiv.apply_symm_apply]
    at h
  exact sub_eq_zero.1 (I.toAdic_injective F U _ ((I.toAdic_sub F U _ _).trans (sub_eq_zero.2 h)))

end AffineInverse

/-- **Compatibility of the inverses with restriction** between nested affine opens `U' ⊆ U`. -/
private lemma completionToPullback_map [F.IsQuasicoherent] {U U' : X.affineOpens}
    [IsNoetherianRing Γ(X, (U : X.Opens))] [Module.Finite Γ(X, (U : X.Opens)) Γ(F, (U : X.Opens))]
    [IsNoetherianRing Γ(X, (U' : X.Opens))]
    [Module.Finite Γ(X, (U' : X.Opens)) Γ(F, (U' : X.Opens))]
    (hUU : (U' : X.Opens) ≤ U)
    (h : I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U' : X.Opens) ≤
      I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))
    (x : (I.moduleCompletion F).val.obj (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)))) :
    I.completionToPullback F U' ((I.moduleCompletion F).val.map (homOfLE h).op x) =
      ((SheafOfModules.pullback.{u} χ).obj F).val.map (homOfLE h).op
        (I.completionToPullback F U x) := by
  obtain ⟨t, rfl⟩ : ∃ t, (I.pullbackToModuleCompletion F).val.app
      (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.tensorToPullback F U t) = x :=
    ⟨_, I.pullbackToModuleCompletion_completionToPullback F U x⟩
  induction t using TensorProduct.induction_on with
  | zero =>
    have h0 : (I.pullbackToModuleCompletion F).val.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.tensorToPullback F U 0) = 0 :=
      (congrArg _ (map_zero _)).trans (map_zero _)
    rw [h0, map_zero]
    exact (I.completionToPullback F U').map_zero.trans
      ((congrArg _ (I.completionToPullback F U).map_zero).trans (map_zero _)).symm
  | tmul b s =>
    rw [I.pullbackToModuleCompletion_tensorToPullback_tmul F U b s]
    have hψ := (PresheafOfModules.naturality_apply (I.toModuleCompletionPushforward F).val
      (homOfLE hUU).op s).symm
    have hη := (PresheafOfModules.naturality_apply
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} χ).unit.app F).val (homOfLE hUU).op s).symm
    have hσ := I.completionToPullback_toModuleCompletionPushforward F U s
    have hσ' := I.completionToPullback_toModuleCompletionPushforward F U'
      (F.val.map (homOfLE hUU).op s)
    erw [PresheafOfModules.map_smul, I.completionToPullback_smul F U', hψ, hσ',
      I.completionToPullback_smul F U, hσ, PresheafOfModules.map_smul]
    exact congrArg _ hη.symm
  | add t t' ht ht' =>
    have hadd : ∀ t₁ t₂, (I.pullbackToModuleCompletion F).val.app
        (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.tensorToPullback F U (t₁ + t₂)) =
        (I.pullbackToModuleCompletion F).val.app
          (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.tensorToPullback F U t₁) +
        (I.pullbackToModuleCompletion F).val.app
          (op (I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens))) (I.tensorToPullback F U t₂) :=
      fun t₁ t₂ => (congrArg _ (map_add _ _ _)).trans (map_add _ _ _)
    rw [hadd, map_add]
    exact ((I.completionToPullback F U').map_add _ _).trans ((congrArg₂ (· + ·) ht ht').trans
      ((congrArg _ ((I.completionToPullback F U).map_add _ _)).trans (map_add _ _ _)).symm)

section Glue

/-- Sections of a sheaf of modules on a space that agree on an open cover agree. -/
private lemma sheafOfModules_eq_of_locally_eq {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} (M : SheafOfModules.{u} R)
    {V : Opens T} {κ : Type*} (W : κ → Opens T) (hW : ∀ k, W k ≤ V) (hcov : V ≤ iSup W)
    (s t : M.val.obj (op V))
    (h : ∀ k, M.val.map (homOfLE (hW k)).op s = M.val.map (homOfLE (hW k)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} T)
    W V (fun k => homOfLE (hW k)) hcov s t h

/-- Morphisms of sheaves of modules on a space that agree on the sections over the members of a
basis agree. -/
private lemma sheafOfModules_hom_ext_of_isBasis {T : TopCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} {M N : SheafOfModules.{u} R}
    {ι : Type*} {B : ι → Opens T} (hB : Opens.IsBasis (Set.range B)) {φ φ' : M ⟶ N}
    (h : ∀ i (x : M.val.obj (op (B i))), φ.val.app (op (B i)) x = φ'.val.app (op (B i)) x) :
    φ = φ' := by
  refine SheafOfModules.hom_ext ((PresheafOfModules.toPresheaf R.obj).map_injective ?_)
  exact TopCat.Sheaf.hom_ext (F := M.val.presheaf) (F' := ⟨N.val.presheaf, N.isSheaf⟩) hB
    (fun i => by ext x; exact h i x)

/-- The traces `U ∩ |Y|` of the affine opens `U` of `X`. -/
private abbrev affineTrace (U : X.affineOpens) : (I.infinitesimalNeighborhood 1).Opens :=
  I.infinitesimalNeighborhoodι 1 ⁻¹ᵁ (U : X.Opens)

private lemma isBasis_affineTrace : Opens.IsBasis (Set.range I.affineTrace) := by
  have h := opens_isBasis_map_image _
    (I.infinitesimalNeighborhoodι 1).isClosedEmbedding.isInducing X.isBasis_affineOpens
  rw [Set.image_eq_range] at h
  exact h

/-- Sections of a sheaf of modules on `|Y|` agreeing on the traces of the affine opens of `X`
inside agree. -/
private lemma eq_of_affineTrace
    {R : Sheaf (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1 : TopCat)) RingCat.{u}}
    (M : SheafOfModules.{u} R) {V : (I.infinitesimalNeighborhood 1).Opens}
    (s t : M.val.obj (op V))
    (h : ∀ (U : X.affineOpens) (hU : I.affineTrace U ≤ V),
      M.val.map (homOfLE hU).op s = M.val.map (homOfLE hU).op t) : s = t := by
  have key : ∀ y : V, ∃ U : X.affineOpens, (y : I.infinitesimalNeighborhood 1) ∈ I.affineTrace U ∧
      I.affineTrace U ≤ V := by
    intro y
    obtain ⟨_, ⟨U, rfl⟩, hy, hle⟩ := Opens.isBasis_iff_nbhd.mp I.isBasis_affineTrace y.2
    exact ⟨U, hy, hle⟩
  choose U hyU hUV using key
  exact sheafOfModules_eq_of_locally_eq M (fun y => I.affineTrace (U y)) hUV
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩) s t (fun y => h (U y) (hUV y))

variable [IsLocallyNoetherian X] (hF : IsCoherent F)

/-- The inverse `Γ(U ∩ |Y|, F̂) ⟶ Γ(U ∩ |Y|, f^* F)` on the trace of an affine open `U`. -/
private def sigmaApp (U : X.affineOpens) :
    (I.moduleCompletion F).val.obj (op (I.affineTrace U)) →+
      ((SheafOfModules.pullback.{u} χ).obj F).val.obj (op (I.affineTrace U)) :=
  haveI := hF.isQuasicoherent
  haveI := IsLocallyNoetherian.component_noetherian U
  haveI := (forall_affine_finite_of_isCoherent F hF U).1
  I.completionToPullback F U

private lemma sigmaApp_smul (U : X.affineOpens)
    (a : I.formalCompletionRingCatSheaf.obj.obj (op (I.affineTrace U)))
    (x : (I.moduleCompletion F).val.obj (op (I.affineTrace U))) :
    I.sigmaApp F hF U (a • x) = a • I.sigmaApp F hF U x :=
  haveI := hF.isQuasicoherent
  haveI := IsLocallyNoetherian.component_noetherian U
  haveI := (forall_affine_finite_of_isCoherent F hF U).1
  I.completionToPullback_smul F U a x

private lemma sigmaApp_toModuleCompletionPushforward (U : X.affineOpens) (s : Γ(F, (U : X.Opens))) :
    I.sigmaApp F hF U ((I.toModuleCompletionPushforward F).val.app (op (U : X.Opens)) s) =
      I.pullbackUnitApp F U s :=
  haveI := hF.isQuasicoherent
  haveI := IsLocallyNoetherian.component_noetherian U
  haveI := (forall_affine_finite_of_isCoherent F hF U).1
  I.completionToPullback_toModuleCompletionPushforward F U s

private lemma pullbackToModuleCompletion_sigmaApp (U : X.affineOpens)
    (x : (I.moduleCompletion F).val.obj (op (I.affineTrace U))) :
    (I.pullbackToModuleCompletion F).val.app (op (I.affineTrace U)) (I.sigmaApp F hF U x) = x :=
  haveI := hF.isQuasicoherent
  haveI := IsLocallyNoetherian.component_noetherian U
  haveI := (forall_affine_finite_of_isCoherent F hF U).1
  I.pullbackToModuleCompletion_completionToPullback F U x

private lemma sigmaApp_map_of_le {U U' : X.affineOpens} (hUU : (U' : X.Opens) ≤ U)
    (h : I.affineTrace U' ≤ I.affineTrace U)
    (x : (I.moduleCompletion F).val.obj (op (I.affineTrace U))) :
    I.sigmaApp F hF U' ((I.moduleCompletion F).val.map (homOfLE h).op x) =
      ((SheafOfModules.pullback.{u} χ).obj F).val.map (homOfLE h).op (I.sigmaApp F hF U x) :=
  haveI := hF.isQuasicoherent
  haveI := IsLocallyNoetherian.component_noetherian U
  haveI := (forall_affine_finite_of_isCoherent F hF U).1
  haveI := IsLocallyNoetherian.component_noetherian U'
  haveI := (forall_affine_finite_of_isCoherent F hF U').1
  I.completionToPullback_map F hUU h x

/-- **Compatibility of the inverses with restriction** along any inclusion of traces
`U' ∩ |Y| ⊆ U ∩ |Y|`, checked on traces of affine opens inside `U ∩ U'`. -/
private lemma sigmaApp_map {U U' : X.affineOpens} (h : I.affineTrace U' ≤ I.affineTrace U)
    (x : (I.moduleCompletion F).val.obj (op (I.affineTrace U))) :
    I.sigmaApp F hF U' ((I.moduleCompletion F).val.map (homOfLE h).op x) =
      ((SheafOfModules.pullback.{u} χ).obj F).val.map (homOfLE h).op (I.sigmaApp F hF U x) := by
  have key : ∀ y : I.affineTrace U', ∃ V : X.affineOpens,
      I.infinitesimalNeighborhoodι 1 (y : I.infinitesimalNeighborhood 1) ∈ (V : X.Opens) ∧
        (V : X.Opens) ≤ (U : X.Opens) ⊓ (U' : X.Opens) := by
    intro y
    obtain ⟨V, hV, hyV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (U := (U : X.Opens) ⊓ (U' : X.Opens)) (show _ ∈ (U : X.Opens) ⊓ (U' : X.Opens) from
        ⟨h y.2, y.2⟩)
    exact ⟨⟨V, hV⟩, hyV, hVU⟩
  choose V hyV hVUU' using key
  have ha : ∀ y, I.affineTrace (V y) ≤ I.affineTrace U' := fun y z hz => (hVUU' y hz).2
  refine sheafOfModules_eq_of_locally_eq _ (fun y => I.affineTrace (V y)) ha
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hyV ⟨z, hz⟩⟩) _ _ (fun y => ?_)
  have hVU : (V y : X.Opens) ≤ U := fun z hz => (hVUU' y hz).1
  have hVU' : (V y : X.Opens) ≤ U' := fun z hz => (hVUU' y hz).2
  have hVU'' : I.affineTrace (V y) ≤ I.affineTrace U := fun z hz => h (hVU' hz)
  have hc : (homOfLE h).op ≫ (homOfLE (ha y)).op = (homOfLE hVU'').op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have e1 := I.sigmaApp_map_of_le F hF hVU' (ha y)
    ((I.moduleCompletion F).val.map (homOfLE h).op x)
  have e2 := PresheafOfModules.map_comp_apply (I.moduleCompletion F).val (homOfLE h).op
    (homOfLE (ha y)).op x
  have e3 := I.sigmaApp_map_of_le F hF hVU hVU'' x
  have e4 := PresheafOfModules.map_comp_apply ((SheafOfModules.pullback.{u} χ).obj F).val
    (homOfLE h).op (homOfLE (ha y)).op (I.sigmaApp F hF U x)
  rw [hc] at e2 e4
  rw [← e1, ← e2, ← e4]
  exact e3

/-- The inverses on the traces of the affine opens, as a morphism of presheaves of abelian groups
on the basis of these traces. -/
private def sigmaBasis :
    (inducedFunctor I.affineTrace).op ⋙ (I.moduleCompletion F).val.presheaf ⟶
      (inducedFunctor I.affineTrace).op ⋙ ((SheafOfModules.pullback.{u} χ).obj F).val.presheaf where
  app U := AddCommGrpCat.ofHom (I.sigmaApp F hF U.unop)
  naturality U U' f := by
    ext x
    exact I.sigmaApp_map F hF (leOfHom f.unop.hom) x

/-- The glued inverse, as a morphism of sheaves of abelian groups on `|Y|`. -/
private def sigmaAb :
    (I.moduleCompletion F).val.presheaf ⟶ ((SheafOfModules.pullback.{u} χ).obj F).val.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom (I.moduleCompletion F).val.presheaf
    ⟨((SheafOfModules.pullback.{u} χ).obj F).val.presheaf,
      ((SheafOfModules.pullback.{u} χ).obj F).isSheaf⟩
    I.isBasis_affineTrace (I.sigmaBasis F hF)

private lemma sigmaAb_app (U : X.affineOpens)
    (x : (I.moduleCompletion F).val.obj (op (I.affineTrace U))) :
    (I.sigmaAb F hF).app (op (I.affineTrace U)) x = I.sigmaApp F hF U x := by
  have h := TopCat.Sheaf.extend_hom_app (B := I.affineTrace) (I.moduleCompletion F).val.presheaf
    ⟨((SheafOfModules.pullback.{u} χ).obj F).val.presheaf,
      ((SheafOfModules.pullback.{u} χ).obj F).isSheaf⟩ I.isBasis_affineTrace (I.sigmaBasis F hF) U
  exact (ConcreteCategory.congr_hom h x).trans rfl

private lemma sigmaAb_smul (V : (I.infinitesimalNeighborhood 1).Opens)
    (r : I.formalCompletionRingCatSheaf.obj.obj (op V))
    (x : (I.moduleCompletion F).val.obj (op V)) :
    (I.sigmaAb F hF).app (op V) (r • x) = r • (I.sigmaAb F hF).app (op V) x := by
  refine I.eq_of_affineTrace _ _ _ (fun U hU => ?_)
  have n1 := NatTrans.naturality_apply (I.sigmaAb F hF) (homOfLE hU).op (r • x)
  have n2 := NatTrans.naturality_apply (I.sigmaAb F hF) (homOfLE hU).op x
  have hs := PresheafOfModules.map_smul (I.moduleCompletion F).val (homOfLE hU).op r x
  have hs' := PresheafOfModules.map_smul ((SheafOfModules.pullback.{u} χ).obj F).val
    (homOfLE hU).op r ((I.sigmaAb F hF).app (op V) x)
  refine n1.symm.trans ?_
  refine (congrArg _ hs).trans ?_
  refine (I.sigmaAb_app F hF U _).trans ?_
  refine (I.sigmaApp_smul F hF U _ _).trans ?_
  refine (congrArg _ ((I.sigmaAb_app F hF U _).symm.trans n2)).trans ?_
  exact hs'.symm

/-- **The inverse `F̂ ⟶ f^* F`**, a morphism of `𝒪_X̂`-modules. -/
private def completionToPullbackHom :
    I.moduleCompletion F ⟶ (SheafOfModules.pullback.{u} χ).obj F :=
  ⟨PresheafOfModules.homMk (I.sigmaAb F hF) (fun V r x => I.sigmaAb_smul F hF V.unop r x)⟩

private lemma completionToPullbackHom_val_app (U : X.affineOpens)
    (x : (I.moduleCompletion F).val.obj (op (I.affineTrace U))) :
    (I.completionToPullbackHom F hF).val.app (op (I.affineTrace U)) x = I.sigmaApp F hF U x :=
  I.sigmaAb_app F hF U x

private lemma completionToPullbackHom_comp_pullbackToModuleCompletion :
    I.completionToPullbackHom F hF ≫ I.pullbackToModuleCompletion F = 𝟙 _ :=
  sheafOfModules_hom_ext_of_isBasis I.isBasis_affineTrace (fun U x =>
    (congrArg ((I.pullbackToModuleCompletion F).val.app (op (I.affineTrace U)))
      (I.completionToPullbackHom_val_app F hF U x)).trans
      (I.pullbackToModuleCompletion_sigmaApp F hF U x))

private lemma toModuleCompletionPushforward_comp_completionToPullbackHom :
    I.toModuleCompletionPushforward F ≫ (𝒫).map (I.completionToPullbackHom F hF) =
      (SheafOfModules.pullbackPushforwardAdjunction.{u} χ).unit.app F := by
  have hB : Opens.IsBasis (Set.range (Subtype.val : X.affineOpens → X.Opens)) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  exact sheafOfModules_hom_ext_of_isBasis hB (fun U s =>
    (I.completionToPullbackHom_val_app F hF U _).trans
      (I.sigmaApp_toModuleCompletionPushforward F hF U s))

private lemma pullbackToModuleCompletion_comp_completionToPullbackHom :
    I.pullbackToModuleCompletion F ≫ I.completionToPullbackHom F hF = 𝟙 _ := by
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{u} χ
  have e : adj.unit.app F ≫ (𝒫).map (I.pullbackToModuleCompletion F) =
      I.toModuleCompletionPushforward F :=
    (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have h1 : adj.unit.app F ≫ (𝒫).map (I.pullbackToModuleCompletion F ≫
      I.completionToPullbackHom F hF) = adj.unit.app F ≫ (𝒫).map (𝟙 _) :=
    ((congrArg _ ((𝒫).map_comp _ _)).trans (Category.assoc _ _ _).symm).trans
      (((congrArg (· ≫ (𝒫).map (I.completionToPullbackHom F hF)) e).trans
        (I.toModuleCompletionPushforward_comp_completionToPullbackHom F hF)).trans
        ((Category.comp_id _).symm.trans (congrArg _ ((𝒫).map_id _).symm)))
  exact (adj.homEquiv _ _).injective ((adj.homEquiv_unit _ _ _).trans
    (h1.trans (adj.homEquiv_unit _ _ _).symm))

end Glue

/-- **Hartshorne II, Corollary 9.8** (tensor product): on a locally Noetherian scheme `X`
(Hartshorne: Noetherian), for a coherent `𝒪_X`-module `F`, the canonical map
`F|_{|Y|} ⊗_{𝒪_X|_{|Y|}} 𝒪_X̂ ⟶ F̂` is an isomorphism. The left side is the module pullback
`f^* F` along `f : (|Y|, 𝒪_X̂) ⟶ (X, 𝒪_X)`, an ordinary tensor product of sheaves of modules. -/
theorem isIso_pullbackToModuleCompletion [IsLocallyNoetherian X] (hF : IsCoherent F) :
    IsIso (I.pullbackToModuleCompletion F) :=
  ⟨⟨I.completionToPullbackHom F hF, I.pullbackToModuleCompletion_comp_completionToPullbackHom F hF,
    I.completionToPullbackHom_comp_pullbackToModuleCompletion F hF⟩⟩

/-- **Hartshorne II, Corollary 9.8** (the isomorphism): on a locally Noetherian scheme
(Hartshorne: Noetherian), for `F` coherent, `F|_{|Y|} ⊗_{𝒪_X|_{|Y|}} 𝒪_X̂ ≅ F̂` as
`𝒪_X̂`-modules, the canonical map `pullbackToModuleCompletion`. -/
def pullbackIsoModuleCompletion [IsLocallyNoetherian X] (hF : IsCoherent F) :
    (SheafOfModules.pullback.{u} χ).obj F ≅ I.moduleCompletion F :=
  have := I.isIso_pullbackToModuleCompletion F hF
  asIso (I.pullbackToModuleCompletion F)

end QuasicoherentIdealSubsheaf

end Hartshorne
