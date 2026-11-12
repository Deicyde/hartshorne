/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Hartshorne.Scheme.PicardPullback
import Hartshorne.Scheme.ExteriorPowerExactFiltration
import Hartshorne.Scheme.Differentials.CanonicalSheaf
import Hartshorne.Scheme.Differentials.CanonicalSheafOfProduct
import Hartshorne.Scheme.Differentials.NormalConormalSheaves

/-!
# Adjunction via the determinant of the normal bundle

Hartshorne, *Algebraic Geometry*, II, first part of Proposition 8.20 (p. 182): if `Y` is a
nonsingular subvariety of codimension `r` of a nonsingular variety `X` over `k`, then
`ω_Y ≅ ω_X|_Y ⊗ ⋀^r N_{Y/X}`.

## Proof

Following the book:

* the conormal sequence `0 → N^*_{Y/X} → Ω_X ⊗ 𝒪_Y → Ω_Y → 0` (Theorem 8.17) is a short exact
  sequence of locally free sheaves of ranks `r`, `n = dim X` and `m = dim Y`; taking highest
  exterior powers (Exercise II.5.16(d)) gives `⋀^n (Ω_X ⊗ 𝒪_Y) ≅ ⋀^r N^* ⊗ ω_Y`, and
  `⋀^n (Ω_X ⊗ 𝒪_Y) ≅ ω_X|_Y` because pullback commutes with exterior powers of locally free
  sheaves;
* the top exterior power commutes with duals: for `F` locally free of rank `r` on a ringed space,
  the determinant pairing `⋀^r F^∨ × ⋀^r F → 𝒪_X`,
  `(ψ₁ ∧ ⋯ ∧ ψ_r, x₁ ∧ ⋯ ∧ x_r) ↦ det (ψ_j(x_i))`, is perfect, giving
  `⋀^r F^∨ ≅ (⋀^r F)^∨` (`Hartshorne.ExteriorDual.exteriorPowerDualIso`);
* hence `ω_X|_Y ⊗ ⋀^r N ≅ (⋀^r N^* ⊗ ω_Y) ⊗ (⋀^r N^*)^∨ ≅ ω_Y`, as `⋀^r N^*` is invertible.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace ExteriorDual

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

open Ringed SheafAlgebraOperations SheafTensorOperations

set_option hygiene false in
/-- Sections of the structure sheaf, as the rings over which presheaves of modules take values. -/
local notation3 "𝒪ᵣ(" V ")" => (R.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)

section Abstract

variable {A B : Type u} [CommRing A] [CommRing B] {σ : A →+* B}
  {M N P M' N' P' : Type u} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P'] [Module A M] [Module A N] [Module A P]
  [Module B M'] [Module B N'] [Module B P'] {ι κ : Type*}

/-- Two bilinear maps intertwined by semilinear maps on spanning families of both arguments are
intertwined everywhere. -/
theorem bilinear_restrict_eq_of_span (f : M →ₗ[A] N →ₗ[A] P) (g : M' →ₗ[B] N' →ₗ[B] P')
    (rM : M →ₛₗ[σ] M') (rN : N →ₛₗ[σ] N') (rP : P →ₛₗ[σ] P') {u : ι → M} {v : κ → N}
    (hu : Submodule.span A (Set.range u) = ⊤) (hv : Submodule.span A (Set.range v) = ⊤)
    (h : ∀ i j, rP (f (u i) (v j)) = g (rM (u i)) (rN (v j))) (m : M) (n : N) :
    rP (f m n) = g (rM m) (rN n) := by
  refine semilinear_eq_comp_of_span (τ := RingHom.id B) hv (rP.comp (f m)) rN (g (rM m))
    (fun _ => rfl) (fun j => ?_) n
  exact semilinear_eq_comp_of_span (τ := RingHom.id B) hu (rP.comp (f.flip (v j))) rM
    (g.flip (rN (v j))) (fun _ => rfl) (fun i => h i j) m

end Abstract

variable (F : SheafOfModules.{u} (ringCatSheafOf R)) (r : ℕ)

/-- A section of `F^∨` over `U` as a linear form on `F(U)`. -/
noncomputable def dualToDual (U : Opens X) :
    (moduleSheafDual F).val.obj (op U) →ₗ[𝒪ᵣ(U)] Module.Dual 𝒪ᵣ(U) (F.val.obj (op U)) where
  toFun ψ := dualEval ψ (le_refl U)
  map_add' ψ φ := moduleSheafHomEval_add ψ φ _
  map_smul' a ψ := by
    ext x
    refine (moduleSheafHomEval_smul a ψ (le_refl U) x).trans ?_
    rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl

/-- The determinant pairing `⋀^r F^∨(U) × ⋀^r F(U) → 𝒪_X(U)` on sections. -/
noncomputable def pairingApp (U : (Opens X)ᵒᵖ) :
    ⋀[𝒪ᵣ(U.unop)]^r ((moduleSheafDual F).val.obj U) →ₗ[𝒪ᵣ(U.unop)]
      Module.Dual 𝒪ᵣ(U.unop) (⋀[𝒪ᵣ(U.unop)]^r (F.val.obj U)) :=
  exteriorPower.pairingDual _ _ r ∘ₗ exteriorPower.map r (dualToDual F U.unop)

lemma pairingApp_ιMulti (U : (Opens X)ᵒᵖ) (ψ : Fin r → (moduleSheafDual F).val.obj U)
    (c : Fin r → F.val.obj U) :
    pairingApp F r U (exteriorPower.ιMulti _ r ψ) (exteriorPower.ιMulti _ r c) =
      Matrix.det (Matrix.of fun a b => dualToDual F U.unop (ψ b) (c a)) := by
  rw [pairingApp, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    exteriorPower.pairingDual_ιMulti_ιMulti]
  rfl

lemma dualToDual_restrict {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (ψ : (moduleSheafDual F).val.obj U)
    (c : F.val.obj U) :
    dualToDual F V.unop ((moduleSheafDual F).val.map i ψ) (F.val.map i c) =
      R.obj.map i (dualToDual F U.unop ψ c) := by
  change moduleSheafHomEval ((moduleSheafDual F).val.presheaf.map (homOfLE (leOfHom i.unop)).op ψ)
      (le_refl V.unop) (F.val.presheaf.map (homOfLE (leOfHom i.unop)).op c) = _
  exact moduleSheafHomEval_natural ψ (le_refl U.unop) (leOfHom i.unop) c

lemma pairingApp_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (p : (moduleSheafExteriorPowerPresheaf r (moduleSheafDual F)).obj U)
    (q : (moduleSheafExteriorPowerPresheaf r F).obj U) :
    (structureModule R).val.map i (pairingApp F r U p q) =
      pairingApp F r V ((moduleSheafExteriorPowerPresheaf r (moduleSheafDual F)).map i p)
        ((moduleSheafExteriorPowerPresheaf r F).map i q) := by
  refine bilinear_restrict_eq_of_span (σ := ((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom)
    (pairingApp F r U) (pairingApp F r V)
    ((moduleSheafExteriorPowerPresheaf r (moduleSheafDual F)).restrictₛₗ i)
    ((moduleSheafExteriorPowerPresheaf r F).restrictₛₗ i)
    ((structureModule R).val.restrictₛₗ i)
    (exteriorPower.ιMulti_span _ r _) (exteriorPower.ιMulti_span _ r _) (fun ψ c => ?_) p q
  change (structureModule R).val.map i (pairingApp F r U (exteriorPower.ιMulti _ r ψ)
      (exteriorPower.ιMulti _ r c)) =
    pairingApp F r V (exteriorPowerMap r _ ((moduleSheafDual F).val.restrictₛₗ i)
        (exteriorPower.ιMulti _ r ψ))
      (exteriorPowerMap r _ (F.val.restrictₛₗ i) (exteriorPower.ιMulti _ r c))
  rw [exteriorPowerMap_ιMulti, exteriorPowerMap_ιMulti, pairingApp_ιMulti, pairingApp_ιMulti]
  change R.obj.map i _ = _
  rw [RingHom.map_det]
  congr 1
  ext a b
  exact (dualToDual_restrict F i (ψ b) (c a)).symm

/-- The determinant pairing `⋀^r F^∨ × ⋀^r F → 𝒪_X` on the presheaf exterior powers. -/
noncomputable def presheafPairing :
    PresheafBilinear (moduleSheafExteriorPowerPresheaf r (moduleSheafDual F))
      (moduleSheafExteriorPowerPresheaf r F) (structureModule R).val where
  app := pairingApp F r
  naturality := pairingApp_naturality F r


/-- The determinant pairing `⋀^r F × ⋀^r F^∨ → 𝒪_X` on the sheaf exterior powers,
`(x₁ ∧ ⋯ ∧ x_r, ψ₁ ∧ ⋯ ∧ ψ_r) ↦ det (ψ_j(x_i))`: the extension to sheafifications of
`presheafPairing`, with its arguments swapped. -/
noncomputable def sheafPairing :
    ModuleSheafBilinear (moduleSheafExteriorPower r F)
      (moduleSheafExteriorPower r (moduleSheafDual F)) (structureModule R) where
  app U := ((extendBilinear (H := structureModule R) (presheafPairing F r)).app U).flip
  naturality i a b := (extendBilinear (H := structureModule R) (presheafPairing F r)).naturality i b a

/-- The comparison morphism `⋀^r F^∨ ⟶ (⋀^r F)^∨` induced by the determinant pairing. -/
noncomputable def exteriorPowerDualMap :
    moduleSheafExteriorPower r (moduleSheafDual F) ⟶
      moduleSheafDual (moduleSheafExteriorPower r F) :=
  bilinearCurry (sheafPairing F r)

private lemma map_id_apply (A : SheafOfModules.{u} (ringCatSheafOf R)) {U : Opens X}
    (x : A.val.obj (op U)) : A.val.presheaf.map (homOfLE (le_refl U)).op x = x := by
  rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- The dual frame evaluated on the frame. -/
lemma dualToDual_dualLocalFrame {ι : Type*} [Fintype ι] [DecidableEq ι] {U : Opens X}
    {e : ι → F.val.obj (op U)} (he : IsLocalFrame F U e) (i j : ι) :
    dualToDual F U (he.dualLocalFrame i) (e j) = (Pi.single i (1 : 𝒪ᵣ(U)) : ι → 𝒪ᵣ(U)) j := by
  refine Eq.trans ?_ ((localFrameEval_apply e (le_refl U) _ j).symm.trans
    (congrFun (he.localFrameEval_dualLocalFrame (le_refl U) i) j))
  erw [map_id_apply, map_id_apply]
  rfl

/-- Over an open carrying a frame `e₁, …, e_r` of `F`, the comparison morphism sends
`e₁^∨ ∧ ⋯ ∧ e_r^∨` to the dual of `e₁ ∧ ⋯ ∧ e_r`. -/
lemma exteriorPowerDualMap_frame {ι : Type*} [Fintype ι] [LinearOrder ι] [DecidableEq ι]
    {U : Opens X} {e : ι → F.val.obj (op U)} (he : IsLocalFrame F U e)
    (hcard : Fintype.card ι = r) (K : Set.powersetCard ι r) :
    sectionsMap (exteriorPowerDualMap F r) U
        (ExteriorPerfectPairing.exteriorPowerFrame _ r he.dualLocalFrame K) =
      (ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame F he r).dualLocalFrame K := by
  have hsub : Subsingleton (Set.powersetCard ι r) :=
    ExteriorPerfectPairing.powersetCard_subsingleton (r := r) (s := 0) (by simp [hcard])
  apply (ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame F he r).hom_ext (le_refl U)
  rw [← map_id_apply _
      ((ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame F he r).dualLocalFrame K),
    IsLocalFrame.localFrameEval_dualLocalFrame]
  funext J
  obtain rfl := Subsingleton.elim J K
  rw [Pi.single_eq_same, localFrameEval_apply]
  refine (bilinearCurry_app_eval (sheafPairing F r) U _ (le_refl U) _).trans ?_
  erw [map_id_apply, map_id_apply]
  refine (extendBilinear_unit (H := structureModule R) (presheafPairing F r) (op U)
    (exteriorPower.ιMulti_family 𝒪ᵣ(U) r he.dualLocalFrame J)
    (exteriorPower.ιMulti_family 𝒪ᵣ(U) r e J)).trans ?_
  show pairingApp F r (op U) (exteriorPower.ιMulti_family 𝒪ᵣ(U) r he.dualLocalFrame J)
    (exteriorPower.ιMulti_family 𝒪ᵣ(U) r e J) = 1
  unfold exteriorPower.ιMulti_family
  rw [pairingApp_ιMulti, ← Matrix.det_one (n := Fin r) (R := 𝒪ᵣ(U))]
  congr 1
  ext a b
  rw [Matrix.of_apply]
  refine (dualToDual_dualLocalFrame F he _ _).trans ?_
  rw [Pi.single_apply, Matrix.one_apply]
  simp only [(Set.powersetCard.ofFinEmbEquiv.symm J).injective.eq_iff]

/-- **The top exterior power commutes with duals.** For `F` locally free of rank `r`, the
morphism `⋀^r F^∨ ⟶ (⋀^r F)^∨` induced by the determinant pairing is an isomorphism. -/
theorem exteriorPowerDualMap_isIso (hF : IsLocallyFreeOfRank F r) :
    IsIso (exteriorPowerDualMap F r) :=
  modules_isIso_of_locally_bijective _ fun x => by
    classical
    obtain ⟨U, hxU, ⟨α⟩⟩ := hF x
    have he := isLocalFrame_of_over_iso α
    exact ⟨U, hxU, fun V h => IsLocalFrame.app_bijective_of_map _
      (ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame _ he.dual r)
      (ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame F he r).dual
      (exteriorPowerDualMap_frame F r he (by simp)) h⟩

/-- **The top exterior power commutes with duals:** `⋀^r F^∨ ≅ (⋀^r F)^∨` for `F` locally free of
rank `r`, induced by the determinant pairing. -/
noncomputable def exteriorPowerDualIso (hF : IsLocallyFreeOfRank F r) :
    moduleSheafExteriorPower r (moduleSheafDual F) ≅
      moduleSheafDual (moduleSheafExteriorPower r F) :=
  haveI := exteriorPowerDualMap_isIso F r hF
  asIso (exteriorPowerDualMap F r)

end ExteriorDual

section Adjunction

open Ringed

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (i : Y ⟶ X) [IsClosedImmersion i]

/-- **Hartshorne II, Proposition 8.20** (first part). Let `X` be a nonsingular variety over an
algebraically closed field `k` and `i : Y ⟶ X` a nonsingular irreducible closed subscheme of
codimension `r`. Then `ω_Y ≅ ω_X|_Y ⊗ ⋀^r N_{Y/X}`, where `ω_X|_Y = i^* ω_X` and
`N_{Y/X} = (N^*_{Y/X})^∨` is the normal sheaf.

The isomorphism is the composite of the determinant isomorphism of the conormal sequence
`0 → N^*_{Y/X} → i^* Ω_X → Ω_Y → 0` (Theorem 8.17, Exercise II.5.16(d)), the isomorphism
`i^*(⋀^n Ω_X) ≅ ⋀^n (i^* Ω_X)`, the isomorphism `⋀^r (N^*)^∨ ≅ (⋀^r N^*)^∨` given by the
determinant pairing, and the evaluation `⋀^r N^* ⊗ (⋀^r N^*)^∨ ≅ 𝒪_Y` of the invertible sheaf
`⋀^r N^*`. As in the formalization of Theorem 8.17, `X` is irreducible, regular and of finite
type over `k`, and `Y` is irreducible and regular; separatedness is not used. -/
theorem adjunction_determinant_normalSheaf (hp : FiniteType p) [IrreducibleSpace X]
    (hX : X.IsRegular) [IrreducibleSpace Y] (hY : Y.IsRegular) (r : ℕ)
    (hr : codim (Set.range i.base) = r) :
    Nonempty (canonicalSheaf (i ≫ p) ≅
      moduleSheafTensor (R := Y.sheaf) ((Scheme.Modules.pullback i).obj (canonicalSheaf p))
        (moduleSheafExteriorPower (R := Y.sheaf) r (normalSheaf i))) := by
  have := hp.1
  have := hp.2
  have hq : FiniteType (i ≫ p) := ⟨inferInstance, inferInstance⟩
  have : IsIntegral X := isIntegral_of_isRegular hX
  have : IsIntegral Y := isIntegral_of_isRegular hY
  obtain ⟨n, hn⟩ := ProductNonsingular.exists_topologicalKrullDim_eq p hp
  obtain ⟨m, hm⟩ := ProductNonsingular.exists_topologicalKrullDim_eq (i ≫ p) hq
  have hΩX := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank p hp n hn).1 hX
  have hΩY := (isRegular_iff_relativeDifferentials_isLocallyFreeOfRank (i ≫ p) hq m hm).1 hY
  have hE := ProductNonsingular.isLocallyFreeOfRank_pullback i hΩX
  have hC := immersionConormalSheaf_isLocallyFreeOfRank i p hp hX hY r hr
  obtain ⟨hS, -, -⟩ := NonsingularConormal.nonsingular_closedImmersion_conormal p i hp hX hY r hr
  -- the conormal sequence `0 → N^* → i^* Ω_X → Ω_Y → 0`, with `N^*` the conormal sheaf
  let T : ShortComplex Y.Modules :=
    ShortComplex.mk ((immersionConormalSheafIso i).hom ≫ ClosedConormal.conormalToPullback i p)
      (Scheme.pullbackRelativeDifferentialsToComp i p)
      (by rw [Category.assoc, ClosedConormal.conormalToPullback_comp, Limits.comp_zero])
  have hT : T.ShortExact := by
    refine ShortComplex.shortExact_of_iso ?_ hS
    exact ShortComplex.isoMk (immersionConormalSheafIso i).symm (Iso.refl _) (Iso.refl _)
      (by simp [T]) (by simp [T])
  have hΩX' := hΩX
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at hE hC hΩY hΩX'
  -- determinant of the conormal sequence: `⋀^n (i^* Ω_X) ≅ ⋀^r N^* ⊗ ω_Y`
  obtain ⟨φ⟩ := ExteriorPowerExactFiltration.exteriorPower_exact_det T hT hC hE hΩY
  rw [canonicalSheaf_eq _ hm, canonicalSheaf_eq _ hn]
  have hL : IsInvertible (moduleSheafExteriorPower r (immersionConormalSheaf i)) := by
    have := hC.moduleSheafExteriorPower r
    rwa [Nat.choose_self] at this
  let W := moduleSheafExteriorPower (R := Y.sheaf) m (Scheme.relativeDifferentials (i ≫ p))
  let L := moduleSheafExteriorPower (R := Y.sheaf) r (immersionConormalSheaf i)
  exact ⟨(moduleSheafTensorIsoOfIso (pullbackExteriorPowerIso i hΩX n ≪≫ φ)
      (ExteriorDual.exteriorPowerDualIso _ r hC) ≪≫
    moduleSheafTensorIsoOfIso (moduleSheafTensorComm L W) (Iso.refl _) ≪≫
    moduleSheafTensorAssoc W L (moduleSheafDual L) ≪≫
    moduleSheafTensorIsoOfIso (Iso.refl W) (moduleSheafDualEvalIso L hL) ≪≫
    moduleSheafTensorComm W (structureModule Y.sheaf) ≪≫ moduleSheafUnitTensor W).symm⟩

end Adjunction

end Hartshorne
