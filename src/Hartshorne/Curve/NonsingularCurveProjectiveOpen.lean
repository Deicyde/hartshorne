/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.CurveToValuationSpaceIso
import Hartshorne.Curve.FunctionFieldProjectiveModel

/-!
# Completion of a nonsingular curve

Hartshorne, *Algebraic Geometry*, I.6, Corollary 6.10 (second assertion), p. 45.

A nonsingular quasi-projective curve is an open subcurve of its valuation
curve.  Theorem 6.9 identifies the full valuation curve with a nonsingular
projective curve, and transporting that open gives a projective completion.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

namespace ValuationSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable [IsAlgClosed k] [Algebra.EssFiniteType k K]

private def restrictOpenOfLE (X : Variety k) (U V : Opens X.carrier)
    (hV : (V : Set X.carrier).Nonempty) :
    Opens (X.restrict V hV).carrier where
  carrier := {x | x.1 ∈ U}
  is_open' := U.isOpen.preimage continuous_subtype_val

omit [IsAlgClosed k] in
private theorem restrictOpenOfLE_nonempty (X : Variety k)
    (U V : Opens X.carrier) (hUV : U ≤ V)
    (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    ((restrictOpenOfLE X U V hV : Opens (X.restrict V hV).carrier) :
      Set (X.restrict V hV).carrier).Nonempty := by
  obtain ⟨x, hx⟩ := hU
  exact ⟨⟨x, hUV hx⟩, hx⟩

private noncomputable def restrictToRestrictOfLEHom (X : Variety k)
    (U V : Opens X.carrier) (hUV : U ≤ V)
    (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    VarietyHom (X.restrict U hU)
      ((X.restrict V hV).restrict (restrictOpenOfLE X U V hV)
        (restrictOpenOfLE_nonempty X U V hUV hU hV)) :=
  VarietyHom.liftToRestrict (X.inclHomOfLE hUV hU hV)
    (restrictOpenOfLE X U V hV)
    (restrictOpenOfLE_nonempty X U V hUV hU hV) (fun x ↦ x.2)

private noncomputable def restrictToRestrictOfLEInv (X : Variety k)
    (U V : Opens X.carrier) (hUV : U ≤ V)
    (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    VarietyHom
      ((X.restrict V hV).restrict (restrictOpenOfLE X U V hV)
        (restrictOpenOfLE_nonempty X U V hUV hU hV))
      (X.restrict U hU) :=
  VarietyHom.liftToRestrict
    ((X.inclHom V hV).comp
      ((X.restrict V hV).inclHom (restrictOpenOfLE X U V hV)
        (restrictOpenOfLE_nonempty X U V hUV hU hV)))
    U hU (fun x ↦ x.2)

omit [IsAlgClosed k] in
private theorem restrictToRestrictOfLEHom_isIso (X : Variety k)
    (U V : Opens X.carrier) (hUV : U ≤ V)
    (hU : (U : Set X.carrier).Nonempty)
    (hV : (V : Set X.carrier).Nonempty) :
    (restrictToRestrictOfLEHom X U V hUV hU hV).IsIso := by
  refine ⟨restrictToRestrictOfLEInv X U V hUV hU hV, ?_, ?_⟩
  · apply VarietyHom.ext
    funext x
    rfl
  · apply VarietyHom.ext
    funext x
    rfl

private noncomputable def abstractCurveOpenInFull
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K)) :
    Opens (abstractNonsingularCurveOfFunctionField htrdeg).carrier where
  carrier := {R | R.1 ∈ U}
  is_open' := U.isOpen.preimage continuous_subtype_val

private theorem abstractCurveOpenInFull_nonempty
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    ((abstractCurveOpenInFull htrdeg U : Opens
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier) :
      Set (abstractNonsingularCurveOfFunctionField htrdeg).carrier).Nonempty := by
  obtain ⟨R, hR⟩ := hU
  exact ⟨⟨R, trivial⟩, hR⟩

private noncomputable def abstractCurveOpenToFullRestrictionHom
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    VarietyHom (abstractNonsingularCurve htrdeg U hU)
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict
        (abstractCurveOpenInFull htrdeg U)
        (abstractCurveOpenInFull_nonempty htrdeg U hU)) := by
  have htop : ((⊤ : Opens (ValuationSpace k K)) :
      Set (ValuationSpace k K)).Nonempty := ⟨hU.some, trivial⟩
  unfold abstractNonsingularCurveOfFunctionField
  unfold abstractNonsingularCurve
  unfold abstractCurveOpenInFull
  exact restrictToRestrictOfLEHom (abstractNonsingularCurveAmbient htrdeg)
    U ⊤ (fun _ _ ↦ trivial) hU htop

private theorem abstractCurveOpenToFullRestrictionHom_isIso
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    (abstractCurveOpenToFullRestrictionHom htrdeg U hU).IsIso := by
  have htop : ((⊤ : Opens (ValuationSpace k K)) :
      Set (ValuationSpace k K)).Nonempty := ⟨hU.some, trivial⟩
  unfold abstractCurveOpenToFullRestrictionHom
  unfold abstractNonsingularCurveOfFunctionField
  unfold abstractNonsingularCurve
  unfold abstractCurveOpenInFull
  exact restrictToRestrictOfLEHom_isIso
    (abstractNonsingularCurveAmbient htrdeg)
    U ⊤ (fun _ _ ↦ trivial) hU htop

end ValuationSpace

variable {k : Type u} [Field k] [IsAlgClosed k]
variable { σ : Type u } [Finite σ]
variable {Y : Set (ProjectiveSpace k σ)}

/-- **Hartshorne I.6, Corollary 6.10 (second assertion).** Every nonsingular
quasi-projective curve is isomorphic to an open subcurve of a nonsingular
projective curve. -/
theorem IsQuasiProjVariety.exists_nonsingular_projective_open_model
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    ∃ ( τ : Type u) (_ : Finite τ) (_ : Nonempty τ)
      (Z : Set (ProjectiveSpace k τ)) (hZ : IsProjVariety Z)
      (V : Opens (Variety.ofProjective hZ).carrier)
      (hV : (V : Set (Variety.ofProjective hZ).carrier).Nonempty)
      (f : VarietyHom (Variety.ofQuasiProjective hY)
        ((Variety.ofProjective hZ).restrict V hV)),
      f.IsIso ∧
        (Variety.ofProjective hZ).IsCurve ∧
        (Variety.ofProjective hZ).Nonsingular := by
  classical
  have hσ : Nonempty σ := by
    obtain ⟨P, _⟩ := hY.1
    by_contra h
    apply P.rep_nonzero
    funext i
    exact (h ⟨i⟩).elim
  let _ := hσ
  let X := Variety.ofQuasiProjective hY
  let hX := Variety.hasAffineOpenBasis_ofQuasiProjective hY
  let _ : Algebra.EssFiniteType k X.FunctionField :=
    RationalMapFunctionField.essFiniteType_functionField hX
  let htrdeg : Algebra.trdeg k X.FunctionField = 1 :=
    hX.isCurve_iff_trdeg_eq_one.mp hcurve
  let U := hY.localRingMapRangeOpen hcurve hns
  let hU := hY.localRingMapRangeOpen_nonempty hcurve hns
  let curveToOpen : VarietyHom X
      (ValuationSpace.abstractNonsingularCurve htrdeg U hU) :=
    hY.localRingMapAbstractCurveHom hcurve hns
  have hCurveToOpen : curveToOpen.IsIso := by
    exact hY.localRingMapAbstractCurveHom_isIso hcurve hns
  obtain ⟨D, hD, hDcurve, hDnonsingular⟩ :=
    ValuationSpace.exists_nonsingular_projective_model htrdeg
  obtain ⟨g, hgf, hfg⟩ := hD
  have hg : g.IsIso := ⟨D.φ, hfg, hgf⟩
  let W := ValuationSpace.abstractCurveOpenInFull htrdeg U
  have hW : ((W : Opens
      (ValuationSpace.abstractNonsingularCurveOfFunctionField htrdeg).carrier) :
      Set (ValuationSpace.abstractNonsingularCurveOfFunctionField
        htrdeg).carrier).Nonempty :=
    ValuationSpace.abstractCurveOpenInFull_nonempty htrdeg U hU
  let V : Opens (Variety.ofProjective D.isProjVariety).carrier :=
    Variety.isoPreimageOpen g W
  have hV : ((V : Opens (Variety.ofProjective D.isProjVariety).carrier) :
      Set (Variety.ofProjective D.isProjVariety).carrier).Nonempty := by
    obtain ⟨P, hP⟩ := hW
    obtain ⟨Q, hQP⟩ := hg.bijective.surjective P
    refine ⟨Q, ?_⟩
    change g Q ∈ W
    rw [hQP]
    exact hP
  let targetToFullRestriction : VarietyHom
      ((Variety.ofProjective D.isProjVariety).restrict V hV)
      ((ValuationSpace.abstractNonsingularCurveOfFunctionField htrdeg).restrict
        W hW) :=
    Variety.restrictIsoPreimageHom g W hW hV
  have hTargetToFullRestriction : targetToFullRestriction.IsIso :=
    Variety.restrictIsoPreimageHom_isIso hg W hW hV
  obtain ⟨fullRestrictionToTarget, hleft, hright⟩ :=
    hTargetToFullRestriction
  have hFullRestrictionToTarget : fullRestrictionToTarget.IsIso :=
    ⟨targetToFullRestriction, hright, hleft⟩
  let openToFullRestriction :=
    ValuationSpace.abstractCurveOpenToFullRestrictionHom htrdeg U hU
  have hOpenToFullRestriction : openToFullRestriction.IsIso :=
    ValuationSpace.abstractCurveOpenToFullRestrictionHom_isIso htrdeg U hU
  let f : VarietyHom X
      ((Variety.ofProjective D.isProjVariety).restrict V hV) :=
    fullRestrictionToTarget.comp
      (openToFullRestriction.comp curveToOpen)
  have hf : f.IsIso :=
    hFullRestrictionToTarget.comp
      (hOpenToFullRestriction.comp hCurveToOpen)
  let _ := D.M₀.finite_ι
  let _ := D.M₁.finite_ι
  exact ⟨Option D.M₀.ι × Option D.M₁.ι, inferInstance, inferInstance,
    D.Y, D.isProjVariety, V, hV, f, hf, hDcurve, hDnonsingular⟩

end

end Hartshorne
