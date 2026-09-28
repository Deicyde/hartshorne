/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.FunctionFieldProjectiveModel

/-!
# Abstract nonsingular curves are quasi-projective

Hartshorne, *Algebraic Geometry*, I.6, Corollary 6.10 (first assertion), p. 45.

An abstract nonsingular curve is an open subcurve of the valuation curve of
its function field.  Theorem 6.9 identifies that valuation curve with a
nonsingular projective curve, so transporting the open gives the required
quasi-projective model.
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

/-- **Hartshorne I.6, Corollary 6.10 (first assertion).** Every abstract
nonsingular curve is isomorphic to a nonsingular quasi-projective curve.

Here the quasi-projective target is exhibited intrinsically as a nonempty open
subvariety of the concrete nonsingular projective model supplied by Theorem
6.9. -/
theorem abstractNonsingularCurve_isomorphic_quasiProjective
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    ∃ (D : ProjectiveDiagonalModel htrdeg)
      (V : Opens (Variety.ofProjective D.isProjVariety).carrier)
      (hV : (V : Set (Variety.ofProjective D.isProjVariety).carrier).Nonempty)
      (f : VarietyHom (abstractNonsingularCurve htrdeg U hU)
        ((Variety.ofProjective D.isProjVariety).restrict V hV)),
      f.IsIso ∧
        ((Variety.ofProjective D.isProjVariety).restrict V hV).IsCurve ∧
        ((Variety.ofProjective D.isProjVariety).restrict V hV).Nonsingular := by
  obtain ⟨D, hD, _hDcurve, hDnonsingular⟩ :=
    exists_nonsingular_projective_model htrdeg
  obtain ⟨g, hgf, hfg⟩ := hD
  have hg : g.IsIso := ⟨D.φ, hfg, hgf⟩
  let W := abstractCurveOpenInFull htrdeg U
  have hW : ((W : Opens
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier) :
      Set (abstractNonsingularCurveOfFunctionField htrdeg).carrier).Nonempty :=
    abstractCurveOpenInFull_nonempty htrdeg U hU
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
      ((abstractNonsingularCurveOfFunctionField htrdeg).restrict W hW) :=
    Variety.restrictIsoPreimageHom g W hW hV
  have hTargetToFullRestriction : targetToFullRestriction.IsIso :=
    Variety.restrictIsoPreimageHom_isIso hg W hW hV
  obtain ⟨fullRestrictionToTarget, hleft, hright⟩ :=
    hTargetToFullRestriction
  have hFullRestrictionToTarget : fullRestrictionToTarget.IsIso :=
    ⟨targetToFullRestriction, hright, hleft⟩
  let sourceToFullRestriction :=
    abstractCurveOpenToFullRestrictionHom htrdeg U hU
  have hSourceToFullRestriction : sourceToFullRestriction.IsIso :=
    abstractCurveOpenToFullRestrictionHom_isIso htrdeg U hU
  let f : VarietyHom (abstractNonsingularCurve htrdeg U hU)
      ((Variety.ofProjective D.isProjVariety).restrict V hV) :=
    fullRestrictionToTarget.comp sourceToFullRestriction
  have hf : f.IsIso :=
    hFullRestrictionToTarget.comp hSourceToFullRestriction
  refine ⟨D, V, hV, f, hf, ?_, ?_⟩
  · exact hf.topologicalKrullDim_eq.symm.trans
      (abstractNonsingularCurve_isCurve htrdeg U hU)
  · intro P
    exact (Variety.nonsingularAt_restrict_iff P).mpr
      (hDnonsingular P.1)

end ValuationSpace

end

end Hartshorne
