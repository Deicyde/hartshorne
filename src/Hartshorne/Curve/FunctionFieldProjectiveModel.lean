/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.AbstractCurveDimension
import Hartshorne.Curve.Cofinite
import Hartshorne.Curve.DominatingDVR
import Hartshorne.Curve.ProjectiveModelLocalRings
import Hartshorne.Morphism.IsomorphismCriterion
import Hartshorne.Nonsingular.IntrinsicNonsingular
import Hartshorne.Projective.LocalRingDeterminesPoint

/-!
# Nonsingular projective models of function fields

Hartshorne, *Algebraic Geometry*, I.6, Theorem 6.9 (pp. 44--45).

Every one-dimensional function field over an algebraically closed field is the
function field of a nonsingular projective curve.  More precisely, the
abstract curve of its discrete valuation rings is isomorphic to the
projective diagonal model constructed from two normalization charts.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

namespace ValuationSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable [IsAlgClosed k] [Algebra.EssFiniteType k K]

private theorem valuationSpaceTop_nonempty
    (htrdeg : Algebra.trdeg k K = 1) :
    ((⊤ : Opens (ValuationSpace k K)) : Set (ValuationSpace k K)).Nonempty := by
  let _ : Infinite (FunctionFieldDVR k K) :=
    FunctionFieldDVR.infinite_of_trdeg_eq_one htrdeg
  exact Set.univ_nonempty

private theorem projectiveDiagonal_isCurve
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ProjectiveDiagonalModel htrdeg) :
    (Variety.ofProjective D.isProjVariety).IsCurve := by
  classical
  let _ := D.M₀.finite_ι
  let _ := D.M₁.finite_ι
  let hYbasis := Variety.hasAffineOpenBasis_ofProjective D.isProjVariety
  exact (Variety.HasAffineOpenBasis.isCurve_iff_trdeg_eq_one hYbasis).mpr
      ((projectiveDiagonalFunctionFieldAlgEquiv D).trdeg_eq.trans htrdeg)

private theorem projectiveDiagonal_injective
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ProjectiveDiagonalModel htrdeg) :
    Function.Injective D.φ.toFun := by
  let Y := Variety.ofProjective D.isProjVariety
  let e := projectiveDiagonalFunctionFieldAlgEquiv D
  intro P Q hPQ
  apply Subtype.ext
  apply (ValuationSpace.of k K).symm.injective
  apply FunctionFieldDVR.ext
  intro x
  change x ∈ ((ValuationSpace.of k K).symm P.1).toValuationSubring.toSubring ↔
    x ∈ ((ValuationSpace.of k K).symm Q.1).toValuationSubring.toSubring
  rw [← projectiveDiagonal_localRingRange_eq D P,
    ← projectiveDiagonal_localRingRange_eq D Q]
  change x ∈ (e.toAlgHom.comp
      (Y.localToFunctionFieldAlgHom (D.φ P))).range.toSubring ↔
    x ∈ (e.toAlgHom.comp
      (Y.localToFunctionFieldAlgHom (D.φ Q))).range.toSubring
  rw [hPQ]

private theorem projectiveDiagonal_surjective
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ProjectiveDiagonalModel htrdeg) :
    Function.Surjective D.φ.toFun := by
  classical
  let _ := D.M₀.finite_ι
  let _ := D.M₁.finite_ι
  let Y := Variety.ofProjective D.isProjVariety
  let e := projectiveDiagonalFunctionFieldAlgEquiv D
  have hYbasis : Y.HasAffineOpenBasis :=
    Variety.hasAffineOpenBasis_ofProjective D.isProjVariety
  have hYcurve : Y.IsCurve := projectiveDiagonal_isCurve D
  intro Q
  obtain ⟨R, hR⟩ :=
    hYbasis.exists_functionFieldDVR_dominating_localRing hYcurve Q
  let S : FunctionFieldDVR k K := ValuationSpace.transportDVR e R
  let P : (abstractNonsingularCurveOfFunctionField htrdeg).carrier :=
    ⟨ValuationSpace.of k K S, trivial⟩
  refine ⟨P, ?_⟩
  apply D.isProjVariety.isQuasiProjVariety.eq_of_localRingRange_le
  rintro x ⟨a, rfl⟩
  have hxR : Y.localToFunctionFieldAlgHom Q a ∈ R.toValuationSubring := by
    apply hR.1
    exact ⟨a, rfl⟩
  have hxS : e (Y.localToFunctionFieldAlgHom Q a) ∈
      ((ValuationSpace.of k K).symm P.1).toValuationSubring := by
    simpa only [P, S, ValuationSpace.of_symm_apply_apply] using
      (ValuationSpace.transportDVR_apply_mem e R
        (Y.localToFunctionFieldAlgHom Q a)).2 hxR
  have hxRange : e (Y.localToFunctionFieldAlgHom Q a) ∈
      (projectiveDiagonalLocalToAmbientAlgHom D P).range.toSubring := by
    rw [projectiveDiagonal_localRingRange_eq D P]
    exact hxS
  obtain ⟨b, hb⟩ := hxRange
  refine ⟨b, ?_⟩
  apply e.injective
  change projectiveDiagonalLocalToAmbientAlgHom D P b =
    e (Y.localToFunctionFieldAlgHom Q a)
  exact hb

private theorem projectiveDiagonal_isHomeomorph
    {htrdeg : Algebra.trdeg k K = 1}
    (D : ProjectiveDiagonalModel htrdeg)
    (hbijective : Function.Bijective D.φ.toFun) :
    IsHomeomorph D.φ.toFun := by
  classical
  let _ := D.M₀.finite_ι
  let _ := D.M₁.finite_ι
  have hSourceClosed (Z : Set
      (abstractNonsingularCurveOfFunctionField htrdeg).carrier) :
      IsClosed Z → Z = Set.univ ∨ Z.Finite := by
    intro hZ
    obtain ⟨T, hTclosed, hTZ⟩ :=
      Topology.IsInducing.subtypeVal.isClosed_iff.mp hZ
    rcases (ValuationSpace.isClosed_iff k K).mp hTclosed with
      hTuniv | hTfinite
    · left
      apply Set.eq_univ_of_forall
      intro z
      have hz : z ∈ Subtype.val ⁻¹' T := by
        rw [hTuniv]
        trivial
      exact hTZ ▸ hz
    · right
      rw [← hTZ]
      exact hTfinite.preimage Subtype.val_injective.injOn
  have hTargetClosed :=
    (D.isProjVariety.isQuasiProjVariety.isCurve_infinite_and_isClosed_iff
      (projectiveDiagonal_isCurve D)).2
  apply isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
  refine ⟨D.φ.continuous_toFun, ?_, hbijective⟩
  intro Z hZ
  rcases hSourceClosed Z hZ with rfl | hZfinite
  · apply (hTargetClosed _).mpr
    left
    rw [Set.image_univ]
    exact Set.range_eq_univ.mpr hbijective.2
  · apply (hTargetClosed _).mpr
    exact Or.inr (hZfinite.image D.φ.toFun)

/-- **Hartshorne I.6, Theorem 6.9.** A one-dimensional function field over an
algebraically closed field has a nonsingular projective model: the abstract
curve of its discrete valuation rings is isomorphic to the packaged
projective diagonal curve. -/
theorem exists_nonsingular_projective_model
    (htrdeg : Algebra.trdeg k K = 1) :
    ∃ D : ProjectiveDiagonalModel htrdeg,
      D.φ.IsIso ∧
        (Variety.ofProjective D.isProjVariety).IsCurve ∧
        (Variety.ofProjective D.isProjVariety).Nonsingular := by
  obtain ⟨D⟩ := exists_dense_projective_diagonal htrdeg
  have hbijective : Function.Bijective D.φ.toFun :=
    ⟨projectiveDiagonal_injective D, projectiveDiagonal_surjective D⟩
  have hhomeomorph : IsHomeomorph D.φ.toFun :=
    projectiveDiagonal_isHomeomorph D hbijective
  have hIso : D.φ.IsIso :=
    D.φ.isIso_of_isHomeomorph_of_surjective_localRingHom hhomeomorph
      (fun P ↦ (projectiveDiagonal_localRingHom_bijective D P).2)
  refine ⟨D, hIso, projectiveDiagonal_isCurve D, ?_⟩
  apply (Variety.nonsingular_iff_of_isIso hIso).mp
  exact abstractNonsingularCurve_nonsingular htrdeg
    (⊤ : Opens (ValuationSpace k K)) (valuationSpaceTop_nonempty htrdeg)

end ValuationSpace

end

end Hartshorne
