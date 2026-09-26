/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.Cofinite
import Hartshorne.Curve.DedekindSubringLocalization
import Hartshorne.Curve.FinitePoles
import Hartshorne.Curve.NonsingularAffineDedekind
import Hartshorne.Curve.Valuation
import Hartshorne.Curve.ValuationSpaceTopology
import Hartshorne.Morphism.LocalRingFunctionField
import Hartshorne.Projective.LocalRingDeterminesPoint

/-!
# The local-ring map of a nonsingular curve

Hartshorne, *Algebraic Geometry*, I.6, Proposition 6.7 (pp. 42--43).

The local ring of every point of a nonsingular quasi-projective curve gives a
discrete valuation ring in its function field.  The resulting map to the
cofinite valuation space is injective, has open image, and is a homeomorphism
onto that image.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace Variety

/-- The local ring at a nonsingular point of a curve, regarded as a discrete
valuation ring in the fixed function field. -/
noncomputable def HasAffineOpenBasis.functionFieldDVRAt
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (hns : X.Nonsingular) (P : X.carrier) :
    FunctionFieldDVR k X.FunctionField := by
  let R := hX.valuationSubringAt hcurve P (hns P)
  refine ⟨R, hX.isDiscreteValuationRing_valuationSubringAt hcurve P (hns P), ?_⟩
  exact (ValuationSubring.contains_algebraMap_iff_isTrivialOn R).mpr
    (hX.valuationSubringAt_valuation_isTrivialOn hcurve P (hns P))

/-- The point-to-local-ring map from a nonsingular curve to its cofinite
valuation space. -/
noncomputable def HasAffineOpenBasis.localRingMap
    {X : Variety k} (hX : X.HasAffineOpenBasis) (hcurve : X.IsCurve)
    (hns : X.Nonsingular) : X.carrier → ValuationSpace k X.FunctionField :=
  fun P ↦ ValuationSpace.of k X.FunctionField
    (hX.functionFieldDVRAt hcurve hns P)

end Variety

/-- The canonical map from a localization at a prime to a specified fraction
field.  It is kept private here because it is used only to compare an affine
chart with the ambient function field. -/
private noncomputable def localizationAtPrimeToFunctionField
    (B : Type u) (K : Type v) [CommRing B] [IsDomain B] [Field K]
    [Algebra k B] [Algebra B K] [IsFractionRing B K]
    [Algebra k K] [IsScalarTower k B K]
    (p : Ideal B) [p.IsPrime] :
    Localization.AtPrime p →ₐ[k] K :=
  IsLocalization.liftAlgHom (M := p.primeCompl)
    (f := IsScalarTower.toAlgHom k B K) fun y ↦
      IsLocalization.map_units K
        ⟨y.1, mem_nonZeroDivisors_of_ne_zero fun hy ↦ y.2 (hy ▸ p.zero_mem)⟩

omit [IsAlgClosed k] in
@[simp]
private theorem localizationAtPrimeToFunctionField_algebraMap
    (B : Type u) (K : Type v) [CommRing B] [IsDomain B] [Field K]
    [Algebra k B] [Algebra B K] [IsFractionRing B K]
    [Algebra k K] [IsScalarTower k B K]
    (p : Ideal B) [p.IsPrime] (b : B) :
    localizationAtPrimeToFunctionField (k := k) B K p
        (algebraMap B (Localization.AtPrime p) b) = algebraMap B K b := by
  change IsLocalization.lift _ (algebraMap B (Localization.AtPrime p) b) =
    algebraMap B K b
  exact IsLocalization.lift_eq _ b

omit [IsAlgClosed k] in
/-- The local-ring and function-field identifications attached to an affine
chart form the required commuting triangle. -/
private theorem affineChart_localToFunctionField
    {X : Variety k} {τ : Type u} [Finite τ]
    {Z : Set (τ → k)} (V : Opens X.carrier)
    (hV : (V : Set X.carrier).Nonempty) (hZ : IsAffineVariety Z)
    (φ : VarietyHom (X.restrict V hV)
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety)) (hφ : φ.IsIso)
    (Q : (X.restrict V hV).carrier)
    (z : LocalRingAt hZ.isIrreducible
      (affinePoint hZ.isQuasiAffineVariety (φ Q))) :
    let eK :=
      (RationalMapFunctionField.affineChartFunctionFieldAlgEquiv
          V hV hZ φ hφ).trans
        (RationalMapFunctionField.functionFieldAlgEquivAffine
          hZ.isQuasiAffineVariety)
    let eIsoL :
        (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).LocalRingAt (φ Q) ≃+*
          (X.restrict V hV).LocalRingAt Q :=
      RingEquiv.ofBijective (φ.localRingHom Q)
        (VarietyHom.bijective_localRingHom_of_isIso hφ Q)
    let eL :=
      (localRingEquivAffine hZ.isQuasiAffineVariety (φ Q)).symm.trans
        (eIsoL.trans (Variety.localRingEquivRestrict Q))
    eK (X.localToFunctionFieldAlgHom Q.1 (eL z)) =
      localToFunctionField hZ.isIrreducible
        (affinePoint hZ.isQuasiAffineVariety (φ Q)) z := by
  let eOpenK :=
    RationalMapFunctionField.openFunctionFieldAlgEquiv X V hV
  let eIsoK :=
    (RationalMapFunctionField.functionFieldAlgEquivOfIsIso φ hφ).symm
  let eAffK :=
    RationalMapFunctionField.functionFieldAlgEquivAffine
      hZ.isQuasiAffineVariety
  let eOpenL := Variety.localRingEquivRestrict Q
  let eIsoL :
      (Variety.ofQuasiAffine hZ.isQuasiAffineVariety).LocalRingAt (φ Q) ≃+*
        (X.restrict V hV).LocalRingAt Q :=
    RingEquiv.ofBijective (φ.localRingHom Q)
      (VarietyHom.bijective_localRingHom_of_isIso hφ Q)
  let eAffL := localRingEquivAffine hZ.isQuasiAffineVariety (φ Q)
  change eAffK (eIsoK (eOpenK
      (X.localToFunctionFieldAlgHom Q.1
        (eOpenL (φ.localRingHom Q (eAffL.symm z)))))) = _
  rw [RationalMapFunctionField.openFunctionFieldAlgEquiv_localToFunctionField]
  rw [RationalMapFunctionField.functionFieldAlgEquivOfIsIso_localToFunctionField]
  change functionFieldEquivAffine hZ.isQuasiAffineVariety
      ((Variety.ofQuasiAffine hZ.isQuasiAffineVariety).localToFunctionFieldAlgHom
        (φ Q) (eAffL.symm z)) = _
  rw [functionFieldEquivAffine_localToFunctionField]
  exact congrArg (localToFunctionField hZ.isIrreducible
    (affinePoint hZ.isQuasiAffineVariety (φ Q)))
      (eAffL.apply_symm_apply z)

/-- A finite-type subalgebra of a one-dimensional function field fails to be
contained in only finitely many function-field DVRs. -/
private theorem finite_not_contains_range
    {B : Type u} {K : Type v} [CommRing B] [Field K]
    [Algebra k B] [Algebra k K] [Algebra.FiniteType k B]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (ι : B →ₐ[k] K) :
    {R : FunctionFieldDVR k K |
      ¬ ∀ b : B, ι b ∈ R.toValuationSubring}.Finite := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_adjoin_eq_top (k := k) (A := B)
  let bad : Set (FunctionFieldDVR k K) :=
    ⋃ b ∈ (↑s : Set B), {R | R.HasPoleAt (ι b)}
  have hbad : bad.Finite := by
    exact s.finite_toSet.biUnion fun b _ ↦
      FunctionFieldDVR.finite_hasPoleAt htrdeg (ι b)
  refine hbad.subset ?_
  intro R hR
  by_contra hRbad
  apply hR
  let T : Subalgebra k B := Subalgebra.comap ι R.toSubalgebra
  have hsT : Algebra.adjoin k (↑s : Set B) ≤ T := by
    apply Algebra.adjoin_le
    intro b hb
    change ι b ∈ R.toValuationSubring
    by_contra hbR
    apply hRbad
    exact Set.mem_iUnion_of_mem b
      (Set.mem_iUnion_of_mem hb hbR)
  have hT : T = ⊤ := by
    apply top_unique
    simpa [hs] using hsT
  intro b
  change b ∈ T
  rw [hT]
  exact Set.mem_univ b

variable {σ : Type u} [Finite σ] [DecidableEq σ] [Nonempty σ]
  {Y : Set (ProjectiveSpace k σ)}

/-- The local-ring map is injective: inclusion of the corresponding local
rings in the common function field determines the point. -/
theorem IsQuasiProjVariety.localRingMap_injective
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    Function.Injective
      ((Variety.hasAffineOpenBasis_ofQuasiProjective hY).localRingMap hcurve hns) := by
  let X := Variety.ofQuasiProjective hY
  let hX := Variety.hasAffineOpenBasis_ofQuasiProjective hY
  intro P Q hPQ
  have hDVR : hX.functionFieldDVRAt hcurve hns P =
      hX.functionFieldDVRAt hcurve hns Q := by
    apply (ValuationSpace.of k X.FunctionField).injective
    exact hPQ
  have hvaluation : hX.valuationSubringAt hcurve P (hns P) =
      hX.valuationSubringAt hcurve Q (hns Q) := by
    simpa [Variety.HasAffineOpenBasis.functionFieldDVRAt] using
      congrArg FunctionFieldDVR.toValuationSubring hDVR
  apply hY.eq_of_localRingRange_le
  intro x hx
  change x ∈ (X.localRingRange P).toSubring
  rw [← hX.valuationSubringAt_toSubring hcurve P (hns P), hvaluation,
    hX.valuationSubringAt_toSubring hcurve Q (hns Q)]
  exact hx

/-- The image of the local-ring map is open in the cofinite valuation space. -/
theorem IsQuasiProjVariety.isOpen_range_localRingMap
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    IsOpen (Set.range
      ((Variety.hasAffineOpenBasis_ofQuasiProjective hY).localRingMap hcurve hns)) := by
  classical
  let X := Variety.ofQuasiProjective hY
  let hX := Variety.hasAffineOpenBasis_ofQuasiProjective hY
  let x : X.carrier := X.nonempty.some
  obtain ⟨V, hV, hxV, -, τ, hτ, Z, hZ, φ, hφ⟩ := hX ⊤ x trivial
  let _ : Finite τ := hτ
  let A := Variety.ofQuasiAffine hZ.isQuasiAffineVariety
  let eKA : X.FunctionField ≃ₐ[k] A.FunctionField :=
    RationalMapFunctionField.affineChartFunctionFieldAlgEquiv V hV hZ φ hφ
  let eK : X.FunctionField ≃ₐ[k] FunctionField hZ.isIrreducible :=
    eKA.trans
      (RationalMapFunctionField.functionFieldAlgEquivAffine
        hZ.isQuasiAffineVariety)
  let B := coordinateRing Z
  let ι : B →ₐ[k] X.FunctionField :=
    eK.symm.toAlgHom.comp (coordToRational hZ.isIrreducible)
  let _ : IsDomain B := isDomain_coordinateRing hZ
  let _ : Algebra B X.FunctionField := ι.toRingHom.toAlgebra
  let _ : IsScalarTower k B X.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (ι.commutes c).symm
  let _ : IsFractionRing B (FunctionField hZ.isIrreducible) :=
    isFractionRing_functionField hZ.isIrreducible
  let eFrac : FunctionField hZ.isIrreducible ≃ₐ[B] X.FunctionField :=
    AlgEquiv.ofRingEquiv (f := eK.symm.toRingEquiv) fun b ↦ rfl
  let _ : IsFractionRing B X.FunctionField := IsFractionRing.of_algEquiv eFrac
  have htrdeg : Algebra.trdeg k X.FunctionField = 1 :=
    hX.isCurve_iff_trdeg_eq_one.mp hcurve
  have hcurveA : A.IsCurve := by
    apply (Variety.hasAffineOpenBasis_ofAffine hZ).isCurve_iff_trdeg_eq_one.mpr
    exact eKA.trdeg_eq.symm.trans htrdeg
  have hnsV : (X.restrict V hV).Nonsingular := by
    intro Q
    exact (Variety.nonsingularAt_restrict_iff Q).mpr (hns Q.1)
  have hnsA : A.Nonsingular :=
    (Variety.nonsingular_iff_of_isIso hφ).mp hnsV
  let _ : IsDedekindDomain B :=
    hZ.isDedekindDomain_coordinateRing_of_nonsingular hcurveA hnsA
  let fDVR : X.carrier → FunctionFieldDVR k X.FunctionField :=
    hX.functionFieldDVRAt hcurve hns
  have hgood_range (R : FunctionFieldDVR k X.FunctionField)
      (hR : ∀ b : B, ι b ∈ R.toValuationSubring) :
      R ∈ Set.range fDVR := by
    have hRB : ∀ b : B,
        algebraMap B X.FunctionField b ∈ R.toValuationSubring := by
      intro b
      change ι b ∈ R.toValuationSubring
      exact hR b
    let _ : (R.center hRB).IsMaximal := R.center_isMaximal hRB
    obtain ⟨z, hz⟩ :=
      maximalIdealAt_surjective hZ.isAlgebraicSet
        (show (R.center hRB).IsMaximal from inferInstance)
    let zA : A.carrier := ⟨z.1, z.2⟩
    obtain ⟨Q, hQ⟩ := hφ.bijective.2 zA
    let zQ : Z := affinePoint hZ.isQuasiAffineVariety (φ Q)
    have hzQ : maximalIdealAt Z zQ = R.center hRB := by
      rw [show zQ = z by
        apply Subtype.ext
        exact congrArg Subtype.val hQ]
      exact hz
    have hpne : maximalIdealAt Z zQ ≠ ⊥ := by
      rw [hzQ]
      exact R.center_ne_bot hRB
    let p : IsDedekindDomain.HeightOneSpectrum B :=
      ⟨maximalIdealAt Z zQ, (maximalIdealAt_isMaximal zQ).isPrime, hpne⟩
    let S := hX.functionFieldDVRAt hcurve hns Q.1
    let eOpenL := Variety.localRingEquivRestrict Q
    let eIsoL : A.LocalRingAt (φ Q) ≃+* (X.restrict V hV).LocalRingAt Q :=
      RingEquiv.ofBijective (φ.localRingHom Q)
        (VarietyHom.bijective_localRingHom_of_isIso hφ Q)
    let eAffL := localRingEquivAffine hZ.isQuasiAffineVariety (φ Q)
    let eL : LocalRingAt hZ.isIrreducible zQ ≃+* X.LocalRingAt Q.1 :=
      eAffL.symm.trans (eIsoL.trans eOpenL)
    let eLoc : Localization.AtPrime (maximalIdealAt Z zQ) ≃+*
        X.LocalRingAt Q.1 :=
      (localizationEquivLocalRing hZ.isIrreducible zQ).trans eL
    let locToK : Localization.AtPrime (maximalIdealAt Z zQ) →ₐ[k]
        X.FunctionField :=
      localizationAtPrimeToFunctionField (k := k) B X.FunctionField
        (maximalIdealAt Z zQ)
    have hloc (a : Localization.AtPrime (maximalIdealAt Z zQ)) :
        X.localToFunctionFieldAlgHom Q.1 (eLoc a) = locToK a := by
      let f : Localization.AtPrime (maximalIdealAt Z zQ) →+* X.FunctionField :=
        (X.localToFunctionFieldAlgHom Q.1).toRingHom.comp eLoc.toRingHom
      have hfg : f = locToK.toRingHom := by
        apply IsLocalization.ringHom_ext (maximalIdealAt Z zQ).primeCompl
        apply DFunLike.ext _ _
        intro b
        change X.localToFunctionFieldAlgHom Q.1
            (eLoc (algebraMap B
              (Localization.AtPrime (maximalIdealAt Z zQ)) b)) =
          locToK (algebraMap B
            (Localization.AtPrime (maximalIdealAt Z zQ)) b)
        have heLoc : eLoc (algebraMap B
              (Localization.AtPrime (maximalIdealAt Z zQ)) b) =
            eL (coordToLocal hZ.isIrreducible zQ b) := by
          change eL ((localizationEquivLocalRing hZ.isIrreducible zQ)
              (algebraMap B
                (Localization.AtPrime (maximalIdealAt Z zQ)) b)) = _
          congr 1
          change localizationToLocal hZ.isIrreducible zQ
              (algebraMap B
                (Localization.AtPrime (maximalIdealAt Z zQ)) b) = _
          rw [localizationToLocal, IsLocalization.lift_eq]
          rfl
        rw [heLoc,
          localizationAtPrimeToFunctionField_algebraMap (k := k)]
        apply eK.injective
        rw [affineChart_localToFunctionField V hV hZ φ hφ Q,
          localToFunctionField_coordToLocal hZ.isQuasiAffineVariety zQ b]
        change coordToRational hZ.isIrreducible b =
          eK (eK.symm (coordToRational hZ.isIrreducible b))
        exact (eK.apply_symm_apply _).symm
      exact DFunLike.congr_fun hfg a
    have hcanonicalR :
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            X.FunctionField p = R.toValuationSubring := by
      calc
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
              X.FunctionField p =
            IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
              X.FunctionField (R.centerHeightOne hRB) := by
                congr 1
                apply IsDedekindDomain.HeightOneSpectrum.ext
                exact hzQ
        _ = R.toValuationSubring := R.localizationAtCenter_eq hRB
    have hcanonicalS :
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
            X.FunctionField p = S.toValuationSubring := by
      apply ValuationSubring.eq_of_le_of_ne_top _ _ S.toValuationSubring_ne_top
      rintro q ⟨a, s, hs, rfl⟩
      let aLoc : Localization.AtPrime (maximalIdealAt Z zQ) :=
        IsLocalization.mk' _ a ⟨s, hs⟩
      have hCa : locToK aLoc =
          algebraMap B X.FunctionField a *
            (algebraMap B X.FunctionField s)⁻¹ := by
        change IsLocalization.lift _
            (IsLocalization.mk'
              (Localization.AtPrime (maximalIdealAt Z zQ)) a ⟨s, hs⟩) = _
        apply (IsLocalization.lift_mk'_spec _ _ _ _).mpr
        change algebraMap B X.FunctionField a =
          algebraMap B X.FunctionField s *
            (algebraMap B X.FunctionField a *
              (algebraMap B X.FunctionField s)⁻¹)
        have hs0 : algebraMap B X.FunctionField s ≠ 0 :=
          IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
            (mem_nonZeroDivisors_of_ne_zero fun hszero ↦
              hs (hszero ▸ (maximalIdealAt Z zQ).zero_mem))
        rw [← mul_assoc, mul_comm (algebraMap B X.FunctionField s),
          mul_assoc, mul_inv_cancel₀ hs0, mul_one]
      have hqrange :
          algebraMap B X.FunctionField a *
              (algebraMap B X.FunctionField s)⁻¹ ∈
            (X.localRingRange Q.1).toSubring :=
        ⟨eLoc aLoc, (hloc aLoc).trans hCa⟩
      change algebraMap B X.FunctionField a *
          (algebraMap B X.FunctionField s)⁻¹ ∈
        (hX.valuationSubringAt hcurve Q.1 (hns Q.1)).toSubring
      rw [hX.valuationSubringAt_toSubring hcurve Q.1 (hns Q.1)]
      exact hqrange
    have hRS : R = S := by
      apply Subtype.ext
      exact hcanonicalR.symm.trans hcanonicalS
    exact ⟨Q.1, hRS.symm⟩
  have hbad :
      {R : FunctionFieldDVR k X.FunctionField |
        ¬ ∀ b : B, ι b ∈ R.toValuationSubring}.Finite :=
    by
      let _ : Algebra.EssFiniteType k X.FunctionField :=
        RationalMapFunctionField.essFiniteType_functionField hX
      exact finite_not_contains_range htrdeg ι
  have hcomplDVR : (Set.range fDVR)ᶜ.Finite := by
    refine hbad.subset ?_
    intro R hR
    change ¬ ∀ b : B, ι b ∈ R.toValuationSubring
    intro hgood
    exact hR (hgood_range R hgood)
  apply (ValuationSpace.isOpen_iff k X.FunctionField).mpr
  right
  have hpreimage :
      ((ValuationSpace.of k X.FunctionField).symm ⁻¹'
        (Set.range fDVR)ᶜ).Finite :=
    Set.Finite.preimage
      (ValuationSpace.of k X.FunctionField).symm.injective.injOn hcomplDVR
  have hrange :
      (ValuationSpace.of k X.FunctionField).symm ⁻¹' Set.range fDVR =
        Set.range (hX.localRingMap hcurve hns) := by
    ext R
    constructor
    · rintro ⟨P, hP⟩
      refine ⟨P, ?_⟩
      calc
        hX.localRingMap hcurve hns P =
            ValuationSpace.of k X.FunctionField (fDVR P) := rfl
        _ = ValuationSpace.of k X.FunctionField
            ((ValuationSpace.of k X.FunctionField).symm R) :=
          congrArg (ValuationSpace.of k X.FunctionField) hP
        _ = R := ValuationSpace.of_apply_symm_apply k X.FunctionField R
    · rintro ⟨P, hP⟩
      refine ⟨P, ?_⟩
      rw [← hP]
      exact ValuationSpace.of_symm_apply_apply k X.FunctionField _
  rw [← hrange]
  exact hpreimage

/-- The local-ring map, corestricted to its image, is a homeomorphism. -/
noncomputable def IsQuasiProjVariety.localRingMapHomeomorph
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    (Variety.ofQuasiProjective hY).carrier ≃ₜ
      Set.range
        ((Variety.hasAffineOpenBasis_ofQuasiProjective hY).localRingMap hcurve hns) := by
  let hX := Variety.hasAffineOpenBasis_ofQuasiProjective hY
  let f : (Variety.ofQuasiProjective hY).carrier →
      ValuationSpace k (Variety.ofQuasiProjective hY).FunctionField :=
    hX.localRingMap hcurve hns
  have hinj : Function.Injective f := hY.localRingMap_injective hcurve hns
  let e : (Variety.ofQuasiProjective hY).carrier ≃ Set.range f :=
    Equiv.ofInjective f hinj
  have hclosedY : ∀ C : Set (Variety.ofQuasiProjective hY).carrier,
      IsClosed C ↔ C = Set.univ ∨ C.Finite :=
    (hY.isCurve_infinite_and_isClosed_iff hcurve).2
  have hf : Continuous f := by
    rw [continuous_iff_isClosed]
    intro C hC
    apply (hclosedY (f ⁻¹' C)).mpr
    rcases (ValuationSpace.isClosed_iff k
      (Variety.ofQuasiProjective hY).FunctionField).mp hC with rfl | hCfinite
    · left
      exact Set.preimage_univ
    · right
      exact Set.Finite.preimage hinj.injOn hCfinite
  refine Homeomorph.mk e (hf.subtype_mk _) ?_
  rw [continuous_iff_isClosed]
  intro C hC
  rcases (hclosedY C).mp hC with rfl | hCfinite
  · simpa only [Set.preimage_univ] using
      (isClosed_univ : IsClosed (Set.univ : Set (Set.range f)))
  · exact (Set.Finite.preimage e.symm.injective.injOn hCfinite).isClosed

/-- **Hartshorne I.6, Proposition 6.7.** For a nonsingular quasi-projective
curve, the map sending a point to its local ring inside the common function
field is injective, has open image in the cofinite valuation space, and is a
homeomorphism onto that image. -/
theorem IsQuasiProjVariety.localRingMap_injective_open_homeomorph
    (hY : IsQuasiProjVariety Y)
    (hcurve : (Variety.ofQuasiProjective hY).IsCurve)
    (hns : (Variety.ofQuasiProjective hY).Nonsingular) :
    let f :=
      (Variety.hasAffineOpenBasis_ofQuasiProjective hY).localRingMap hcurve hns
    Function.Injective f ∧ IsOpen (Set.range f) ∧
      ∃ e : (Variety.ofQuasiProjective hY).carrier ≃ₜ Set.range f,
        ∀ P, (e P).1 = f P := by
  dsimp only
  refine ⟨hY.localRingMap_injective hcurve hns,
    hY.isOpen_range_localRingMap hcurve hns, ?_⟩
  refine ⟨hY.localRingMapHomeomorph hcurve hns, ?_⟩
  intro P
  rfl

end

end Hartshorne
