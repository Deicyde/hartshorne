/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.AffineGermCompare
import Hartshorne.Morphism.ChartIso
import Hartshorne.Morphism.LocalRingLocalization
import Hartshorne.Morphism.OpenSubvariety

/-!
# The local ring of a projective variety, on a chart

Hartshorne, *Algebraic Geometry*, I.3, the reduction step in Theorem 3.4(b)
(pp. 18-19).

For `Y` projective and `P ∈ Y ∩ Uᵢ`,

`𝒪_{P,Y} ≅ A(Yᵢ)_{𝔪}`,

where `Yᵢ` is the affine variety `φᵢ(Y ∩ Uᵢ)` and `𝔪` is the maximal ideal at
`φᵢ(P)`. This is what Hartshorne means by "the result follows from the affine
case", and it is a composite of four isomorphisms, none of which he states:

* `𝒪_{P,Y} ≅ 𝒪_{P,Y∩Uᵢ}`, since the local ring does not see beyond an open
  neighbourhood;
* `𝒪_{P,Y∩Uᵢ} ≅ 𝒪_{φᵢ(P),Yᵢ}`, since `φᵢ` is an isomorphism of varieties onto
  its image and an isomorphism induces one on local rings;
* the abstract germ ring on `Yᵢ` is the affine germ ring, the two having been
  built separately;
* `A(Yᵢ)_{𝔪} ≅ 𝒪_{φᵢ(P),Yᵢ}`, Theorem 3.2(c).

What is left of 3.4(b) after this is the graded step: rewriting `A(Yᵢ)_{𝔪}` as
`S(Y)_(𝔪_P)`. That is a statement about homogeneous localisation and has nothing
to do with germs.

## Main definitions

* `Hartshorne.projLocalRingEquiv`

## Main results

* `Hartshorne.ringKrullDim_projLocalRing`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace

variable {k : Type*} [Field k] [IsAlgClosed k] {σ : Type*} [Finite σ] [DecidableEq σ]
  [Nonempty σ] {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y) (i : σ)
  (P : (Variety.ofQuasiProjective hY.isQuasiProjVariety).carrier)
  (hP : P.1 ∈ standardChart i)

omit [IsAlgClosed k] [Finite σ] [DecidableEq σ] [Nonempty σ] in
include hP in
/-- The chart meets `Y`, since `P` is in both. -/
theorem nonempty_inter_standardChart : (Y ∩ standardChart i).Nonempty :=
  ⟨P.1, P.2, hP⟩

/-- `P`, as a point of the chart piece `Y ∩ Uᵢ`. -/
abbrev chartPoint : (chartVariety k i hY.isQuasiProjVariety
    (nonempty_inter_standardChart hY i P hP)).carrier :=
  ⟨P.1, P.2, hP⟩

/-- **The local ring of a projective variety is a localisation of the
coordinate ring of a chart.**

Four isomorphisms in a row: restrict to the chart piece, transport along the
chart isomorphism, identify the abstract germ ring with the affine one, and
apply Theorem 3.2(c). -/
noncomputable def projLocalRingEquiv :
    Variety.LocalRingAt (Variety.ofQuasiProjective hY.isQuasiProjVariety) P
      ≃+* Localization.AtPrime (maximalIdealAt _
        (affinePoint (isQuasiAffineVariety_chartMap_image i hY.isQuasiProjVariety
            (nonempty_inter_standardChart hY i P hP))
          (chartFun k i hY.isQuasiProjVariety (nonempty_inter_standardChart hY i P hP)
            (chartPoint hY i P hP)))) :=
  let hne := nonempty_inter_standardChart hY i P hP
  let hYq := hY.isQuasiProjVariety
  let hYi := isQuasiProjVariety_inter_standardChart k i hYq hne
  let hW := isQuasiAffineVariety_chartMap_image i hYq hne
  let Q := chartPoint hY i P hP
  let e₁ : Variety.LocalRingAt (Variety.ofQuasiProjective hYq) P
      ≃+* Variety.LocalRingAt (Variety.ofQuasiProjective hYi) Q :=
    RingEquiv.ofBijective ((inclHom hYq hYi Set.inter_subset_left).localRingHom Q)
      (bijective_localRingHom_inclHom hYq hYi Set.inter_subset_left
        (isOpen_inter_standardChart_in k i) Q)
  let e₂ : Variety.LocalRingAt (chartTarget k i hYq hne)
        (chartFun k i hYq hne Q)
      ≃+* Variety.LocalRingAt (Variety.ofQuasiProjective hYi) Q :=
    RingEquiv.ofBijective ((chartHom k i hYq hne).localRingHom Q)
      (VarietyHom.bijective_localRingHom_of_isIso (isIso_chartHom k i hYq hne) Q)
  let e₃ := localRingEquivAffine hW (chartFun k i hYq hne Q)
  let e₄ := localizationEquivLocalRing hW.isIrreducible
    (affinePoint hW (chartFun k i hYq hne Q))
  ((e₁.trans e₂.symm).trans e₃).trans e₄.symm


/-- The maximal ideal of the chart's coordinate ring at `φᵢ(P)`. -/
noncomputable abbrev chartMaximalIdeal : Ideal (coordinateRing
    (chartMap i '' (Y ∩ standardChart i))) :=
  maximalIdealAt _
    (affinePoint (isQuasiAffineVariety_chartMap_image i hY.isQuasiProjVariety
        (nonempty_inter_standardChart hY i P hP))
      (chartFun k i hY.isQuasiProjVariety (nonempty_inter_standardChart hY i P hP)
        (chartPoint hY i P hP)))

/-- **`dim 𝒪_P = height 𝔪` for a projective variety.**

Immediate from the reduction to the affine case, since Mathlib computes the
dimension of a localisation at a prime as that prime's height. Turning the
right-hand side into `dim Y` is the clause of Theorem 1.8A that is still
missing, exactly as in the affine case. -/
theorem ringKrullDim_projLocalRing :
    ringKrullDim (Variety.LocalRingAt (Variety.ofQuasiProjective hY.isQuasiProjVariety) P)
      = (chartMaximalIdeal hY i P hP).height := by
  rw [ringKrullDim_eq_of_ringEquiv (projLocalRingEquiv hY i P hP)]
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (chartMaximalIdeal hY i P hP)
    (Localization.AtPrime (chartMaximalIdeal hY i P hP))

end Hartshorne
