/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.LocalCompleteIntersectionCohenMacaulay
import Hartshorne.Scheme.SerreNormalityCriterion
import Hartshorne.Scheme.Normal

/-!
# Normality of a local complete intersection

Hartshorne, *Algebraic Geometry*, II, Proposition 8.23(b) (p. 186).

Let `X` be a regular scheme, for instance a nonsingular variety, and `i : Y ⟶ X` a closed
immersion which is a local complete intersection in `X`. Then `Y` is normal if and only if it is
regular in codimension one in the sense of `(R1)` of Theorem 8.22A: every local ring of `Y` of
dimension at most one is regular (`Hartshorne.isNormal_iff_of_isLocalCompleteIntersectionIn`).

The condition includes the local rings of dimension zero. Without them the equivalence fails:
`Spec k[x]/(x²) ⊆ 𝔸¹` is a local complete intersection with no local ring of dimension one, and it
is not normal.

## Proof

`Y` is Cohen–Macaulay by Proposition 8.23(a). On a Cohen–Macaulay scheme normality is `(R1)`
(`Hartshorne.isNormal_iff_of_isCohenMacaulay`). A normal Noetherian local ring of dimension at most
one is regular. Conversely, on an affine open `Spec R` the localization `R_𝔮` is the local ring of
`Y` at the point `𝔮`. It is Cohen–Macaulay, so its depth is its dimension `ht 𝔮`, giving `(S2)`.
The hypothesis gives `(R1)`, and Serre's criterion (Theorem 8.22A) makes `R` normal.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace Hartshorne

/-- On a Cohen–Macaulay scheme `Y`, normality is equivalent to `(R1)`: every local ring of `Y` of
dimension at most one is regular. -/
theorem isNormal_iff_of_isCohenMacaulay {Y : Scheme.{u}} (hY : Y.IsCohenMacaulay) :
    IsNormal Y ↔ ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
      IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨hLN, hCM⟩ := hY
  refine ⟨fun _ y hy => SerreNormality.isRegularLocalRing_of_isIntegrallyClosed hy,
    fun hR1 => ?_⟩
  have key : ∀ x : Y,
      IsDomain (Y.presheaf.stalk x) ∧ IsIntegrallyClosed (Y.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have hiso : ∀ (Q : Ideal Γ(Y, U)) [Q.IsPrime],
        ∃ z : Y, Nonempty (Localization.AtPrime Q ≃+* Y.presheaf.stalk z) := by
      intro Q _
      obtain ⟨z, hz⟩ : ∃ z : U, hU.primeIdealOf z = ⟨Q, ‹_›⟩ :=
        ⟨⟨hU.fromSpec ⟨Q, ‹_›⟩, hU.range_fromSpec.subset ⟨_, rfl⟩⟩,
          hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)⟩
      let := Y.presheaf.algebra_section_stalk z
      have := hU.isLocalization_stalk z
      have hQ : Q = (hU.primeIdealOf z).asIdeal := by rw [hz]
      subst hQ
      exact ⟨z.1, ⟨(IsLocalization.algEquiv (hU.primeIdealOf z).asIdeal.primeCompl
        (Y.presheaf.stalk z.1)
          (Localization.AtPrime (hU.primeIdealOf z).asIdeal)).symm.toRingEquiv⟩⟩
    have hR : ∀ (Q : Ideal Γ(Y, U)) [Q.IsPrime], Q.height ≤ 1 →
        IsRegularLocalRing (Localization.AtPrime Q) := by
      intro Q _ hQ
      obtain ⟨z, ⟨e⟩⟩ := hiso Q
      have hdim : ringKrullDim (Y.presheaf.stalk z) ≤ 1 := by
        rw [← ringKrullDim_eq_of_ringEquiv e,
          IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
        exact_mod_cast hQ
      have := hR1 z hdim
      exact IsRegularLocalRing.of_ringEquiv e.symm
    have hS : ∀ (Q : Ideal Γ(Y, U)) [Q.IsPrime], 2 ≤ Q.height →
        2 ≤ Module.depth (Localization.AtPrime Q) (Localization.AtPrime Q) := by
      intro Q _ hQ
      obtain ⟨z, ⟨e⟩⟩ := hiso Q
      have := hCM z
      have hcm := LCICohenMacaulay.isCohenMacaulayLocalRing_of_ringEquiv e.symm
      have h := hcm.depth_eq_ringKrullDim
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)] at h
      rw [WithBot.coe_inj.mp h]
      exact hQ
    have hN := (SerreNormality.normal_iff_R1_and_S2 Γ(Y, U)).mpr ⟨hR, hS⟩
    let P := hU.primeIdealOf ⟨x, hxU⟩
    let := Y.presheaf.algebra_section_stalk ⟨x, hxU⟩
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    obtain ⟨hd, hic⟩ := hN P.asIdeal
    let e := IsLocalization.algEquiv P.asIdeal.primeCompl (Y.presheaf.stalk x)
      (Localization.AtPrime P.asIdeal)
    exact ⟨e.toRingEquiv.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm.toRingEquiv⟩
  exact ⟨fun x => (key x).1, fun x => (key x).2⟩

/-- **Normality of a local complete intersection** (Hartshorne II, Proposition 8.23(b)). Let `X`
be a regular scheme (for example a nonsingular variety) and `i : Y ⟶ X` a closed immersion which
is a local complete intersection in `X`. Then `Y` is normal if and only if it is regular in
codimension one: every local ring of `Y` of dimension at most one is regular. -/
theorem isNormal_iff_of_isLocalCompleteIntersectionIn {X Y : Scheme.{u}} (hX : X.IsRegular)
    (i : Y ⟶ X) [IsClosedImmersion i] (h : IsLocalCompleteIntersectionIn i) :
    IsNormal Y ↔ ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 1 →
      IsRegularLocalRing (Y.presheaf.stalk y) :=
  isNormal_iff_of_isCohenMacaulay (isCohenMacaulay_of_isLocalCompleteIntersectionIn hX i h)

end Hartshorne
