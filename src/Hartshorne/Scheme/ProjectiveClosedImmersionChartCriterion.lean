/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoordinateNonvanishingOpen

/-!
# The projective closed-immersion chart criterion

Hartshorne, *Algebraic Geometry*, II, Proposition 7.2 (pp. 151–152).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

section Charts

variable (n : ℕ) (Y : Scheme.{u})

/-- The standard opens `D₊(xᵢ)` cover `ℙⁿ_Y`. -/
theorem iSup_projectiveSpaceChart : ⨆ i, projectiveSpaceChart n Y i = ⊤ := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨k, hk⟩ := exists_mem_chartPreimage (𝟙 (projectiveSpaceOverScheme n Y)) x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hk⟩

/-- Over an affine base, each standard open `D₊(xᵢ)` of `ℙⁿ_Y` is affine. -/
theorem isAffineOpen_projectiveSpaceChart [IsAffine Y] (i : Fin (n + 1)) :
    IsAffineOpen (projectiveSpaceChart n Y i) := by
  have : IsAffineHom (schemeToSpecZ Y) := isAffineHom_of_isAffine _
  have : IsAffineHom (toProjInt n Y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback _ _).flip this
  exact (Proj.isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule_one _ i)
    Nat.one_pos).preimage _

end Charts

section Restrict

/-- For an affine open `U` of the target with preimage `V`, the restriction `f⁻¹(U) ⟶ U` is a
closed immersion iff `V` is affine and `Γ(U, 𝒪) → Γ(V, 𝒪)` is surjective (Hartshorne II,
Exercise 3.11(b) for the forward direction and Exercise 2.18(c) for the converse). -/
theorem isClosedImmersion_morphismRestrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsAffineOpen U) {V : X.Opens} (h : f ⁻¹ᵁ U = V) :
    IsClosedImmersion (f ∣_ U) ↔ IsAffineOpen V ∧ Function.Surjective (f.appLE U V h.ge) := by
  subst h
  have : IsAffine U := hU
  have hsurj : Function.Surjective (f ∣_ U).appTop ↔
      Function.Surjective (f.appLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.appTop, morphismRestrict_app']
    exact Scheme.Hom.appLE_congr _ _ U.ι_image_top (f ⁻¹ᵁ U).ι_image_top
      (fun g => Function.Surjective g)
  rw [← hsurj]
  refine ⟨fun _ => IsClosedImmersion.isAffine_surjective_of_isAffine (f ∣_ U), fun ⟨hV, h⟩ => ?_⟩
  have : IsAffine (f ⁻¹ᵁ U) := hV
  rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (arrowIsoSpecΓOfIsAffine (f ∣_ U))]
  exact IsClosedImmersion.spec_of_surjective _ h

end Restrict

section Criterion

variable {n : ℕ} {X Y : Scheme.{u}} {L : X.Modules} (hL : L.IsInvertible)
  (s : Fin (n + 1) → Γ(L, ⊤)) (φ : X ⟶ projectiveSpaceOverScheme n Y)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n Y i)) = s i)

include he in
/-- **Hartshorne II, Proposition 7.2.** Let `Y` be affine (Hartshorne takes `Y = Spec A`), and let
`φ : X ⟶ ℙⁿ_Y` be the morphism defined by an invertible sheaf `L` and sections `s₀, …, sₙ`, i.e.
with an isomorphism `φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ` to `sᵢ`. Then `φ` is a closed immersion
iff for every `i`, the open `X_{sᵢ} = φ⁻¹(D₊(xᵢ))` is affine and the ring map
`Γ(D₊(xᵢ), 𝒪) → Γ(X_{sᵢ}, 𝒪_X)` induced by `φ` (which sends `xⱼ/xᵢ` to `sⱼ/sᵢ`) is surjective. -/
theorem isClosedImmersion_iff_isAffineOpen_and_surjective [IsAffine Y] :
    IsClosedImmersion φ ↔ ∀ i, IsAffineOpen (nonvanishingLocusOpens hL (s i)) ∧
      Function.Surjective (φ.appLE (projectiveSpaceChart n Y i) (nonvanishingLocusOpens hL (s i))
        (preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i).ge) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _
    (iSup_projectiveSpaceChart n Y)]
  exact forall_congr' fun i => isClosedImmersion_morphismRestrict_iff φ
    (isAffineOpen_projectiveSpaceChart n Y i)
    (preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i)

end Criterion

end Hartshorne
