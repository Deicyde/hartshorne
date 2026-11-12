/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BlowupUniversalProperty
import Hartshorne.Scheme.ProjSurjectionClosedImmersion
import Hartshorne.Scheme.ProjClosedSubschemeTruncation
import Hartshorne.Cohomology.SerreAffinenessCriterion

/-!
# Functoriality of blowing up

Hartshorne, *Algebraic Geometry*, II, Corollary 7.15 (p. 165).

Let `f : Y ⟶ X` be a morphism of Noetherian schemes, `I` a coherent sheaf of ideals on `X`,
`π : X̃ ⟶ X` the blowing-up of `I` and `π' : Ỹ ⟶ Y` the blowing-up of the inverse image ideal
sheaf `J = f⁻¹I · 𝒪_Y`. Then there is a unique morphism `f̃ : Ỹ ⟶ X̃` with `π ∘ f̃ = f ∘ π'`, and
if `f` is a closed immersion, so is `f̃`.

## Proof

*Existence and uniqueness.* The inverse image of `I` under `f ∘ π'` is
`π'⁻¹(f⁻¹I · 𝒪_Y) · 𝒪_{Ỹ}`, the exceptional ideal of `Ỹ`, which is invertible (Proposition
7.13(a)); the universal property of `X̃` (Proposition 7.14) gives `f̃`.

*Closed immersion.* Being a closed immersion is local on the target, and `X̃` is covered by the
open pieces `Proj S(U)`, `S = ⨁_d Iᵈ`, over the affine opens `U ⊆ X`. Since `f` is a closed
immersion, `V = f⁻¹U` is affine and `A = Γ(U, 𝒪_X) → B = Γ(V, 𝒪_Y)` is surjective, and
`Γ(V, J) = Γ(U, I) B`. Hence the map of Rees algebras `A[Γ(U, I) t] → B[Γ(V, J) t]` is a surjection
of graded rings (the surjection of the Rees algebra of `I`, restricted to `U`, onto the Rees algebra
of `J` on `V`), so it induces a closed immersion `Proj T(V) ⟶ Proj S(U)`, `T = ⨁_d Jᵈ`
(Hartshorne II, Exercise 3.12(a)). By the uniqueness in Proposition 7.14, this closed immersion is
the restriction of `f̃` over `Proj S(U)`: the square formed by `Proj T(V) ⟶ Ỹ`, `f̃`, and
`Proj S(U) ⟶ X̃` is a pullback, by pasting with the pullback squares `Proj T(V) = V ×_Y Ỹ`,
`V = U ×_X Y` and `Proj S(U) = U ×_X X̃`.

## Main results

* `Hartshorne.QuasicoherentIdealSubsheaf.isCoherent_inverseImage`: on a Noetherian `Y`, the
  inverse image ideal sheaf `f⁻¹I · 𝒪_Y` is coherent.
* `Hartshorne.QuasicoherentIdealSubsheaf.existsUnique_blowup_map`: Corollary 7.15, existence and
  uniqueness of `f̃`.
* `Hartshorne.QuasicoherentIdealSubsheaf.isClosedImmersion_of_blowup_map`: Corollary 7.15, if `f`
  is a closed immersion then so is `f̃`.
* `Hartshorne.reesMap_surjective_of_surjective`: a surjection `φ : R → S` induces a surjection of
  Rees algebras `R[It] → S[(IS)t]`.
-/

noncomputable section

universe u

open CategoryTheory Limits Polynomial AlgebraicGeometry

namespace Hartshorne

/-- A surjective ring map `φ : R → S` induces a surjection of Rees algebras `R[It] → S[Jt]` when
`J = I S`. -/
theorem reesMap_surjective_of_surjective {R S : Type*} [CommRing R] [CommRing S] {I : Ideal R}
    (φ : R →+* S) (hφ : Function.Surjective φ) {J : Ideal S} (hJ : I.map φ = J) :
    Function.Surjective (reesMap φ hJ.le) := by
  rintro ⟨q, hq⟩
  have hc : ∀ n, ∃ a ∈ I ^ n, φ a = q.coeff n := fun n => by
    have : q.coeff n ∈ (I ^ n).map φ := by
      rw [Ideal.map_pow, hJ]
      exact (mem_reesAlgebra_iff J q).1 hq n
    exact (Ideal.mem_map_iff_of_surjective φ hφ).1 this
  choose a ha hφa using hc
  refine ⟨⟨∑ n ∈ q.support, monomial n (a n),
    Subalgebra.sum_mem _ fun n _ => reesAlgebra.monomial_mem.2 (ha n)⟩, Subtype.ext ?_⟩
  rw [coe_reesMap]
  simp only [Polynomial.map_sum, Polynomial.map_monomial, hφa]
  exact q.as_sum_support.symm

namespace QuasicoherentIdealSubsheaf

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : Y ⟶ X)
  (I : QuasicoherentIdealSubsheaf X) (hI : IsCoherent I.toModules)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- On a Noetherian scheme `Y`, the inverse image ideal sheaf `f⁻¹I · 𝒪_Y` is coherent. -/
theorem isCoherent_inverseImage : IsCoherent (I.inverseImage f).toModules :=
  SerreAffineness.isCoherent_toModules _

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The exceptional ideal of the blowing-up `Ỹ ⟶ Y` of `f⁻¹I · 𝒪_Y` is the inverse image of `I`
under `Ỹ ⟶ Y ⟶ X`. -/
private theorem exceptionalIdeal_inverseImage :
    (I.inverseImage f).exceptionalIdeal (I.isCoherent_inverseImage f) =
      inverseImageIdeal ((I.inverseImage f).blowupProjection (I.isCoherent_inverseImage f) ≫ f)
        (quasicoherentIdealSubsheafEquiv I) := by
  change inverseImageIdeal _ (quasicoherentIdealSubsheafEquiv (quasicoherentIdealSubsheafEquiv.symm
    (inverseImageIdeal f (quasicoherentIdealSubsheafEquiv I)))) = _
  rw [Equiv.apply_symm_apply, inverseImageIdeal, inverseImageIdeal, inverseImageIdeal,
    Scheme.IdealSheafData.comap_comp]

/-- **Hartshorne II, Corollary 7.15 (functoriality of blowing up).** Let `f : Y ⟶ X` be a
morphism of Noetherian schemes, `I` a coherent sheaf of ideals on `X`, `π : X̃ ⟶ X` the blowing-up
of `I` and `π' : Ỹ ⟶ Y` the blowing-up of the inverse image ideal sheaf `f⁻¹I · 𝒪_Y`. Then there
is a unique morphism `f̃ : Ỹ ⟶ X̃` with `π ∘ f̃ = f ∘ π'`. -/
theorem existsUnique_blowup_map :
    ∃! g : (I.inverseImage f).blowup (I.isCoherent_inverseImage f) ⟶ I.blowup hI,
      g ≫ I.blowupProjection hI =
        (I.inverseImage f).blowupProjection (I.isCoherent_inverseImage f) ≫ f := by
  refine I.existsUnique_blowup_lift hI _ ?_
  rw [← exceptionalIdeal_inverseImage]
  exact (I.inverseImage f).isInvertible_exceptionalIdealSheaf _

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Over an affine open `U ⊆ X`, with `V = f⁻¹U` for a closed immersion `f`, a morphism
`g : Ỹ ⟶ X̃` over `f` restricts over `Proj S(U) ⊆ X̃` to the closed immersion
`Proj T(V) ⟶ Proj S(U)` induced by the surjection of Rees algebras. -/
private theorem isClosedImmersion_pullback_snd_projι [IsClosedImmersion f]
    (g : (I.inverseImage f).reesAlgebra.relProj ⟶ I.reesAlgebra.relProj)
    (hg : g ≫ I.reesAlgebra.relProjToBase = (I.inverseImage f).reesAlgebra.relProjToBase ≫ f)
    (U : X.AffineZariskiSite) :
    IsClosedImmersion (pullback.snd g (I.reesAlgebra.projι U)) := by
  have hJ := I.isCoherent_inverseImage f
  have hU : IsAffineOpen (f ⁻¹ᵁ U.1) := U.2.preimage f
  let V : Y.AffineZariskiSite := ⟨f ⁻¹ᵁ U.1, hU⟩
  let φ : Γ(X, U.1) ⟶ Γ(Y, V.1) := f.appLE U.1 V.1 le_rfl
  have hφ : Function.Surjective φ := by
    change Function.Surjective (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl)
    rw [Scheme.Hom.appLE_eq_app]
    exact f.app_surjective U.1 U.2
  have hJV : (ReesAlgebraSheaf.idealOn (quasicoherentIdealSubsheafEquiv I) U).map φ.hom =
      ReesAlgebraSheaf.idealOn (quasicoherentIdealSubsheafEquiv (I.inverseImage f)) V := by
    change _ = (quasicoherentIdealSubsheafEquiv (quasicoherentIdealSubsheafEquiv.symm
      (inverseImageIdeal f (quasicoherentIdealSubsheafEquiv I)))).ideal ⟨V.1, V.2⟩
    rw [Equiv.apply_symm_apply]
    exact (inverseImageIdeal_ideal f _ ⟨U.1, U.2⟩ ⟨V.1, V.2⟩ le_rfl).symm
  let ψ : I.reesAlgebra.grading U →+*ᵍ (I.inverseImage f).reesAlgebra.grading V :=
    { reesMap φ.hom hJV.le with
      map_mem := fun hx => reesMap_mem_reesGrading φ.hom hJV.le hx }
  have hψ : Function.Surjective ψ := reesMap_surjective_of_surjective φ.hom hφ hJV
  let h : Proj ((I.inverseImage f).reesAlgebra.grading V) ⟶ Proj (I.reesAlgebra.grading U) :=
    Proj.map ψ (ProjTruncation.irrelevant_le_map_of_surjective hψ)
  have hci : IsClosedImmersion h := by
    change IsClosedImmersion (Proj.map ψ (ProjTruncation.irrelevant_le_map_of_surjective hψ))
    rw [← ProjTruncation.topIso_inv_homOfLE_projPartialMap hψ]
    exact isClosedImmersion_projPartialMap_comp_top_of_surjective hψ
  have hzero : I.reesAlgebra.toZero U ≫ CommRingCat.ofHom (GradedRingHom.gradedZeroRingHom ψ) =
      φ ≫ (I.inverseImage f).reesAlgebra.toZero V := by
    ext r
    exact Subtype.ext (Polynomial.map_C (a := r) φ.hom)
  have hcomm : h ≫ I.reesAlgebra.projToOpen U =
      (I.inverseImage f).reesAlgebra.projToOpen V ≫ f ∣_ U.1 := by
    rw [← cancel_mono U.1.ι, Category.assoc, I.reesAlgebra.projToOpen_ι, Category.assoc,
      morphismRestrict_ι, ← Category.assoc ((I.inverseImage f).reesAlgebra.projToOpen V),
      (I.inverseImage f).reesAlgebra.projToOpen_ι]
    change Proj.map ψ _ ≫ _ = _
    rw [← Category.assoc (Proj.map ψ _), projMap_toSpecZero, Category.assoc, Category.assoc,
      Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f U.2 hU le_rfl,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hzero]
  have hZ : (h ≫ I.reesAlgebra.projι U) ≫ I.reesAlgebra.relProjToBase =
      (I.inverseImage f).reesAlgebra.projToOpen V ≫ V.1.ι ≫ f := by
    rw [Category.assoc, I.reesAlgebra.projι_relProjToBase, ← Category.assoc, hcomm,
      Category.assoc, morphismRestrict_ι]
  have hZ' : ((I.inverseImage f).reesAlgebra.projι V ≫ g) ≫ I.reesAlgebra.relProjToBase =
      (I.inverseImage f).reesAlgebra.projToOpen V ≫ V.1.ι ≫ f := by
    rw [Category.assoc, hg, ← Category.assoc, (I.inverseImage f).reesAlgebra.projι_relProjToBase,
      Category.assoc]
  have hloc : (inverseImageIdeal ((I.inverseImage f).reesAlgebra.projToOpen V ≫ V.1.ι ≫ f)
      (quasicoherentIdealSubsheafEquiv I)).IsLocallyPrincipalNonZeroDivisor := by
    rw [← Category.assoc, ← (I.inverseImage f).reesAlgebra.projι_relProjToBase, Category.assoc,
      inverseImageIdeal, Scheme.IdealSheafData.comap_comp]
    have hexc : (((quasicoherentIdealSubsheafEquiv I).comap
        ((I.inverseImage f).reesAlgebra.relProjToBase ≫ f))).IsLocallyPrincipalNonZeroDivisor := by
      have := (I.inverseImage f).isLocallyPrincipalNonZeroDivisor_exceptionalIdeal hJ
      rwa [exceptionalIdeal_inverseImage] at this
    exact isLocallyPrincipalNonZeroDivisor_comap_of_isOpenImmersion hexc
      ((I.inverseImage f).reesAlgebra.projι V)
  have hsq : h ≫ I.reesAlgebra.projι U = (I.inverseImage f).reesAlgebra.projι V ≫ g :=
    ReesAlgebraSheaf.hom_ext_of_isLocallyPrincipalNonZeroDivisor _ hloc hZ hZ'
  have hpb : IsPullback h ((I.inverseImage f).reesAlgebra.projι V) (I.reesAlgebra.projι U) g := by
    refine IsPullback.of_right ?_ hsq (I.reesAlgebra.isPullback_projι U)
    rw [hcomm, hg]
    exact ((I.inverseImage f).reesAlgebra.isPullback_projι V).paste_horiz
      (isPullback_morphismRestrict f U.1)
  rw [← hpb.flip.isoPullback_inv_snd]
  infer_instance

/-- **Hartshorne II, Corollary 7.15 (closed immersions).** Let `f : Y ⟶ X` be a
closed immersion of Noetherian schemes, `I` a coherent sheaf of ideals on `X`, `π : X̃ ⟶ X` the
blowing-up of `I` and `π' : Ỹ ⟶ Y` the blowing-up of the inverse image ideal sheaf `f⁻¹I · 𝒪_Y`.
Then the morphism `f̃ : Ỹ ⟶ X̃` with `π ∘ f̃ = f ∘ π'` (unique by `existsUnique_blowup_map`) is a
closed immersion. -/
theorem isClosedImmersion_of_blowup_map [IsClosedImmersion f]
    (g : (I.inverseImage f).blowup (I.isCoherent_inverseImage f) ⟶ I.blowup hI)
    (hg : g ≫ I.blowupProjection hI =
      (I.inverseImage f).blowupProjection (I.isCoherent_inverseImage f) ≫ f) :
    IsClosedImmersion g :=
  IsZariskiLocalAtTarget.of_openCover I.reesAlgebra.relativeGluingData.cover fun U =>
    isClosedImmersion_pullback_snd_projι f I g hg U

end QuasicoherentIdealSubsheaf

end Hartshorne
