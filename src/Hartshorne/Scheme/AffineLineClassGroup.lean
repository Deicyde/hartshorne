/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.WeilClassGroup
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# The class group of the relative affine line

Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.6 (pp. 134--135).

The relative affine line over a scheme `X` is `𝔸¹_X = X ×_ℤ Spec ℤ[t]`, written
`𝔸(PUnit; X)`. If `X` satisfies Hartshorne's condition `(*)` then so does `𝔸¹_X`:
it is Noetherian and separated because the projection is affine of finite type, integral
because the projection is geometrically integral, and regular in codimension one because,
for a Noetherian domain `A` whose height-one localizations are regular, every height-one
localization of `A[t]` is regular. The last fact reduces, after localizing at the
contraction `q` of a height-one prime of `A[t]` (which has height at most one by going
down along the flat extension `A → A[t]`), to Mathlib's theorem that a polynomial ring over
a regular local ring has regular localizations at primes lying over the maximal ideal.
-/

noncomputable section

open Polynomial IsLocalRing Ideal

namespace Hartshorne

/-- A commutative ring is regular in codimension one when its localization at every prime of
height one is a regular local ring. -/
def RingIsRegularInCodimensionOne (R : Type*) [CommRing R] : Prop :=
  ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → IsRegularLocalRing (Localization.AtPrime p)

/-- In a Noetherian domain that is regular in codimension one, the localization at any prime of
height at most one is regular. -/
theorem isRegularLocalRing_localization_of_height_le_one {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (hA : RingIsRegularInCodimensionOne A)
    (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  rcases (show q.height = 0 ∨ q.height = 1 by
    rcases eq_or_lt_of_le hq with h | h
    · exact Or.inr h
    · exact Or.inl ((Order.lt_one_iff).mp h)) with h0 | h1
  · have hdim : ringKrullDim (Localization.AtPrime q) = 0 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q), h0]
      rfl
    have : Ring.KrullDimLE 0 (Localization.AtPrime q) := Ring.krullDimLE_iff.mpr hdim.le
    have hfield : IsField (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isDomain
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [(isField_iff_maximalIdeal_eq.mp hfield), Submodule.spanFinrank_bot, hdim]
    rfl
  · exact hA q h1

/-- **Polynomial rings preserve regularity in codimension one.** If `A` is a Noetherian domain
whose localizations at height-one primes are regular, then so is `A[X]`. -/
theorem Polynomial.ringIsRegularInCodimensionOne {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (hA : RingIsRegularInCodimensionOne A) :
    RingIsRegularInCodimensionOne A[X] := by
  intro p hp hp1
  let q := p.comap C
  have hqle : q.height ≤ 1 := by
    have : p.LiesOver q := ⟨rfl⟩
    rw [← hp1, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q p]
    exact le_self_add
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra A[X] S := Polynomial.algebra A (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap A[X] S)
  have disj : Disjoint (pc : Set A[X]) (p : Set A[X]) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have := isRegularLocalRing_localization_of_height_le_one hA q hqle
  have eq : comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq A (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq A A[X] (Localization.AtPrime q)[X], ← comap_comap,
      ← Ideal.under_def A[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  have := Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal _ pS eq
  exact IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime pS)
    (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

/-- Regularity in codimension one is invariant under ring isomorphisms. -/
theorem RingIsRegularInCodimensionOne.of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hR : RingIsRegularInCodimensionOne R) : RingIsRegularInCodimensionOne S := by
  intro P hP hP1
  let Q : Ideal R := P.comap e
  have hQ1 : Q.height = 1 := by
    rw [← hP1]
    exact e.height_comap P
  have := hR Q hQ1
  have hmap : Q.primeCompl.map (e : R →* S) = P.primeCompl := by
    ext s
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hs
      refine ⟨e.symm s, ?_, by simp⟩
      change e.symm s ∉ P.comap e
      rw [Ideal.mem_comap]
      simpa using hs
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime Q) (Localization.AtPrime P) e hmap)

end Hartshorne

namespace AlgebraicGeometry

open CategoryTheory Limits

universe u

/-- Regularity in codimension one of an affine scheme is the corresponding property of its
ring. -/
theorem isRegularInCodimensionOne_Spec_iff (R : CommRingCat.{u}) :
    (Spec R).IsRegularInCodimensionOne ↔ Hartshorne.RingIsRegularInCodimensionOne R := by
  constructor
  · intro h p hp hp1
    let x : Spec R := ⟨p, hp⟩
    have hx : Order.coheight x = 1 := by
      rw [← idealHeight_eq_coheight]
      exact hp1
    have := h x hx
    let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) p :=
      StructureSheaf.IsLocalization.to_stalk R x
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
      ((Spec R).presheaf.stalk x) (Localization.AtPrime p)).toRingEquiv
  · intro h x hx
    have : x.asIdeal.IsPrime := x.isPrime
    have hx' : x.asIdeal.height = 1 := by
      rw [idealHeight_eq_coheight]
      exact hx
    have := h x.asIdeal hx'
    let _ : Algebra R ((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra R x
    have : IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk R x
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv x.asIdeal.primeCompl
      (Localization.AtPrime x.asIdeal) ((Spec R).presheaf.stalk x)).toRingEquiv

/-- Regularity in codimension one restricts along open immersions. -/
theorem Scheme.IsRegularInCodimensionOne.of_isOpenImmersion {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (hZ : Z.IsRegularInCodimensionOne) : Y.IsRegularInCodimensionOne := by
  intro y hy
  have hy' : Order.coheight (f.base y) = 1 := by
    rw [coheight_eq_of_isOpenImmersion]
    exact hy
  have := hZ _ hy'
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv

/-- Regularity in codimension one can be checked on a family of open immersions covering the
scheme. -/
theorem Scheme.IsRegularInCodimensionOne.of_forall_exists_isOpenImmersion {Z : Scheme.{u}}
    (h : ∀ z : Z, ∃ (Y : Scheme.{u}) (f : Y ⟶ Z), IsOpenImmersion f ∧
      Y.IsRegularInCodimensionOne ∧ z ∈ Set.range f.base) :
    Z.IsRegularInCodimensionOne := by
  intro z hz
  obtain ⟨Y, f, hf, hY, y, rfl⟩ := h z
  have hy : Order.coheight y = 1 := by
    rw [← coheight_eq_of_isOpenImmersion f]
    exact hz
  have := hY y hy
  exact IsRegularLocalRing.of_ringEquiv (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv.symm

/-- The relative affine line over a locally Noetherian integral scheme that is regular in
codimension one is again regular in codimension one. -/
theorem Scheme.IsRegularInCodimensionOne.affineLine {X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsIntegral X] (hX : X.IsRegularInCodimensionOne) :
    𝔸(PUnit.{u + 1}; X).IsRegularInCodimensionOne := by
  apply of_forall_exists_isOpenImmersion
  intro z
  obtain ⟨R, f, hf, ⟨u, hu⟩, -⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (show (𝔸(PUnit.{u + 1}; X) ↘ X).base z ∈ (⊤ : X.Opens) from trivial)
  have hRspec : (Spec R).IsRegularInCodimensionOne := hX.of_isOpenImmersion f
  have hR : Hartshorne.RingIsRegularInCodimensionOne R :=
    (isRegularInCodimensionOne_Spec_iff R).mp hRspec
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp this
  have : Nonempty (Spec R) := ⟨u⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion f
  have : IsDomain R := (affine_isIntegral_iff R).mp this
  have hpoly : Hartshorne.RingIsRegularInCodimensionOne (MvPolynomial PUnit.{u + 1} R) :=
    (Hartshorne.Polynomial.ringIsRegularInCodimensionOne hR).of_ringEquiv
      (MvPolynomial.uniqueAlgEquiv R PUnit.{u + 1}).toRingEquiv.symm
  have hA : (𝔸(PUnit.{u + 1}; Spec R)).IsRegularInCodimensionOne :=
    ((isRegularInCodimensionOne_Spec_iff (.of (MvPolynomial PUnit.{u + 1} R))).mpr hpoly).of_isOpenImmersion
      (AffineSpace.SpecIso PUnit.{u + 1} R).hom
  have hpb := AffineSpace.isPullback_map (n := PUnit.{u + 1}) f
  have : IsOpenImmersion (AffineSpace.map PUnit.{u + 1} f) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip hf
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback hpb z u hu.symm
  exact ⟨_, AffineSpace.map PUnit.{u + 1} f, inferInstance, hA, w, hw⟩

/-- **Hartshorne II.6, Proposition 6.6, first part.** If `X` satisfies `(*)`, so does the
relative affine line `X × Spec ℤ[t]`. -/
theorem Scheme.SatisfiesConditionStar.affineLine {X : Scheme.{u}}
    (hX : X.SatisfiesConditionStar) : 𝔸(PUnit.{u + 1}; X).SatisfiesConditionStar := by
  have := hX.isNoetherian
  have := hX.isIntegral
  have := hX.isSeparated
  refine ⟨?_, inferInstance, ?_, hX.isRegularInCodimensionOne.affineLine⟩
  · have : IsLocallyNoetherian 𝔸(PUnit.{u + 1}; X) :=
      LocallyOfFiniteType.isLocallyNoetherian (𝔸(PUnit.{u + 1}; X) ↘ X)
    have : CompactSpace 𝔸(PUnit.{u + 1}; X) :=
      QuasiCompact.compactSpace_of_compactSpace (𝔸(PUnit.{u + 1}; X) ↘ X)
    exact {}
  · exact ⟨by rw [← terminal.comp_from (𝔸(PUnit.{u + 1}; X) ↘ X)]; infer_instance⟩

end AlgebraicGeometry
