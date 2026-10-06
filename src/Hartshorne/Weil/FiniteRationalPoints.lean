/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteType

/-!
# Rational points of finite-type schemes over finite fields

Hartshorne, *Algebraic Geometry*, Appendix C, §1 (p. 449).

A finite-type scheme over a finite field has only finitely many rational points
over any finite extension.  We prove this by passing to a finite affine cover.
On an affine chart, a morphism from the spectrum of a finite field is determined
by a ring homomorphism from a finite-type algebra into a finite ring.
-/

open CategoryTheory
open AlgebraicGeometry

universe u uR uA uB

namespace Hartshorne

private theorem finite_algHom_of_finiteType
    (R : Type uR) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Finite B] [Algebra.FiniteType R A] :
    Finite (A →ₐ[R] B) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  exact Finite.of_injective (fun f : A →ₐ[R] B ↦ fun x : s ↦ f x.1)
    fun f g h ↦ AlgHom.ext_of_adjoin_eq_top hs fun x hx ↦ congr_fun h ⟨x, hx⟩

private theorem finite_ringHom_of_finiteType
    (R : Type uR) (A : Type uA) (B : Type uB)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Finite R] [Finite B] [Algebra.FiniteType R A] :
    Finite (A →+* B) := by
  let _ : Algebra.FiniteType ℤ R := inferInstance
  let _ : Algebra.FiniteType ℤ A :=
    Algebra.FiniteType.trans (S := R) (inferInstance : Algebra.FiniteType ℤ R)
      (inferInstance : Algebra.FiniteType R A)
  have _ : Finite (A →ₐ[ℤ] B) := finite_algHom_of_finiteType ℤ A B
  exact Finite.of_equiv (A →ₐ[ℤ] B) (RingHom.equivIntAlgHom A B).symm

private theorem finite_hom_from_spec_of_affine_finiteType
    (k K : Type u) [Field k] [Finite k] [Field K] [Finite K]
    (Y : Scheme.{u}) [IsAffine Y] (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType g] :
    Finite (Spec (.of K) ⟶ Y) := by
  let _ : Finite Γ(Spec (.of k), ⊤) :=
    Finite.of_equiv k (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  have hg : g.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  let _ : Algebra Γ(Spec (.of k), ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  let _ : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(Y, ⊤) := hg
  have _ : Finite (Γ(Y, ⊤) →+* K) :=
    finite_ringHom_of_finiteType Γ(Spec (.of k), ⊤) Γ(Y, ⊤) K
  exact Finite.of_injective
    (fun p : Spec (.of K) ⟶ Y ↦ (Spec.preimage (p ≫ Y.isoSpec.hom)).hom) fun p q h ↦ by
      apply (cancel_mono Y.isoSpec.hom).mp
      apply Spec.homEquiv.injective
      exact CommRingCat.hom_ext h

private theorem finite_hom_from_spec_of_finiteType
    (k K : Type u) [Field k] [Finite k] [Field K] [Finite K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (hf : FiniteType f) :
    Finite (Spec (.of K) ⟶ X) := by
  let _ : LocallyOfFiniteType f := hf.1
  let _ : QuasiCompact f := hf.2
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  let _ : Fintype 𝒰.I₀ := by
    dsimp [𝒰]
    infer_instance
  have hfinite (i : 𝒰.I₀) : Finite (Spec (.of K) ⟶ 𝒰.X i) := by
    let _ : LocallyOfFiniteType (𝒰.f i ≫ f) := inferInstance
    exact finite_hom_from_spec_of_affine_finiteType k K (𝒰.X i) (𝒰.f i ≫ f)
  let _ (i : 𝒰.I₀) : Finite (Spec (.of K) ⟶ 𝒰.X i) := hfinite i
  apply Finite.of_surjective
    (fun p : Σ i, Spec (.of K) ⟶ 𝒰.X i ↦ p.2 ≫ 𝒰.f p.1)
  intro p
  have hp : ∃ i, Set.range p ⊆ Set.range (𝒰.f i) := by
    refine ⟨𝒰.idx (p (IsLocalRing.closedPoint (CommRingCat.of K))), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map p.continuous).mem_open
      (𝒰.f _).opensRange.2 (𝒰.covers _)
  obtain ⟨i, hi⟩ := hp
  exact ⟨⟨i, IsOpenImmersion.lift (𝒰.f i) p hi⟩,
    IsOpenImmersion.lift_fac (𝒰.f i) p hi⟩

/-- If `X` is of finite type over a finite field `k`, then its `K`-rational
points form a finite type for every finite field extension `K / k`.

The rational points are represented scheme-theoretically as morphisms over
`Spec k`, rather than as coordinate tuples. -/
theorem finite_rationalPoints_of_finiteType
    (k K : Type u) [Field k] [Finite k] [Field K] [Finite K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (hf : FiniteType f) :
    Finite ((Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⟶ Over.mk f) := by
  exact @Finite.of_injective _ (Spec (.of K) ⟶ X)
    (finite_hom_from_spec_of_finiteType k K X f hf) (fun p ↦ p.left)
      fun p q h ↦ Over.OverMorphism.ext h

end Hartshorne
