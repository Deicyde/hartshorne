/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteType
import Hartshorne.Weil.FiniteFieldExtensionTower
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution

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

/-- The finite-extension point-count sequence of a finite-type scheme over a
finite field. At `r : ℕ+`, this is the number of scheme-valued points over the
canonical degree-`r` extension inside the fixed algebraic closure. -/
noncomputable def pointCountSequence
    (k : Type u) [Field k] [Finite k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (hf : FiniteType f) :
    ℕ+ → ℕ :=
  fun r =>
    letI : Finite
        ((Over.mk (Spec.map (CommRingCat.ofHom
          (algebraMap k (finiteFieldExtension k r))))) ⟶ Over.mk f) :=
      finite_rationalPoints_of_finiteType k (finiteFieldExtension k r) X f hf
    Nat.card
      ((Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap k (finiteFieldExtension k r))))) ⟶ Over.mk f)

/-- The logarithm series whose formal exponential is the Hasse–Weil zeta
series. Its coefficient in positive degree `r` is `N_r / r`. -/
noncomputable def hasseWeilZetaLogSeries
    (k : Type u) [Field k] [Finite k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (hf : FiniteType f) :
    PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if h : n = 0 then 0
    else (pointCountSequence k X f hf ⟨n, Nat.pos_of_ne_zero h⟩ : ℚ) / n

theorem hasseWeilZetaLogSeries_constantCoeff
    (k : Type u) [Field k] [Finite k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (hf : FiniteType f) :
    MvPowerSeries.constantCoeff (hasseWeilZetaLogSeries k X f hf) = 0 := by
  change PowerSeries.constantCoeff (hasseWeilZetaLogSeries k X f hf) = 0
  rw [hasseWeilZetaLogSeries, PowerSeries.constantCoeff_mk]
  simp

/-- The Hasse–Weil zeta function as a rational formal power series,
`exp (∑_{r ≥ 1} N_r X^r / r)`. This definition does not assert rationality. -/
noncomputable def hasseWeilZetaSeries
    (k : Type u) [Field k] [Finite k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (hf : FiniteType f) :
    PowerSeries ℚ :=
  (PowerSeries.exp ℚ).subst (hasseWeilZetaLogSeries k X f hf)

/-- The Hasse–Weil zeta series has constant coefficient one. -/
theorem hasseWeilZetaSeries_constantCoeff
    (k : Type u) [Field k] [Finite k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (hf : FiniteType f) :
    PowerSeries.constantCoeff (hasseWeilZetaSeries k X f hf) = 1 := by
  rw [hasseWeilZetaSeries]
  change MvPowerSeries.constantCoeff
    ((PowerSeries.exp ℚ).subst (hasseWeilZetaLogSeries k X f hf)) = 1
  rw [PowerSeries.constantCoeff_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero'
      (hasseWeilZetaLogSeries_constantCoeff k X f hf))]
  simp only [map_pow, hasseWeilZetaLogSeries_constantCoeff]
  rw [finsum_eq_single _ 0 (fun d hd => by simp [hd])]
  simp

/-- Isomorphic finite-type schemes over a finite field have equal point-count
sequences and equal Hasse–Weil zeta series. -/
theorem pointCountSequence_eq_and_hasseWeilZetaSeries_eq_of_iso
    (k : Type u) [Field k] [Finite k]
    {X Y : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {g : Y ⟶ Spec (.of k)}
    (hf : FiniteType f) (hg : FiniteType g)
    (e : Over.mk f ≅ Over.mk g) :
    pointCountSequence k X f hf = pointCountSequence k Y g hg ∧
      hasseWeilZetaSeries k X f hf = hasseWeilZetaSeries k Y g hg := by
  have hcount : pointCountSequence k X f hf = pointCountSequence k Y g hg := by
    funext r
    rw [pointCountSequence, pointCountSequence]
    exact Nat.card_congr ((Iso.refl _).homCongr e)
  refine ⟨hcount, ?_⟩
  have hlog : hasseWeilZetaLogSeries k X f hf =
      hasseWeilZetaLogSeries k Y g hg := by
    rw [hasseWeilZetaLogSeries, hasseWeilZetaLogSeries, hcount]
  exact congrArg (fun S : PowerSeries ℚ => (PowerSeries.exp ℚ).subst S) hlog

end Hartshorne
