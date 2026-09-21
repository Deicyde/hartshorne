/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Morphism.LocalRingLocalization
import Hartshorne.Nonsingular.AmbientCotangent

/-!
# The defining ideal and the local cotangent space

Toward Hartshorne, *Algebraic Geometry*, I.5, Theorem 5.1 (p. 32).

For an affine variety `Y`, a point `P`, its defining ideal `𝔟 = I(Y)`,
and the ambient point ideal `𝔫`, this file identifies the cotangent space of
the local ring at `P` with the literal quotient `𝔫 / (𝔟 + 𝔫²)`.  Under the
ambient derivative equivalence, the subspace contributed by `𝔟` is the span
of the gradients of equations vanishing on `Y`.
-/

namespace Hartshorne

open MvPolynomial

universe u v w

section ResidueField

variable {k : Type u} [Field k] {σ : Type v} {Y : Set (σ → k)}
  {hY : IsIrreducible Y} {P : Y}

/-- Evaluation at `P`, as a `k`-algebra homomorphism from the local ring. -/
def evalAtPointAlgHom : LocalRingAt hY P →ₐ[k] k :=
  { evalAtPoint with
    commutes' := by intro c; rfl }

/-- The project's residue-field identification, upgraded to a `k`-algebra
equivalence. -/
noncomputable def residueFieldAlgEquiv :
    IsLocalRing.ResidueField (LocalRingAt hY P) ≃ₐ[k] k where
  __ := residueFieldEquiv (hY := hY) (P := P)
  commutes' _ := rfl

@[simp]
theorem residueFieldAlgEquiv_mk (x : LocalRingAt hY P) :
    residueFieldAlgEquiv (Ideal.Quotient.mk _ x) = evalAtPoint x := by
  rfl

/-- Scalar multiplication through the residue field agrees with scalar
multiplication through its identification with `k`. -/
theorem residueField_smul_cotangentSpace_eq_baseField_smul
    (r : IsLocalRing.ResidueField (LocalRingAt hY P))
    (x : IsLocalRing.CotangentSpace (LocalRingAt hY P)) :
    r • x = (residueFieldAlgEquiv r) • x := by
  let L := LocalRingAt hY P
  let m := IsLocalRing.maximalIdeal L
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨y, rfl⟩ := m.toCotangent_surjective x
  change m.toCotangent (a • y) =
    m.toCotangent ((algebraMap k L (evalAtPoint a)) • y)
  rw [m.toCotangent_eq]
  have ha : a - algebraMap k L (evalAtPoint a) ∈ m := by
    change a - algebraMap k (LocalRingAt hY P) (evalAtPoint a) ∈
      IsLocalRing.maximalIdeal (LocalRingAt hY P)
    rw [maximalIdeal_eq_ker, RingHom.mem_ker, map_sub]
    change evalAtPoint a - evalAtPoint a = 0
    simp
  simpa [Algebra.smul_def, sub_mul, pow_two] using Ideal.mul_mem_mul ha y.2

/-- The cotangent-space dimension is unchanged by identifying the residue
field with `k`. -/
theorem finrank_cotangentSpace_residueField_eq_baseField
    : Module.finrank (IsLocalRing.ResidueField (LocalRingAt hY P))
        (IsLocalRing.CotangentSpace (LocalRingAt hY P)) =
      Module.finrank k (IsLocalRing.CotangentSpace (LocalRingAt hY P)) := by
  unfold Module.finrank
  exact congrArg Cardinal.toNat <| rank_eq_of_equiv_equiv residueFieldAlgEquiv
    (AddEquiv.refl (IsLocalRing.CotangentSpace (LocalRingAt hY P)))
    residueFieldAlgEquiv.bijective
    residueField_smul_cotangentSpace_eq_baseField_smul

end ResidueField

section Localization

variable {k : Type u} [CommRing k] {R : Type v} {Rloc : Type w}
  [CommRing R] [CommRing Rloc] [Algebra k R] [Algebra k Rloc]
  (p : Ideal R) [p.IsMaximal] [Algebra R Rloc] [IsScalarTower k R Rloc]
  [IsLocalization.AtPrime Rloc p] [IsLocalRing Rloc]

/-- Localization at a maximal ideal preserves its cotangent space, with the
equivalence linear over every compatible base ring. -/
noncomputable def localizationCotangentEquiv :
    p.Cotangent ≃ₗ[k] (IsLocalRing.maximalIdeal Rloc).Cotangent := by
  let m := IsLocalRing.maximalIdeal Rloc
  let q : R →ₐ[k] Rloc := IsScalarTower.toAlgHom k R Rloc
  have hp : p ≤ m.comap q := by
    intro x hx
    change algebraMap R Rloc x ∈ m
    rw [← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal Rloc p]
    exact hx
  let f : p.Cotangent →ₗ[k] m.Cotangent := Ideal.mapCotangent p m q hp
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := p.toCotangent_surjective z
    rw [Ideal.mapCotangent_toCotangent, m.toCotangent_eq_zero] at hz
    rw [p.toCotangent_eq_zero]
    change algebraMap R Rloc x.1 ∈ m ^ 2 at hz
    rw [← Ideal.mem_under,
      IsLocalization.AtPrime.under_maximalIdeal_pow p Rloc 2] at hz
    exact hz
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨y, rfl⟩ := m.toCotangent_surjective z
    let e := IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rloc 2
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      (e.symm (Ideal.Quotient.mk (m ^ 2) y.1))
    have he : e (Ideal.Quotient.mk (p ^ 2) r) =
        Ideal.Quotient.mk (m ^ 2) y.1 := by
      rw [hr, e.apply_symm_apply]
    have hrp : r ∈ p := by
      have hdiff : algebraMap R Rloc r - y.1 ∈ m ^ 2 := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
        simpa [e] using congrArg (fun z => z - (m ^ 2).mkQ y.1) he
      have har : algebraMap R Rloc r ∈ m := by
        simpa only [sub_add_cancel] using
          m.add_mem (Ideal.pow_le_self (by decide) hdiff) y.2
      rw [← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal Rloc p] at har
      exact har
    refine ⟨p.toCotangent ⟨r, hrp⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent, m.toCotangent_eq]
    change algebraMap R Rloc r - y.1 ∈ m ^ 2
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    simpa [e] using congrArg (fun z => z - (m ^ 2).mkQ y.1) he
  exact LinearEquiv.ofBijective f ⟨hinj, hsurj⟩

end Localization

section Affine

variable {k : Type u} [Field k] {σ : Type v} {Y : Set (σ → k)}

private theorem affinePointIdeal_eq_vanishingIdeal_singleton (P : σ → k) :
    affinePointIdeal P = vanishingIdeal k ({P} : Set (σ → k)) := by
  ext f
  rw [affinePointIdeal, RingHom.mem_ker, mem_vanishingIdeal_singleton_iff]

/-- The literal relation subspace `I(Y) + 𝔫_P²` inside the point ideal
`𝔫_P`. -/
noncomputable def definingIdealCotangentRelations (Y : Set (σ → k)) (P : Y) :
    Submodule k (affinePointIdeal (P : σ → k)) :=
  Submodule.comap
    ((affinePointIdeal (P : σ → k)).subtype.restrictScalars k)
    ((vanishingIdeal k Y ⊔ affinePointIdeal (P : σ → k) ^ 2).restrictScalars k)

/-- Hartshorne's literal quotient `𝔫_P / (I(Y) + 𝔫_P²)`. -/
abbrev DefiningIdealCotangentQuotient (Y : Set (σ → k)) (P : Y) :=
  (affinePointIdeal (P : σ → k)) ⧸ definingIdealCotangentRelations Y P

/-- The quotient map from the ambient point ideal to the cotangent space of
the coordinate-ring maximal ideal. -/
noncomputable def ambientIdealToCoordinateCotangent (Y : Set (σ → k)) (P : Y) :
    affinePointIdeal (P : σ → k) →ₗ[k] (maximalIdealAt Y P).Cotangent := by
  let n := affinePointIdeal (P : σ → k)
  let m := maximalIdealAt Y P
  let q := Ideal.Quotient.mkₐ k (vanishingIdeal k Y)
  have hn : n ≤ m.comap q := by
    rw [show m.comap q = vanishingIdeal k ({(P : σ → k)} : Set (σ → k)) by
      exact comap_maximalIdealAt P]
    exact (affinePointIdeal_eq_vanishingIdeal_singleton (P : σ → k)).le
  exact (Ideal.mapCotangent n m q hn).comp (n.toCotangent.restrictScalars k)

private theorem ambientIdealToCoordinateCotangent_surjective
    (Y : Set (σ → k)) (P : Y) :
    Function.Surjective (ambientIdealToCoordinateCotangent Y P) := by
  let n := affinePointIdeal (P : σ → k)
  let m := maximalIdealAt Y P
  let q := Ideal.Quotient.mkₐ k (vanishingIdeal k Y)
  have hcomap : m.comap q = n := by
    rw [show m.comap q = vanishingIdeal k ({(P : σ → k)} : Set (σ → k)) by
      exact comap_maximalIdealAt P]
    exact (affinePointIdeal_eq_vanishingIdeal_singleton (P : σ → k)).symm
  have hmap : n.map q = m := by
    rw [← hcomap]
    exact Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective m
  intro z
  obtain ⟨y, rfl⟩ := m.toCotangent_surjective z
  have hy : y.1 ∈ n.map q := hmap.symm ▸ y.2
  obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective q
    Ideal.Quotient.mk_surjective).1 hy
  refine ⟨⟨x, hx⟩, ?_⟩
  simp only [ambientIdealToCoordinateCotangent, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, Ideal.mapCotangent_toCotangent]
  apply m.toCotangent.congr_arg
  exact Subtype.ext hxy

private theorem ambientIdealToCoordinateCotangent_ker
    (Y : Set (σ → k)) (P : Y) :
    (ambientIdealToCoordinateCotangent Y P).ker =
      definingIdealCotangentRelations Y P := by
  let n := affinePointIdeal (P : σ → k)
  let m := maximalIdealAt Y P
  let q := Ideal.Quotient.mkₐ k (vanishingIdeal k Y)
  have hcomap : m.comap q = n := by
    rw [show m.comap q = vanishingIdeal k ({(P : σ → k)} : Set (σ → k)) by
      exact comap_maximalIdealAt P]
    exact (affinePointIdeal_eq_vanishingIdeal_singleton (P : σ → k)).symm
  have hmap : n.map q = m := by
    rw [← hcomap]
    exact Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective m
  have hpow : (m ^ 2).comap q = vanishingIdeal k Y ⊔ n ^ 2 := by
    rw [← hmap, ← Ideal.map_pow]
    rw [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective]
    have hkerq : RingHom.ker q = vanishingIdeal k Y :=
      Ideal.Quotient.mkₐ_ker k (vanishingIdeal k Y)
    rw [hkerq]
    exact sup_comm _ _
  ext x
  rw [LinearMap.mem_ker]
  simp only [ambientIdealToCoordinateCotangent, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, Ideal.mapCotangent_toCotangent]
  rw [m.toCotangent_eq_zero]
  change q x.1 ∈ m ^ 2 ↔ _
  rw [← Ideal.mem_comap, hpow]
  rfl

/-- The literal quotient `𝔫_P/(I(Y)+𝔫_P²)` is the cotangent space of the
maximal ideal of the affine coordinate ring. -/
noncomputable def coordinateCotangentEquiv (Y : Set (σ → k)) (P : Y) :
    DefiningIdealCotangentQuotient Y P ≃ₗ[k] (maximalIdealAt Y P).Cotangent :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl k _)
      (by simpa using (ambientIdealToCoordinateCotangent_ker Y P).symm) ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective (ambientIdealToCoordinateCotangent Y P)
      (ambientIdealToCoordinateCotangent_surjective Y P)

/-- The coordinate-ring cotangent space agrees with the cotangent space of
the germ local ring. -/
noncomputable def coordinateToLocalCotangentEquiv
    (hY : IsIrreducible Y) (P : Y) :
    (maximalIdealAt Y P).Cotangent ≃ₗ[k]
      IsLocalRing.CotangentSpace (LocalRingAt hY P) := by
  let m := maximalIdealAt Y P
  let _ : m.IsMaximal := maximalIdealAt_isMaximal P
  let L := LocalRingAt hY P
  letI : Algebra (coordinateRing Y) L := (coordToLocal hY P).toAlgebra
  let _ : IsScalarTower k (coordinateRing Y) L :=
    IsScalarTower.of_algebraMap_eq fun c => (coordToLocal hY P).commutes c |>.symm
  let e : Localization.AtPrime m ≃ₐ[coordinateRing Y] L :=
    { __ := localizationEquivLocalRing hY P
      commutes' x := by
        change localizationToLocal hY P
          (algebraMap (coordinateRing Y) (Localization.AtPrime m) x) =
            coordToLocal hY P x
        rw [localizationToLocal, IsLocalization.lift_eq]
        rfl }
  let _ : IsLocalization m.primeCompl L :=
    IsLocalization.isLocalization_of_algEquiv m.primeCompl e
  exact localizationCotangentEquiv (Rloc := L) (k := k) m

/-- **The defining ideal and the local cotangent space.** For an affine
variety, `𝔪/𝔪²` in the germ local ring is `𝔫_P/(I(Y)+𝔫_P²)`. -/
noncomputable def definingIdealCotangentEquiv
    (hY : IsAffineVariety Y) (P : Y) :
    IsLocalRing.CotangentSpace (LocalRingAt hY.isIrreducible P) ≃ₗ[k]
      DefiningIdealCotangentQuotient Y P :=
  ((coordinateCotangentEquiv Y P).trans
    (coordinateToLocalCotangentEquiv hY.isIrreducible P)).symm

/-- The defining-ideal description of the local cotangent space exists as a
`k`-linear equivalence. -/
theorem definingIdealCotangentEquiv_nonempty
    (hY : IsAffineVariety Y) (P : Y) :
    Nonempty
      (IsLocalRing.CotangentSpace (LocalRingAt hY.isIrreducible P) ≃ₗ[k]
        DefiningIdealCotangentQuotient Y P) :=
  ⟨definingIdealCotangentEquiv hY P⟩

theorem affinePointIdeal_eq_comap_maximalIdealAt (P : Y) :
    affinePointIdeal (P : σ → k) =
      (maximalIdealAt Y P).comap
        (Ideal.Quotient.mk (vanishingIdeal k Y)) := by
  ext f
  simp only [affinePointIdeal, RingHom.mem_ker, Ideal.mem_comap,
    mem_maximalIdealAt, evalAt_mk]

theorem vanishingIdeal_le_affinePointIdeal (P : Y) :
    vanishingIdeal k Y ≤ affinePointIdeal (P : σ → k) := by
  intro f hf
  rw [affinePointIdeal, RingHom.mem_ker]
  exact hf P.1 P.2

private theorem coordinateCotangent_comap_eq (P : Y) :
    (maximalIdealAt Y P).comap
        (algebraMap (MvPolynomial σ k) (coordinateRing Y)) =
      RingHom.ker
          (algebraMap (MvPolynomial σ k) (coordinateRing Y)) ⊔
        affinePointIdeal (P : σ → k) := by
  change (maximalIdealAt Y P).comap
      (Ideal.Quotient.mk (vanishingIdeal k Y)) =
    RingHom.ker (Ideal.Quotient.mk (vanishingIdeal k Y)) ⊔
      affinePointIdeal (P : σ → k)
  rw [← affinePointIdeal_eq_comap_maximalIdealAt]
  apply (sup_eq_right.mpr ?_).symm
  rw [Ideal.mk_ker]
  exact vanishingIdeal_le_affinePointIdeal P

/-- The cotangent map induced by the quotient from the ambient polynomial
ring to the coordinate ring. -/
noncomputable def ambientToCoordinateCotangent (P : Y) :
    (affinePointIdeal (P : σ → k)).Cotangent →ₗ[k]
      (maximalIdealAt Y P).Cotangent :=
  Ideal.mapCotangent _ _ (Ideal.Quotient.mkₐ k (vanishingIdeal k Y))
    (le_of_eq (affinePointIdeal_eq_comap_maximalIdealAt P))

theorem ambientToCoordinateCotangent_surjective (P : Y) :
    Function.Surjective (ambientToCoordinateCotangent P) := by
  apply Ideal.mapCotangent_surjective_of_comap_eq
    (A := MvPolynomial σ k) (B := coordinateRing Y)
    Ideal.Quotient.mk_surjective
  exact coordinateCotangent_comap_eq P

/-- Equations vanishing on `Y`, mapped to their classes in the ambient
cotangent space at `P`. -/
noncomputable def definingIdealToAmbientCotangent (P : Y) :
    (vanishingIdeal k Y : Type _) →ₗ[k]
      (affinePointIdeal (P : σ → k)).Cotangent :=
  ((affinePointIdeal (P : σ → k)).toCotangent.comp
    (Submodule.inclusion
      (vanishingIdeal_le_affinePointIdeal P))).restrictScalars k

private theorem ambientToCoordinateCotangent_ker_raw (P : Y) :
    (ambientToCoordinateCotangent P).ker =
      ((Submodule.comap (affinePointIdeal (P : σ → k)).subtype
        (vanishingIdeal k Y)).map
          (affinePointIdeal (P : σ → k)).toCotangent).restrictScalars k := by
  have h := Ideal.mapCotangent_ker_of_surjective
    (A := MvPolynomial σ k) (B := coordinateRing Y)
    Ideal.Quotient.mk_surjective (coordinateCotangent_comap_eq P)
  have hk := congrArg
    (fun q : Submodule (MvPolynomial σ k)
        (affinePointIdeal (P : σ → k)).Cotangent => q.restrictScalars k) h
  let fR := Ideal.mapCotangent (affinePointIdeal (P : σ → k))
    (maximalIdealAt Y P)
    (Algebra.ofId (MvPolynomial σ k) (coordinateRing Y))
    (le_of_le_of_eq le_sup_right (coordinateCotangent_comap_eq P).symm)
  calc
    (ambientToCoordinateCotangent P).ker = fR.ker.restrictScalars k := by
      ext x
      rfl
    _ = _ := by simpa [fR] using hk

theorem definingIdealToAmbientCotangent_range (P : Y) :
    LinearMap.range (definingIdealToAmbientCotangent P) =
      (ambientToCoordinateCotangent P).ker := by
  rw [ambientToCoordinateCotangent_ker_raw]
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    let w : affinePointIdeal (P : σ → k) :=
      ⟨z.1, vanishingIdeal_le_affinePointIdeal P z.2⟩
    have hw : w ∈ Submodule.comap
        (affinePointIdeal (P : σ → k)).subtype
        (vanishingIdeal k Y) := z.2
    exact ⟨w, hw, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z.1, hz⟩, rfl⟩

/-- The linear space of gradients at `P` of equations vanishing on `Y`. -/
noncomputable def definingIdealGradient [Finite σ] (P : Y) :
    (vanishingIdeal k Y : Type _) →ₗ[k] (σ → k) :=
  (ambientCotangentEquiv (P : σ → k)).toLinearMap.comp
    (definingIdealToAmbientCotangent P)

@[simp]
theorem definingIdealGradient_apply [Finite σ] (P : Y)
    (f : vanishingIdeal k Y) (i : σ) :
    definingIdealGradient P f i =
      aeval (P : σ → k) (pderiv i f.1) := by
  change ambientCotangentEquiv (P : σ → k)
    ((affinePointIdeal (P : σ → k)).toCotangent
      ⟨f.1, vanishingIdeal_le_affinePointIdeal P f.2⟩) i = _
  exact ambientCotangentEquiv_toCotangent (P : σ → k)
    ⟨f.1, vanishingIdeal_le_affinePointIdeal P f.2⟩ i

/-- The span of all gradients at `P` of polynomials vanishing on `Y`. -/
noncomputable def definingIdealGradientSpace [Finite σ] (P : Y) :
    Submodule k (σ → k) :=
  LinearMap.range (definingIdealGradient P)

/-- The map from ambient coordinate directions to the germ cotangent space. -/
noncomputable def affineCoordinatesToLocalCotangent [Finite σ]
    (hY : IsIrreducible Y) (P : Y) :
    (σ → k) →ₗ[k] IsLocalRing.CotangentSpace (LocalRingAt hY P) :=
  (coordinateToLocalCotangentEquiv hY P).toLinearMap.comp
    ((ambientToCoordinateCotangent P).comp
      (ambientCotangentEquiv (P : σ → k)).symm.toLinearMap)

theorem affineCoordinatesToLocalCotangent_surjective [Finite σ]
    (hY : IsIrreducible Y) (P : Y) :
    Function.Surjective (affineCoordinatesToLocalCotangent hY P) :=
  (coordinateToLocalCotangentEquiv hY P).surjective.comp
    ((ambientToCoordinateCotangent_surjective P).comp
      (ambientCotangentEquiv (P : σ → k)).symm.surjective)

theorem affineCoordinatesToLocalCotangent_ker [Finite σ]
    (hY : IsIrreducible Y) (P : Y) :
    (affineCoordinatesToLocalCotangent hY P).ker =
      definingIdealGradientSpace P := by
  let eA := ambientCotangentEquiv (P : σ → k)
  let eL := coordinateToLocalCotangentEquiv hY P
  let f := ambientToCoordinateCotangent P
  have hgrad : definingIdealGradientSpace P =
      f.ker.map eA.toLinearMap := by
    rw [definingIdealGradientSpace, definingIdealGradient,
      LinearMap.range_comp, definingIdealToAmbientCotangent_range]
  rw [hgrad]
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    change eL (f (eA.symm x)) = 0 at hx
    have hfx : f (eA.symm x) = 0 := by
      apply eL.injective
      simpa using hx
    exact ⟨eA.symm x, hfx, eA.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [LinearMap.mem_ker]
    change eL (f (eA.symm (eA y))) = 0
    rw [eA.symm_apply_apply, LinearMap.mem_ker.mp hy, map_zero]

/-- The local cotangent space is the exact quotient of affine coordinate
directions by the span of gradients of equations defining `Y`. -/
noncomputable def affineCoordinatesQuotientEquivLocalCotangent [Finite σ]
    (hY : IsIrreducible Y) (P : Y) :
    ((σ → k) ⧸ definingIdealGradientSpace P) ≃ₗ[k]
      IsLocalRing.CotangentSpace (LocalRingAt hY P) :=
  (Submodule.quotEquivOfEq _ _
      (affineCoordinatesToLocalCotangent_ker hY P).symm) ≪≫ₗ
    (affineCoordinatesToLocalCotangent hY P).quotKerEquivOfSurjective
      (affineCoordinatesToLocalCotangent_surjective hY P)

/-- Hartshorne's cotangent dimension count: the dimension of `𝑚/𝑚²`
plus the dimension of the span of the defining gradients is the ambient
dimension. -/
theorem finrank_localCotangent_add_finrank_gradientSpace [Finite σ]
    (hY : IsAffineVariety Y) (P : Y) :
    Module.finrank
        (IsLocalRing.ResidueField (LocalRingAt hY.isIrreducible P))
        (IsLocalRing.CotangentSpace (LocalRingAt hY.isIrreducible P)) +
      Module.finrank k (definingIdealGradientSpace P) = Nat.card σ := by
  rw [finrank_cotangentSpace_residueField_eq_baseField]
  let eA := ambientCotangentEquiv (P : σ → k)
  let eL := coordinateToLocalCotangentEquiv hY.isIrreducible P
  let f := ambientToCoordinateCotangent P
  let _ : FiniteDimensional k
      (affinePointIdeal (P : σ → k)).Cotangent :=
    FiniteDimensional.of_injective eA.toLinearMap eA.injective
  have hf : Function.Surjective f :=
    ambientToCoordinateCotangent_surjective P
  have hrange : LinearMap.range f = ⊤ :=
    LinearMap.range_eq_top.mpr hf
  have hgrad : definingIdealGradientSpace P =
      f.ker.map eA.toLinearMap := by
    rw [definingIdealGradientSpace, definingIdealGradient,
      LinearMap.range_comp, definingIdealToAmbientCotangent_range]
  calc
    Module.finrank k
          (IsLocalRing.CotangentSpace (LocalRingAt hY.isIrreducible P)) +
        Module.finrank k (definingIdealGradientSpace P) =
      Module.finrank k (maximalIdealAt Y P).Cotangent +
        Module.finrank k f.ker := by
      rw [← eL.finrank_eq, hgrad, eA.finrank_map_eq]
    _ = Module.finrank k (LinearMap.range f) +
        Module.finrank k f.ker := by
      rw [hrange, finrank_top]
    _ = Module.finrank k
        (affinePointIdeal (P : σ → k)).Cotangent :=
      f.finrank_range_add_finrank_ker
    _ = Module.finrank k (σ → k) := eA.finrank_eq
    _ = Nat.card σ := by
      let _ : Fintype σ := Fintype.ofFinite σ
      simpa only [← Nat.card_eq_fintype_card] using Module.finrank_pi k

end Affine

end Hartshorne
