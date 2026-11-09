/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.DimensionAtClosedPoint
import Hartshorne.Scheme.Differentials.RegularLocalDifferentialCriterion
import Hartshorne.Scheme.Differentials.RelativeDifferentialsAffineFibre
import Hartshorne.Scheme.Differentials.RelativeDifferentialsFibreRank
import Hartshorne.Scheme.Regular
import Hartshorne.Scheme.SerreRegularity

/-!
# Differentials characterize nonsingular varieties

Hartshorne, *Algebraic Geometry*, II, Theorem 8.15 (pp. 177–178).

Let `X` be an integral scheme of finite type over an algebraically closed field `k`, of
dimension `n` (Hartshorne also assumes `X` separated, which the proof does not use). Then `X` is
nonsingular (all local rings are regular) if and only if `Ω_{X/k}` is locally free of rank `n`.

## Proof

Since `X` is integral, `Ω_{X/k}` is locally free of rank `n` exactly when every fibre
`(Ω_{X/k})_x ⊗ k(x)` has dimension `n`. Let `x` lie in an affine open `Spec T`, with prime
`q ⊂ T`; the fibre is `κ(q) ⊗_T Ω_{T/k}`. Choose a maximal ideal `m ⊇ q`. Its point is closed in
`X` (finite-type `k`-schemes are Jacobson), so `dim T_m = n`, and `T_m` has residue field `k`.
Since `Ω_{T_m/k} = T_m ⊗_T Ω_{T/k}`, the fibre at `q` is `κ(q) ⊗_{T_m} Ω_{T_m/k}`.

* If `X` is nonsingular, `T_m` is regular of dimension `n`, so `Ω_{T_m/k}` is free of rank `n`
  (Theorem 8.8) and every fibre has dimension `n`.
* Conversely, if every fibre has dimension `n`, then at `m` this gives
  `dim_k m/m² = dim (κ(m) ⊗ Ω_{T_m/k}) = n = dim T_m`, so `T_m` is regular, and so is its
  localization `T_q`.

## Main results

* `Hartshorne.isRegular_iff_relativeDifferentials_isLocallyFreeOfRank`: Theorem 8.15.
-/

open CategoryTheory TensorProduct IsLocalRing Module Topology

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

namespace DifferentialsNonsingular

section Algebra

variable {k T : Type u} [Field k] [CommRing T] [Algebra k T]

/-- For a finitely generated algebra `T` over an algebraically closed field `k` and a maximal
ideal `m`, the residue field of `T_m` is `k`. -/
theorem bijective_algebraMap_residueField [IsAlgClosed k] [Algebra.FiniteType k T]
    (m : Ideal T) [m.IsMaximal] :
    Function.Bijective (algebraMap k (ResidueField (Localization.AtPrime m))) := by
  have : Algebra.FiniteType k m.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom k T m.ResidueField)
      m.algebraMap_residueField_surjective
  have : Module.Finite k m.ResidueField := finite_of_finite_type_of_isJacobsonRing k _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- Fibres of `Ω_{T/k}` can be computed after localizing `T`: for a localization `T_M` of `T` and
a field `K` over `T_M`, `K ⊗_T Ω_{T/k} ≅ K ⊗_{T_M} Ω_{T_M/k}`. -/
theorem finrank_tensor_kaehler_localization (M : Submonoid T) (Tm : Type u) [CommRing Tm]
    [Algebra T Tm] [Algebra k Tm] [IsScalarTower k T Tm] [IsLocalization M Tm]
    (K : Type u) [Field K] [Algebra T K] [Algebra Tm K] [IsScalarTower T Tm K] :
    finrank K (K ⊗[T] Ω[T⁄k]) = finrank K (K ⊗[Tm] Ω[Tm⁄k]) :=
  ((IsLocalizedModule.isBaseChange M Tm (KaehlerDifferential.map k k T Tm)).comp
    (TensorProduct.isBaseChange Tm Ω[Tm⁄k] K)).equiv.finrank_eq

end Algebra

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIntegral X]

omit [IsIntegral X] in
/-- The point of `X` given by a prime `y` of an affine open `U` lies in `U`. -/
theorem fromSpec_mem (U : X.affineOpens) (y : Spec Γ(X, (U : X.Opens))) :
    U.2.fromSpec y ∈ (U : X.Opens) := by
  exact U.2.range_fromSpec.le ⟨y, rfl⟩

/-- On an integral scheme of finite type over a field, of dimension `n`, the local ring at a
maximal ideal of the ring of an affine open has dimension `n`. -/
theorem ringKrullDim_localization_of_isMaximal (hf : FiniteType f) {n : ℕ}
    (hn : topologicalKrullDim X = n) (U : X.affineOpens) (m : Ideal Γ(X, (U : X.Opens)))
    [m.IsMaximal] : ringKrullDim (Localization.AtPrime m) = n := by
  have : LocallyOfFiniteType f := hf.1
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  let y : Spec Γ(X, (U : X.Opens)) := ⟨m, inferInstance⟩
  have hy := fromSpec_mem U y
  have hclosed : IsClosed ({U.2.fromSpec y} : Set X) := by
    apply isClosed_singleton_of_isLocallyClosed_singleton
    have h1 : IsLocallyClosed ({y} : Set (Spec Γ(X, (U : X.Opens)))) :=
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr ‹_›).isLocallyClosed
    have h2 := h1.image U.2.fromSpec.isOpenEmbedding.isInducing
      U.2.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
    simpa using h2
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨U.2.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec y)) m :=
    U.2.isLocalization_stalk' y hy
  rw [← hn, dimension_at_closed_point f hf _ hclosed]
  exact ringKrullDim_eq_of_ringEquiv
    (IsLocalization.algEquiv m.primeCompl (Localization.AtPrime m) _).toRingEquiv

end Scheme

end DifferentialsNonsingular

open DifferentialsNonsingular in
/-- **Hartshorne II, Theorem 8.15.** Let `X` be an integral scheme of finite type over an
algebraically closed field `k`, of dimension `n`. Then `X` is nonsingular (regular) if and only if
`Ω_{X/k}` is locally free of rank `n`. Hartshorne states this for varieties, which are also
separated; the proof does not use separatedness. -/
theorem isRegular_iff_relativeDifferentials_isLocallyFreeOfRank {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsIntegral X]
    (hf : FiniteType f) (n : ℕ) (hn : topologicalKrullDim X = n) :
    X.IsRegular ↔ (Scheme.relativeDifferentials f).IsLocallyFreeOfRank n := by
  have : LocallyOfFiniteType f := hf.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [Scheme.relativeDifferentials_isLocallyFreeOfRank_iff f n]
  -- the base ring `Γ(Spec k, ⊤) ≅ k` is an algebraically closed field
  let eA := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eA.toMulEquiv.isField (Field.toIsField k)).toField
  have : IsAlgClosed Γ(Spec (.of k), ⊤) := IsAlgClosed.of_ringEquiv k _ eA.symm
  let V : (Spec (.of k)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  -- reduce to a point `fromSpec y` of an affine open `U`
  suffices key : ∀ (U : X.affineOpens) (y : Spec Γ(X, (U : X.Opens))),
      ((∀ x : X, X.IsRegularAt x) →
        finrank (ResidueField (X.presheaf.stalk (U.2.fromSpec y)))
          (ResidueField (X.presheaf.stalk (U.2.fromSpec y)) ⊗[X.presheaf.stalk (U.2.fromSpec y)]
            (Scheme.relativeDifferentials f).presheaf.stalk (U.2.fromSpec y)) = n) ∧
      ((∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
          (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
            (Scheme.relativeDifferentials f).presheaf.stalk x) = n) →
        X.IsRegularAt (U.2.fromSpec y)) by
    have hcover : ∀ x : X, ∃ (U : X.affineOpens) (y : Spec Γ(X, (U : X.Opens))),
        U.2.fromSpec y = x := by
      intro x
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact ⟨⟨U, hU⟩, hU.primeIdealOf ⟨x, hxU⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
    refine ⟨fun ⟨_, hreg⟩ x => ?_, fun h => ⟨inferInstance, fun x => ?_⟩⟩
    · obtain ⟨U, y, rfl⟩ := hcover x
      exact (key U y).1 hreg
    · obtain ⟨U, y, rfl⟩ := hcover x
      exact (key U y).2 h
  intro U y
  have : y.asIdeal.IsPrime := y.isPrime
  let T := Γ(X, (U : X.Opens))
  have hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens) := le_top
  let : Algebra Γ(Spec (.of k), ⊤) T := (f.appLE ⊤ U hUV).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of k), ⊤) T := f.finiteType_appLE V.2 U.2 hUV
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing Γ(Spec (.of k), ⊤) T
  have hfib (z : Spec T) := finrank_fibre_relativeDifferentials_affine f U V hUV z
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
  let z : Spec T := ⟨m, hm.isPrime⟩
  have hdim := ringKrullDim_localization_of_isMaximal f hf hn U m
  have hbij := bijective_algebraMap_residueField (k := Γ(Spec (.of k), ⊤)) m
  have : Algebra.EssFiniteType Γ(Spec (.of k), ⊤) (Localization.AtPrime m) :=
    Algebra.EssFiniteType.comp _ T _
  -- the stalk at `fromSpec z` is `T_m`
  have hstalk (w : Spec T) := U.2.isLocalization_stalk' w (fromSpec_mem U w)
  constructor
  · intro hreg
    rw [hfib y]
    have hregm : IsRegularLocalRing (Localization.AtPrime m) := by
      have : IsRegularLocalRing (X.presheaf.stalk (U.2.fromSpec z)) := hreg (U.2.fromSpec z)
      let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨U.2.fromSpec z, fromSpec_mem U z⟩
      have : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec z)) m := hstalk z
      exact IsRegularLocalRing.of_ringEquiv
        (IsLocalization.algEquiv m.primeCompl (X.presheaf.stalk (U.2.fromSpec z))
          (Localization.AtPrime m)).toRingEquiv
    obtain ⟨hfree, hrank⟩ :=
      free_kaehlerDifferential_of_isRegularLocalRing Γ(Spec (.of k), ⊤) (Localization.AtPrime m)
        hbij
    have hunit : ∀ s : m.primeCompl, IsUnit (algebraMap T y.asIdeal.ResidueField s) := by
      intro s
      rw [IsScalarTower.algebraMap_apply T (Localization.AtPrime y.asIdeal)]
      exact (IsLocalization.map_units (Localization.AtPrime y.asIdeal)
        (⟨s, fun hs => s.2 (hqm hs)⟩ : y.asIdeal.primeCompl)).map _
    let : Algebra (Localization.AtPrime m) y.asIdeal.ResidueField :=
      (IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m) hunit).toAlgebra
    have : IsScalarTower T (Localization.AtPrime m) y.asIdeal.ResidueField :=
      IsScalarTower.of_algebraMap_eq'
        (IsLocalization.lift_comp (M := m.primeCompl) (S := Localization.AtPrime m) hunit).symm
    rw [finrank_tensor_kaehler_localization m.primeCompl (Localization.AtPrime m),
      Module.finrank_baseChange]
    exact_mod_cast hrank.trans hdim
  · intro h
    have hz := h (U.2.fromSpec z)
    rw [hfib z] at hz
    change finrank m.ResidueField (m.ResidueField ⊗[T] Ω[T⁄Γ(Spec (.of k), ⊤)]) = n at hz
    rw [finrank_tensor_kaehler_localization m.primeCompl (Localization.AtPrime m),
      ← finrank_cotangentSpace_eq_finrank_residueField_tensor_kaehlerDifferential _ _ hbij] at hz
    have hregm : IsRegularLocalRing (Localization.AtPrime m) := by
      rw [IsRegularLocalRing.iff_finrank_cotangentSpace, hz, hdim]
    -- `T_q` is a localization of `T_m`
    have hdisj : Disjoint (m.primeCompl : Set T) y.asIdeal :=
      Set.disjoint_left.mpr fun s hs hsq => hs (hqm hsq)
    let p := y.asIdeal.map (algebraMap T (Localization.AtPrime m))
    have : p.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ _ y.isPrime hdisj
    have hp : p.under T = y.asIdeal :=
      IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ y.isPrime hdisj
    have : IsRegularLocalRing (Localization.AtPrime p) :=
      RegularLocal.isRegularLocalRing_localization_atPrime _ p
    have hl : IsLocalization.AtPrime (Localization.AtPrime p) y.asIdeal := by
      have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := m.primeCompl) (S := Localization.AtPrime m) (T := Localization.AtPrime p) p
      have key : ∀ (I : Ideal T) [I.IsPrime], I = y.asIdeal →
          IsLocalization.AtPrime (Localization.AtPrime p) I →
            IsLocalization.AtPrime (Localization.AtPrime p) y.asIdeal := by
        rintro I _ rfl h
        exact h
      exact key _ hp this
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨U.2.fromSpec y, fromSpec_mem U y⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec y)) y.asIdeal := hstalk y
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime p)
        (X.presheaf.stalk (U.2.fromSpec y))).toRingEquiv

end

end Hartshorne
