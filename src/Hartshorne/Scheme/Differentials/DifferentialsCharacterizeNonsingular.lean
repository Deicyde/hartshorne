/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.DimensionAtClosedPoint
import Hartshorne.Scheme.Differentials.RegularLocalDifferentialCriterion
import Hartshorne.Scheme.Differentials.RelativeDifferentialsAffineFibre
import Hartshorne.Scheme.ReducedInducedSubscheme
import Hartshorne.Scheme.Regular
import Hartshorne.Scheme.SerreRegularity

/-!
# Differentials characterize nonsingular varieties

Hartshorne, *Algebraic Geometry*, II, Theorem 8.15 (pp. 177–178).

Let `X` be an irreducible scheme of finite type over an algebraically closed field `k`, of
dimension `n`. Then `X` is nonsingular (all local rings are regular; then `X` is also reduced,
hence integral) if and only if `Ω_{X/k}` is locally free of rank `n`. Hartshorne states this for
irreducible separated schemes of finite type, concluding that `X` is a nonsingular variety;
separatedness is not used.

## Proof

If `X` is regular, its local rings are domains, so `X` is reduced and hence integral; then
`Ω_{X/k}` is locally free of rank `n` exactly when every fibre `(Ω_{X/k})_x ⊗ k(x)` has dimension
`n`. Conversely, local freeness of rank `n` gives fibre dimension `n` at every point, with no
integrality needed. Let `x` lie in an affine open `Spec T`, with prime `q ⊂ T`; the fibre is
`κ(q) ⊗_T Ω_{T/k}`. Choose a maximal ideal `m ⊇ q`. Its point is closed in `X` (finite-type
`k`-schemes are Jacobson), so `dim T_m = n` (Exercise II.3.20(a) applied to the reduced scheme
`X_red`, which is integral, has the same underlying space as `X`, and has the same local
dimensions), and `T_m` has residue field `k`.
Since `Ω_{T_m/k} = T_m ⊗_T Ω_{T/k}`, the fibre at `q` is `κ(q) ⊗_{T_m} Ω_{T_m/k}`.

* If `X` is nonsingular, `T_m` is regular of dimension `n`, so `Ω_{T_m/k}` is free of rank `n`
  (Theorem 8.8) and every fibre has dimension `n`.
* Conversely, if every fibre has dimension `n`, then at `m` this gives
  `dim_k m/m² = dim (κ(m) ⊗ Ω_{T_m/k}) = n = dim T_m`, so `T_m` is regular, and so is its
  localization `T_q`.

## Main results

* `Hartshorne.isRegular_iff_relativeDifferentials_isLocallyFreeOfRank`: Theorem 8.15.
* `Hartshorne.isIntegral_of_isRegular`: a regular irreducible scheme is integral.
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

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IrreducibleSpace X]

omit [IrreducibleSpace X] in
/-- The point of `X` given by a prime `y` of an affine open `U` lies in `U`. -/
theorem fromSpec_mem (U : X.affineOpens) (y : Spec Γ(X, (U : X.Opens))) :
    U.2.fromSpec y ∈ (U : X.Opens) := by
  exact U.2.range_fromSpec.le ⟨y, rfl⟩

/-- An irreducible space of dimension `n` has all irreducible components of dimension `n`. -/
theorem topologicalKrullDim_irreducibleComponent {n : ℕ} (hn : topologicalKrullDim X = n) :
    ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = n := by
  intro C hC
  obtain rfl : C = Set.univ :=
    Set.eq_univ_of_univ_subset (hC.2 (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ C))
  rw [← hn]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

open Order in
/-- On an irreducible scheme of finite type over a field, of dimension `n`, the local ring at a
closed point has dimension `n`. This is Exercise II.3.20(a) (`dimension_at_closed_point`) applied
to the reduced induced structure `X_red` on `X`: it is integral, `X_red → X` is a homeomorphism,
and local dimensions are coheights in the specialization order. -/
theorem ringKrullDim_stalk_of_isClosed (hf : FiniteType f) {n : ℕ}
    (hn : topologicalKrullDim X = n) (z : X) (hz : IsClosed ({z} : Set X)) :
    ringKrullDim (X.presheaf.stalk z) = n := by
  have := hf.1
  have := hf.2
  let Z : TopologicalSpace.Closeds X := ⊤
  let W := reducedInducedSubscheme Z
  let ι : W ⟶ X := reducedInducedSubschemeι Z
  have hsurj : Function.Surjective ι := by
    rw [← Set.range_eq_univ, range_reducedInducedSubschemeι]
    rfl
  have hh : IsHomeomorph ι :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨ι.isClosedEmbedding.isEmbedding, hsurj⟩
  have : IrreducibleSpace W :=
    hh.homeomorph.symm.surjective.irreducibleSpace hh.homeomorph.symm.continuous
  have : IsIntegral W := isIntegral_of_irreducibleSpace_of_isReduced W
  have hft : FiniteType (ι ≫ f) := ⟨inferInstance, inferInstance⟩
  obtain ⟨w, rfl⟩ := hsurj z
  have hw : IsClosed ({w} : Set W) := by
    have hpre : ι ⁻¹' {ι w} = {w} :=
      Set.ext fun a =>
        ⟨fun ha => hh.injective ha, fun ha => by rw [Set.mem_singleton_iff.mp ha]; rfl⟩
    rw [← hpre]
    exact hz.preimage ι.continuous
  let Φ : W ≃o X :=
    { hh.homeomorph.toEquiv with
      map_rel_iff' := fun {a b} => ι.isClosedEmbedding.isInducing.specializes_iff }
  calc ringKrullDim (X.presheaf.stalk (ι w)) = coheight (Φ w) := ringKrullDim_stalk_eq_coheight _
    _ = coheight w := by rw [coheight_orderIso]
    _ = ringKrullDim (W.presheaf.stalk w) := (ringKrullDim_stalk_eq_coheight w).symm
    _ = topologicalKrullDim W := (dimension_at_closed_point (ι ≫ f) hft w hw).symm
    _ = n := by rw [← hn]; exact hh.topologicalKrullDim_eq

omit [IrreducibleSpace X] in
/-- On a scheme of finite type over a field whose local rings at closed points all have dimension
`n`, the local ring at a maximal ideal of the ring of an affine open has dimension `n`. -/
theorem ringKrullDim_localization_of_isMaximal_of_forall_isClosed (hf : FiniteType f) {n : ℕ}
    (hdim : ∀ z : X, IsClosed ({z} : Set X) → ringKrullDim (X.presheaf.stalk z) = n)
    (U : X.affineOpens) (m : Ideal Γ(X, (U : X.Opens))) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = n := by
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
  rw [← hdim _ hclosed]
  exact ringKrullDim_eq_of_ringEquiv
    (IsLocalization.algEquiv m.primeCompl (Localization.AtPrime m) _).toRingEquiv

/-- On an irreducible scheme of finite type over a field, of dimension `n`, the local ring at a
maximal ideal of the ring of an affine open has dimension `n`. -/
theorem ringKrullDim_localization_of_isMaximal (hf : FiniteType f) {n : ℕ}
    (hn : topologicalKrullDim X = n) (U : X.affineOpens) (m : Ideal Γ(X, (U : X.Opens)))
    [m.IsMaximal] : ringKrullDim (Localization.AtPrime m) = n :=
  ringKrullDim_localization_of_isMaximal_of_forall_isClosed f hf
    (ringKrullDim_stalk_of_isClosed f hf hn) U m

end Scheme

end DifferentialsNonsingular

/-- A regular irreducible scheme is integral: its local rings are domains, so it is reduced. -/
theorem isIntegral_of_isRegular {X : Scheme.{u}} [IrreducibleSpace X] (h : X.IsRegular) :
    IsIntegral X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    have : IsRegularLocalRing (X.presheaf.stalk x) := h.2 x
    have := RegularLocal.isDomain (X.presheaf.stalk x)
    infer_instance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

open DifferentialsNonsingular in
/-- Let `X` be a scheme of finite type over an algebraically closed field `k` whose local rings at
closed points all have dimension `n`. Then every local ring of `X` is regular if and only if
every fibre `κ(x) ⊗ Ω_{X/k,x}` of the sheaf of differentials has dimension `n`. (This generalizes
the argument of Hartshorne II, proof of Theorem 8.15.) -/
theorem forall_isRegularAt_iff_finrank_fibre_of_forall_isClosed {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (hf : FiniteType f) (n : ℕ)
    (hdim : ∀ z : X, IsClosed ({z} : Set X) → ringKrullDim (X.presheaf.stalk z) = n) :
    (∀ x : X, X.IsRegularAt x) ↔
      ∀ x : X, finrank (ResidueField (X.presheaf.stalk x))
        (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
          (Scheme.relativeDifferentials f).presheaf.stalk x) = n := by
  have : LocallyOfFiniteType f := hf.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- the base ring `Γ(Spec k, ⊤) ≅ k` is an algebraically closed field
  let eA := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eA.toMulEquiv.isField (Field.toIsField k)).toField
  have : IsAlgClosed Γ(Spec (.of k), ⊤) := IsAlgClosed.of_ringEquiv k _ eA.symm
  let V : (Spec (.of k)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
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
    refine ⟨fun h x => ?_, fun h x => ?_⟩
    · obtain ⟨U, y, rfl⟩ := hcover x
      exact (key U y).1 h
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
  have hdimm := ringKrullDim_localization_of_isMaximal_of_forall_isClosed f hf hdim U m
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
    exact_mod_cast hrank.trans hdimm
  · intro h
    have hz := h (U.2.fromSpec z)
    rw [hfib z] at hz
    change finrank m.ResidueField (m.ResidueField ⊗[T] Ω[T⁄Γ(Spec (.of k), ⊤)]) = n at hz
    rw [finrank_tensor_kaehler_localization m.primeCompl (Localization.AtPrime m),
      ← finrank_cotangentSpace_eq_finrank_residueField_tensor_kaehlerDifferential _ _ hbij] at hz
    have hregm : IsRegularLocalRing (Localization.AtPrime m) := by
      rw [IsRegularLocalRing.iff_finrank_cotangentSpace, hz, hdimm]
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
      have hp' : p.comap (algebraMap T (Localization.AtPrime m)) = y.asIdeal := hp
      convert this
      exact hp'.symm
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨U.2.fromSpec y, fromSpec_mem U y⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec y)) y.asIdeal := hstalk y
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv y.asIdeal.primeCompl (Localization.AtPrime p)
        (X.presheaf.stalk (U.2.fromSpec y))).toRingEquiv

open DifferentialsNonsingular in
/-- **Hartshorne II, Theorem 8.15.** Let `X` be an irreducible scheme of finite type over an
algebraically closed field `k`, of dimension `n`. Then `X` is nonsingular (regular; it is then also
integral, `Hartshorne.isIntegral_of_isRegular`) if and only if `Ω_{X/k}` is locally free of rank
`n`. Hartshorne states this for irreducible separated schemes of finite type, concluding that `X`
is a nonsingular variety; separatedness is not used. -/
theorem isRegular_iff_relativeDifferentials_isLocallyFreeOfRank {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IrreducibleSpace X]
    (hf : FiniteType f) (n : ℕ) (hn : topologicalKrullDim X = n) :
    X.IsRegular ↔ (Scheme.relativeDifferentials f).IsLocallyFreeOfRank n := by
  have : LocallyOfFiniteType f := hf.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim := ringKrullDim_stalk_of_isClosed f hf hn
  constructor
  · intro hX
    -- a regular irreducible scheme is integral, so the fibre-rank criterion (Ex. II.5.8(c))
    -- applies to the coherent sheaf `Ω_{X/k}`
    have : IsIntegral X := isIntegral_of_isRegular hX
    rw [isLocallyFreeOfRank_iff_forall_finrank_fibre _
      (Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f) n]
    exact (forall_isRegularAt_iff_finrank_fibre_of_forall_isClosed f hf n hdim).1 hX.2
  · intro h
    -- local freeness of rank `n` gives fibre dimension `n` at every point
    exact ⟨inferInstance, (forall_isRegularAt_iff_finrank_fibre_of_forall_isClosed f hf n hdim).2
      (finrank_fibre_of_isLocallyFreeOfRank _ n h)⟩

end

end Hartshorne
