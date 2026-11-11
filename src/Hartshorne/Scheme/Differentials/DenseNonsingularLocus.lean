/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentFibreRank
import Hartshorne.Scheme.Differentials.DifferentialsCharacterizeNonsingular
import Hartshorne.Scheme.Differentials.FieldDifferentialsDimension
import Hartshorne.Scheme.Differentials.StandardSmoothFieldDimension
import Hartshorne.Scheme.Regular
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Etale.Field

/-!
# The dense nonsingular locus

Hartshorne, *Algebraic Geometry*, II.8, Corollary 8.16 (p. 178): if `X` is a variety over an
algebraically closed field `k`, then the regular points of `X` contain a nonempty open dense
subset.

We prove this for an integral scheme locally of finite type over a perfect field, following
Hartshorne's proof.

* The function field `K` of `X` is finitely generated and separably generated over the perfect
  field `k` (I, 4.8A), so `Ω_{K/k}` has dimension `n = tr.deg_k K` (Theorem 8.6A).
* The sheaf `Ω_{X/k}` is coherent and its stalk at the generic point is a vector space over `K`,
  so it is free on a nonempty open set `W` (Exercise II.5.7). Its fibres at points of `W` all
  have the same dimension, namely the dimension `n` of the fibre `Ω_{K/k}` at the generic point.
* `W` is nonsingular, by the argument of Theorem 8.15. Let `x ∈ W` lie in an affine open
  `Spec T ⊆ W`, with prime `q ⊂ T`, and choose a maximal ideal `m ⊇ q`. Then `dim T_m = n`
  (Theorem I.1.8A), and since the residue field of `T_m` is separable over `k`, the cotangent
  space `m/m²` injects into the fibre of `Ω_{T_m/k}` (a supplement to Proposition 8.7), which
  has dimension `n`. So `T_m` is regular, and so is its localization `T_q` (Theorem 8.14A).

Hartshorne's Theorem 8.15 is stated over an algebraically closed field, where the residue field
of `T_m` is `k` itself; over a perfect field the residue field is a finite separable extension of
`k`, and the injectivity of `m/m² → κ(m) ⊗ Ω_{T_m/k}` still holds.

We also record that a scheme smooth over a field is regular at every point
(`Hartshorne.isRegularAt_of_smooth`), since its local rings are localizations of standard
smooth algebras over the field.
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct

universe u

/-- Every point of a scheme smooth over a field is regular. -/
theorem isRegularAt_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [Smooth g] (y : Y) : Y.IsRegularAt y := by
  obtain ⟨U, -, V, hV, hyV, e, hf⟩ := Smooth.exists_isStandardSmooth g y
  obtain rfl : U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = g y := Subsingleton.elim _ _
    rw [this]
    exact e hyV
  have hfield : IsField Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  let : Field Γ(Spec (.of k), ⊤) := hfield.toField
  let := (g.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Spec (.of k), ⊤) Γ(Y, V) := hf
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
  set t := hV.primeIdealOf ⟨y, hyV⟩
  have hreg := SubmersivePresentation.isRegularLocalRing_localization P t.asIdeal
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hyV⟩
  have := hV.isLocalization_stalk ⟨y, hyV⟩
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv t.asIdeal.primeCompl
    (Localization.AtPrime t.asIdeal) (Y.presheaf.stalk y)).toRingEquiv

namespace DenseNonsingular

open IsLocalRing

section Algebra

/-- Let `B` be a local ring containing a field `F` whose residue field is formally smooth over
`F` (for example, a finite separable extension of `F`). Then the cotangent space `𝔪/𝔪²` injects
into the fibre `κ ⊗_B Ω_{B/F}`, so its dimension is at most that of the fibre. This supplements
Hartshorne II, Proposition 8.7, where the residue field is `F` itself. -/
theorem finrank_cotangentSpace_le_finrank_fibre (F B : Type u) [Field F] [CommRing B]
    [IsLocalRing B] [Algebra F B] [Algebra.FormallySmooth F (ResidueField B)]
    [Module.Finite (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄F])] :
    finrank (ResidueField B) (CotangentSpace B) ≤
      finrank (ResidueField B) (ResidueField B ⊗[B] Ω[B⁄F]) := by
  have hsurj : Function.Surjective (algebraMap B (ResidueField B)) := residue_surjective
  let g := IsScalarTower.toAlgHom F B (ResidueField B)
  have hgs : Function.Surjective g.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hsq : RingHom.ker g.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift, Ideal.cotangentIdeal_square]
  have hnil : IsNilpotent (RingHom.ker g.kerSquareLift.toRingHom) := ⟨2, hsq⟩
  -- a section `κ → B/𝔪²` of the residue map, by formal smoothness
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id F (ResidueField B))
    g.kerSquareLift hgs hnil
  have hs : g.kerSquareLift.comp s = AlgHom.id F (ResidueField B) := by
    ext x
    exact Algebra.FormallySmooth.liftOfSurjective_apply _ _ hgs hnil x
  -- hence a retraction of the conormal map `𝔪/𝔪² → κ ⊗_B Ω_{B/F}`
  let r := (retractionKerCotangentToTensorEquivSection (R := F) (P := B)
    (S := ResidueField B) hsurj).symm ⟨s, hs⟩
  have hinj : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor F B (ResidueField B)) := by
    apply Function.LeftInverse.injective (g := r.1)
    intro x
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun r.2 x
  let e : CotangentSpace B ≃ₗ[B] (RingHom.ker (algebraMap B (ResidueField B))).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ (by rw [ResidueField.algebraMap_eq, ker_residue])
  let φ : CotangentSpace B →ₗ[ResidueField B] ResidueField B ⊗[B] Ω[B⁄F] :=
    LinearMap.extendScalarsOfSurjectiveEquiv hsurj
      ((KaehlerDifferential.kerCotangentToTensor F B (ResidueField B)).comp e.toLinearMap)
  exact LinearMap.finrank_le_finrank_of_injective (f := φ) (hinj.comp e.injective)

/-- The residue field at a maximal ideal of a finitely generated algebra over a perfect field
`F` is a finite separable extension of `F`, hence formally smooth over `F`. -/
theorem formallySmooth_residueField_of_isMaximal {F T : Type u} [Field F] [PerfectField F]
    [CommRing T] [Algebra F T] [Algebra.FiniteType F T] (m : Ideal T) [m.IsMaximal] :
    Algebra.FormallySmooth F m.ResidueField := by
  have : Algebra.FiniteType F m.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom F T m.ResidueField)
      m.algebraMap_residueField_surjective
  have : Module.Finite F m.ResidueField := finite_of_finite_type_of_isJacobsonRing F _
  have : Algebra.FormallyEtale F m.ResidueField := Algebra.FormallyEtale.of_isSeparable F _
  infer_instance

variable {F T : Type u} [Field F] [PerfectField F] [CommRing T] [IsDomain T] [Algebra F T]
  [Algebra.FiniteType F T]

/-- For a finitely generated domain `T` over a perfect field `F`, the fibre of `Ω_{T/F}` at the
generic point, which is `Ω_{K/F}` for the fraction field `K` of `T`, has dimension `dim T`.
This combines Theorem 8.6A, applied to the separably generated extension `K/F`, with
Theorem I.1.8A. -/
theorem finrank_fibre_bot_eq_ringKrullDim :
    (finrank (⊥ : Ideal T).ResidueField ((⊥ : Ideal T).ResidueField ⊗[T] Ω[T⁄F]) :
      WithBot ℕ∞) = ringKrullDim T := by
  set K := (⊥ : Ideal T).ResidueField
  obtain ⟨s, hs, htr⟩ := exists_ringKrullDim_eq_trdeg F T K
  have : Algebra.EssFiniteType F K := Algebra.EssFiniteType.comp F T K
  -- (I, 4.8A) `K/F` is separably generated, so (8.6A) `dim_K Ω_{K/F} = tr.deg_F K`
  obtain ⟨t, ht, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField F K
  have hfg : (⊤ : IntermediateField F K).FG := IntermediateField.fg_top_iff.mpr inferInstance
  have h := ((trdeg_le_rank_kaehlerDifferential hfg).2.1).mpr ⟨(t : Set K), ht, hsep⟩
  -- the generic fibre of `Ω_{T/F}` is `Ω_{K/F}`
  have h1 : finrank K (K ⊗[T] Ω[T⁄F]) = finrank K (K ⊗[K] Ω[K⁄F]) :=
    DifferentialsNonsingular.finrank_tensor_kaehler_localization (nonZeroDivisors T) K K
  have h2 : finrank K (K ⊗[K] Ω[K⁄F]) = finrank K Ω[K⁄F] := (TensorProduct.lid K _).finrank_eq
  have h3 : finrank K Ω[K⁄F] = s := Module.finrank_eq_of_rank_eq (h.symm.trans htr)
  rw [h1, h2, h3, hs]

/-- Let `T` be a finitely generated domain over a perfect field `F` and `m` a maximal ideal. If
the fibre of `Ω_{T/F}` at `m` has the same dimension as the fibre at the generic point, then
`T_m` is a regular local ring. (This is the argument of Hartshorne II, proof of Theorem 8.15,
over a perfect field.) -/
theorem isRegularLocalRing_localization_of_finrank_fibre (m : Ideal T) [m.IsMaximal]
    (h : finrank m.ResidueField (m.ResidueField ⊗[T] Ω[T⁄F]) =
      finrank (⊥ : Ideal T).ResidueField ((⊥ : Ideal T).ResidueField ⊗[T] Ω[T⁄F])) :
    IsRegularLocalRing (Localization.AtPrime m) := by
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing F T
  have : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl _ inferInstance
  have : Algebra.EssFiniteType F (Localization.AtPrime m) := Algebra.EssFiniteType.comp F T _
  have : Algebra.FormallySmooth F (ResidueField (Localization.AtPrime m)) :=
    formallySmooth_residueField_of_isMaximal m
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
    height_eq_ringKrullDim_of_isMaximal F T m, ← finrank_fibre_bot_eq_ringKrullDim (F := F), ← h,
    DifferentialsNonsingular.finrank_tensor_kaehler_localization m.primeCompl
      (Localization.AtPrime m) m.ResidueField]
  exact_mod_cast finrank_cotangentSpace_le_finrank_fibre F (Localization.AtPrime m)

/-- Let `T` be a finitely generated domain over a perfect field `F`. If the fibre of `Ω_{T/F}`
at every maximal ideal has the same dimension as the fibre at the generic point, then every
localization `T_q` at a prime is a regular local ring. -/
theorem isRegularLocalRing_localization_of_forall_finrank_fibre
    (h : ∀ (m : Ideal T) [m.IsMaximal], finrank m.ResidueField (m.ResidueField ⊗[T] Ω[T⁄F]) =
      finrank (⊥ : Ideal T).ResidueField ((⊥ : Ideal T).ResidueField ⊗[T] Ω[T⁄F]))
    (q : Ideal T) [q.IsPrime] : IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q (Ideal.IsPrime.ne_top ‹_›)
  have : IsRegularLocalRing (Localization.AtPrime m) :=
    isRegularLocalRing_localization_of_finrank_fibre m (h m)
  -- `T_q` is a localization of `T_m` (Theorem 8.14A)
  have hdisj : Disjoint (m.primeCompl : Set T) q :=
    Set.disjoint_left.mpr fun s hs hsq => hs (hqm hsq)
  let p := q.map (algebraMap T (Localization.AtPrime m))
  have : p.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ _ ‹_› hdisj
  have hp : p.under T = q :=
    IsLocalization.under_map_of_isPrime_disjoint m.primeCompl _ ‹_› hdisj
  have : IsRegularLocalRing (Localization.AtPrime p) :=
    RegularLocal.isRegularLocalRing_localization_atPrime _ p
  have hl : IsLocalization.AtPrime (Localization.AtPrime p) q := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := m.primeCompl) (S := Localization.AtPrime m) (T := Localization.AtPrime p) p
    have hp' : p.comap (algebraMap T (Localization.AtPrime m)) = q := hp
    convert this
    exact hp'.symm
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q)).toRingEquiv

end Algebra

end DenseNonsingular

open DenseNonsingular in
/-- **Hartshorne II, Corollary 8.16.** If `X` is an integral scheme locally of finite type over a
perfect field `k`, then the regular points of `X` contain a nonempty open dense subset.
Hartshorne states this for a variety over an algebraically closed field; separatedness and
finite type beyond local finite type are not used, and perfectness of `k` suffices.

The proof is Hartshorne's: the stalk of the coherent sheaf `Ω_{X/k}` at the generic point is a
vector space over the function field `K`, so `Ω_{X/k}` is free on a nonempty open set `W`
(Exercise II.5.7), with fibres of constant dimension `dim_K Ω_{K/k} = tr.deg_k K` (I, 4.8A and
Theorem 8.6A), and `W` is nonsingular by the argument of Theorem 8.15. -/
theorem exists_nonempty_dense_isRegularAt {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Dense (U : Set X) ∧ ∀ x ∈ U, X.IsRegularAt x := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  -- (Ex. II.5.7) `Ω_{X/k}` is free near the generic point, whose stalk is a vector space
  obtain ⟨W, hηW, I, ⟨α⟩⟩ := exists_isFree_restrict_of_free_stalk_of_isLocallyNoetherian
    (Scheme.relativeDifferentials f)
    (Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f) (genericPoint X)
    inferInstance
  refine ⟨W, ⟨_, hηW⟩, W.isOpen.dense ⟨_, hηW⟩, fun x hx => ?_⟩
  -- the base ring `Γ(Spec k, ⊤) ≅ k` is a perfect field
  let eA := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eA.toMulEquiv.isField (Field.toIsField k)).toField
  have : PerfectField Γ(Spec (.of k), ⊤) := PerfectField.of_ringEquiv eA.symm
  -- an affine chart `Spec T ⊆ W` around `x`
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  replace hVW : V ≤ W := hVW
  let U : X.affineOpens := ⟨V, hV⟩
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hUV : V ≤ f ⁻¹ᵁ ⊤ := le_top
  let : Algebra Γ(Spec (.of k), ⊤) Γ(X, V) := (f.appLE ⊤ V hUV).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, V) :=
    f.finiteType_appLE (isAffineOpen_top _) hV hUV
  -- the fibres of `Ω_{T/k}` all have dimension `#I`
  have hfib (y : PrimeSpectrum Γ(X, V)) :
      finrank y.asIdeal.ResidueField
        (y.asIdeal.ResidueField ⊗[Γ(X, V)] Ω[Γ(X, V)⁄Γ(Spec (.of k), ⊤)]) =
        (Cardinal.mk I).toNat := by
    rw [← finrank_fibre_relativeDifferentials_affine f U ⟨⊤, isAffineOpen_top _⟩ hUV y]
    exact congrArg Cardinal.toNat (rank_fibre_of_restrict_iso_free _ α
      (hVW (DifferentialsNonsingular.fromSpec_mem U y)))
  -- (Theorem 8.15) hence every local ring of `Spec T` is regular
  set q := hV.primeIdealOf ⟨x, hxV⟩
  have hreg := isRegularLocalRing_localization_of_forall_finrank_fibre
    (F := Γ(Spec (.of k), ⊤)) (T := Γ(X, V))
    (fun m _ => (hfib ⟨m, inferInstance⟩).trans (hfib ⟨⊥, Ideal.isPrime_bot⟩).symm) q.asIdeal
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) (X.presheaf.stalk x)).toRingEquiv

end Hartshorne
