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

This follows the printed proof. Let `x` be a closed point. The local ring `B = 𝒪_{X,x}` has
dimension `n` (Exercise II.3.20(a), applied to the reduced scheme `X_red`, which is integral and
has the same underlying space and local dimensions as `X`) and residue field `k`. In an affine
chart `Spec T ∋ x`, where `x` is a maximal ideal `m ⊂ T`, `B = T_m` and the stalk `(Ω_{X/k})_x` is
the localization of `Ω_{T/k}` at `m`, as is `Ω_{B/k}`. By Theorem 8.8, `(Ω_{X/k})_x` is free of
rank `n` if and only if `B` is regular.

* If `Ω_{X/k}` is locally free of rank `n`, every local ring at a closed point is regular. Every
  point specializes to a closed point (finite-type `k`-schemes are Jacobson), and its local ring
  is a localization of the one there, hence regular by Theorem 8.14A.
* If `X` is nonsingular, `Ω_{X/k}` is free of rank `n` near every closed point (Exercise
  II.5.7), and these neighbourhoods cover `X`, since every point specializes to a closed point.

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

section Stalk

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Two presentations of the same localization of a module are free together: if `f : M → M'`
and `g : M → M''` are localizations at `S`, `M'` is a module over a localization `R₁` and `M''`
over a localization `R₂` of `R` at `S`, then `M'` is free over `R₁` iff `M''` is free over
`R₂`. -/
theorem free_iff_of_isLocalizedModule {R : Type*} [CommRing R] (S : Submonoid R)
    {M M' M'' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M''] (f : M →ₗ[R] M') (g : M →ₗ[R] M'')
    [IsLocalizedModule S f] [IsLocalizedModule S g]
    (R₁ R₂ : Type*) [CommRing R₁] [CommRing R₂] [Algebra R R₁] [Algebra R R₂]
    [IsLocalization S R₁] [IsLocalization S R₂] [Module R₁ M'] [IsScalarTower R R₁ M']
    [Module R₂ M''] [IsScalarTower R R₂ M''] :
    Module.Free R₁ M' ↔ Module.Free R₂ M'' := by
  let σ := (IsLocalization.algEquiv S R₁ R₂).toRingEquiv
  refine Module.Free.iff_of_equiv (σ := (σ : R₁ →+* R₂))
    { __ := IsLocalizedModule.linearEquiv S f g, map_smul' := ?_ }
  intro r x
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S r
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)).1
  simp [σ, ← map_smul, ← smul_assoc]

attribute [local instance] FreeLocusAux.freeLocusStalkAlgebra
  FreeLocusAux.freeLocus_asIdeal_isPrime FreeLocusAux.freeLocus_stalk_isLocalization
  FreeLocusAux.freeLocusStalkModule FreeLocusAux.freeLocus_stalk_isScalarTower

/-- The stalk of `Ω_{X/Y}` at a point is the module of differentials of the local ring: on affine
opens `U ⊆ f⁻¹ V`, with `A = Γ(Y, V)` and `T = Γ(X, U)`, the stalk at the point given by a prime
`q ⊂ T` is free over `𝒪_{X,x}` exactly when `Ω_{T_q/A}` is free over `T_q`, since both are the
localization of `Ω_{T/A}` at `q`. -/
theorem free_stalk_relativeDifferentials_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (h : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens))
    (y : Spec Γ(X, (U : X.Opens))) :
    letI := (f.appLE V U h).hom.toAlgebra
    Module.Free (X.presheaf.stalk (U.2.fromSpec y))
        ((Scheme.relativeDifferentials f).presheaf.stalk (U.2.fromSpec y)) ↔
      Module.Free (Localization.AtPrime y.asIdeal)
        Ω[Localization.AtPrime y.asIdeal⁄Γ(Y, (V : Y.Opens))] := by
  let := (f.appLE V U h).hom.toAlgebra
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  rw [FreeLocusAux.free_stalk_restrict_iff U.2.fromSpec]
  let T := Γ(X, (U : X.Opens))
  let G := (Scheme.relativeDifferentials f).restrict U.2.fromSpec
  let hG : G ≅ (tilde.functor T).obj (ModuleCat.of T Ω[T⁄Γ(Y, (V : Y.Opens))]) :=
    RelDiffLocal.affineIso f U V h
  have : IsIso (Scheme.Modules.fromTildeΓ (R := T) G) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨hG.symm⟩⟩
  have hloc : IsLocalizing (modulesSpecToSheaf.obj G) :=
    (isIso_fromTildeΓ_iff_isLocalizing _).mp this
  have := FreeLocusAux.isLocalizedModule_germTopLinear G hloc y
  let e : Γ(G, ⊤) ≃ₗ[T] Ω[T⁄Γ(Y, (V : Y.Opens))] :=
    (moduleSpecΓFunctor.mapIso hG ≪≫ (tilde.toTildeΓNatIso.app _).symm).toLinearEquiv
  exact free_iff_of_isLocalizedModule y.asIdeal.primeCompl
    (FreeLocusAux.germTopLinear G y ∘ₗ e.symm.toLinearMap)
    (KaehlerDifferential.map Γ(Y, (V : Y.Opens)) Γ(Y, (V : Y.Opens)) T
      (Localization.AtPrime y.asIdeal)) _ _

/-- On a scheme locally of finite type over `Y`, every fibre `(Ω_{X/Y})_x ⊗ k(x)` is finite
dimensional. -/
theorem finite_fibre_relativeDifferentials {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    Module.Finite (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
        (Scheme.relativeDifferentials f).presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hfxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ V from hfxV)
      (f ⁻¹ᵁ V).2
  let Ua : X.affineOpens := ⟨U, hU⟩
  let Va : Y.affineOpens := ⟨V, hV⟩
  replace hUV : (Ua : X.Opens) ≤ f ⁻¹ᵁ (Va : Y.Opens) := hUV
  let := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, V) Γ(X, U) := f.finiteType_appLE hV hU hUV
  obtain ⟨y, rfl⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  rw [← Module.rank_lt_aleph0_iff, rank_fibre_relativeDifferentials_affine f Ua Va hUV y]
  exact Module.rank_lt_aleph0 _ _

end Stalk

section Closed

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The point of `X` given by a maximal ideal of the ring of an affine open is closed, when `X`
is locally of finite type over a field (so a Jacobson space). -/
theorem isClosed_fromSpec_of_isMaximal [LocallyOfFiniteType f] (U : X.affineOpens)
    (y : Spec Γ(X, (U : X.Opens))) (hy : y.asIdeal.IsMaximal) :
    IsClosed ({U.2.fromSpec y} : Set X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  apply isClosed_singleton_of_isLocallyClosed_singleton
  have h1 : IsLocallyClosed ({y} : Set (Spec Γ(X, (U : X.Opens)))) :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hy).isLocallyClosed
  have h2 := h1.image U.2.fromSpec.isOpenEmbedding.isInducing
    U.2.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
  simpa using h2

/-- A closed point of `X` lying in an affine open corresponds to a maximal ideal of its ring. -/
theorem isMaximal_of_isClosed_fromSpec {X : Scheme.{u}} (U : X.affineOpens)
    (y : Spec Γ(X, (U : X.Opens))) (hy : IsClosed ({U.2.fromSpec y} : Set X)) :
    y.asIdeal.IsMaximal := by
  have : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  have hpre : U.2.fromSpec ⁻¹' {U.2.fromSpec y} = {y} :=
    Set.ext fun a => ⟨fun ha => U.2.fromSpec.isOpenEmbedding.injective ha,
      fun ha => by rw [Set.mem_singleton_iff.mp ha]; rfl⟩
  have := hy.preimage U.2.fromSpec.continuous
  rw [hpre] at this
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp this

/-- Inside any affine open `U = Spec T` containing it, every point of a scheme locally of finite
type over a field specializes to a closed point: if the point corresponds to the prime `q ⊂ T`,
take a maximal ideal `m ⊇ q`. -/
theorem exists_isMaximal_specializes [LocallyOfFiniteType f] (U : X.affineOpens)
    (y : Spec Γ(X, (U : X.Opens))) :
    ∃ z : Spec Γ(X, (U : X.Opens)), y.asIdeal ≤ z.asIdeal ∧ z.asIdeal.IsMaximal ∧
      IsClosed ({U.2.fromSpec z} : Set X) ∧ U.2.fromSpec y ⤳ U.2.fromSpec z := by
  obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal y.asIdeal y.isPrime.ne_top
  let z : Spec Γ(X, (U : X.Opens)) := ⟨m, hm.isPrime⟩
  exact ⟨z, hqm, hm, isClosed_fromSpec_of_isMaximal f U z hm,
    ((PrimeSpectrum.le_iff_specializes y z).mp hqm).map U.2.fromSpec.continuous⟩

/-- Every point of a scheme lies in the image of some affine open chart. -/
theorem exists_fromSpec_eq {X : Scheme.{u}} (x : X) :
    ∃ (U : X.affineOpens) (y : Spec Γ(X, (U : X.Opens))), U.2.fromSpec y = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hU.primeIdealOf ⟨x, hxU⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩

/-- On a scheme locally of finite type over a field, if the local rings at all closed points are
regular, then all local rings are regular: each local ring is a localization of the local ring at
a closed point, and localizations of regular local rings are regular (Theorem 8.14A). -/
theorem forall_isRegularAt_of_forall_isClosed [LocallyOfFiniteType f]
    (h : ∀ z : X, IsClosed ({z} : Set X) → X.IsRegularAt z) (x : X) : X.IsRegularAt x := by
  obtain ⟨U, y, rfl⟩ := exists_fromSpec_eq x
  obtain ⟨z, hqm, -, hz, -⟩ := exists_isMaximal_specializes f U y
  let T := Γ(X, (U : X.Opens))
  let m := z.asIdeal
  have : m.IsPrime := z.isPrime
  have hstalk (w : Spec T) := U.2.isLocalization_stalk' w (fromSpec_mem U w)
  have hregm : IsRegularLocalRing (Localization.AtPrime m) := by
    have : IsRegularLocalRing (X.presheaf.stalk (U.2.fromSpec z)) := h _ hz
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨U.2.fromSpec z, fromSpec_mem U z⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec z)) m := hstalk z
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv m.primeCompl (X.presheaf.stalk (U.2.fromSpec z))
        (Localization.AtPrime m)).toRingEquiv
  -- `T_q` is a localization of `T_m`, hence regular (Theorem 8.14A)
  have : y.asIdeal.IsPrime := y.isPrime
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

/-- **Hartshorne II, proof of Theorem 8.15**, the local step. Let `X` be of finite type over an
algebraically closed field `k`, and let `x` be a closed point whose local ring `B = 𝒪_{X,x}` has
dimension `n`. Then `B` has residue field `k`, `Ω_{B/k}` is the stalk `(Ω_{X/k})_x`, and by
Theorem 8.8 the stalk `(Ω_{X/k})_x` is free of rank `n` (free, with fibre `(Ω_{X/k})_x ⊗ k(x)` of
dimension `n`) if and only if `B` is a regular local ring. -/
theorem isRegularAt_iff_free_stalk_relativeDifferentials [IsAlgClosed k] (hf : FiniteType f)
    (n : ℕ) (x : X) (hx : IsClosed ({x} : Set X)) (hdim : ringKrullDim (X.presheaf.stalk x) = n) :
    X.IsRegularAt x ↔
      Module.Free (X.presheaf.stalk x) ((Scheme.relativeDifferentials f).presheaf.stalk x) ∧
        finrank (ResidueField (X.presheaf.stalk x))
          (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x]
            (Scheme.relativeDifferentials f).presheaf.stalk x) = n := by
  have : LocallyOfFiniteType f := hf.1
  -- the base ring `Γ(Spec k, ⊤) ≅ k` is an algebraically closed field
  let eA := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eA.toMulEquiv.isField (Field.toIsField k)).toField
  have : IsAlgClosed Γ(Spec (.of k), ⊤) := IsAlgClosed.of_ringEquiv k _ eA.symm
  let V : (Spec (.of k)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨U, y, rfl⟩ := exists_fromSpec_eq x
  have hm : y.asIdeal.IsMaximal := isMaximal_of_isClosed_fromSpec U y hx
  let T := Γ(X, (U : X.Opens))
  have hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : (Spec (.of k)).Opens) := le_top
  let : Algebra Γ(Spec (.of k), ⊤) T := (f.appLE ⊤ U hUV).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of k), ⊤) T := f.finiteType_appLE V.2 U.2 hUV
  -- `B = 𝒪_{X,x}` is the localization `T_m` at the maximal ideal `m` of `x`
  let B := Localization.AtPrime y.asIdeal
  have : Algebra.EssFiniteType Γ(Spec (.of k), ⊤) B := Algebra.EssFiniteType.comp _ T _
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨U.2.fromSpec y, fromSpec_mem U y⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec y)) y.asIdeal :=
    U.2.isLocalization_stalk' y (fromSpec_mem U y)
  let eB : X.presheaf.stalk (U.2.fromSpec y) ≃+* B :=
    (IsLocalization.algEquiv y.asIdeal.primeCompl _ B).toRingEquiv
  -- `B` has dimension `n` and residue field `k`
  have hdimB : ringKrullDim B = n := (ringKrullDim_eq_of_ringEquiv eB).symm.trans hdim
  have hbij := bijective_algebraMap_residueField (k := Γ(Spec (.of k), ⊤)) y.asIdeal
  -- the fibre of `Ω_{X/k}` at `x` is the fibre of `Ω_{B/k}`
  have hfib : finrank (ResidueField (X.presheaf.stalk (U.2.fromSpec y)))
      (ResidueField (X.presheaf.stalk (U.2.fromSpec y)) ⊗[X.presheaf.stalk (U.2.fromSpec y)]
        (Scheme.relativeDifferentials f).presheaf.stalk (U.2.fromSpec y)) =
      finrank y.asIdeal.ResidueField (y.asIdeal.ResidueField ⊗[B] Ω[B⁄Γ(Spec (.of k), ⊤)]) := by
    rw [finrank_fibre_relativeDifferentials_affine f U V hUV y]
    exact finrank_tensor_kaehler_localization y.asIdeal.primeCompl B _
  have hreg : X.IsRegularAt (U.2.fromSpec y) ↔ IsRegularLocalRing B :=
    ⟨fun h => have : IsRegularLocalRing (X.presheaf.stalk (U.2.fromSpec y)) := h
      IsRegularLocalRing.of_ringEquiv eB,
      fun h => have := h; IsRegularLocalRing.of_ringEquiv eB.symm⟩
  -- Theorem 8.8
  rw [hreg, isRegularLocalRing_iff_free_kaehlerDifferential _ B hbij, hdimB, hfib,
    free_stalk_relativeDifferentials_iff f U V hUV y]
  constructor
  · rintro ⟨hfree, hrank⟩
    exact ⟨hfree, by rw [Module.finrank_baseChange]; exact_mod_cast hrank⟩
  · rintro ⟨hfree, hrank⟩
    rw [Module.finrank_baseChange] at hrank
    exact ⟨hfree, by rw [hrank]⟩

end Closed

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
  -- at a closed point `x`, `𝒪_{X,x}` has dimension `n` (Exercise II.3.20(a)), so by
  -- Theorem 8.8 the stalk of `Ω_{X/k}` there is free of rank `n` iff `𝒪_{X,x}` is regular
  have key (x : X) (hx : IsClosed ({x} : Set X)) :=
    isRegularAt_iff_free_stalk_relativeDifferentials f hf n x hx
      (ringKrullDim_stalk_of_isClosed f hf hn x hx)
  let F := Scheme.relativeDifferentials f
  constructor
  · intro hX
    -- `Ω_{X/k}` is free of rank `n` near every closed point (Exercise II.5.7), and every point
    -- specializes to a closed point, so these neighbourhoods cover `X`
    have hnbhd (x : X) : ∃ W : X.Opens, x ∈ W ∧
        ∃ I : Type u, Nonempty (F.restrict W.ι ≅ SheafOfModules.free I) ∧
          Cardinal.mk I = n := by
      obtain ⟨U, y, rfl⟩ := exists_fromSpec_eq x
      obtain ⟨z, -, -, hz, hyz⟩ := exists_isMaximal_specializes f U y
      obtain ⟨hfree, hrank⟩ := (key _ hz).1 (hX.2 _)
      obtain ⟨W, hzW, I, ⟨α⟩⟩ := exists_isFree_restrict_of_free_stalk_of_isLocallyNoetherian F
        (Scheme.relativeDifferentials_isCoherent_of_locallyOfFiniteType f) _ hfree
      refine ⟨W, hyz.mem_open W.2 hzW, I, ⟨α⟩, ?_⟩
      have := finite_fibre_relativeDifferentials f (U.2.fromSpec z)
      rw [← rank_fibre_of_restrict_iso_free F α hzW, ← Module.finrank_eq_rank, hrank]
    refine (F.isLocallyFreeOfRank_iff n).mpr ⟨fun x => ?_, fun x => ?_⟩
    · obtain ⟨W, hxW, I, hα, -⟩ := hnbhd x
      exact ⟨W, hxW, I, hα⟩
    · obtain ⟨W, hxW, I, ⟨α⟩, hI⟩ := hnbhd x
      rw [F.rankAt_eq α hxW, hI]
  · intro h
    -- the stalks of `Ω_{X/k}` at closed points are free of rank `n`, so the local rings there
    -- are regular; every local ring is a localization of one of these (Theorem 8.14A)
    have hlf : F.IsLocallyFree := ((F.isLocallyFreeOfRank_iff n).mp h).1
    exact ⟨inferInstance, forall_isRegularAt_of_forall_isClosed f fun z hz =>
      (key z hz).2 ⟨free_stalk_of_isLocallyFree F hlf z,
        finrank_fibre_of_isLocallyFreeOfRank F n h z⟩⟩

end

end Hartshorne
