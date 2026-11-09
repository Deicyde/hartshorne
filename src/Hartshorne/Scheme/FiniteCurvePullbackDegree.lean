/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteCurveDivisorPullback
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# The degree of the pullback of a divisor along a finite morphism of curves

Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.9 (p. 138).

Let `f : X ⟶ Y` be a finite morphism of nonsingular curves over an algebraically closed field
`k`. For every divisor `D` on `Y`, `deg f^*D = deg f · deg D`.

By additivity it suffices to treat a closed point `Q` of `Y`, where the claim is
`∑_{f(P) = Q} ord_P(t) = [K(X) : K(Y)]` for a local parameter `t` at `Q`. Choose an affine open
`V ∋ Q`; then `A = Γ(Y, V)` is a Dedekind domain and `B = Γ(X, f⁻¹V)` is a finite torsion-free,
hence flat, `A`-algebra. The points of `X` over `Q` correspond to the primes of `B` over the
maximal ideal `p` of `Q`; the ramification index of such a prime is the length of
`𝒪_{X,P} / t 𝒪_{X,P}`, which is `ord_P(t)`; its inertia degree is `1` because both residue
fields are `k`; and `rank_A B = [K(X) : K(Y)]`. The fundamental identity
`∑ e_q f_q = rank_A B` for finite flat algebras over a domain gives the result.
-/

noncomputable section

open CategoryTheory Limits Order TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- For a finitely generated algebra `A` over an algebraically closed field `K`, a finite
`A`-algebra `B`, a maximal ideal `p` of `A` and a prime `q` of `B` over `p`, the inertia degree
of `q` over `A` is `1`: both residue fields are `K`. -/
theorem inertiaDeg_eq_one_of_isAlgClosed {K A B : Type*} [Field K] [IsAlgClosed K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra.FiniteType K A] [Module.Finite A B] (p : Ideal A) [p.IsMaximal] (q : Ideal B)
    [q.IsPrime] [q.LiesOver p] : q.inertiaDeg A = 1 := by
  have : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q p
  rw [Ideal.inertiaDeg_eq_of_isMaximal p q]
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Field (B ⧸ q) := Ideal.Quotient.field q
  have : Algebra.FiniteType K B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : Algebra.FiniteType K (B ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K q) Ideal.Quotient.mk_surjective
  have : Module.Finite K (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing K _
  have hbij : Function.Bijective (algebraMap K (B ⧸ q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hsurj : Function.Surjective (algebraMap (A ⧸ p) (B ⧸ q)) := by
    intro y
    obtain ⟨c, rfl⟩ := hbij.2 y
    refine ⟨Ideal.Quotient.mk p (algebraMap K A c), ?_⟩
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, ← IsScalarTower.algebraMap_apply]
    rfl
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap (A ⧸ p) (B ⧸ q))
    ⟨(algebraMap (A ⧸ p) (B ⧸ q)).injective, hsurj⟩).finrank_eq, Module.finrank_self]

namespace Scheme.IsNonsingularCurve

section OneCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- The ring of sections of a nonsingular curve over a nonempty affine open subset is a
Dedekind domain. -/
theorem isDedekindDomain_of_isAffineOpen (hX : X.IsNonsingularCurve k) {V : X.Opens}
    (hV : IsAffineOpen V) [Nonempty V] : IsDedekindDomain Γ(X, V) := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsDedekindDomainDvr Γ(X, V) :=
    { toIsNoetherian := inferInstance
      is_dvr_at_nonzero_prime := by
        intro P hP hPrime
        let y : PrimeSpectrum Γ(X, V) := ⟨P, hPrime⟩
        have hy : hV.fromSpec y ∈ V := hV.range_fromSpec.subset ⟨y, rfl⟩
        let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hV.fromSpec y, hy⟩
        have hloc : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) P :=
          hV.isLocalization_stalk' y hy
        by_cases hx : coheight (hV.fromSpec y) = 1
        · have := X.codimensionOneStalk_isDiscreteValuationRing hX.satisfiesConditionStar hx
          exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
            (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hV.fromSpec y))
              (Localization.AtPrime P)).toRingEquiv
        · exfalso
          have hgen : hV.fromSpec y = genericPoint X := by
            by_contra h
            exact hx ((hX.coheight_eq_one_iff _).mpr h)
          have hfield : IsField (X.presheaf.stalk (hV.fromSpec y)) := by
            rw [hgen]
            exact Field.toIsField X.functionField
          obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
          have hmem : algebraMap Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) a ∈
              IsLocalRing.maximalIdeal _ :=
            (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P a).mpr haP
          have hne : algebraMap Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) a ≠ 0 :=
            fun h ↦ ha0 (germ_injective_of_isIntegral X _ hy (h.trans (map_zero _).symm))
          obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
          exact (IsLocalRing.mem_maximalIdeal _).mp hmem (IsUnit.of_mul_eq_one b hb) }
  infer_instance

/-- The degree of a divisor on a curve is the sum of its coefficients over any finite set
containing its support. -/
theorem divisorDegree_eq_sum (hX : X.IsNonsingularCurve k) (D : X.WeilDivisor) (s : Finset X)
    (hs : Function.support D.1 ⊆ s) : hX.divisorDegree D = ∑ x ∈ s, D.1 x := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  rw [divisorDegree_apply, Finsupp.sum]
  refine Finset.sum_bij_ne_zero (fun P _ _ ↦ P.1) (fun P _ hP ↦ hs hP) ?_ ?_ ?_
  · intro P _ _ P' _ _ h
    exact Subtype.ext h
  · intro x _ hx
    have hc : coheight x = 1 := by
      by_contra hc
      exact hx (D.2 x hc)
    exact ⟨⟨x, hc⟩, Finsupp.mem_support_iff.mpr hx, hx, rfl⟩
  · intro P _ _
    rfl

end OneCurve

section TwoCurves

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] [IsIntegral X] [IsIntegral Y]

/-- `f^# : K(Y) → K(X)` is compatible with `f^# : Γ(Y, V) → Γ(X, f⁻¹V)`. -/
theorem finiteCurveFunctionFieldMap_germToFunctionField (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [LocallyQuasiFinite f] (V : Y.Opens)
    [Nonempty V] [Nonempty (f ⁻¹ᵁ V)] (a : Γ(Y, V)) :
    hX.finiteCurveFunctionFieldMap hY f (Y.germToFunctionField V a) =
      X.germToFunctionField (f ⁻¹ᵁ V) (f.app V a) := by
  change f.stalkMap _ (Y.presheaf.stalkSpecializes _ (Y.presheaf.germ V _ _ a)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

/-- The rank of `Γ(X, f⁻¹V)` over `Γ(Y, V)` is the degree `[K(X) : K(Y)]` of `f`. -/
theorem finrank_sections_eq_finiteCurveDegree (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] {V : Y.Opens} (hV : IsAffineOpen V)
    [Nonempty V] [Nonempty (f ⁻¹ᵁ V)] :
    letI := (f.app V).hom.toAlgebra
    Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = hX.finiteCurveDegree hY f := by
  let := (f.app V).hom.toAlgebra
  let := (hX.finiteCurveFunctionFieldMap hY f).toAlgebra
  let : Algebra Γ(Y, V) X.functionField :=
    ((algebraMap Γ(X, f ⁻¹ᵁ V) X.functionField).comp (algebraMap Γ(Y, V) _)).toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) X.functionField := .of_algebraMap_eq' rfl
  have : IsScalarTower Γ(Y, V) Y.functionField X.functionField :=
    .of_algebraMap_eq fun a ↦ (hX.finiteCurveFunctionFieldMap_germToFunctionField hY f V a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y V hV
  have := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ V) (hV.preimage f)
  exact (IsFractionRing.finrank_eq Γ(Y, V) Y.functionField Γ(X, f ⁻¹ᵁ V) X.functionField).symm

omit [IsIntegral X] [IsIntegral Y] in
/-- The prime of `Γ(X, f⁻¹V)` at a point `x` lies over the prime of `Γ(Y, V)` at `f x`. -/
theorem liesOver_primeIdealOf (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V)) {x : X} (hx : x ∈ f ⁻¹ᵁ V) :
    letI := (f.app V).hom.toAlgebra
    (hV'.primeIdealOf ⟨x, hx⟩).asIdeal.LiesOver (hV.primeIdealOf ⟨f x, hx⟩).asIdeal := by
  let := (f.app V).hom.toAlgebra
  refine ⟨?_⟩
  have h := IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hV' le_rfl hx
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact (congrArg PrimeSpectrum.asIdeal h).symm

/-- The ramification index of the prime of `Γ(X, f⁻¹V)` at a point `x` over a closed point
`f x` is the multiplicity `ord_x(t)` of `x` in `f^*(f x)`. -/
theorem ramificationIdx_primeIdealOf (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] {V : Y.Opens} (hV : IsAffineOpen V)
    {x : X} (hx : x ∈ f ⁻¹ᵁ V) (hx1 : coheight (f x) = 1) :
    letI := (f.app V).hom.toAlgebra
    ((((hV.preimage f).primeIdealOf ⟨x, hx⟩).asIdeal.ramificationIdx Γ(Y, V) : ℕ) : ℤ) =
      hX.finiteCurvePullbackMultiplicity hY f x := by
  let := (f.app V).hom.toAlgebra
  let _ := hX.satisfiesConditionStar.isNoetherian
  let _ := hY.satisfiesConditionStar.isNoetherian
  set q := (hV.preimage f).primeIdealOf ⟨x, hx⟩
  set p := hV.primeIdealOf ⟨f x, hx⟩
  have : q.asIdeal.LiesOver p.asIdeal := liesOver_primeIdealOf f hV (hV.preimage f) hx
  rw [Ideal.ramificationIdx_eq p.asIdeal q.asIdeal]
  -- pass from `Γ(X, f⁻¹V)_q` to the stalk `𝒪_{X,x}`
  let : Algebra Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    (hV.preimage f).isLocalization_stalk ⟨x, hx⟩
  let : Algebra Γ(Y, V) (X.presheaf.stalk x) :=
    ((algebraMap Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x)).comp (algebraMap Γ(Y, V) _)).toAlgebra
  have : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x) := .of_algebraMap_eq' rfl
  let e : Localization.AtPrime q.asIdeal ≃ₐ[Γ(X, f ⁻¹ᵁ V)] X.presheaf.stalk x :=
    IsLocalization.algEquiv q.asIdeal.primeCompl _ _
  let : Algebra (Localization.AtPrime q.asIdeal) (X.presheaf.stalk x) := e.toRingHom.toAlgebra
  have : IsScalarTower Γ(Y, V) (Localization.AtPrime q.asIdeal) (X.presheaf.stalk x) :=
    .of_algebraMap_eq fun a ↦ by
      rw [IsScalarTower.algebraMap_apply Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x),
        IsScalarTower.algebraMap_apply Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (Localization.AtPrime q.asIdeal)]
      exact (e.commutes _).symm
  let e' : (Localization.AtPrime q.asIdeal ⧸
        p.asIdeal.map (algebraMap Γ(Y, V) (Localization.AtPrime q.asIdeal))) ≃ₐ[_]
      X.presheaf.stalk x ⧸ p.asIdeal.map (algebraMap Γ(Y, V) (X.presheaf.stalk x)) :=
    Ideal.quotientEquivAlg _ _ (AlgEquiv.ofBijective (Algebra.ofId _ _) e.bijective)
      (by
        rw [IsScalarTower.algebraMap_eq Γ(Y, V) (Localization.AtPrime q.asIdeal)
          (X.presheaf.stalk x), ← Ideal.map_map]
        rfl)
  rw [e'.toLinearEquiv.length_eq, Module.length_eq_of_surjective e.surjective]
  -- the extension of `p` to `𝒪_{X,x}` is generated by the image of a local parameter at `f x`
  set t := hY.localParameter (f x)
  have ht := hY.irreducible_localParameter hx1
  have := Y.codimensionOneStalk_isDiscreteValuationRing hY.satisfiesConditionStar hx1
  have hmap : p.asIdeal.map (algebraMap Γ(Y, V) (X.presheaf.stalk x)) =
      Ideal.span {f.stalkMap x t} := by
    let : Algebra Γ(Y, V) (Y.presheaf.stalk (f x)) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨f x, hx⟩
    have : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) p.asIdeal :=
      hV.isLocalization_stalk ⟨f x, hx⟩
    have hcomp : algebraMap Γ(Y, V) (X.presheaf.stalk x) =
        (f.stalkMap x).hom.comp (algebraMap Γ(Y, V) (Y.presheaf.stalk (f x))) := by
      ext a
      exact (Scheme.Hom.germ_stalkMap_apply f V x hx a).symm
    rw [hcomp, ← Ideal.map_map, IsLocalization.AtPrime.map_eq_maximalIdeal,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht, Ideal.map_span,
      Set.image_singleton]
  rw [hmap]
  -- compare with the order of vanishing
  have hx1' : coheight x = 1 := hX.coheight_eq_one_of_coheight_apply_eq_one hY f hx1
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx1'.le
  have ht0 : algebraMap _ Y.functionField t ≠ 0 := by
    simpa [map_ne_zero_iff _ (IsFractionRing.injective _ _)] using ht.ne_zero
  have hs0 : algebraMap _ X.functionField (f.stalkMap x t) ≠ 0 := by
    rw [← hX.finiteCurveFunctionFieldMap_algebraMap hY f]
    exact (map_ne_zero _).mpr ht0
  have hs : f.stalkMap x t ≠ 0 := fun h ↦ hs0 (by rw [h, map_zero])
  change _ = X.ord (hX.finiteCurveFunctionFieldMap hY f (algebraMap _ _ t)) x
  rw [finiteCurveFunctionFieldMap_algebraMap, eq_comm, X.ord_eq_iff hx1' hs0]
  change Ring.ordFrac (X.presheaf.stalk x) _ = _
  rw [Ring.ordFrac_eq_ord _ hs]
  exact Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hs)
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hs))).symm

omit [X.Over (Spec (.of k))] [IsIntegral X] in
/-- The inertia degree of the prime of `Γ(X, f⁻¹V)` at a point `x` over a closed point `f x`
is `1`. -/
theorem inertiaDeg_primeIdealOf [IsAlgClosed k] (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y)
    [IsFinite f] {V : Y.Opens} (hV : IsAffineOpen V) {x : X} (hx : x ∈ f ⁻¹ᵁ V)
    (hx1 : IsClosed ({f x} : Set Y)) :
    letI := (f.app V).hom.toAlgebra
    ((hV.preimage f).primeIdealOf ⟨x, hx⟩).asIdeal.inertiaDeg Γ(Y, V) = 1 := by
  let := (f.app V).hom.toAlgebra
  have := hY.locallyOfFiniteType
  let eK := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of k), ⊤) := (eK.toMulEquiv.isField (Field.toIsField k)).toField
  have : IsAlgClosed Γ(Spec (.of k), ⊤) := IsAlgClosed.of_ringEquiv k _ eK.symm
  have hle : V ≤ (Y ↘ Spec (.of k)) ⁻¹ᵁ ⊤ := le_top
  let : Algebra Γ(Spec (.of k), ⊤) Γ(Y, V) := ((Y ↘ Spec (.of k)).appLE ⊤ V hle).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(Y, V) :=
    (Y ↘ Spec (.of k)).finiteType_appLE (isAffineOpen_top _) hV hle
  let : Algebra Γ(Spec (.of k), ⊤) Γ(X, f ⁻¹ᵁ V) :=
    ((algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)).comp (algebraMap Γ(Spec (.of k), ⊤) _)).toAlgebra
  have : IsScalarTower Γ(Spec (.of k), ⊤) Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := .of_algebraMap_eq' rfl
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  have : (hV.primeIdealOf ⟨f x, hx⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed _ hx1
  have : ((hV.preimage f).primeIdealOf ⟨x, hx⟩).asIdeal.LiesOver
      (hV.primeIdealOf ⟨f x, hx⟩).asIdeal := liesOver_primeIdealOf f hV (hV.preimage f) hx
  exact inertiaDeg_eq_one_of_isAlgClosed (K := Γ(Spec (.of k), ⊤))
    (hV.primeIdealOf ⟨f x, hx⟩).asIdeal _

/-- **The fibre sum.** For a closed point `Q` of `Y`, `∑_{f(P) = Q} ord_P(t) = deg f`. -/
theorem sum_finiteCurvePullbackMultiplicity [IsAlgClosed k] (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] {Q : Y}
    (hQ : IsClosed ({Q} : Set Y)) :
    ∑ x ∈ (f.finite_preimage_singleton Q).toFinset, hX.finiteCurvePullbackMultiplicity hY f x =
      hX.finiteCurveDegree hY f := by
  have hQ1 := (hY.isClosed_singleton_iff_coheight_eq_one Q).mp hQ
  obtain ⟨_, ⟨V, hV, rfl⟩, hQV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ Q) isOpen_univ
  have : Nonempty V := ⟨⟨Q, hQV⟩⟩
  have hU := hV.preimage f
  have hgen : genericPoint X ∈ f ⁻¹ᵁ V := by
    change f (genericPoint X) ∈ V
    rw [hX.apply_genericPoint_eq hY f]
    exact ((genericPoint_spec Y).mem_open_set_iff V.isOpen).mpr ⟨Q, trivial, hQV⟩
  have : Nonempty (f ⁻¹ᵁ V) := ⟨⟨_, hgen⟩⟩
  let := (f.app V).hom.toAlgebra
  have : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := f.finite_app V hV
  have : IsDedekindDomain Γ(Y, V) := hY.isDedekindDomain_of_isAffineOpen hV
  have hinj : Function.Injective (algebraMap Γ(Y, V) Γ(X, f ⁻¹ᵁ V)) := by
    intro a b hab
    apply Y.germToFunctionField_injective V
    apply (hX.finiteCurveFunctionFieldMap hY f).injective
    rw [finiteCurveFunctionFieldMap_germToFunctionField, finiteCurveFunctionFieldMap_germToFunctionField]
    exact congrArg (X.germToFunctionField (f ⁻¹ᵁ V)) hab
  have : FaithfulSMul Γ(Y, V) Γ(X, f ⁻¹ᵁ V) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let p := hV.primeIdealOf ⟨Q, hQV⟩
  have : p.asIdeal.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed _ hQ
  have : Fintype (p.asIdeal.primesOver Γ(X, f ⁻¹ᵁ V)) :=
    (Algebra.QuasiFinite.finite_primesOver p.asIdeal).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p.asIdeal Γ(X, f ⁻¹ᵁ V)
  rw [← hX.finrank_sections_eq_finiteCurveDegree hY f hV, ← hsum, Nat.cast_sum]
  have hmemU : ∀ x ∈ (f.finite_preimage_singleton Q).toFinset, x ∈ f ⁻¹ᵁ V := by
    intro x hx
    have hfx : f x = Q := (f.finite_preimage_singleton Q).mem_toFinset.mp hx
    change f x ∈ V
    rw [hfx]
    exact hQV
  have hpt : ∀ x (hx : x ∈ f ⁻¹ᵁ V), f x = Q →
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.LiesOver p.asIdeal := by
    intro x hx hfx
    have h := liesOver_primeIdealOf f hV hU hx
    have hpQ : hV.primeIdealOf ⟨f x, hx⟩ = p := by
      exact congrArg hV.primeIdealOf (Subtype.ext hfx)
    rwa [hpQ] at h
  refine Finset.sum_bij'
    (fun x hx ↦ ⟨(hU.primeIdealOf ⟨x, hmemU x hx⟩).asIdeal, (hU.primeIdealOf _).isPrime,
      hpt x _ ((f.finite_preimage_singleton Q).mem_toFinset.mp hx)⟩)
    (fun q _ ↦ hU.fromSpec ⟨q.1, q.2.1⟩) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ ?_ ?_
  · -- points of `Spec Γ(X, f⁻¹V)` over `p` lie in the fibre over `Q`
    intro q _
    have hqU : hU.fromSpec ⟨q.1, q.2.1⟩ ∈ f ⁻¹ᵁ V := hU.range_fromSpec.subset ⟨_, rfl⟩
    have hq : hU.primeIdealOf ⟨_, hqU⟩ = ⟨q.1, q.2.1⟩ :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hqU⟩)
    have h := liesOver_primeIdealOf f hV hU hqU
    rw [hq] at h
    have h2 : hV.primeIdealOf ⟨f (hU.fromSpec ⟨q.1, q.2.1⟩), hqU⟩ = p :=
      PrimeSpectrum.ext (h.1.trans q.2.2.1.symm)
    rw [Set.Finite.mem_toFinset]
    have h3 := congrArg hV.fromSpec h2
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at h3
  · intro x hx
    exact hU.fromSpec_primeIdealOf ⟨x, hmemU x hx⟩
  · intro q _
    have hqU : hU.fromSpec ⟨q.1, q.2.1⟩ ∈ f ⁻¹ᵁ V := hU.range_fromSpec.subset ⟨_, rfl⟩
    have hq : hU.primeIdealOf ⟨_, hqU⟩ = ⟨q.1, q.2.1⟩ :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hqU⟩)
    exact Subtype.ext (congrArg PrimeSpectrum.asIdeal hq)
  · intro x hx
    have hfx : f x = Q := (f.finite_preimage_singleton Q).mem_toFinset.mp hx
    have hx1 : IsClosed ({f x} : Set Y) := hfx ▸ hQ
    dsimp only
    rw [inertiaDeg_primeIdealOf hY f hV (hmemU x hx) hx1, mul_one,
      ramificationIdx_primeIdealOf hX hY f hV (hmemU x hx) (hfx ▸ hQ1)]

/-- **Hartshorne II.6.9.** For a finite morphism `f : X ⟶ Y` of nonsingular curves over an
algebraically closed field and a divisor `D` on `Y`, `deg f^*D = deg f · deg D`. -/
theorem divisorDegree_finiteCurveDivisorPullback [IsAlgClosed k] (hX : X.IsNonsingularCurve k)
    (hY : Y.IsNonsingularCurve k) (f : X ⟶ Y) [IsFinite f] [f.IsOver (Spec (.of k))]
    (D : Y.WeilDivisor) :
    hX.divisorDegree (hX.finiteCurveDivisorPullback hY f D) =
      hX.finiteCurveDegree hY f * hY.divisorDegree D := by
  classical
  let _ := hY.satisfiesConditionStar.isNoetherian
  obtain ⟨F, rfl⟩ := Y.weilDivisorAddEquivFinsupp.symm.surjective D
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F G hF hG => simp only [map_add, hF, hG, mul_add]
  | single Q n =>
    rw [← Finsupp.smul_single_one, map_zsmul, map_zsmul, map_zsmul, map_zsmul,
      finiteCurveDivisorPullback_primeDivisor, divisorDegree_single, smul_eq_mul, smul_eq_mul,
      mul_one, mul_comm]
    congr 1
    have hQ : IsClosed ({Q.1} : Set Y) := (hY.isClosed_singleton_iff_coheight_eq_one _).mpr Q.2
    rw [hX.divisorDegree_eq_sum _ (f.finite_preimage_singleton Q.1).toFinset
      ((finiteCurvePointPullback_support_subset hX hY f Q.1).1.trans (by simp)),
      ← hX.sum_finiteCurvePullbackMultiplicity hY f hQ]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    change (if f x = Q.1 then hX.finiteCurvePullbackMultiplicity hY f x else 0) = _
    exact if_pos ((f.finite_preimage_singleton Q.1).mem_toFinset.mp hx)

end TwoCurves

end Scheme.IsNonsingularCurve

end AlgebraicGeometry
