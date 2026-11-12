/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteCurveDivisorPullback
import Hartshorne.Scheme.ProjectiveIntersectionDegree
import Hartshorne.Scheme.ProjectiveIntersectionDegreeFormula
import Hartshorne.Intersection.ProjectivePointDegree
import Hartshorne.Projective.LinearSeparation
import Hartshorne.Scheme.InvertibleSectionDivisor
import Hartshorne.Scheme.VeryAmpleTensorProduct
import Hartshorne.Intersection.ProjectiveLinearSubspaceCycle
import Hartshorne.Scheme.RegularLocalFactorial

/-!
# The degree of an embedded curve and hyperplane sections

Hartshorne, *Algebraic Geometry*, IV, Example 3.3.2 (p. 309), first part of the proof.

Let `k` be algebraically closed and let `ι : X ⟶ ℙⁿ_k = Proj k[x₀, …, xₙ]` be a closed immersion
of a nonsingular curve. A closed point of `ℙⁿ_k` has projective degree one, so for a divisor `E`
on `X` the degree of `E` in the embedding (the weighted sum of the projective degrees of its
points) is the divisor degree `deg E` (`Hartshorne.weilDivisorProjectiveDegree_eq_divisorDegree`).
If the coordinate hyperplane `H = V(xᵢ)` does not contain `X`, then the generalized Bézout theorem
(II, Exercise 6.2(c)) with `deg H = 1` gives `deg ι(X) = deg (H · X)`
(`Hartshorne.projectiveSpectrumPointDegree_eq_divisorDegree_hyperplane`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝒜" => homogeneousSubmodule (Fin (n + 1)) k

local notation "S" => MvPolynomial (Fin (n + 1)) k

/-- Points are closed in classical projective space. -/
private theorem isClosed_singleton_projectiveSpace' (P : ProjectiveSpace k (Fin (n + 1))) :
    IsClosed ({P} : Set (ProjectiveSpace k (Fin (n + 1)))) := by
  rw [isClosed_iff_isProjAlgebraicSet]
  refine ⟨homogeneousVanishingSet {P},
    isHomogeneousSet_homogeneousVanishingSet {P},
    Set.Subset.antisymm (subset_projZeroSet_homogeneousVanishingSet {P}) ?_⟩
  intro Q hQ
  by_contra hQP
  have hPQ : P ≠ Q := by
    simpa [Set.mem_singleton_iff, eq_comm] using hQP
  obtain ⟨_, h, _, hh, _, _, hhP, hhQ⟩ :=
    exists_linear_forms_separating_projective_points hPQ
  apply hhQ
  exact hQ h ⟨⟨1, hh⟩, by
    intro R hRP
    rw [Set.mem_singleton_iff.mp hRP]
    exact hhP⟩

/-- **A closed point of `ℙⁿ_k` has degree one** (`k` algebraically closed): the zero set of its
homogeneous prime is a single classical point. -/
theorem projectiveSpectrumPointDegree_of_isClosed [IsAlgClosed k] (x : Proj 𝒜)
    (hx : IsClosed ({x} : Set (Proj 𝒜))) : projectiveSpectrumPointDegree x = 1 := by
  obtain ⟨hYv, hJ⟩ := isProjVariety_projZeroSet_asHomogeneousIdeal x
  obtain ⟨P, hP⟩ := hYv.1.nonempty
  set Q := homogeneousVanishingIdeal ({P} : Set (ProjectiveSpace k (Fin (n + 1))))
  have hQhom : IsHomogeneousIdeal Q := isHomogeneousIdeal_homogeneousVanishingIdeal _
  have hQprime : Q.IsPrime := isPrime_homogeneousVanishingIdeal_singleton P
  have hZQ : projZeroSet (Q : Set S) = {P} := by
    rw [projZeroSet_homogeneousVanishingIdeal_eq_closure,
      (isClosed_singleton_projectiveSpace' P).closure_eq]
  have hrel : ¬(HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Q :=
    (projZeroSet_nonempty_iff_not_irrelevant_le hQhom).mp (by rw [hZQ]; exact ⟨P, rfl⟩)
  let y : Proj 𝒜 := ⟨⟨Q, hQhom⟩, hQprime, hrel⟩
  have hxy : x ⤳ y := by
    rw [projectiveSpace_specializes_iff_le]
    change x.asHomogeneousIdeal.toIdeal ≤ Q
    rw [← hJ]
    exact homogeneousVanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hP)
  have hyx : y = x := by
    have := specializes_iff_mem_closure.mp hxy
    rw [hx.closure_eq] at this
    exact this
  have hxQ : x.asHomogeneousIdeal.toIdeal = Q := by rw [← hyx]
  have h := projectiveSpectrumPointDegree_cast x
  change (projectiveSpectrumPointDegree x : ℚ) =
    projectiveDegree (projZeroSet (x.asHomogeneousIdeal.toIdeal : Set S)) at h
  rw [hxQ, hZQ, (projectivePoint_hilbertPolynomial_and_degree P).2] at h
  exact_mod_cast h

/-- A coordinate hyperplane of `ℙⁿ_k` (`n ≥ 1`) has degree one. -/
theorem projectiveSpectrumPointDegree_hyperplane [IsAlgClosed k] (hn : 0 < n) (i : Fin (n + 1)) :
    projectiveSpectrumPointDegree
      (projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
        (MvPolynomial.X_prime (R := k) (i := i)).irreducible).1 = 1 := by
  set V := projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
    (MvPolynomial.X_prime (R := k) (i := i)).irreducible
  have h := projectiveSpectrumPointDegree_cast V.1
  have hs : (V.1.asHomogeneousIdeal : Set S) = (Ideal.span {(MvPolynomial.X i : S)} : Set S) := by
    rw [← projectiveHypersurfacePrimeDivisor_asHomogeneousIdeal hn (isHomogeneous_X k i)
      (MvPolynomial.X_prime (R := k) (i := i)).irreducible]
    rfl
  rw [hs, projZeroSet_span, (hypersurface_hilbertPolynomial_and_degree hn one_pos _
    (isHomogeneous_X k i) (MvPolynomial.X_prime (R := k) (i := i)).irreducible).2] at h
  exact_mod_cast h

section Curve

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- **Degrees of divisors on an embedded curve.** For a closed immersion `ι : X ⟶ ℙⁿ_k` of a
nonsingular curve (`k` algebraically closed), the degree of a divisor `E` in the embedding, the
weighted sum of the projective degrees of its points, is its divisor degree: closed points of
`ℙⁿ_k` have degree one. -/
theorem weilDivisorProjectiveDegree_eq_divisorDegree [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (E : X.WeilDivisor) :
    weilDivisorProjectiveDegree ι E = hX.divisorDegree E := by
  let _ := hX.satisfiesConditionStar.isNoetherian
  have hdeg : ∀ P : X.PrimeDivisor, primeDivisorProjectiveDegree ι P = 1 := by
    intro P
    apply projectiveSpectrumPointDegree_of_isClosed
    have hP : IsClosed ({P.1} : Set X) := (hX.isClosed_singleton_iff_coheight_eq_one P.1).mpr P.2
    have := ι.isClosedEmbedding.isClosedMap _ hP
    rwa [Set.image_singleton] at this
  rw [weilDivisorProjectiveDegree_apply, Scheme.IsNonsingularCurve.divisorDegree_apply]
  simp only [hdeg, mul_one]
  rw [Finsupp.sum]
  exact finsum_eq_sum_of_support_subset (fun P : X.PrimeDivisor ↦ E.1 P.1) fun P hP ↦
    Finsupp.mem_support_iff.mpr hP

/-- A nonsingular curve has more than one point. -/
theorem nontrivial_of_isNonsingularCurve (hX : X.IsNonsingularCurve k) : Nontrivial X := by
  obtain ⟨x, hx⟩ := hX.exists_ne_genericPoint
  exact ⟨⟨x, genericPoint X, hx⟩⟩

/-- **The degree of an embedded curve is the degree of a hyperplane section** (Hartshorne IV,
Example 3.3.2, first step). Let `k` be algebraically closed, `ι : X ⟶ ℙⁿ_k` (`n ≥ 1`) a closed
immersion of a nonsingular curve, and `H = V(xᵢ)` a coordinate hyperplane not containing `X`, that
is, `xᵢ` does not vanish at the image of the generic point. Then `deg ι(X) = deg (H · X)`, where
`H · X` is the divisor cut on `X` by `H`. -/
theorem projectiveSpectrumPointDegree_eq_divisorDegree_hyperplane [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (hn : 0 < n)
    (i : Fin (n + 1)) (hi : (MvPolynomial.X i : S) ∉ (ι.base (genericPoint X)).asHomogeneousIdeal) :
    projectiveSpectrumPointDegree (ι.base (genericPoint X)) =
      hX.divisorDegree (projectiveIntersectionDivisor ι hX.satisfiesConditionStar
        (projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
          (MvPolynomial.X_prime (R := k) (i := i)).irreducible)) := by
  set V := projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
    (MvPolynomial.X_prime (R := k) (i := i)).irreducible
  have hXV : ¬Set.range ι ⊆ closure ({V.1} : Set (Proj 𝒜)) := fun h ↦ hi <|
    (mem_closure_projectiveHypersurfacePrimeDivisor_iff hn _ _ _).mp (h ⟨genericPoint X, rfl⟩)
  have h := weilDivisorProjectiveDegree_projectiveIntersectionDivisor ι hX.satisfiesConditionStar
    (nontrivial_of_isNonsingularCurve hX) V hXV
  simp only at h
  rw [projectiveSpectrumPointDegree_hyperplane hn i, one_mul,
    weilDivisorProjectiveDegree_eq_divisorDegree hX] at h
  exact h.symm

end Curve

section DivisorOfZeros

open Opposite TopologicalSpace Scheme.CartierDivisor

variable {X : Scheme.{u}}

/-- Associated germs have the same order. -/
private theorem ord_algebraMap_stalk_eq_of_associated'' [IsIntegral X] [IsLocallyNoetherian X]
    {x : X} {a b : X.presheaf.stalk x} (hab : Associated a b) (ha : a ≠ 0) :
    X.ord (algebraMap _ X.functionField b) x = X.ord (algebraMap _ X.functionField a) x := by
  obtain ⟨u, rfl⟩ := hab
  have hinj := IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have ha' : algebraMap _ X.functionField a ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr ha
  have hu' : algebraMap _ X.functionField (u : X.presheaf.stalk x) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr u.ne_zero
  rw [map_mul, Scheme.ord_mul ha' hu', add_eq_left]
  exact ord_algebraMap_stalk_of_isUnit u.isUnit

/-- On `D₊(x_j)`, the chart function `x_i / x_j` is `Away.mk`. -/
private theorem hypersurfaceChartEquation_X_X (i j : Fin (n + 1)) :
    hypersurfaceChartEquation (MvPolynomial.X i : S) (MvPolynomial.X j) (isHomogeneous_X k i)
        (isHomogeneous_X k j) =
      Proj.awayToSection 𝒜 (MvPolynomial.X j)
        (HomogeneousLocalization.Away.mk 𝒜 (X_mem_homogeneousSubmodule_one (R := k) j) 1
          (MvPolynomial.X i) (by
            rw [smul_eq_mul, mul_one]; exact X_mem_homogeneousSubmodule_one (R := k) i)) := by
  rw [hypersurfaceChartEquation]
  congr 1
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mk]
  congr 1
  exact Subtype.ext (pow_one _).symm

/-- The chart function `x_i / x_j` is a local equation of the hyperplane `V(x_i)` on
`D₊(x_j)`. -/
private theorem isProjectiveHypersurfaceLocalEquation_hyperplane (hn : 0 < n) (i j : Fin (n + 1)) :
    IsProjectiveHypersurfaceLocalEquation
      (projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
        (MvPolynomial.X_prime (R := k) (i := i)).irreducible)
      (Proj.basicOpen 𝒜 (MvPolynomial.X j))
      (hypersurfaceChartEquation (MvPolynomial.X i : S) (MvPolynomial.X j) (isHomogeneous_X k i)
        (isHomogeneous_X k j)) :=
  fun _ hq ↦ ⟨_, _, 1, isHomogeneous_X k i, isHomogeneous_X k j, hq, rfl, Associated.refl _⟩

/-- **The hyperplane section is the divisor of zeros of the pulled-back coordinate** (Hartshorne
IV, Example 3.3.2, second step). Let `ι : X ⟶ ℙⁿ_k` (`n ≥ 1`) be a morphism from a scheme
satisfying `(*)` with `ι^* 𝒪(1)` isomorphic to some `𝒪_X(D₀)`, and let the coordinate hyperplane
`H = V(xᵢ)` not contain the image of `X`. If `C` is the divisor of zeros of the pulled-back section `ι^* xᵢ` of
`ι^* 𝒪(1)`, then the Weil divisor of `C` is `H · X`: on the open set where `x_j ≠ 0`, the section
`ι^* xᵢ` is `ι^#(xᵢ / x_j)` times the generator `ι^* x_j`. -/
theorem cartierToWeil_eq_projectiveIntersectionDivisor_hyperplane
    (hX : X.SatisfiesConditionStar) (ι : X ⟶ Proj 𝒜) (hn : 0 < n) (i : Fin (n + 1))
    (hXV : ¬Set.range ι ⊆ closure ({(projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
      (MvPolynomial.X_prime (R := k) (i := i)).irreducible).1} : Set (Proj 𝒜)))
    {D₀ : X.CartierDivisor}
    (φ : (Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒜 1) ≅ D₀.sheaf)
    {C : X.CartierDivisor}
    (hC : IsDivisorOfZeros ((Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒜 1))
      (Ringed.etaSec (φ := ι.toRingCatSheafHom) (E := projTwistingSheaf 𝒜 1) (W := ⊤)
        (ProjTwistingSheaf.degreeOneSection ⟨MvPolynomial.X i, X_mem_homogeneousSubmodule_one (R := k) i⟩))
      C) :
    let _ : IsIntegral X := hX.isIntegral
    let _ : IsNoetherian X := hX.isNoetherian
    Scheme.cartierToWeil C = projectiveIntersectionDivisor ι hX
      (projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
        (MvPolynomial.X_prime (R := k) (i := i)).irreducible) := by
  intro _ _
  set E := projTwistingSheaf 𝒜 1
  set L := (Scheme.Modules.pullback ι).obj E
  set V := projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
    (MvPolynomial.X_prime (R := k) (i := i)).irreducible
  let sec : Fin (n + 1) → Γ(E, ⊤) := fun l ↦
    ProjTwistingSheaf.degreeOneSection ⟨MvPolynomial.X l, X_mem_homogeneousSubmodule_one (R := k) l⟩
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  obtain ⟨j, hj⟩ := exists_X_notMem_projectiveSpace (ι.base x)
  set Dj : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (MvPolynomial.X j)
  have hxDj : ι.base x ∈ Dj := hj
  set h := hypersurfaceChartEquation (MvPolynomial.X i : S) (MvPolynomial.X j)
    (isHomogeneous_X k i) (isHomogeneous_X k j)
  rw [projectiveIntersectionDivisor_apply_eq_ord ι hX V hXV x Dj h hxDj
    (isProjectiveHypersurfaceLocalEquation_hyperplane hn i j)]
  obtain ⟨U, hxU, ⟨ψ⟩⟩ := exists_trivialization φ x
  obtain ⟨f, hf, hCU⟩ := hC U ψ
  rw [Scheme.cartierToWeil_apply C f hCU hxU]
  have hU : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hη := Scheme.genericPoint_mem_opens_of_mem hxU
  set s := Ringed.etaSec (φ := ι.toRingCatSheafHom) (E := E) (W := ⊤) (sec i) with hs
  set t := Ringed.etaSec (φ := ι.toRingCatSheafHom) (E := E) (W := ⊤) (sec j) with ht
  set r := trivApply ψ (resTop L U s) with hr
  set g := trivApply ψ (resTop L U t) with hg
  have hcoef : (Scheme.totalQuotientUnitsEquivFunctionField U hη f : X.functionField) =
      algebraMap _ X.functionField (X.presheaf.germ U x hxU r) := by
    change Scheme.totalQuotientSheafEquivFunctionField U hη (Scheme.kUnitVal f) = _
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, ← hf]
    exact Scheme.totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf U hη r
  rw [hcoef]
  have hr0 : X.presheaf.germ U x hxU r ≠ 0 := by
    intro h0
    have hr' : r = 0 := (map_eq_zero_iff _ (germ_injective_of_isIntegral X x hxU)).mp h0
    have : Nontrivial (X.totalQuotientSheaf.obj.obj (op U)) :=
      (Scheme.totalQuotientSheafEquivFunctionField (X := X) U hη).symm.injective.nontrivial
    apply Units.ne_zero (show (X.totalQuotientSheaf.obj.obj (op U))ˣ from f)
    change Scheme.kUnitVal f = 0
    rw [← hf, hr', map_zero]
  have hxW : x ∈ (Opens.map ι.base).obj Dj := hxDj
  set V' : X.Opens := U ⊓ (Opens.map ι.base).obj Dj
  have hV'U : V' ≤ U := inf_le_left
  have hV'W : V' ≤ (Opens.map ι.base).obj Dj := inf_le_right
  have hxV' : x ∈ V' := ⟨hxU, hxW⟩
  have res_res : ∀ {U₁ U₂ U₃ : X.Opens} (h₁ : U₂ ≤ U₁) (h₂ : U₃ ≤ U₂)
      (y : L.val.presheaf.obj (op U₁)),
      L.val.presheaf.map (homOfLE h₂).op (L.val.presheaf.map (homOfLE h₁).op y) =
        L.val.presheaf.map (homOfLE (h₂.trans h₁)).op y := by
    intro U₁ U₂ U₃ h₁ h₂ y
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  obtain hrel := by
    have h1 := ProjTwistingSheaf.restrict_degreeOneSection_eq_smul
      (X_mem_homogeneousSubmodule_one (R := k) j) (X_mem_homogeneousSubmodule_one (R := k) i)
    rw [← hypersurfaceChartEquation_X_X] at h1
    have h2 := congrArg (Ringed.etaSec (φ := ι.toRingCatSheafHom) (E := E) (W := Dj)) h1
    have h3 := h2.trans (Ringed.etaSec_smul (φ := ι.toRingCatSheafHom) (E := E) (W := Dj) h _)
    erw [Ringed.etaSec_restrict, Ringed.etaSec_restrict] at h3
    exact h3
  have hfr := Ringed.IsLocalFrame.pullback (φ := ι.toRingCatSheafHom)
    (ProjTwistingSheaf.isLocalFrame_degreeOneSection
      (X_mem_homogeneousSubmodule_one (R := k) j))
  let A : (Over U)ᵒᵖ := op (Over.mk (homOfLE hV'U))
  have hnat : ∀ y : L.val.obj (op U), ψ.hom.val.app A (L.val.presheaf.map (homOfLE hV'U).op y) =
      X.presheaf.map (homOfLE hV'U).op (trivApply ψ y) := fun y ↦
    ConcreteCategory.congr_hom (ψ.hom.val.naturality
      (Over.homMk (homOfLE hV'U) : Over.mk (homOfLE hV'U) ⟶ Over.mk (𝟙 U)).op) y
  let one : (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj A :=
    show Γ(X, V') from 1
  have hψ1 : (show Γ(X, V') from ψ.hom.val.app A (ψ.inv.val.app A one)) = 1 :=
    ConcreteCategory.congr_hom (congrArg (fun φ ↦ φ.val.app A) ψ.inv_hom_id) one
  obtain ⟨a, ha⟩ := (hfr V' hV'W).2 (ψ.inv.val.app A one)
  have key := (congrArg (fun y ↦ ψ.hom.val.app A y) ha).trans hψ1
  simp only at key
  erw [Ringed.localFrameMap_apply, Fintype.sum_unique] at key
  erw [(ψ.hom.val.app A).hom.map_smul] at key
  have hT := hnat (resTop L U t)
  erw [res_res] at hT
  erw [Ringed.etaSec_restrict, res_res, hT] at key
  have hS := hnat (resTop L U s)
  erw [res_res] at hS
  have hrel' := congrArg (fun y ↦ L.val.presheaf.map (homOfLE hV'W).op y) hrel
  simp only at hrel'
  erw [res_res, PresheafOfModules.map_smul, res_res] at hrel'
  have key2 := congrArg (fun y ↦ ψ.hom.val.app A y) hrel'
  simp only at key2
  erw [(ψ.hom.val.app A).hom.map_smul, hS, hT] at key2
  have k1 : (show Γ(X, V') from a PUnit.unit) * X.presheaf.map (homOfLE hV'U).op g = 1 := key
  have k2 : X.presheaf.map (homOfLE hV'U).op r =
      X.presheaf.map (homOfLE hV'W).op (ι.app Dj h) * X.presheaf.map (homOfLE hV'U).op g := key2
  have hgu : IsUnit (X.presheaf.germ U x hxU g) := by
    rw [← X.presheaf.germ_res_apply (homOfLE hV'U) x hxV' g]
    exact (IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans k1)).map _
  have hassoc : Associated (X.presheaf.germ (ι ⁻¹ᵁ Dj) x hxDj (ι.app Dj h))
      (X.presheaf.germ U x hxU r) := by
    refine ⟨hgu.unit, ?_⟩
    rw [IsUnit.unit_spec, ← X.presheaf.germ_res_apply (homOfLE hV'U) x hxV' r, k2, map_mul,
      X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
  exact (ord_algebraMap_stalk_eq_of_associated'' hassoc.symm hr0).symm

/-- The pulled-back coordinate section `ι^* xᵢ` is nonzero when `xᵢ` does not vanish at the
image of the generic point: it generates `ι^* 𝒪(1)` on the nonempty open set `ι⁻¹ D₊(xᵢ)`. -/
private theorem pullback_degreeOneSection_ne_zero [IsIntegral X] (ι : X ⟶ Proj 𝒜)
    (i : Fin (n + 1))
    (hi : (MvPolynomial.X i : S) ∉ (ι.base (genericPoint X)).asHomogeneousIdeal) :
    Ringed.etaSec (φ := ι.toRingCatSheafHom) (E := projTwistingSheaf 𝒜 1) (W := ⊤)
      (ProjTwistingSheaf.degreeOneSection
        ⟨MvPolynomial.X i, X_mem_homogeneousSubmodule_one (R := k) i⟩) ≠ 0 := by
  intro h0
  have hF := Ringed.IsLocalFrame.pullback (φ := ι.toRingCatSheafHom)
    (ProjTwistingSheaf.isLocalFrame_degreeOneSection (X_mem_homogeneousSubmodule_one (R := k) i))
  have h1 : Ringed.etaSec (φ := ι.toRingCatSheafHom) (E := projTwistingSheaf 𝒜 1)
      (W := ProjectiveSpectrum.basicOpen 𝒜 (MvPolynomial.X i))
      ((projTwistingSheaf 𝒜 1).val.presheaf.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 (MvPolynomial.X i) ≤ ⊤)).op
        (ProjTwistingSheaf.degreeOneSection
          ⟨MvPolynomial.X i, X_mem_homogeneousSubmodule_one (R := k) i⟩)) = 0 := by
    erw [Ringed.etaSec_restrict, h0, map_zero]
  have hV : Nonempty ((Opens.map ι.base).obj
      (ProjectiveSpectrum.basicOpen 𝒜 (MvPolynomial.X i))) := ⟨⟨genericPoint X, hi⟩⟩
  have hsz : ∀ (M : PresheafOfModules.{u} (ringCatSheafOf X.sheaf).obj) (W : X.Opensᵒᵖ)
      (a : (ringCatSheafOf X.sheaf).obj.obj W), a • (0 : M.presheaf.obj W) = 0 :=
    fun _ _ a ↦ smul_zero a
  have h2 := (hF _ le_rfl).1 (a₁ := fun _ ↦ 1) (a₂ := 0) (by
    erw [Ringed.localFrameMap_apply, Ringed.localFrameMap_apply, Fintype.sum_unique,
      Fintype.sum_unique, h1]
    rw [map_zero]
    exact (hsz _ _ _).trans (hsz _ _ _).symm)
  exact one_ne_zero (α := Γ(X, (Opens.map ι.base).obj
    (ProjectiveSpectrum.basicOpen 𝒜 (MvPolynomial.X i)))) (congrFun h2 PUnit.unit)

end DivisorOfZeros

section Assembly

open Opposite Scheme.CartierDivisor

variable {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- A nonsingular curve over `k` is separated. -/
theorem isSeparated_of_isNonsingularCurve (hX : X.IsNonsingularCurve k) : X.IsSeparated := by
  have := hX.isSeparated
  refine ⟨?_⟩
  rw [show Limits.terminal.from X = (X ↘ Spec (.of k)) ≫ Limits.terminal.from _ from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- A nonsingular curve admits no closed immersion into `ℙ⁰_k`: the image of the generic point
specializes strictly to the image of a closed point, while the homogeneous primes of `ℙ⁰_k` form a
poset of dimension zero. -/
theorem pos_of_isClosedImmersion_of_isNonsingularCurve (hX : X.IsNonsingularCurve k)
    (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] : 0 < n := by
  obtain ⟨x, hx⟩ := hX.exists_ne_genericPoint
  have hsp : ι.base (genericPoint X) ⤳ ι.base x :=
    ((genericPoint_spec X).specializes trivial).map ι.continuous
  rw [projectiveSpace_specializes_iff_le] at hsp
  have hne : ι.base (genericPoint X) ≠ ι.base x := fun h ↦
    hx (ι.isClosedEmbedding.injective h).symm
  have hlt : @LT.lt (ProjectiveSpectrum 𝒜) _ (ι.base (genericPoint X)) (ι.base x) :=
    lt_of_le_of_ne (α := ProjectiveSpectrum 𝒜) hsp hne
  have h := (Order.krullDim_pos_iff (α := ProjectiveSpectrum 𝒜)).mpr ⟨_, _, hlt⟩
  rw [krullDim_projectiveSpectrum] at h
  exact_mod_cast h

/-- **Embedded degree is the degree of a divisor linearly equivalent to `D`** (Hartshorne IV,
Example 3.3.2, up to the invariance of degree under linear equivalence). Let `k` be algebraically
closed, `X` a nonsingular curve over `k`, `D` a divisor on `X`, and `ι : X ⟶ ℙⁿ_k` a closed
immersion with `ι^* 𝒪(1) ≅ 𝒪_X(D)`. Then there is an effective divisor `E` linearly equivalent
to `D` with `deg ι(X) = deg E`: for a coordinate hyperplane `H` not containing `X`, the hyperplane
section `E = H · X` is the divisor of zeros of the pulled-back section `ι^* xᵢ` of
`ι^* 𝒪(1) ≅ 𝒪_X(D)`, so is effective and linearly equivalent to `D` (II, Proposition 7.7), and its
degree is `deg ι(X)` by Bézout with `deg H = 1`. -/
theorem exists_linearEquivalent_projectiveSpectrumPointDegree_eq_divisorDegree [IsAlgClosed k]
    (hX : X.IsNonsingularCurve k) (ι : X ⟶ Proj 𝒜) [IsClosedImmersion ι] (D : X.WeilDivisor) :
    let _ : IsNoetherian X := hX.satisfiesConditionStar.isNoetherian
    let _ : X.IsSeparated := isSeparated_of_isNonsingularCurve hX
    let hlf : X.IsLocallyFactorial :=
      X.isLocallyFactorial_of_isRegularLocalRing hX.isRegularLocalRing_stalk
    Nonempty ((Scheme.Modules.pullback ι).obj (projTwistingSheaf 𝒜 1) ≅
      (Scheme.weilCartierEquiv hlf D).sheaf) →
    ∃ E : X.WeilDivisor, Scheme.WeilDivisor.IsEffective E ∧
      Scheme.WeilDivisor.LinearEquivalent (Scheme.satisfiesConditionStar_of_isLocallyFactorial hlf)
        E D ∧
      projectiveSpectrumPointDegree (ι.base (genericPoint X)) = hX.divisorDegree E := by
  intro _ _ hlf ⟨e⟩
  have hn := pos_of_isClosedImmersion_of_isNonsingularCurve hX ι
  obtain ⟨i, hi⟩ := exists_X_notMem_projectiveSpace (ι.base (genericPoint X))
  obtain ⟨E, hE, hEeff, hElin⟩ :=
    (Scheme.weil_isDivisorOfZeros hlf e).1 _ (pullback_degreeOneSection_ne_zero ι i hi)
  refine ⟨E, hEeff, hElin, ?_⟩
  have hXV : ¬Set.range ι ⊆ closure ({(projectiveHypersurfacePrimeDivisor hn (isHomogeneous_X k i)
      (MvPolynomial.X_prime (R := k) (i := i)).irreducible).1} : Set (Proj 𝒜)) := fun h ↦ hi <|
    (mem_closure_projectiveHypersurfacePrimeDivisor_iff hn _ _ _).mp (h ⟨genericPoint X, rfl⟩)
  have h1 := cartierToWeil_eq_projectiveIntersectionDivisor_hyperplane
    hX.satisfiesConditionStar ι hn i hXV e hE
  have hEE : Scheme.cartierToWeil (Scheme.weilCartierEquiv hlf E) = E := by
    rw [← Scheme.weilCartierEquiv_symm_apply hlf, AddEquiv.symm_apply_apply]
  rw [projectiveSpectrumPointDegree_eq_divisorDegree_hyperplane hX ι hn i hi]
  simp only at h1
  rw [← h1, hEE]

end Assembly

end Hartshorne
