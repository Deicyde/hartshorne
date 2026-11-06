/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceChart
import Hartshorne.Scheme.ProjectiveSpaceOverScheme
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# A Proj generated in degree one is projective

Hartshorne, *Algebraic Geometry*, II.4, Example 4.8.1.

Let `S` be an `ℕ`-graded ring, finitely generated as an `S₀`-algebra by
homogeneous elements `s₀, …, sₙ` of degree one. Then the structure morphism
`Proj S ⟶ Spec S₀` is projective.

The graded homomorphism `ℤ[x₀, …, xₙ] → S`, `xⱼ ↦ sⱼ`, induces a morphism
`g : Proj S ⟶ ℙⁿ_ℤ`, defined everywhere because the `sⱼ` generate the irrelevant
ideal of `S`. Together with `Proj S ⟶ Spec S₀` it gives a morphism
`ι : Proj S ⟶ ℙⁿ_ℤ ×_{Spec ℤ} Spec S₀ = ℙⁿ_{Spec S₀}` over `Spec S₀`.
Over the chart `D₊(xⱼ) ×_{Spec ℤ} Spec S₀ = Spec (ℤ[x]_(xⱼ) ⊗ S₀)`, the preimage
under `ι` is `D₊(sⱼ) = Spec S_(sⱼ)`, and `ι` is `Spec` of the ring map
`ℤ[x]_(xⱼ) ⊗ S₀ → S_(sⱼ)`, which is surjective because `S_(sⱼ)` is generated
over `S₀` by quotients of monomials in the `sᵢ` by powers of `sⱼ`. Hence `ι` is
a closed immersion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry HomogeneousLocalization MvPolynomial
open scoped TensorProduct

universe u

namespace Hartshorne

namespace GeneratedProj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- If homogeneous elements generate a graded ring over its degree-zero part, they
generate its irrelevant ideal. -/
theorem irrelevant_le_span_of_adjoin_eq_top {ι : Type*} (f : ι → S)
    (hfn : ∀ i, ∃ n, f i ∈ 𝒜 n) (hf : Algebra.adjoin (𝒜 0) (Set.range f) = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f) := by
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have := (eq_iff_iff.mp congr(x ∈ $hf)).mpr trivial
  induction this using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hfn i
    rw [GradedRing.projZeroRingHom_apply]
    by_cases hn' : n = 0
    · rw [DirectSum.decompose_of_mem_same 𝒜 (hn' ▸ hn), sub_self]
      exact zero_mem _
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hn hn', sub_zero]
      exact Ideal.subset_span ⟨_, rfl⟩
  | algebraMap r =>
    convert! zero_mem (Ideal.span _)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same 𝒜 r.2).symm
  | add x y hx hy _ _ =>
    rw [map_add, add_sub_add_comm]
    exact add_mem ‹_› ‹_›
  | mul x y hx hy hx' hy' =>
    convert!
      add_mem (Ideal.mul_mem_left _ x hy')
        (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx') using 1
    rw [map_mul]
    ring

variable {n : ℕ}

/-- The standard grading of `ℤ[x₀, …, xₙ]`, with universe-lifted coefficients. -/
abbrev intGrading (n : ℕ) := homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)

/-- The ring homomorphism `ℤ[x₀, …, xₙ] → S` sending `xⱼ` to `v j`. -/
def evalRingHom (v : Fin (n + 1) → S) : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) →+* S :=
  eval₂Hom ((Int.castRingHom S).comp ULift.ringEquiv.toRingHom) v

/-- The evaluation sends `xⱼ` to `v j`. -/
theorem evalRingHom_X (v : Fin (n + 1) → S) (j : Fin (n + 1)) :
    evalRingHom v (X j) = v j :=
  eval₂_X _ _ _

/-- Evaluation at degree-one elements is degree preserving. -/
theorem evalRingHom_mem {v : Fin (n + 1) → S} (hv : ∀ j, v j ∈ 𝒜 1) {d : ℕ}
    {p : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)} (hp : p ∈ intGrading n d) :
    evalRingHom v p ∈ 𝒜 d := by
  rw [mem_homogeneousSubmodule] at hp
  rw [p.as_sum, map_sum]
  refine sum_mem fun m hm => ?_
  have hdeg : ∑ j ∈ m.support, m j = d := by
    have h : Finsupp.degree m = d := by
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
      exact hp (mem_support_iff.1 hm)
    exact h
  rw [evalRingHom, coe_eval₂Hom, eval₂_monomial]
  have h0 : ((Int.castRingHom S).comp ULift.ringEquiv.toRingHom) (coeff m p) ∈ 𝒜 0 := by
    exact SetLike.intCast_mem_graded 𝒜 (coeff m p).down
  have h1 : (m.prod fun j e => v j ^ e) ∈ 𝒜 d := by
    have := SetLike.prod_pow_mem_graded 𝒜 (F := m.support) (g := v) (i := fun _ => 1) m (fun j _ => hv j)
    rw [Finsupp.prod, ← hdeg]
    simpa using this
  simpa using SetLike.mul_mem_graded h0 h1

/-- The graded homomorphism `ℤ[x₀, …, xₙ] → S` sending `xⱼ` to `v j`. -/
def evalGradedHom {v : Fin (n + 1) → S} (hv : ∀ j, v j ∈ 𝒜 1) : intGrading.{u} n →+*ᵍ 𝒜 where
  __ := evalRingHom v
  map_mem hp := evalRingHom_mem 𝒜 hv hp

section Generators

variable {v : Fin (n + 1) → S} (hv : ∀ j, v j ∈ 𝒜 1)
  (hgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤)

include hgen in
/-- The images of the variables generate the irrelevant ideal of `S`. -/
theorem irrelevant_le_map_evalGradedHom :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      (HomogeneousIdeal.irrelevant (intGrading.{u} n)).toIdeal.map (evalGradedHom 𝒜 hv) := by
  refine (irrelevant_le_span_of_adjoin_eq_top 𝒜 v (fun j => ⟨1, hv j⟩) hgen).trans ?_
  rw [Ideal.span_le, Set.range_subset_iff]
  intro j
  have h := Ideal.mem_map_of_mem (evalGradedHom 𝒜 hv)
    (HomogeneousIdeal.mem_irrelevant_of_mem (intGrading.{u} n) Nat.one_pos
      (X_mem_homogeneousSubmodule_one (ULift.{u} ℤ) j))
  exact (evalRingHom_X v j) ▸ h

/-- The morphism `Proj S ⟶ ℙⁿ_ℤ` induced by `xⱼ ↦ v j`. -/
def toProjectiveSpaceInt : Proj 𝒜 ⟶ projectiveSpaceScheme (ULift.{u} ℤ) n :=
  Proj.map (evalGradedHom 𝒜 hv) (irrelevant_le_map_evalGradedHom 𝒜 hv hgen)

/-- The morphism `Proj S ⟶ ℙⁿ_{Spec S₀}` over `Spec S₀`. -/
def toProjectiveSpace : Proj 𝒜 ⟶ projectiveSpaceOverScheme n (Spec (.of (𝒜 0))) :=
  pullback.lift (toProjectiveSpaceInt 𝒜 hv hgen) (Proj.toSpecZero 𝒜)
    (specULiftZIsTerminal.hom_ext _ _)

/-- The morphism `Proj S ⟶ ℙⁿ_{Spec S₀}` lies over `Spec S₀`. -/
theorem toProjectiveSpace_projection :
    toProjectiveSpace 𝒜 hv hgen ≫ projectiveSpaceOverSchemeProjection n _ =
      Proj.toSpecZero 𝒜 :=
  pullback.lift_snd _ _ _

/-- Followed by the projection to `ℙⁿ_ℤ`, the morphism to `ℙⁿ_{Spec S₀}` is the
morphism induced by `xⱼ ↦ v j`. -/
theorem toProjectiveSpace_fst :
    toProjectiveSpace 𝒜 hv hgen ≫ pullback.fst _ _ = toProjectiveSpaceInt 𝒜 hv hgen :=
  pullback.lift_fst _ _ _

include hgen in
/-- Over the chart `D₊(xⱼ) ×_{Spec ℤ} Spec S₀` of `ℙⁿ_{Spec S₀}`, the morphism from
`Spec S_(sⱼ)` given by `ℤ[x]_(xⱼ) → S_(sⱼ)` and `S₀ → S_(sⱼ)` is a closed immersion. -/
theorem isClosedImmersion_chartLift (j : Fin (n + 1)) :
    IsClosedImmersion (pullback.lift
      (f := Proj.awayι (intGrading.{u} n) (X j) (X_mem_homogeneousSubmodule_one _ j)
        Nat.one_pos ≫ projectiveSpaceOverIntegersMap n)
      (g := schemeToSpecZ (Spec (.of (𝒜 0))))
      (Spec.map (CommRingCat.ofHom (Away.map (evalGradedHom 𝒜 hv) (X j))))
      (Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (.powers (evalGradedHom 𝒜 hv (X j))))))
      (specULiftZIsTerminal.hom_ext _ _)) := by
  let R := ULift.{u} ℤ
  let 𝒵 := intGrading.{u} n
  let ψ := evalGradedHom 𝒜 hv
  have hXj : (X j : MvPolynomial (Fin (n + 1)) R) ∈ 𝒵 1 := X_mem_homogeneousSubmodule_one R j
  have hψj : ψ (X j) ∈ 𝒜 1 := ψ.map_mem hXj
  let algZ : Algebra R (Away 𝒵 (X j)) := ULift.algebra' ℤ _
  let alg0 : Algebra R (𝒜 0) := ULift.algebra' ℤ _
  let algA : Algebra R (Away 𝒜 (ψ (X j))) := ULift.algebra' ℤ _
  let f₁ : Away 𝒵 (X j) →ₐ[R] Away 𝒜 (ψ (X j)) :=
    { Away.map ψ (X j) with
      commutes' := fun r => by simp [R, ULift.algebraMap_apply'] }
  let f₂ : 𝒜 0 →ₐ[R] Away 𝒜 (ψ (X j)) :=
    { fromZeroRingHom 𝒜 _ with
      commutes' := fun r => by simp [R, ULift.algebraMap_apply'] }
  let F : Away 𝒵 (X j) ⊗[R] 𝒜 0 →+* Away 𝒜 (ψ (X j)) :=
    (Algebra.TensorProduct.lift f₁ f₂ (fun _ _ => .all _ _)).toRingHom
  have hF : Function.Surjective F := by
    have hgen' : Algebra.adjoin (𝒜 0) (Set.range fun i => ψ (X i)) = ⊤ := by
      rw [← hgen]
      congr 2
      funext i
      exact evalRingHom_X v i
    have htop := Away.adjoin_mk_prod_pow_eq_top hψj (Fin (n + 1)) (fun i => ψ (X i)) hgen'
      (fun _ => 1) (fun i => ψ.map_mem (X_mem_homogeneousSubmodule_one R i))
    intro y
    have hy : y ∈ Algebra.adjoin (𝒜 0) _ := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨a, ai, hai, -, rfl⟩ := hy
      have hmem : (∏ i, X i ^ ai i : MvPolynomial (Fin (n + 1)) R) ∈ 𝒵 (a • 1) := by
        rw [← hai]
        exact SetLike.prod_pow_mem_graded 𝒵 (F := Finset.univ) (g := X) (i := fun _ => 1) ai
          (fun i _ => X_mem_homogeneousSubmodule_one R i)
      refine ⟨Away.mk 𝒵 hXj a _ hmem ⊗ₜ 1, ?_⟩
      apply val_injective
      simp only [F, f₁, f₂, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      erw [Away.map_mk, Away.val_mk, Away.val_mk]
      congr 1
      simp [map_prod]
    | algebraMap r =>
      exact ⟨1 ⊗ₜ r, by simp [F, f₁, f₂]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩
  have hTe : pullback.lift
      (f := Proj.awayι (intGrading.{u} n) (X j) (X_mem_homogeneousSubmodule_one _ j)
        Nat.one_pos ≫ projectiveSpaceOverIntegersMap n)
      (g := schemeToSpecZ (Spec (.of (𝒜 0))))
      (Spec.map (CommRingCat.ofHom (Away.map (evalGradedHom 𝒜 hv) (X j))))
      (Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (.powers (evalGradedHom 𝒜 hv (X j))))))
      (specULiftZIsTerminal.hom_ext _ _) =
      Spec.map (CommRingCat.ofHom F) ≫ (pullbackSpecIso R (Away 𝒵 (X j)) (𝒜 0)).inv ≫
        (pullback.congrHom (specULiftZIsTerminal.hom_ext _ _)
          (specULiftZIsTerminal.hom_ext _ _)).inv := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_fst, Category.comp_id]
      erw [pullbackSpecIso_inv_fst, ← Spec.map_comp]
      congr 1
      ext x : 2
      simp [F, f₁, f₂]
      rfl
    · simp only [Category.assoc, pullback.congrHom_inv, pullback.lift_snd, Category.comp_id]
      erw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext x : 2
      simp [F, f₁, f₂]
      rfl
  rw [hTe]
  have : IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (R := Away 𝒵 (X j) ⊗[R] 𝒜 0) (S := Away 𝒜 (ψ (X j))) F)) := by
    apply IsClosedImmersion.spec_of_surjective
    exact hF
  infer_instance

/-- The morphism `Proj S ⟶ ℙⁿ_{Spec S₀}` is a closed immersion. -/
theorem isClosedImmersion_toProjectiveSpace :
    IsClosedImmersion (toProjectiveSpace 𝒜 hv hgen) := by
  let R := ULift.{u} ℤ
  let 𝒵 := intGrading.{u} n
  let ψ := evalGradedHom 𝒜 hv
  let ι := toProjectiveSpace 𝒜 hv hgen
  let 𝒰P : (projectiveSpaceScheme R n).OpenCover :=
    (projCoordinateAffineOpenCover R (σ := Fin (n + 1))).openCover
  let 𝒰 := Scheme.Pullback.openCoverOfLeft 𝒰P (projectiveSpaceOverIntegersMap n)
    (schemeToSpecZ (Spec (.of (𝒜 0))))
  refine IsZariskiLocalAtTarget.of_openCover 𝒰 fun (j : Fin (n + 1)) => ?_
  have hXj : (X j : MvPolynomial (Fin (n + 1)) R) ∈ 𝒵 1 := X_mem_homogeneousSubmodule_one R j
  have hψj : ψ (X j) ∈ 𝒜 1 := ψ.map_mem hXj
  have : IsOpenImmersion (𝒰.f j) := 𝒰.map_prop j
  have hrange : Set.range (pullback.fst ι (𝒰.f j)) =
      Set.range (Proj.awayι 𝒜 (ψ (X j)) hψj Nat.one_pos) := by
    have hP : Set.range (𝒰P.f j) = (Proj.basicOpen 𝒵 (X j) : Set (Proj 𝒵)) :=
      congrArg SetLike.coe (Proj.opensRange_awayι _ _ hXj Nat.one_pos)
    have hA : Set.range (Proj.awayι 𝒜 (ψ (X j)) hψj Nat.one_pos) =
        (Proj.basicOpen 𝒜 (ψ (X j)) : Set (Proj 𝒜)) :=
      congrArg SetLike.coe (Proj.opensRange_awayι _ _ hψj Nat.one_pos)
    rw [Scheme.Pullback.range_fst, hA]
    simp only [𝒰, Scheme.Pullback.openCoverOfLeft]
    erw [Scheme.Pullback.range_map, hP]
    ext x
    rw [Set.mem_preimage, Set.mem_inter_iff, and_iff_left ⟨_, rfl⟩]
    change (toProjectiveSpace 𝒜 hv hgen ≫ pullback.fst _ _) x ∈
      (Proj.basicOpen 𝒵 (X j) : Set (Proj 𝒵)) ↔ _
    rw [toProjectiveSpace_fst]
    rfl
  let E := IsOpenImmersion.isoOfRangeEq _ _ hrange
  let T : Spec (.of (Away 𝒜 (ψ (X j)))) ⟶ 𝒰.X j :=
    pullback.lift (Spec.map (CommRingCat.ofHom (Away.map ψ (X j))))
      (Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))) (specULiftZIsTerminal.hom_ext _ _)
  have hT : IsClosedImmersion T := isClosedImmersion_chartLift 𝒜 hv hgen j
  have hcomm : Proj.awayι 𝒜 (ψ (X j)) hψj Nat.one_pos ≫ ι = T ≫ 𝒰.f j := by
    apply pullback.hom_ext
    · simp only [ι, toProjectiveSpace, toProjectiveSpaceInt, 𝒰, Scheme.Pullback.openCoverOfLeft,
        Category.assoc, pullback.lift_fst, T]
      erw [pullback.lift_fst, pullback.lift_fst_assoc]
      exact Proj.awayι_comp_map ψ _ Nat.one_pos (X j) hXj
    · simp only [ι, toProjectiveSpace, 𝒰, Scheme.Pullback.openCoverOfLeft,
        Category.assoc, pullback.lift_snd, T, Category.comp_id]
      erw [pullback.lift_snd]
      exact Proj.awayι_toSpecZero 𝒜 _ hψj Nat.one_pos
  have hsnd : 𝒰.pullbackHom ι j = E.hom ≫ T := by
    change pullback.snd ι (𝒰.f j) = E.hom ≫ T
    rw [← cancel_mono (𝒰.f j), Category.assoc, ← hcomm, ← Category.assoc,
      IsOpenImmersion.isoOfRangeEq_hom_fac, ← pullback.condition]
  rw [hsnd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion E.hom T).mpr hT

end Generators

end GeneratedProj

open GeneratedProj in
/-- **Hartshorne II, Example 4.8.1.** Let `S` be a graded ring with `S₀ = A`, finitely
generated as an `A`-algebra by `S₁`. Then the structure morphism `Proj S ⟶ Spec A` is
projective. -/
theorem projective_projToSpecZero_of_degreeOne_generators
    {S σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ)
    [GradedRing 𝒜]
    (hgen : ∃ s : Finset S, (∀ x ∈ s, x ∈ 𝒜 1) ∧ Algebra.adjoin (𝒜 0) (s : Set S) = ⊤) :
    Projective (Proj.toSpecZero 𝒜) := by
  obtain ⟨s, hs, hadj⟩ := hgen
  let v : Fin (s.card + 1) → S := Fin.cons 0 fun i => (s.equivFin.symm i : S)
  have hv : ∀ j, v j ∈ 𝒜 1 :=
    Fin.cases (zero_mem _) fun i => hs _ (s.equivFin.symm i).2
  have hvgen : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hadj]
    refine Algebra.adjoin_mono fun x hx => ⟨(s.equivFin ⟨x, hx⟩).succ, ?_⟩
    simp [v]
  have := isClosedImmersion_toProjectiveSpace 𝒜 hv hvgen
  exact Projective.mk _ _ (toProjectiveSpace_projection 𝒜 hv hvgen)

end Hartshorne
