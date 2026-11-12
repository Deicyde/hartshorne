/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveBundleGluing

/-!
# Projective-space bundles

Hartshorne, *Algebraic Geometry*, II, Exercise 7.10(a,b) (pp. 170–171).

## Projective `n`-space bundles

Analogously to geometric vector bundles (Exercise II.5.18,
`AlgebraicGeometry.GeometricVectorBundle`), a *projective `n`-space bundle* over `X` is a scheme
`f : P ⟶ X` over `X` together with an open covering `{U_i}` of `X` and isomorphisms
`ψ_i : f⁻¹(U_i) ≅ ℙⁿ_{U_i}` over `U_i`, such that for all `i, j` and every open affine
`V ⊆ U_i ∩ U_j`, with ring of sections `A = Γ(V, 𝒪_X)`, the automorphism `ψ_i ∘ ψ_j⁻¹` of
`ℙⁿ_V = Proj A[x₀, …, xₙ]` is `Proj θ` for the graded `A`-algebra automorphism
`θ(x_k) = ∑_l a_{kl} x_l` of `A[x₀, …, xₙ]` given by an invertible matrix
`(a_{kl}) ∈ GL_{n+1}(A)` (`AlgebraicGeometry.ProjectiveSpaceBundle`).

## Main results

* `AlgebraicGeometry.linearSubstitutionGradedHom`, `AlgebraicGeometry.projLinearAut`: the linear
  change of homogeneous coordinates `x_k ↦ ∑_l a_{kl} x_l` and the automorphism of
  `Proj A[x₀, …, xₙ]` it induces for `(a_{kl})` invertible.
* `AlgebraicGeometry.projectiveSpaceAffineChart`: the chart `Proj A[x₀, …, xₙ] ≅ ℙⁿ_V ⊆ ℙⁿ_U` of
  projective space over an open `U` at an affine open `V ⊆ U`.
* `AlgebraicGeometry.Scheme.Modules.projectiveBundleAtlas`,
  `AlgebraicGeometry.Scheme.Modules.nonempty_projectiveSpaceBundle_projectiveBundleProj`:
  **`P(E)` is a projective `n`-space bundle** for `E` locally free of rank `n + 1`. The covering
  consists of the affine opens `V` on which `E` has a frame `e`, with the trivializations
  `π⁻¹(V) ≅ ℙⁿ_V` sending the coordinate `x_k` to `e_k`; on an affine `W ⊆ V ∩ V'`, the
  transition is the linear substitution expressing the frame `e|_W` in the frame `e'|_W`
  (`frameGradedHom_comp_linearSubstitution`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

open Hartshorne MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

section LinearSubstitution

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The images `∑_l a_{kl} x_l` of the variables under the linear substitution given by `a`. -/
private abbrev linearForms (a : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) A :=
  fun k => ∑ l, C (a k l) * X l

/-- **A linear change of homogeneous coordinates**: for a matrix `(a_{kl})` with entries in `A`,
the graded `A`-algebra endomorphism of `A[x₀, …, xₙ]` with `x_k ↦ ∑_l a_{kl} x_l`. -/
def linearSubstitutionGradedHom (a : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    homogeneousSubmodule (Fin (n + 1)) A →+*ᵍ homogeneousSubmodule (Fin (n + 1)) A where
  toRingHom := (aeval (linearForms A n a)).toRingHom
  map_mem {d} p hp := by
    have h := ((mem_homogeneousSubmodule d p).1 hp).eval₂ (algebraMap A _) (linearForms A n a)
      (fun r => isHomogeneous_C _ r)
      (fun k => IsHomogeneous.sum _ _ _ fun l _ => (isHomogeneous_X A l).C_mul _)
    rw [one_mul] at h
    exact (mem_homogeneousSubmodule d _).2 h

variable {A n}

lemma linearSubstitutionGradedHom_apply (a : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (p : MvPolynomial (Fin (n + 1)) A) :
    linearSubstitutionGradedHom A n a p = aeval (linearForms A n a) p :=
  rfl

lemma linearSubstitutionGradedHom_X (a : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (k : Fin (n + 1)) :
    linearSubstitutionGradedHom A n a (X k) = ∑ l, C (a k l) * X l := by
  rw [linearSubstitutionGradedHom_apply, aeval_X]

lemma linearSubstitutionGradedHom_C (a : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (r : A) :
    linearSubstitutionGradedHom A n a (C r) = C r := by
  rw [linearSubstitutionGradedHom_apply, aeval_C]
  rfl

/-- Composing linear substitutions multiplies their matrices. -/
lemma linearSubstitutionGradedHom_comp_apply (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (p : MvPolynomial (Fin (n + 1)) A) :
    linearSubstitutionGradedHom A n a (linearSubstitutionGradedHom A n b p) =
      linearSubstitutionGradedHom A n (b * a) p := by
  simp only [linearSubstitutionGradedHom_apply]
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun k => ?_
  simp only [AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  ring

lemma linearSubstitutionGradedHom_one_apply (p : MvPolynomial (Fin (n + 1)) A) :
    linearSubstitutionGradedHom A n 1 p = p := by
  rw [linearSubstitutionGradedHom_apply]
  have h : linearForms A n 1 = X := by
    funext k
    simp [linearForms, Matrix.one_apply]
  rw [h, aeval_X_left_apply]

/-- The matrix of a linear substitution is determined by the substitution. -/
lemma eq_one_of_linearSubstitutionGradedHom_apply (a : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (h : ∀ p, linearSubstitutionGradedHom A n a p = p) : a = 1 := by
  classical
  ext k m
  have hk := congrArg (coeff (Finsupp.single m 1)) (h (X k))
  rw [linearSubstitutionGradedHom_X, coeff_sum] at hk
  simp only [coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff, and_true, one_ne_zero,
    and_false, or_false, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at hk
  rw [hk, Matrix.one_apply]

lemma linearSubstitutionGradedHom_bijective (g : Matrix.GeneralLinearGroup (Fin (n + 1)) A) :
    Function.Bijective
      (linearSubstitutionGradedHom A n (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A)) :=
  Function.bijective_iff_has_inverse.2 ⟨linearSubstitutionGradedHom A n (↑g⁻¹ :
      Matrix (Fin (n + 1)) (Fin (n + 1)) A),
    fun p => by rw [linearSubstitutionGradedHom_comp_apply, Units.mul_inv,
      linearSubstitutionGradedHom_one_apply],
    fun p => by rw [linearSubstitutionGradedHom_comp_apply, Units.inv_mul,
      linearSubstitutionGradedHom_one_apply]⟩

variable (A n) in
/-- **The automorphism of `Proj A[x₀, …, xₙ]` induced by an invertible linear change of homogeneous
coordinates** `θ(x_k) = ∑_l a_{kl} x_l`, `(a_{kl}) ∈ GL_{n+1}(A)`: its morphism is `Proj θ`. -/
def projLinearAut (g : Matrix.GeneralLinearGroup (Fin (n + 1)) A) :
    Proj (homogeneousSubmodule (Fin (n + 1)) A) ≅ Proj (homogeneousSubmodule (Fin (n + 1)) A) :=
  projIsoOfBijective (linearSubstitutionGradedHom A n g) (linearSubstitutionGradedHom_bijective g)

end LinearSubstitution

variable {P X : Scheme.{u}}

/-- **The chart of projective space at an affine open**: for an open `U` of `X` and an affine open
`V ⊆ U` with ring of sections `A = Γ(V, 𝒪_X)`, the identification
`Proj A[x₀, …, xₙ] ≅ ℙⁿ_{Spec A} ≅ ℙⁿ_V` followed by `ℙⁿ_V ⟶ ℙⁿ_U`. -/
def projectiveSpaceAffineChart (n : ℕ) {U : X.Opens} (V : X.Opens) (hV : IsAffineOpen V)
    (h : V ≤ U) :
    Proj (homogeneousSubmodule (Fin (n + 1)) Γ(X, V)) ⟶ projectiveSpaceOverScheme n U :=
  (projectiveSpaceOverSpecIso Γ(X, V) n (Equiv.refl _)).hom ≫
    projectiveSpaceOverSchemeMap n hV.isoSpec.inv ≫ projectiveSpaceOverSchemeMap n (X.homOfLE h)

/-- **A projective `n`-space bundle** over `X` (Hartshorne II, Exercise 7.10(a)): the additional
data, on a scheme `f : P ⟶ X` over `X`, of an open covering `{U_i}` of `X` (`U`, `iSup_eq_top`)
and isomorphisms `ψ_i : f⁻¹(U_i) ≅ ℙⁿ_{U_i}` over `U_i` (`ψ`, `ψ_over`), such that for all `i, j`
and every open affine `V ⊆ U_i ∩ U_j`, with ring of sections `A = Γ(V, 𝒪_X)`, the automorphism
`ψ_i ∘ ψ_j⁻¹` of `ℙⁿ_V = Proj A[x₀, …, xₙ]` is `Proj θ` for an invertible linear change of
homogeneous coordinates `θ(x_k) = ∑_l a_{kl} x_l`, `(a_{kl}) ∈ GL_{n+1}(A)` (`linear`).

As for geometric vector bundles, the condition on `ψ_i ∘ ψ_j⁻¹` is stated without restricting
the `ψ_i` to `f⁻¹(V)`: the two open immersions `Proj A[x₀, …, xₙ] ⟶ P` obtained from the charts
of `ℙⁿ_{U_j}` and `ℙⁿ_{U_i}` at `V` (`projectiveSpaceAffineChart`) followed by `ψ_j⁻¹`,
respectively `ψ_i⁻¹`, differ by `Proj θ`. This is the equation `ψ_j⁻¹ = ψ_i⁻¹ ∘ Proj θ` on
`ℙⁿ_V`, that is, `ψ_i ∘ ψ_j⁻¹ = Proj θ`. -/
structure ProjectiveSpaceBundle (f : P ⟶ X) (n : ℕ) where
  /-- The index set of the covering. -/
  ι : Type u
  /-- The open covering `{U_i}` of `X`. -/
  U : ι → X.Opens
  iSup_eq_top : ⨆ i, U i = ⊤
  /-- The trivializations `ψ_i : f⁻¹(U_i) ≅ ℙⁿ_{U_i}`. -/
  ψ : ∀ i, (f ⁻¹ᵁ U i).toScheme ≅ projectiveSpaceOverScheme n (U i)
  ψ_over : ∀ i, (ψ i).hom ≫ projectiveSpaceOverSchemeProjection n (U i) = f ∣_ U i
  linear : ∀ (i j : ι) (V : X.Opens) (hV : IsAffineOpen V) (hi : V ≤ U i) (hj : V ≤ U j),
    ∃ g : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(X, V),
      projectiveSpaceAffineChart n V hV hj ≫ (ψ j).inv ≫ (f ⁻¹ᵁ U j).ι =
        (projLinearAut Γ(X, V) n g).hom ≫
          projectiveSpaceAffineChart n V hV hi ≫ (ψ i).inv ≫ (f ⁻¹ᵁ U i).ι

namespace Scheme.Modules

open Hartshorne.SheafAlgebraOperations Hartshorne.ModuleSheafAlgebra

variable {E : X.Modules} (hE : E.IsLocallyFree) (hfin : ∀ x, E.rankAt x < Cardinal.aleph0)

/-- **Changes of frames are invertible linear substitutions**: for two frames `e, e'` of `E` over
an affine open `V`, with `A = Γ(V, 𝒪_X)`, there is `(a_{kl}) ∈ GL_{n+1}(A)` with
`e_k = ∑_l a_{kl} e'_l`, so that the identification `A[x₀, …, xₙ] ≅ Γ(V, S(E))` of `e'`, after the
substitution `x_k ↦ ∑_l a_{kl} x_l`, is the identification of `e`. -/
theorem frameGradedHom_comp_linearSubstitution {V : X.Opens} (hV : IsAffineOpen V) {n : ℕ}
    {e e' : ULift.{u} (Fin (n + 1)) → Γ(E, V)} (he : Ringed.IsLocalFrame (R := X.sheaf) E V e)
    (he' : Ringed.IsLocalFrame (R := X.sheaf) E V e') :
    ∃ g : Matrix.GeneralLinearGroup (Fin (n + 1)) Γ(X, V), ∀ p,
      frameGradedHom hE hfin hV e' (linearSubstitutionGradedHom Γ(X, V) n g p) =
        frameGradedHom hE hfin hV e p := by
  classical
  -- `φ_{e₂} ∘ θ_a = φ_{e₁}` for the transition matrix `a` expressing `e₁` in the frame `e₂`
  have key : ∀ {e₁ e₂ : ULift.{u} (Fin (n + 1)) → Γ(E, V)},
      Ringed.IsLocalFrame (R := X.sheaf) E V e₂ →
      ∃ a : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(X, V), ∀ p,
        frameGradedHom hE hfin hV e₂ (linearSubstitutionGradedHom Γ(X, V) n a p) =
          frameGradedHom hE hfin hV e₁ p := by
    intro e₁ e₂ he₂
    obtain ⟨a, ha⟩ := E.chartRingHom_transition he₂ e₁
    refine ⟨fun k l => a (ULift.up k) (ULift.up l), fun p => ?_⟩
    have hC : ∀ r, frameGradedHom hE hfin hV e₂ (linearSubstitutionGradedHom Γ(X, V) n
        (fun k l => a (ULift.up k) (ULift.up l)) (C r)) = frameGradedHom hE hfin hV e₁ (C r) := by
      intro r
      rw [linearSubstitutionGradedHom_C, frameGradedHom_apply, frameGradedHom_apply, rename_C,
        chartRingHom_C, chartRingHom_C]
    have hX : ∀ k, frameGradedHom hE hfin hV e₂ (linearSubstitutionGradedHom Γ(X, V) n
        (fun k l => a (ULift.up k) (ULift.up l)) (MvPolynomial.X k)) =
          frameGradedHom hE hfin hV e₁ (MvPolynomial.X k) := by
      intro k
      rw [linearSubstitutionGradedHom_X, frameGradedHom_apply, frameGradedHom_apply, rename_X,
        ha, map_sum]
      congr 1
      simp only [map_mul, rename_C, rename_X]
      exact Equiv.ulift.symm.sum_comp (fun l => C (a (ULift.up k) l) * MvPolynomial.X l)
    induction p using MvPolynomial.induction_on with
    | C r => exact hC r
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp, hX]
  obtain ⟨a, ha⟩ := key (e₁ := e) he'
  obtain ⟨b, hb⟩ := key (e₁ := e') he
  have hinj := (frameGradedHom_bijective hE hfin hV he').1
  have hba : b * a = 1 := eq_one_of_linearSubstitutionGradedHom_apply _ fun p => hinj (by
    rw [← linearSubstitutionGradedHom_comp_apply, ha, hb])
  exact ⟨⟨a, b, mul_eq_one_comm.1 hba, hba⟩, ha⟩

variable [IsNoetherian X]

/-- On an affine open `V ⊆ U`, the inverse of the identification `π⁻¹(U) ≅ ℙⁿ_U` of a frame `e`
over `U`, on the chart at `V`, is `Proj A[x₀, …, xₙ] ≅ Proj Γ(V, S(E)) = π⁻¹(V)` given by the
restricted frame `e|_V`. -/
private lemma projectiveSpaceAffineChart_inv {U : X.Opens} {n : ℕ}
    {e : ULift.{u} (Fin (n + 1)) → Γ(E, U)} (he : Ringed.IsLocalFrame (R := X.sheaf) E U e)
    (ψ : (projectiveBundleProj hE hfin ⁻¹ᵁ U).toScheme ≅ projectiveSpaceOverScheme n U)
    (hψ : ∀ (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U),
        ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⁻¹ᵁ projectiveBundleProj hE hfin ⁻¹ᵁ V).ι ≫
            ψ.hom =
          (Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin)
              hVU)).hom ≫
            (projectiveBundleFrameIso hE hfin hV (he.restrictLE hVU)).hom ≫
              projectiveSpaceOverSchemeMap n (X.homOfLE hVU))
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    projectiveSpaceAffineChart n V hV hVU ≫ ψ.inv ≫ (projectiveBundleProj hE hfin ⁻¹ᵁ U).ι =
      (projIsoOfBijective (frameGradedHom hE hfin hV _)
          (frameGradedHom_bijective hE hfin hV (he.restrictLE hVU))).inv ≫
        ((symmetricGradedAlgebra hE hfin).restrictIso ⟨V, hV⟩).inv ≫
          (projectiveBundleProj hE hfin ⁻¹ᵁ V).ι := by
  have h2 : projectiveSpaceOverSchemeMap n (X.homOfLE hVU) ≫ ψ.inv =
      (projectiveBundleFrameIso hE hfin hV (he.restrictLE hVU)).inv ≫
        (Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono (projectiveBundleProj hE hfin)
          hVU)).inv ≫
        ((projectiveBundleProj hE hfin ⁻¹ᵁ U).ι ⁻¹ᵁ projectiveBundleProj hE hfin ⁻¹ᵁ V).ι := by
    rw [← cancel_epi ((Scheme.Opens.isoOfLE (Scheme.Hom.preimage_mono
      (projectiveBundleProj hE hfin) hVU)).hom ≫
        (projectiveBundleFrameIso hE hfin hV (he.restrictLE hVU)).hom)]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← reassoc_of% (hψ V hV hVU), Iso.hom_inv_id, Category.comp_id]
  simp only [projectiveSpaceAffineChart, Category.assoc]
  rw [reassoc_of% h2, Scheme.Opens.isoOfLE_inv_ι]
  simp only [projectiveBundleFrameIso, Iso.trans_inv, Category.assoc, asIso_inv,
    IsIso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]

/-- **`P(E)` is a projective `n`-space bundle** (Hartshorne II, Exercise 7.10(b)), with this atlas:
for `E` locally free of rank `n + 1`, the covering of `X` by the affine opens `V` on which `E` has
a frame `e`, with the identifications `π⁻¹(V) ≅ ℙⁿ_V` sending the coordinate `x_k` to `e_k`
(`exists_projectiveBundleIso_of_frame`), makes `π : P(E) ⟶ X` a projective `n`-space bundle. On an
affine `W ⊆ V ∩ V'`, the transition is the linear substitution expressing the frame `e|_W` in the
frame `e'|_W` (`frameGradedHom_comp_linearSubstitution`). -/
def projectiveBundleAtlas {n : ℕ} (hrank : ∀ x, E.rankAt x = (n + 1 : ℕ)) :
    ProjectiveSpaceBundle (projectiveBundleProj hE hfin) n where
  ι := AffineFrame E (n + 1)
  U c := c.V
  iSup_eq_top := eq_top_iff.mpr fun x _ => by
    obtain ⟨c, hc⟩ := exists_affineFrame ((isLocallyFreeOfRank_iff E (n + 1)).2 ⟨hE, hrank⟩) x
    exact Opens.mem_iSup.mpr ⟨c, hc⟩
  ψ c := (exists_projectiveBundleIso_of_frame hE hfin c.isLocalFrame).choose
  ψ_over c := (exists_projectiveBundleIso_of_frame hE hfin c.isLocalFrame).choose_spec.1
  linear i j V hV hi hj := by
    obtain ⟨g, hg⟩ := frameGradedHom_comp_linearSubstitution hE hfin hV
      (i.isLocalFrame.restrictLE hi) (j.isLocalFrame.restrictLE hj)
    refine ⟨g, ?_⟩
    rw [projectiveSpaceAffineChart_inv hE hfin j.isLocalFrame _
        (exists_projectiveBundleIso_of_frame hE hfin j.isLocalFrame).choose_spec.2,
      projectiveSpaceAffineChart_inv hE hfin i.isLocalFrame _
        (exists_projectiveBundleIso_of_frame hE hfin i.isLocalFrame).choose_spec.2]
    have hmap : (projIsoOfBijective (frameGradedHom hE hfin hV _)
          (frameGradedHom_bijective hE hfin hV (j.isLocalFrame.restrictLE hj))).hom ≫
        (projLinearAut Γ(X, V) n g).hom =
      (projIsoOfBijective (frameGradedHom hE hfin hV _)
          (frameGradedHom_bijective hE hfin hV (i.isLocalFrame.restrictLE hi))).hom := by
      simp only [projLinearAut, projIsoOfBijective_hom]
      rw [← Proj.map_comp]
      congr 1
      exact GradedRingHom.ext hg
    have hinv : (projLinearAut Γ(X, V) n g).hom ≫
        (projIsoOfBijective (frameGradedHom hE hfin hV _)
          (frameGradedHom_bijective hE hfin hV (i.isLocalFrame.restrictLE hi))).inv =
      (projIsoOfBijective (frameGradedHom hE hfin hV _)
          (frameGradedHom_bijective hE hfin hV (j.isLocalFrame.restrictLE hj))).inv := by
      rw [← cancel_epi (projIsoOfBijective (frameGradedHom hE hfin hV _)
          (frameGradedHom_bijective hE hfin hV (j.isLocalFrame.restrictLE hj))).hom,
        reassoc_of% hmap, Iso.hom_inv_id, Iso.hom_inv_id]
    rw [← reassoc_of% hinv]

/-- **`P(E)` is a projective `n`-space bundle** (Hartshorne II, Exercise 7.10(b)): if `E` is
locally free of rank `n + 1` on a Noetherian scheme `X`, then `π : P(E) ⟶ X` is a projective
`n`-space bundle. (The finiteness hypothesis `hfin` follows from `hrank` and is needed only to
form `P(E)`.) -/
theorem nonempty_projectiveSpaceBundle_projectiveBundleProj {n : ℕ}
    (hrank : ∀ x, E.rankAt x = (n + 1 : ℕ)) :
    Nonempty (ProjectiveSpaceBundle (projectiveBundleProj hE hfin) n) :=
  ⟨projectiveBundleAtlas hE hfin hrank⟩

end Scheme.Modules

end AlgebraicGeometry
