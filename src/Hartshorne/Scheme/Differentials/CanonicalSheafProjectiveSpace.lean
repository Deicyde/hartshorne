/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.EulerSequence
import Hartshorne.Scheme.ExteriorPowerExactFiltration
import Hartshorne.Scheme.Differentials.CanonicalSheaf
import Hartshorne.Scheme.Differentials.RelativeDifferentialsFibreRank
import Hartshorne.Cohomology.SmoothMorphisms.ProjectiveSpaceSmooth
import Hartshorne.Scheme.ProjectiveSpaceOverSpec
import Hartshorne.Scheme.LocallyFreeRinged
import Hartshorne.Intersection.ProjectiveLinearSubspaceCycle
import Hartshorne.Scheme.ProjectiveSpacePicard
import Hartshorne.Scheme.ProjTwistCompatibility
import Hartshorne.Scheme.RankTwoDualDeterminant
import Hartshorne.Scheme.Differentials.GeometricGenus

/-!
# The canonical sheaf of projective space

Hartshorne, *Algebraic Geometry*, II.8, Example 8.20.1 (pp. 182–183): on `X = ℙⁿ_k`,
`ω_X ≅ 𝒪_X(-n-1)` (`Hartshorne.EulerSequence.canonicalSheaf_projectiveSpace`).

The proof takes determinants in the Euler sequence `0 → Ω → 𝒪(-1)^{n+1} → 𝒪 → 0`
(`Hartshorne.ExteriorPowerExactFiltration.exteriorPower_exact_det`):
* `Ω_{ℙⁿ_k/k}` is locally free of rank `n`, since `ℙⁿ_k → Spec k` is smooth of relative
  dimension `n` (`Hartshorne.EulerSequence.toBase_smoothOfRelativeDimension`);
* `𝒪(-1)^{m}` is locally free of rank `m`
  (`AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_biproduct_const`), and the split exact
  sequences `𝒪(-1)^m → 𝒪(-1)^{m+1} → 𝒪(-1)` give `⋀^{m+1} 𝒪(-1)^{m+1} ≅ 𝒪(-m-1)`
  (`Hartshorne.EulerSequence.exteriorPower_biproduct_O1`).
-/


open CategoryTheory AlgebraicGeometry

universe u

namespace Hartshorne.EulerSequence

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {A : Type u} [CommRing A] {n : ℕ}

/-- `ℙⁿ_A → Spec A` is smooth of relative dimension `n`. -/
theorem toBase_smoothOfRelativeDimension : SmoothOfRelativeDimension n (toBase A n) := by
  have := projectiveSpaceOverSchemeProjection_smoothOfRelativeDimension n (Spec (.of A))
  let _ : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension n) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := n)).respectsIso
  have h : toBase A n = (projectiveSpaceOverSpecIso A n (Equiv.refl _)).hom ≫
      projectiveSpaceOverSchemeProjection n (Spec (.of A)) :=
    (projToProjectiveSpaceOverSpec_projection A n (Equiv.refl _)).symm
  rw [h]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension n) _ _).2 this

/-- `Ω_{ℙⁿ_A/A}` is locally free of rank `n`. -/
theorem omega_isLocallyFreeOfRank : (Ω A n).IsLocallyFreeOfRank n := by
  have := toBase_smoothOfRelativeDimension (A := A) (n := n)
  exact Scheme.relativeDifferentials_isLocallyFreeOfRank_of_smoothOfRelativeDimension _ n


end Hartshorne.EulerSequence

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Limits

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {X : Scheme.{u}}

/-- A finite direct sum of copies of an invertible module is locally free of rank the number of
copies. -/
theorem isLocallyFreeOfRank_biproduct_const {L : X.Modules} (hL : L.IsLocallyFreeOfRank 1)
    (k : ℕ) : (⨁ fun _ : Fin k => L).IsLocallyFreeOfRank k := by
  intro x
  obtain ⟨U, hx, ⟨α⟩⟩ := hL x
  refine ⟨U, hx, ⟨?_⟩⟩
  exact (restrictFunctor U.ι).mapIso (biproduct.isoCoproduct _) ≪≫
    PreservesCoproduct.iso (restrictFunctor U.ι) _ ≪≫
    Sigma.whiskerEquiv Equiv.ulift.symm (fun _ => (α ≪≫ coproductUniqueIso _).symm)

/-- The inclusion of the first `k` summands and the projection to the last one. -/
noncomputable abbrev biproductSnocComplex (L : X.Modules) (k : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (biproduct.desc fun j : Fin k => biproduct.ι (fun _ : Fin (k + 1) => L) j.castSucc)
    (biproduct.π (fun _ : Fin (k + 1) => L) (Fin.last k)) (by
      refine biproduct.hom_ext' _ _ fun j => ?_
      simp [(Fin.castSucc_lt_last j).ne])

/-- The sequence `L^k → L^{k+1} → L` is split short exact. -/
theorem biproductSnocComplex_shortExact (L : X.Modules) (k : ℕ) :
    (biproductSnocComplex L k).ShortExact := by
  refine ShortComplex.Splitting.shortExact
    { r := biproduct.lift fun j : Fin k => biproduct.π (fun _ : Fin (k + 1) => L) j.castSucc
      s := biproduct.ι (fun _ : Fin (k + 1) => L) (Fin.last k)
      f_r := by
        refine biproduct.hom_ext' _ _ fun i => biproduct.hom_ext _ _ fun j => ?_
        by_cases h : i = j
        · subst h
          simp [biproductSnocComplex]
        · simp [biproductSnocComplex, h, Fin.castSucc_inj]
      s_g := by simp [biproductSnocComplex]
      id := by
        dsimp only [biproductSnocComplex]
        rw [biproduct.lift_desc, ← biproduct.total, Fin.sum_univ_castSucc] }

end AlgebraicGeometry.Scheme.Modules

namespace Hartshorne.EulerSequence

open CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules ExteriorPowerExactFiltration

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- An isomorphism of sheaves of modules over the structure sheaf, as an isomorphism of
`𝒪_X`-modules. -/
def modulesIsoOfRinged {X : Scheme.{u}} {M N : X.Modules}
    (e : Iso (C := SheafOfModules.{u} (ringCatSheafOf X.sheaf)) M N) : M ≅ N :=
  ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

variable {k : Type u} [Field k] {n : ℕ}

variable (k n) in
/-- `𝒪(-1)^{m}` on `ℙⁿ_k`. -/
noncomputable abbrev O1pow (m : ℕ) : (Proj (grading k n)).Modules := ⨁ fun _ : Fin m => O1 k n

/-- `𝒪(-1)` on `ℙⁿ_k` is invertible. -/
theorem O1_isLocallyFreeOfRank : (O1 k n).IsLocallyFreeOfRank 1 :=
  ProjectiveSpacePicard.projTwistingSheaf_isInvertible (-1)

/-- **`⋀^{m+1} (𝒪(-1)^{m+1}) ≅ 𝒪(-m-1)`** on `ℙⁿ_k`. -/
theorem exteriorPower_biproduct_O1 : ∀ m : ℕ,
    Nonempty (moduleSheafExteriorPower (R := (Proj (grading k n)).sheaf) (m + 1)
      (O1pow k n (m + 1)) ≅ projTwistingSheaf (grading k n) (-((m : ℤ) + 1)))
  | 0 => by
    have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    exact ⟨modulesIsoOfRinged (moduleSheafExteriorPowerOneIso _) ≪≫ biproductUniqueIso _ ≪≫
      eqToIso (congrArg (projTwistingSheaf (grading k n)) (by norm_num))⟩
  | m + 1 => by
    obtain ⟨e⟩ := exteriorPower_biproduct_O1 m
    have hS := biproductSnocComplex_shortExact (O1 k n) (m + 1)
    have h₁ := (isLocallyFreeOfRank_iff_ringed _ _).1
      (isLocallyFreeOfRank_biproduct_const (O1_isLocallyFreeOfRank (k := k) (n := n)) (m + 1))
    have h₂ := (isLocallyFreeOfRank_iff_ringed _ _).1
      (isLocallyFreeOfRank_biproduct_const (O1_isLocallyFreeOfRank (k := k) (n := n)) (m + 1 + 1))
    have h₃ := (isLocallyFreeOfRank_iff_ringed _ _).1 (O1_isLocallyFreeOfRank (k := k) (n := n))
    obtain ⟨d⟩ := exteriorPower_exact_det (R := (Proj (grading k n)).sheaf) _ hS h₁ h₂ h₃
    have tm : (moduleSheafTensor (projTwistingSheaf (grading k n) (-((m : ℤ) + 1)))
        (projTwistingSheaf (grading k n) (-1)) : (Proj (grading k n)).Modules) ≅
        projTwistingSheaf (grading k n) (-((m : ℤ) + 1) + -1) :=
      modulesIsoOfRinged (Ringed.moduleSheafTensorIsoTensor _ _) ≪≫
        twistMulIso (grading k n) (ProjectiveSpacePicard.adjoin_one_eq_top k n) _ _
    exact ⟨modulesIsoOfRinged (d ≪≫ Ringed.moduleSheafTensorIsoOfIso e
        (moduleSheafExteriorPowerOneIso _)) ≪≫
      tm ≪≫ eqToIso (by congr 1)⟩

/-- **Hartshorne II.8, Example 8.20.1.** The canonical sheaf of `ℙⁿ_k` is `𝒪(-n-1)`. -/
theorem canonicalSheaf_projectiveSpace :
    Nonempty (canonicalSheaf (toBase k n) ≅ projTwistingSheaf (grading k n) (-((n : ℤ) + 1))) := by
  have hdim : topologicalKrullDim (Proj (grading k n)) = n := topologicalKrullDim_projectiveSpace
  rw [canonicalSheaf_eq (toBase k n) hdim]
  have hΩ := (isLocallyFreeOfRank_iff_ringed _ _).1 (omega_isLocallyFreeOfRank (A := k) (n := n))
  have hE := (isLocallyFreeOfRank_iff_ringed _ _).1
    (isLocallyFreeOfRank_biproduct_const (O1_isLocallyFreeOfRank (k := k) (n := n)) (n + 1))
  have hO : Ringed.IsLocallyFreeOfRank (R := (Proj (grading k n)).sheaf) (O0 k n) 1 :=
    Ringed.structureModule_isInvertible
  obtain ⟨d⟩ := exteriorPower_exact_det (R := (Proj (grading k n)).sheaf) _
    (eulerSequence (A := k) (n := n)).1 hΩ hE hO
  obtain ⟨e⟩ := exteriorPower_biproduct_O1 (k := k) (n := n) n
  exact ⟨modulesIsoOfRinged ((Ringed.moduleSheafUnitTensor _).symm ≪≫
    Ringed.moduleSheafTensorComm _ _ ≪≫
    Ringed.moduleSheafTensorIsoOfIso (Iso.refl _) (moduleSheafExteriorPowerOneIso _).symm ≪≫
    d.symm) ≪≫ e⟩

end Hartshorne.EulerSequence

namespace Hartshorne.ProjectiveSpacePicard

open Opposite AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

/-- **Negative twists have no global sections:** on `ℙⁿ_k` with `n ≥ 1`, `Γ(ℙⁿ_k, 𝒪(l)) = 0` for
`l < 0`. A nonzero section gives a rational function `φ = s / x₀^l` whose divisor is effective
with coefficient at least `-l > 0` along `H = V(x₀)`, so of positive degree, while principal
divisors have degree zero. -/
theorem projTwistingSheaf_globalSections_eq_zero (hn : 0 < n) {l : ℤ} (hl : l < 0)
    (s : (projTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) l).val.obj
      (op ⊤)) : s = 0 := by
  have hη : genericPoint (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) ∈
      (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).Opens) := trivial
  let s' : (ProjGradedModuleSheaf.sheafInType (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
      (gradedTwist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) l)).1.obj (op ⊤) := s
  suffices h : twistToFunctionField l (s'.1 ⟨_, hη⟩) = 0 from
    section_eq_zero_of_apply_genericPoint l hη s'
      (twistToFunctionField_injective l (h.trans (map_zero _).symm))
  by_contra hφ
  let u := Units.mk0 _ hφ
  have hX := projectiveSpace_satisfiesConditionStar (k := k) (n := n)
  have hdeg := projectiveSpaceWeilDivisorDegree_principalDivisor hn u
  rw [projectiveSpaceWeilDivisorDegree_apply] at hdeg
  have hcoef : ∀ P : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).PrimeDivisor,
      -(l * (hyperplaneX0 hn).toWeilDivisor.1 P.1) ≤
        ((Proj _).principalDivisor projectiveSpace_satisfiesConditionStar u).1 P.1 := fun P => by
    rw [Scheme.principalDivisor_apply]
    exact le_ord_twistToFunctionField hn l s' hη hφ P.1 trivial P.2
  have hH : ∀ P : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).PrimeDivisor,
      0 ≤ (hyperplaneX0 hn).toWeilDivisor.1 P.1 := fun P => by
    by_cases hP : P = hyperplaneX0 hn
    · subst hP
      rw [Scheme.PrimeDivisor.toWeilDivisor_apply_self]
      exact zero_le_one
    · rw [Scheme.PrimeDivisor.toWeilDivisor_apply_of_ne _ (fun h => hP (Subtype.ext h))]
  have hnonneg : ∀ P : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).PrimeDivisor,
      0 ≤ ((Proj _).principalDivisor projectiveSpace_satisfiesConditionStar u).1 P.1 *
        (projectivePrimeDivisorEquationDegree P : ℤ) := fun P =>
    mul_nonneg ((neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg hl.le (hH P))).trans (hcoef P))
      (Nat.cast_nonneg _)
  have hfin : (Function.support fun P :
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)).PrimeDivisor =>
        ((Proj _).principalDivisor projectiveSpace_satisfiesConditionStar u).1 P.1 *
          (projectivePrimeDivisorEquationDegree P : ℤ)).Finite :=
    ((Scheme.WeilDivisor.support_finite _).preimage Subtype.val_injective.injOn).subset
      fun P hP => left_ne_zero_of_mul hP
  have hle := single_le_finsum (hyperplaneX0 hn) hfin hnonneg
  rw [hdeg] at hle
  have hdegH : (projectivePrimeDivisorEquationDegree (hyperplaneX0 (k := k) hn) : ℤ) = 1 := by
    have := projectiveSpaceWeilDivisorDegree_hyperplane hn
      (MvPolynomial.isHomogeneous_X k (0 : Fin (n + 1))) (MvPolynomial.X_ne_zero 0)
    rw [projectiveSpaceWeilDivisorDegree_toWeilDivisor] at this
    exact this
  have hcH := hcoef (hyperplaneX0 hn)
  rw [Scheme.PrimeDivisor.toWeilDivisor_apply_self, mul_one] at hcH
  rw [hdegH, mul_one] at hle
  omega

end Hartshorne.ProjectiveSpacePicard

namespace Hartshorne.EulerSequence

open Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

/-- **Hartshorne II.8, Example 8.20.1, consequence.** The geometric genus of `ℙⁿ_k` is `0` for
`n ≥ 1`. -/
theorem geometricGenus_projectiveSpace (hn : 0 < n) : geometricGenus (toBase k n) = 0 := by
  obtain ⟨e⟩ := canonicalSheaf_projectiveSpace (k := k) (n := n)
  have key : ∀ a : Γ(canonicalSheaf (toBase k n), ⊤), a = 0 := fun a => by
    have h1 : e.hom.app ⊤ a = 0 :=
      ProjectiveSpacePicard.projTwistingSheaf_globalSections_eq_zero hn (by omega) _
    have h2 : e.inv.app ⊤ (e.hom.app ⊤ a) = a := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
      rfl
    rw [← h2, h1, map_zero]
  have hsub : Subsingleton (GlobalSectionsOver (toBase k n) (canonicalSheaf (toBase k n))) :=
    ⟨fun a b => (key a).trans (key b).symm⟩
  exact Module.finrank_zero_of_subsingleton

end Hartshorne.EulerSequence
