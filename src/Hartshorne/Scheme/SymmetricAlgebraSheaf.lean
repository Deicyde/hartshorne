/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Hartshorne.Scheme.SheafTensorAlgebras
import Hartshorne.RingedSpace.PicardGroup
import Hartshorne.Scheme.LocallyFreeRinged
import Hartshorne.Scheme.CoherentAffineLocalCriterion

/-!
# The graded symmetric-algebra sheaf of a finite locally free module

Hartshorne, *Algebraic Geometry*, II.7, definition of the projective bundle `P(E)` (printed
p. 162): for a Noetherian scheme `X` and a locally free `𝒪_X`-module `E` of finite rank, the
symmetric algebra `S(E) = ⊕_d S^d(E)` is a quasi-coherent sheaf of graded `𝒪_X`-algebras,
generated in degree one, with coherent homogeneous components; locally, where `E` is free, it is
a polynomial algebra.

The symmetric algebra `S(F)` and the symmetric powers `S^d F` of a module sheaf, with the grading
of `S(F)`, are constructed in `Hartshorne.Scheme.SheafTensorAlgebras` and
`Hartshorne.Scheme.SheafTensorOperations` (Hartshorne II, Exercise 5.16). Here we prove:

* **Bases of symmetric powers.** If `b` is a basis of a free module `M` indexed by a finite
  linearly ordered type `ι`, the monomials `b_{w 1} ⋯ b_{w d}` for monotone words `w : Fin d → ι`
  form a basis of `Sym^d M` (`symmetricMonomial_bijective`); there are `C(n + d - 1, d)` of them
  (`MonotoneWord.card`). The proof maps `Sym^d M` to the polynomial ring `A[T_i]`.
* **Frames.** If a family of sections of a presheaf of modules restricts to a basis over every open
  contained in `U`, its image in the sheafification is a local frame over `U`
  (`Ringed.isLocalFrame_sheafify`). Hence the monomials of degree `d` in a frame of `E` form a
  frame of `S^d E` (`Ringed.IsLocalFrame.moduleSheafSymmetricPower`), so `S^d E` is locally free of
  rank `C(n + d - 1, d)` when `E` is locally free of rank `n`
  (`Ringed.IsLocallyFreeOfRank.moduleSheafSymmetricPower`).
* **Quasi-coherence and coherence.** A locally free module of finite rank is of finite
  presentation (`Ringed.IsFiniteLocallyFree.isFinitePresentation`); `S(E)` is quasi-coherent,
  being locally a direct sum of free modules
  (`Ringed.IsFiniteLocallyFree.isQuasicoherent_moduleSheafSymmetricAlgebra`).
* **Degree zero.** `S^0 F ≅ 𝒪_X` (`moduleSheafSymmetricPowerZeroIso`), and the composite
  `𝒪_X ≅ S^0 F → S(F)` is unital and multiplicative (`moduleSheafSymmetricAlgebraι_zero_one`,
  `moduleSheafSymmetricAlgebraι_zero_mul`), so the degree-zero part of `S(F)` is `𝒪_X` as an
  algebra.
* **Generation in degree one.** `S^1 F ≅ F` (`moduleSheafSymmetricPowerOneIso`); the canonical maps
  `T^d F → S^d F`, `f₁ ⊗ ⋯ ⊗ f_d ↦ f₁ ⋯ f_d`, are epimorphisms
  (`epi_moduleSheafTensorToSymmetricPower`), and so is the multiplicative map `T(F) → S(F)` from
  the tensor algebra (`epi_moduleSheafTensorToSymmetricAlgebra`,
  `moduleSheafTensorToSymmetricAlgebra_mul`).
* **Polynomial description.** If `E ≅ 𝒪_X^{⊕ ι}` with `ι` finite, then `S(E)` is isomorphic, as
  a sheaf of `𝒪_X`-algebras, to the polynomial algebra `𝒪_X[T_i]`, the sheafification of
  `U ↦ 𝒪_X(U)[T_i]` (`exists_polynomialAlgebraSheaf_iso_symmetricAlgebra`,
  `polynomialAlgebraSymmetricAlgebraIso`). Restriction to an open subscheme commutes with the
  symmetric algebra as sheaves of algebras (`ModuleSheafAlgebra.restrict`,
  `symmetricAlgebraRestrictIso`, `symmetricAlgebraRestrictIso_mul`), so on every open `U` where
  `E` is free, `S(E)|_U ≅ 𝒪_U[T_i]` as sheaves of graded algebras
  (`Scheme.Modules.symmetricAlgebra_restrict_iso_polynomial`).

The statements for schemes are in `AlgebraicGeometry.Scheme.Modules`: `symmetricAlgebra`,
`symmetricPower`, `symmetricAlgebra_graded`, `symmetricAlgebra_isQuasicoherent`,
`symmetricPower_isQuasicoherent`, `symmetricPower_isCoherent`, `symmetricPower_isLocallyFree`,
`symmetricPower_isLocallyFreeOfRank`, `symmetricAlgebra_restrict_iso_polynomial`,
`symmetricPowerOneIso`, `symmetricPowerZeroIso`, `symmetricPowerZeroIso_inv_one` and
`symmetricPowerZeroIso_inv_mul`.
-/

universe u

open CategoryTheory TopologicalSpace Opposite Limits
open scoped TensorProduct

namespace Hartshorne

namespace SheafTensorOperations

section SymmetricPowerBasis

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
  {ι : Type u} [LinearOrder ι] (d : ℕ)

variable (ι) in
/-- The monotone words of length `d` in `ι`; they index the monomials of degree `d` in
variables indexed by `ι`. -/
abbrev MonotoneWord := {w : Fin d → ι // Monotone w}

noncomputable instance [Finite ι] : Fintype (MonotoneWord ι d) := Fintype.ofFinite _

/-- The monotone rearrangement of a word. -/
noncomputable def MonotoneWord.sort (w : Fin d → ι) : MonotoneWord ι d :=
  ⟨w ∘ Tuple.sort w, Tuple.monotone_sort w⟩

/-- The multiset of letters of a monotone word. -/
def MonotoneWord.toSym (w : MonotoneWord ι d) : Sym ι d :=
  ⟨(List.ofFn w.1 : Multiset ι), by simp⟩

theorem MonotoneWord.toSym_injective : Function.Injective (MonotoneWord.toSym (ι := ι) d) := by
  intro w w' h
  have h' : List.ofFn w.1 = List.ofFn w'.1 :=
    List.Perm.eq_of_pairwise' w.2.sortedLE_ofFn.pairwise w'.2.sortedLE_ofFn.pairwise
      (Multiset.coe_eq_coe.mp (congrArg Subtype.val h))
  exact Subtype.ext (List.ofFn_injective h')

theorem MonotoneWord.toSym_surjective : Function.Surjective (MonotoneWord.toSym (ι := ι) d) := by
  intro s
  let l := s.1.sort (· ≤ ·)
  have hl : l.length = d := by simp [l, Multiset.length_sort]
  have hmono : Monotone l.get :=
    List.sortedLE_iff_pairwise.mpr (Multiset.pairwise_sort _ _)
  refine ⟨⟨fun i => l.get (Fin.cast hl.symm i), fun i j hij => hmono hij⟩, ?_⟩
  apply Subtype.ext
  change ((List.ofFn fun i => l.get (Fin.cast hl.symm i) : List ι) : Multiset ι) = s.1
  have : (List.ofFn fun i => l.get (Fin.cast hl.symm i)) = l := by
    apply List.ext_get (by simp [hl])
    intro n h1 h2
    simp
  rw [this]
  exact Multiset.sort_eq _ _

/-- Monotone words of length `d` correspond to multisets of size `d`. -/
noncomputable def MonotoneWord.equivSym : MonotoneWord ι d ≃ Sym ι d :=
  Equiv.ofBijective _ ⟨MonotoneWord.toSym_injective d, MonotoneWord.toSym_surjective d⟩

/-- **Stars and bars.** There are `C(n + d - 1, d)` monotone words of length `d` in `n` letters. -/
theorem MonotoneWord.card [Fintype ι] :
    Fintype.card (MonotoneWord ι d) = (Fintype.card ι + d - 1).choose d := by
  classical
  rw [Fintype.card_congr (MonotoneWord.equivSym d), Sym.card_sym_eq_choose]

variable (A M) in
/-- The monomial `b_{w 1} ⋯ b_{w d}` in `Sym^d M` attached to a family `b` and a monotone word
`w`. -/
noncomputable def symmetricMonomial (b : ι → M) (w : MonotoneWord ι d) :
    SymmetricPowerQuotient A M d :=
  symmetricPowerTprod A M d (b ∘ w.1)

theorem symmetricPowerTprod_comp_eq_monomial (b : ι → M) (w : Fin d → ι) :
    symmetricPowerTprod A M d (b ∘ w) = symmetricMonomial A M d b (MonotoneWord.sort d w) :=
  (symmetricPowerTprod_perm d (Tuple.sort w) (b ∘ w)).symm

theorem symmetricPowerMap_symmetricMonomial {B N : Type u} [CommRing B] [AddCommGroup N]
    [Module B N] (σ : A →+* B) (f : M →ₛₗ[σ] N) (b : ι → M) (w : MonotoneWord ι d) :
    symmetricPowerMap d σ f (symmetricMonomial A M d b w) = symmetricMonomial B N d (f ∘ b) w :=
  symmetricPowerMap_tprod d σ f _

/-- The exponent vector of the monomial attached to a monotone word. -/
noncomputable def MonotoneWord.exponent (w : MonotoneWord ι d) : ι →₀ ℕ :=
  ∑ i, Finsupp.single (w.1 i) 1

theorem MonotoneWord.exponent_injective :
    Function.Injective (MonotoneWord.exponent (ι := ι) d) := by
  intro w w' h
  apply MonotoneWord.toSym_injective d
  apply Subtype.ext
  have key : ∀ v : MonotoneWord ι d, Finsupp.toMultiset (MonotoneWord.exponent d v) =
      (MonotoneWord.toSym d v).1 := by
    intro v
    simp only [MonotoneWord.exponent, map_sum, Finsupp.toMultiset_single, one_nsmul,
      MonotoneWord.toSym]
    rw [← Fin.univ_val_map, Finset.sum_eq_multiset_sum]
    conv_rhs => rw [← Multiset.sum_map_singleton (Multiset.map _ _), Multiset.map_map]
    rfl
  rw [← key, ← key, h]

variable [Fintype ι]

/-- **`Sym^d` of a free module is free on the monomials of degree `d`.** If `b` is a basis of `M`
(the linear combination map `(ι → A) → M` is bijective), then the monomials
`b_{w 1} ⋯ b_{w d}`, for monotone words `w` of length `d`, form a basis of `Sym^d M`. -/
theorem symmetricMonomial_bijective {b : ι → M}
    (hb : Function.Bijective (Fintype.linearCombination A b)) :
    Function.Bijective (Fintype.linearCombination A (symmetricMonomial A M d b)) := by
  classical
  let L := LinearEquiv.ofBijective _ hb
  have hm : ∀ m : M, m = ∑ j, L.symm m j • b j := fun m => by
    conv_lhs => rw [← L.apply_symm_apply m]
    exact Fintype.linearCombination_apply _ _ _
  have hLb : ∀ j, L.symm (b j) = Pi.single j 1 := fun j => by
    rw [LinearEquiv.symm_apply_eq]
    change b j = Fintype.linearCombination A b (Pi.single j 1)
    rw [Fintype.linearCombination_apply_single, one_smul]
  constructor
  · rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    let g : M →ₗ[A] MvPolynomial ι A :=
      Fintype.linearCombination A (fun j => MvPolynomial.X j) ∘ₗ L.symm.toLinearMap
    have hg : ∀ j, g (b j) = MvPolynomial.X j := fun j => by
      change Fintype.linearCombination A _ (L.symm (b j)) = _
      rw [hLb, Fintype.linearCombination_apply_single, one_smul]
    let φ : MultilinearMap A (fun _ : Fin d => M) (MvPolynomial ι A) :=
      (MultilinearMap.mkPiAlgebra A (Fin d) (MvPolynomial ι A)).compLinearMap (fun _ => g)
    have hφ : ∀ (e : Equiv.Perm (Fin d)) (m : Fin d → M), φ (m ∘ e) = φ m := fun e m => by
      simp only [φ, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
        Function.comp_apply]
      exact Equiv.prod_comp e (fun i => g (m i))
    let Ψ := symmetricPowerLift d φ hφ
    have hΨ : Ψ ∘ symmetricMonomial A M d b =
        (MvPolynomial.basisMonomials ι A) ∘ MonotoneWord.exponent d := by
      funext w
      simp only [Function.comp_apply, Ψ, symmetricMonomial, symmetricPowerLift_tprod, φ,
        MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, hg,
        MvPolynomial.coe_basisMonomials, MonotoneWord.exponent, MvPolynomial.monomial_sum_one]
      rfl
    refine LinearIndependent.of_comp Ψ ?_
    rw [hΨ]
    exact (MvPolynomial.basisMonomials ι A).linearIndependent.comp _
      (MonotoneWord.exponent_injective d)
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff,
      ← span_symmetricPowerTprod d, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    rw [show m = fun i => ∑ j, L.symm (m i) j • b j from funext fun i => hm (m i),
      MultilinearMap.map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨MonotoneWord.sort d r, ?_⟩)
    exact (symmetricPowerTprod_comp_eq_monomial d b r).symm

end SymmetricPowerBasis

section DegreeOne

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

variable (A M) in
/-- The first symmetric power of a module is the module itself: `Sym^1 M ≅ M`,
`m ↦ m` on generators. -/
noncomputable def symmetricPowerOneEquiv : SymmetricPowerQuotient A M 1 ≃ₗ[A] M :=
  LinearEquiv.ofLinearMap
    (symmetricPowerLift 1 (MultilinearMap.ofSubsingleton A M M 0 LinearMap.id)
      (fun e m => by rw [Subsingleton.elim e 1]; rfl))
    ((symmetricPowerTprod A M 1).toLinearMap 0 0)
    (by
      ext x
      simp [MultilinearMap.toLinearMap])
    (by
      apply symmetricPower_linearMap_ext
      intro m
      simp only [LinearMap.coe_comp, Function.comp_apply, symmetricPowerLift_tprod,
        MultilinearMap.ofSubsingleton_apply_apply, LinearMap.id_coe, id_eq,
        MultilinearMap.toLinearMap_apply]
      congr 1
      funext i
      rw [Subsingleton.elim i 0]
      simp)

theorem symmetricPowerOneEquiv_tprod (m : Fin 1 → M) :
    symmetricPowerOneEquiv A M (symmetricPowerTprod A M 1 m) = m 0 := by
  simp [symmetricPowerOneEquiv]

theorem symmetricPowerOneEquiv_map {B N : Type u} [CommRing B] [AddCommGroup N] [Module B N]
    (σ : A →+* B) (f : M →ₛₗ[σ] N) (x : SymmetricPowerQuotient A M 1) :
    symmetricPowerOneEquiv B N (symmetricPowerMap 1 σ f x) = f (symmetricPowerOneEquiv A M x) :=
  semilinear_eq_comp_of_span (span_symmetricPowerTprod 1)
    (((symmetricPowerOneEquiv B N).toLinearMap).comp (symmetricPowerMap 1 σ f))
    (symmetricPowerOneEquiv A M).toLinearMap f (fun _ => rfl)
    (fun m => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        symmetricPowerMap_tprod, symmetricPowerOneEquiv_tprod]) x

end DegreeOne

section DegreeZero

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]

variable (A M) in
/-- The linear map `Sym^0 M → A` sending the empty product to `1`. -/
noncomputable def symmetricPowerZeroLift : SymmetricPowerQuotient A M 0 →ₗ[A] A :=
  symmetricPowerLift 0 (MultilinearMap.constOfIsEmpty A (fun _ : Fin 0 => M) (1 : A))
    (fun _ _ => rfl)

theorem symmetricPowerZeroLift_tprod (m : Fin 0 → M) :
    symmetricPowerZeroLift A M (symmetricPowerTprod A M 0 m) = 1 :=
  symmetricPowerLift_tprod 0 _ _ m

variable (A M) in
/-- The zeroth symmetric power of a module is the base ring: `Sym^0 M ≅ A`, the empty product
corresponding to `1`. -/
noncomputable def symmetricPowerZeroEquiv : SymmetricPowerQuotient A M 0 ≃ₗ[A] A :=
  LinearEquiv.ofLinearMap (symmetricPowerZeroLift A M)
    (LinearMap.toSpanSingleton A _ (symmetricPowerTprod A M 0 Fin.elim0))
    (by
      ext
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply,
        one_smul, LinearMap.id_coe, id_eq]
      exact symmetricPowerZeroLift_tprod _)
    (by
      apply symmetricPower_linearMap_ext
      intro m
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply,
        LinearMap.id_coe, id_eq, symmetricPowerZeroLift_tprod, one_smul]
      exact congrArg _ (Subsingleton.elim _ _))

theorem symmetricPowerZeroEquiv_tprod (m : Fin 0 → M) :
    symmetricPowerZeroEquiv A M (symmetricPowerTprod A M 0 m) = 1 :=
  symmetricPowerZeroLift_tprod m

theorem symmetricPowerZeroEquiv_symm_one :
    (symmetricPowerZeroEquiv A M).symm 1 = symmetricPowerTprod A M 0 Fin.elim0 := by
  rw [LinearEquiv.symm_apply_eq, symmetricPowerZeroEquiv_tprod]

theorem symmetricPowerZeroEquiv_map {B N : Type u} [CommRing B] [AddCommGroup N] [Module B N]
    (σ : A →+* B) (f : M →ₛₗ[σ] N) (x : SymmetricPowerQuotient A M 0) :
    symmetricPowerZeroEquiv B N (symmetricPowerMap 0 σ f x) = σ (symmetricPowerZeroEquiv A M x) :=
  semilinear_eq_comp_of_span (span_symmetricPowerTprod 0)
    (((symmetricPowerZeroEquiv B N).toLinearMap).comp (symmetricPowerMap 0 σ f))
    (symmetricPowerZeroEquiv A M).toLinearMap σ.toSemilinearMap (fun _ => rfl)
    (fun m => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        symmetricPowerMap_tprod, symmetricPowerZeroEquiv_tprod]
      exact σ.map_one.symm) x

/-- The degree-zero part of the symmetric algebra is spanned by `1`. -/
theorem symmetricPowerToAlgebra_zero_tprod (m : Fin 0 → M) :
    symmetricPowerToAlgebra A M 0 (symmetricPowerTprod A M 0 m) = 1 := by
  rw [symmetricPowerTprod_apply, symmetricPowerToAlgebra_mk, TensorPower.toTensorAlgebra_tprod,
    TensorAlgebra.tprod_apply]
  simp

end DegreeZero

section PolynomialNaturality

variable {A B : Type u} [CommRing A] [CommRing B] {M N : Type u} [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module B N] {ι : Type u}

/-- The identification of the symmetric algebra of a free module with a polynomial algebra is
compatible with a semilinear map sending a basis to a basis. -/
theorem equivMvPolynomial_symm_map (σ : A →+* B) (g : M →ₛₗ[σ] N) (bM : Module.Basis ι A M)
    (bN : Module.Basis ι B N) (hg : ∀ i, g (bM i) = bN i) (p : MvPolynomial ι A) :
    (SymmetricAlgebra.equivMvPolynomial bN).symm (MvPolynomial.map σ p) =
      symmetricAlgebraRingHom σ g ((SymmetricAlgebra.equivMvPolynomial bM).symm p) := by
  let φ₁ := (SymmetricAlgebra.equivMvPolynomial bN).symm.toRingEquiv.toRingHom.comp
    (MvPolynomial.map (σ := ι) σ)
  let φ₂ := (symmetricAlgebraRingHom σ g).comp
    (SymmetricAlgebra.equivMvPolynomial bM).symm.toRingEquiv.toRingHom
  have h : φ₁ = φ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [φ₁, φ₂, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C]
      rw [← MvPolynomial.algebraMap_eq, ← MvPolynomial.algebraMap_eq]
      change (SymmetricAlgebra.equivMvPolynomial bN).symm (algebraMap _ _ (σ r)) =
        symmetricAlgebraRingHom σ g ((SymmetricAlgebra.equivMvPolynomial bM).symm
          (algebraMap _ _ r))
      rw [AlgEquiv.commutes, AlgEquiv.commutes, symmetricAlgebraRingHom_algebraMap]
    · simp only [φ₁, φ₂, RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X]
      change (SymmetricAlgebra.equivMvPolynomial bN).symm (MvPolynomial.X i) =
        symmetricAlgebraRingHom σ g
          ((SymmetricAlgebra.equivMvPolynomial bM).symm (MvPolynomial.X i))
      rw [SymmetricAlgebra.equivMvPolynomial_symm_X, SymmetricAlgebra.equivMvPolynomial_symm_X,
        symmetricAlgebraRingHom_ι, hg]
  exact RingHom.congr_fun h p

end PolynomialNaturality

end SheafTensorOperations

section DegreeOneSheaf

open SheafTensorOperations

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
  (F : SheafOfModules.{u} (siteRingCatSheaf R))

/-- The presheaf `U ↦ Sym^1 F(U)` is the presheaf of sections of `F`. -/
noncomputable def symmetricPowerPresheafOneIso :
    moduleSheafSymmetricPowerPresheaf 1 F ≅
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj F :=
  PresheafOfModules.isoMk (fun U => (symmetricPowerOneEquiv _ (F.val.obj U)).toModuleIso)
    (fun U V i => by
      ext x
      exact symmetricPowerOneEquiv_map _ (F.val.restrictₛₗ i) x)

/-- **The degree-one part of the symmetric algebra.** `S^1 F ≅ F`. -/
noncomputable def moduleSheafSymmetricPowerOneIso : moduleSheafSymmetricPower 1 F ≅ F :=
  (PresheafOfModules.sheafification (𝟙 (siteRingCatSheaf R).obj)).mapIso
      (symmetricPowerPresheafOneIso F) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteRingCatSheaf R).obj)).counit.app F)

end DegreeOneSheaf

section DegreeZeroSheaf

open SheafTensorOperations

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
  (F : SheafOfModules.{u} (siteRingCatSheaf R))

/-- The presheaf `U ↦ Sym^0 F(U)` is the presheaf of sections of the structure sheaf. -/
noncomputable def symmetricPowerPresheafZeroIso :
    moduleSheafSymmetricPowerPresheaf 0 F ≅
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).obj
        (SheafOfModules.unit (siteRingCatSheaf R)) :=
  PresheafOfModules.isoMk (fun U => (symmetricPowerZeroEquiv _ (F.val.obj U)).toModuleIso)
    (fun U V i => by
      ext x
      exact symmetricPowerZeroEquiv_map _ (F.val.restrictₛₗ i) x)

/-- **The degree-zero part of the symmetric algebra.** `S^0 F ≅ 𝒪_X`. -/
noncomputable def moduleSheafSymmetricPowerZeroIso :
    moduleSheafSymmetricPower 0 F ≅ SheafOfModules.unit (siteRingCatSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (siteRingCatSheaf R).obj)).mapIso
      (symmetricPowerPresheafZeroIso F) ≪≫
    asIso ((PresheafOfModules.sheafificationAdjunction (𝟙 (siteRingCatSheaf R).obj)).counit.app
      (SheafOfModules.unit (siteRingCatSheaf R)))

/-- The isomorphism `𝒪_X ≅ S^0 F` sends the section `1` to the class of the empty product. -/
theorem moduleSheafSymmetricPowerZeroIso_inv_one (U : Cᵒᵖ) :
    (moduleSheafSymmetricPowerZeroIso F).inv.val.app U (1 : (siteRingCatSheaf R).obj.obj U) =
      (moduleSheafSymmetricPowerUnit 0 F).app U
        (symmetricPowerTprod _ (F.val.obj U) 0 Fin.elim0) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (siteRingCatSheaf R).obj)
  let G := SheafOfModules.forget (siteRingCatSheaf R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (siteRingCatSheaf R).obj)
  have hc : G.map (inv (adj.counit.app (SheafOfModules.unit (siteRingCatSheaf R)))) =
      adj.unit.app (G.obj (SheafOfModules.unit (siteRingCatSheaf R))) := by
    rw [Functor.map_inv]
    exact IsIso.inv_eq_of_inv_hom_id (adj.right_triangle_components _)
  let L := PresheafOfModules.sheafification (𝟙 (siteRingCatSheaf R).obj)
  have h1 := congrArg
    (fun φ => (PresheafOfModules.Hom.app φ U).hom (1 : (siteRingCatSheaf R).obj.obj U)) hc
  have h2 := congrArg
    (fun φ => (PresheafOfModules.Hom.app φ U).hom (1 : (siteRingCatSheaf R).obj.obj U))
    (adj.unit.naturality (symmetricPowerPresheafZeroIso F).inv)
  simp only at h1 h2
  calc _ = ((L ⋙ G).map (symmetricPowerPresheafZeroIso F).inv).app U
        ((G.map (inv (adj.counit.app (SheafOfModules.unit (siteRingCatSheaf R))))).app U
          (1 : (siteRingCatSheaf R).obj.obj U)) := rfl
    _ = ((L ⋙ G).map (symmetricPowerPresheafZeroIso F).inv).app U
        ((adj.unit.app (G.obj (SheafOfModules.unit (siteRingCatSheaf R)))).app U
          (1 : (siteRingCatSheaf R).obj.obj U)) := by rw [h1]
    _ = _ := by
      refine h2.symm.trans ?_
      change (moduleSheafSymmetricPowerUnit 0 F).app U
        ((symmetricPowerZeroEquiv _ (F.val.obj U)).symm 1) = _
      rw [symmetricPowerZeroEquiv_symm_one]

end DegreeZeroSheaf

section DegreeZeroAlgebra

open SheafTensorOperations SheafAlgebraOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (F : SheafOfModules.{u} (ringCatSheafOf R))

/-- **The identification `𝒪_X ≅ S^0 F` is unital:** followed by the inclusion `S^0 F → S(F)`, it
sends the section `1` of `𝒪_X` to the unit of the sheaf of algebras `S(F)`. -/
theorem moduleSheafSymmetricAlgebraι_zero_one (U : (Opens X)ᵒᵖ) :
    (moduleSheafSymmetricAlgebraι 0 F).val.app U
        ((moduleSheafSymmetricPowerZeroIso F).inv.val.app U (1 : (ringCatSheafOf R).obj.obj U)) =
      (moduleSheafSymmetricAlgebraStructure F).one U := by
  rw [moduleSheafSymmetricPowerZeroIso_inv_one, moduleSheafSymmetricAlgebra_one]
  refine (sheafifyMap_unit _ U _).trans (congrArg _ ?_)
  exact symmetricPowerToAlgebra_zero_tprod _

/-- The composite `𝒪_X ≅ S^0 F → S(F)` sends a section `a` of `𝒪_X` to `a • 1`. -/
theorem moduleSheafSymmetricAlgebraι_zero_apply (U : (Opens X)ᵒᵖ)
    (a : (ringCatSheafOf R).obj.obj U) :
    (moduleSheafSymmetricAlgebraι 0 F).val.app U
        ((moduleSheafSymmetricPowerZeroIso F).inv.val.app U a) =
      a • (moduleSheafSymmetricAlgebraStructure F).one U := by
  have h : (moduleSheafSymmetricPowerZeroIso F).inv.val.app U a =
      a • (moduleSheafSymmetricPowerZeroIso F).inv.val.app U (1 : (ringCatSheafOf R).obj.obj U) :=
    (congrArg ((moduleSheafSymmetricPowerZeroIso F).inv.val.app U) (mul_one a).symm).trans
      (map_smul ((moduleSheafSymmetricPowerZeroIso F).inv.val.app U).hom a
        (1 : (ringCatSheafOf R).obj.obj U))
  rw [← moduleSheafSymmetricAlgebraι_zero_one, ← map_smul]
  exact congrArg ((moduleSheafSymmetricAlgebraι 0 F).val.app U) h

/-- **The identification `𝒪_X ≅ S^0 F` is multiplicative:** followed by the inclusion
`S^0 F → S(F)`, it sends products of sections of `𝒪_X` to products in `S(F)`. -/
theorem moduleSheafSymmetricAlgebraι_zero_mul (U : (Opens X)ᵒᵖ)
    (a b : (ringCatSheafOf R).obj.obj U) :
    (moduleSheafSymmetricAlgebraι 0 F).val.app U
        ((moduleSheafSymmetricPowerZeroIso F).inv.val.app U (a * b)) =
      (moduleSheafSymmetricAlgebraStructure F).mul.app U
        ((moduleSheafSymmetricAlgebraι 0 F).val.app U
          ((moduleSheafSymmetricPowerZeroIso F).inv.val.app U a))
        ((moduleSheafSymmetricAlgebraι 0 F).val.app U
          ((moduleSheafSymmetricPowerZeroIso F).inv.val.app U b)) := by
  rw [moduleSheafSymmetricAlgebraι_zero_apply, moduleSheafSymmetricAlgebraι_zero_apply,
    moduleSheafSymmetricAlgebraι_zero_apply, LinearMap.map_smul₂, LinearMap.map_smul,
    (moduleSheafSymmetricAlgebraStructure F).mul_one, smul_smul]

end DegreeZeroAlgebra

section Generation

open SheafTensorOperations SheafAlgebraOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- A morphism from the sheafification of a presheaf of `𝒪_X`-algebras to a sheaf of
`𝒪_X`-algebras is multiplicative as soon as it is multiplicative on the images of presheaf
sections. -/
theorem PresheafAlgebra.sheafify_hom_mul
    {P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (S : PresheafAlgebra P)
    {H : SheafOfModules.{u} (ringCatSheafOf R)} (T : ModuleSheafAlgebra H) (ψ : sheafify P ⟶ H)
    (hψ : ∀ U a b, ψ.val.app U ((sheafifyUnit P).app U (S.mul.app U a b)) =
      T.mul.app U (ψ.val.app U ((sheafifyUnit P).app U a))
        (ψ.val.app U ((sheafifyUnit P).app U b)))
    (U : (Opens X)ᵒᵖ) (a b : (sheafify P).val.obj U) :
    ψ.val.app U (S.sheafification.mul.app U a b) =
      T.mul.app U (ψ.val.app U a) (ψ.val.app U b) := by
  obtain ⟨U⟩ := U
  apply sheaf_section_ext H
  intro x hx
  obtain ⟨V₁, h₁, i₁, p₁, e₁⟩ := exists_unit_eq_map P a hx
  obtain ⟨V₂, h₂, i₂, p₂, e₂⟩ := exists_unit_eq_map P b hx
  let W := V₁ ⊓ V₂
  let k : W ⟶ U := homOfLE inf_le_left ≫ i₁
  refine ⟨W, ⟨h₁, h₂⟩, k, ?_⟩
  obtain ⟨q₁, ha⟩ := map_eq_unit_of_le P e₁ (homOfLE inf_le_left) k
  obtain ⟨q₂, hb⟩ := map_eq_unit_of_le P e₂ (homOfLE inf_le_right) k
  have key : ∀ q₁ q₂ : P.obj (op W),
      ψ.val.app _ (S.sheafification.mul.app _ ((sheafifyUnit P).app _ q₁)
        ((sheafifyUnit P).app _ q₂)) = T.mul.app _
        (ψ.val.app _ ((sheafifyUnit P).app _ q₁))
        (ψ.val.app _ ((sheafifyUnit P).app _ q₂)) := by
    intro q₁ q₂
    exact (congrArg (ψ.val.app (op W)) (S.sheafification_mul_unit (op W) q₁ q₂)).trans
      (hψ _ q₁ q₂)
  rw [← PresheafOfModules.naturality_apply, S.sheafification.mul.naturality,
    T.mul.naturality, ← PresheafOfModules.naturality_apply,
    ← PresheafOfModules.naturality_apply]
  have e1 := congrArg₂ (fun s t => ψ.val.app (op W)
    (S.sheafification.mul.app (op W) s t)) ha hb
  have e2 := congrArg₂ (fun s t => T.mul.app (op W)
    (ψ.val.app (op W) s) (ψ.val.app (op W) t)) ha hb
  exact e1.trans ((key q₁ q₂).trans e2.symm)

/-- A multiplicative morphism of presheaves of `𝒪_X`-algebras induces a multiplicative morphism of
their sheafifications. -/
theorem PresheafAlgebra.sheafifyMap_mul
    {P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (S : PresheafAlgebra P)
    (S' : PresheafAlgebra Q) (f : P ⟶ Q)
    (hf : ∀ U a b, f.app U (S.mul.app U a b) = S'.mul.app U (f.app U a) (f.app U b))
    (U : (Opens X)ᵒᵖ) (a b : (sheafify P).val.obj U) :
    (sheafifyMap f).val.app U (S.sheafification.mul.app U a b) =
      S'.sheafification.mul.app U ((sheafifyMap f).val.app U a) ((sheafifyMap f).val.app U b) := by
  obtain ⟨U⟩ := U
  apply sheaf_section_ext (sheafify Q)
  intro x hx
  obtain ⟨V₁, h₁, i₁, p₁, e₁⟩ := exists_unit_eq_map P a hx
  obtain ⟨V₂, h₂, i₂, p₂, e₂⟩ := exists_unit_eq_map P b hx
  let W := V₁ ⊓ V₂
  let k : W ⟶ U := homOfLE inf_le_left ≫ i₁
  refine ⟨W, ⟨h₁, h₂⟩, k, ?_⟩
  obtain ⟨q₁, ha⟩ := map_eq_unit_of_le P e₁ (homOfLE inf_le_left) k
  obtain ⟨q₂, hb⟩ := map_eq_unit_of_le P e₂ (homOfLE inf_le_right) k
  have key : ∀ q₁ q₂ : P.obj (op W),
      (sheafifyMap f).val.app _ (S.sheafification.mul.app _ ((sheafifyUnit P).app _ q₁)
        ((sheafifyUnit P).app _ q₂)) = S'.sheafification.mul.app _
        ((sheafifyMap f).val.app _ ((sheafifyUnit P).app _ q₁))
        ((sheafifyMap f).val.app _ ((sheafifyUnit P).app _ q₂)) := by
    intro q₁ q₂
    have h1 := S.sheafification_mul_unit (op W) q₁ q₂
    have h2 := S'.sheafification_mul_unit (op W) (f.app _ q₁) (f.app _ q₂)
    have h3 := fun q => sheafifyMap_unit f (op W) q
    exact (congrArg ((sheafifyMap f).val.app (op W)) h1).trans ((h3 _).trans
      ((congrArg ((sheafifyUnit Q).app (op W)) (hf _ q₁ q₂)).trans (h2.symm.trans
        (congrArg₂ (fun s t => S'.sheafification.mul.app (op W) s t)
          (h3 q₁).symm (h3 q₂).symm))))
  rw [← PresheafOfModules.naturality_apply, S.sheafification.mul.naturality,
    S'.sheafification.mul.naturality, ← PresheafOfModules.naturality_apply,
    ← PresheafOfModules.naturality_apply]
  have e1 := congrArg₂ (fun s t => (sheafifyMap f).val.app (op W)
    (S.sheafification.mul.app (op W) s t)) ha hb
  have e2 := congrArg₂ (fun s t => S'.sheafification.mul.app (op W)
    ((sheafifyMap f).val.app (op W) s) ((sheafifyMap f).val.app (op W) t)) ha hb
  exact e1.trans ((key q₁ q₂).trans e2.symm)

/-- A unital morphism of presheaves of `𝒪_X`-algebras induces a unital morphism of their
sheafifications. -/
theorem PresheafAlgebra.sheafifyMap_one
    {P Q : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} (S : PresheafAlgebra P)
    (S' : PresheafAlgebra Q) (f : P ⟶ Q) (hf : ∀ U, f.app U (S.one U) = S'.one U)
    (U : (Opens X)ᵒᵖ) :
    (sheafifyMap f).val.app U (S.sheafification.one U) = S'.sheafification.one U :=
  (sheafifyMap_unit f U _).trans (congrArg _ (hf U))

variable (F : SheafOfModules.{u} (ringCatSheafOf R)) (d : ℕ)

/-- The quotient maps `⨂^d F(U) → Sym^d F(U)`, as a morphism of presheaves of modules. -/
noncomputable def tensorToSymmetricPowerPresheaf :
    moduleSheafTensorPowerPresheaf d F ⟶ moduleSheafSymmetricPowerPresheaf d F where
  app U := ModuleCat.ofHom (symmetricPowerRel _ (F.val.obj U) d).mkQ
  naturality _ := rfl

/-- The canonical epimorphism `T^d F → S^d F`, `f₁ ⊗ ⋯ ⊗ f_d ↦ f₁ ⋯ f_d`. -/
noncomputable def moduleSheafTensorToSymmetricPower :
    moduleSheafTensorPower d F ⟶ moduleSheafSymmetricPower d F :=
  sheafifyMap (tensorToSymmetricPowerPresheaf F d)

/-- **`S^d F` is generated by products of `d` sections of `F`:** the canonical map
`T^d F → S^d F` is an epimorphism. -/
instance epi_moduleSheafTensorToSymmetricPower :
    Epi (moduleSheafTensorToSymmetricPower F d) := by
  have : Epi (tensorToSymmetricPowerPresheaf F d) :=
    PresheafOfModules.epi_of_surjective fun U => Submodule.mkQ_surjective _
  exact (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).map_epi _

/-- The canonical map `T^d F → S^d F` sends `f₁ ⊗ ⋯ ⊗ f_d` to the symmetric product
`f₁ ⋯ f_d`. -/
theorem moduleSheafTensorToSymmetricPower_multilinear (U : (Opens X)ᵒᵖ)
    (m : Fin d → F.val.obj U) :
    (moduleSheafTensorToSymmetricPower F d).val.app U
        ((moduleSheafTensorPowerMultilinear d F).app U m) =
      (moduleSheafSymmetricPowerMultilinear d F).app U m :=
  sheafifyMap_unit _ U _

/-- The quotient maps `T(F(U)) → S(F(U))`, as a morphism of presheaves of modules. -/
noncomputable def tensorToSymmetricAlgebraPresheaf :
    moduleSheafTensorAlgebraPresheaf F ⟶ moduleSheafSymmetricAlgebraPresheaf F where
  app U := ModuleCat.ofHom (SymmetricAlgebra.algHom _ (F.val.obj U)).toLinearMap
  naturality i := by
    ext t
    exact (symmetricAlgebraRingHom_algHom _ (F.val.restrictₛₗ i) t).symm

/-- The canonical map `T(F) → S(F)` of sheaves of algebras. -/
noncomputable def moduleSheafTensorToSymmetricAlgebra :
    moduleSheafTensorAlgebra F ⟶ moduleSheafSymmetricAlgebra F :=
  sheafifyMap (tensorToSymmetricAlgebraPresheaf F)

/-- **`S(F)` is a quotient of the tensor algebra:** the canonical map `T(F) → S(F)` is an
epimorphism. -/
instance epi_moduleSheafTensorToSymmetricAlgebra :
    Epi (moduleSheafTensorToSymmetricAlgebra F) := by
  have : Epi (tensorToSymmetricAlgebraPresheaf F) :=
    PresheafOfModules.epi_of_surjective fun U => SymmetricAlgebra.algHom_surjective _ _
  exact (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).map_epi _

/-- The map `T(F) → S(F)` restricts to `T^d F → S^d F` on the homogeneous components of
degree `d`. -/
theorem moduleSheafTensorAlgebraι_comp_toSymmetricAlgebra :
    moduleSheafTensorAlgebraι d F ≫ moduleSheafTensorToSymmetricAlgebra F =
      moduleSheafTensorToSymmetricPower F d ≫ moduleSheafSymmetricAlgebraι d F := by
  change (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).map _ ≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).map _ =
    (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).map _ ≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- The map `T(F) → S(F)` is unital. -/
theorem moduleSheafTensorToSymmetricAlgebra_one (U : (Opens X)ᵒᵖ) :
    (moduleSheafTensorToSymmetricAlgebra F).val.app U
        ((moduleSheafTensorAlgebraStructure F).one U) =
      (moduleSheafSymmetricAlgebraStructure F).one U :=
  PresheafAlgebra.sheafifyMap_one _ _ _ (fun _ => map_one (SymmetricAlgebra.algHom _ _)) U

/-- The map `T(F) → S(F)` is multiplicative. -/
theorem moduleSheafTensorToSymmetricAlgebra_mul (U : (Opens X)ᵒᵖ)
    (a b : (moduleSheafTensorAlgebra F).val.obj U) :
    (moduleSheafTensorToSymmetricAlgebra F).val.app U
        ((moduleSheafTensorAlgebraStructure F).mul.app U a b) =
      (moduleSheafSymmetricAlgebraStructure F).mul.app U
        ((moduleSheafTensorToSymmetricAlgebra F).val.app U a)
        ((moduleSheafTensorToSymmetricAlgebra F).val.app U b) :=
  PresheafAlgebra.sheafifyMap_mul _ _ _
    (fun U (a b : TensorAlgebra ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U) (F.val.obj U)) =>
      map_mul (SymmetricAlgebra.algHom _ _) a b) U a b

end Generation

namespace Ringed

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

open SheafAlgebraOperations ModuleSheafTensor SheafTensorOperations

section FrameSheafify

variable {P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)} {U : Opens X}
  {ι : Type u} [Fintype ι] (c : ι → P.obj (op U))

/-- The restrictions `c_i|_V` of a family of sections over `U` to an open `V ⊆ U`. -/
noncomputable def presheafRestrictFamily {V : Opens X} (h : V ≤ U) : ι → P.obj (op V) :=
  fun i => P.map (homOfLE h).op (c i)

/-- The map `(a_i) ↦ ∑ a_i c_i|_V` for a family of sections `c` of a presheaf of modules over `U`
and an open `V ⊆ U`. -/
noncomputable def presheafFrameMap {V : Opens X} (h : V ≤ U) :
    (ι → (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) →ₗ[
      (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)] P.obj (op V) :=
  Fintype.linearCombination _ (presheafRestrictFamily c h)

theorem presheafFrameMap_restrict {V W : Opens X} (h : V ≤ U) (hWV : W ≤ V)
    (a : ι → (R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)) :
    P.map (homOfLE hWV).op (presheafFrameMap c h a) =
      presheafFrameMap c (hWV.trans h)
        (fun i => ((R.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE hWV).op).hom (a i)) := by
  rw [presheafFrameMap, presheafFrameMap, Fintype.linearCombination_apply,
    Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (PresheafOfModules.map_smul P (homOfLE hWV).op (a i)
    (presheafRestrictFamily c h i)).trans ?_
  congr 1
  exact (PresheafOfModules.map_comp_apply P _ _ (c i)).symm

/-- The images in the sheafification of a family of sections of a presheaf of modules. -/
noncomputable def sheafifyFamily : ι → (sheafify P).val.presheaf.obj (op U) :=
  fun i => (sheafifyUnit P).app (op U) (c i)

/-- If a family of sections `c` of a presheaf of modules over `U` restricts to a basis over every
open `V ⊆ U`, its image in the sheafification is a local frame over `U`. -/
theorem isLocalFrame_sheafify
    (hc : ∀ (V : Opens X) (h : V ≤ U), Function.Bijective (presheafFrameMap c h)) :
    IsLocalFrame (sheafify P) U (sheafifyFamily c) := by
  have key : ∀ (V : Opens X) (h : V ≤ U) a,
      localFrameMap (sheafify P) (sheafifyFamily c) h a =
        (sheafifyUnit P).app (op V) (presheafFrameMap c h a) := by
    intro V h a
    rw [localFrameMap_apply, presheafFrameMap, Fintype.linearCombination_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
    rw [presheafRestrictFamily]
    exact (PresheafOfModules.naturality_apply (sheafifyUnit P) (homOfLE h).op (c i)).symm
  have hinj : ∀ (V : Opens X) (h : V ≤ U) a b,
      (sheafifyUnit P).app (op V) (presheafFrameMap c h a) =
        (sheafifyUnit P).app (op V) (presheafFrameMap c h b) → a = b := by
    intro V h a b hab
    funext i
    apply TopCat.Presheaf.section_ext R V
    intro x hx
    have hg : sectionGerm P x V hx (presheafFrameMap c h a) =
        sectionGerm P x V hx (presheafFrameMap c h b) := by
      apply (stalkMap_sheafifyUnit_bijective P x).1
      rw [stalkMap_germ, stalkMap_germ, hab]
    obtain ⟨W, hxW, iW, iW', he⟩ := TopCat.Presheaf.germ_eq P.presheaf x hx hx _ _ hg
    have hWV : W ≤ V := leOfHom iW
    have he' : P.map (homOfLE hWV).op (presheafFrameMap c h a) =
        P.map (homOfLE hWV).op (presheafFrameMap c h b) := he
    rw [presheafFrameMap_restrict, presheafFrameMap_restrict] at he'
    have hi := congrFun ((hc W (hWV.trans h)).1 he') i
    rw [← TopCat.Presheaf.germ_res_apply R.obj (homOfLE hWV) x hxW,
      ← TopCat.Presheaf.germ_res_apply R.obj (homOfLE hWV) x hxW]
    exact congrArg _ hi
  intro V h
  constructor
  · intro a b hab
    rw [key, key] at hab
    exact hinj V h a b hab
  · intro s
    change (sheafify P).val.obj (op V) at s
    have hloc : ∀ x : V, ∃ (W : Opens X) (_ : x.1 ∈ W) (i : W ⟶ V) (p : P.obj (op W)),
        (sheafifyUnit P).app (op W) p = (sheafify P).val.map i.op s :=
      fun x => exists_unit_eq_map P s x.2
    choose W hxW iW p hp using hloc
    have hWU : ∀ x, W x ≤ U := fun x => (leOfHom (iW x)).trans h
    choose a ha using fun x => (hc (W x) (hWU x)).2 (p x)
    have hcompat : ∀ x y,
        (fun i => ((R.obj ⋙ forget₂ CommRingCat RingCat).map
          (homOfLE (inf_le_left : W x ⊓ W y ≤ W x)).op).hom (a x i)) =
        (fun i => ((R.obj ⋙ forget₂ CommRingCat RingCat).map
          (homOfLE (inf_le_right : W x ⊓ W y ≤ W y)).op).hom (a y i)) := by
      intro x y
      apply hinj (W x ⊓ W y) (inf_le_left.trans (hWU x))
      rw [← presheafFrameMap_restrict c (hWU x) inf_le_left,
        ← presheafFrameMap_restrict c (hWU y) inf_le_right, ha, ha,
        PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hp, hp,
        ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
      exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) s
    have hglue : ∀ i, ∃ g : R.obj.obj (op V), ∀ x, R.obj.map (iW x).op g = a x i := by
      intro i
      obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' R W V iW
        (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW _⟩) (fun x => a x i)
        (fun x y => congrFun (hcompat x y) i)
      exact ⟨g, hg⟩
    choose g hg using hglue
    refine ⟨g, ?_⟩
    rw [key]
    apply sheaf_section_ext (sheafify P)
    intro x hx
    refine ⟨W ⟨x, hx⟩, hxW _, iW _, ?_⟩
    rw [← hp, ← PresheafOfModules.naturality_apply]
    congr 1
    rw [← ha]
    refine (presheafFrameMap_restrict c h (leOfHom (iW ⟨x, hx⟩)) g).trans ?_
    congr 1
    funext i
    exact hg i ⟨x, hx⟩

end FrameSheafify

section SymmetricPowerFrame

variable {E : SheafOfModules.{u} (ringCatSheafOf R)} {U : Opens X} {ι : Type u} [Fintype ι]
  [LinearOrder ι] (e : ι → E.val.presheaf.obj (op U)) (d : ℕ)

/-- The monomials of degree `d` in a family of sections `e` of `E` over `U`, as sections over `U`
of the presheaf `V ↦ Sym^d E(V)`. -/
noncomputable def symmetricPowerMonomials :
    MonotoneWord ι d → (moduleSheafSymmetricPowerPresheaf d E).obj (op U) :=
  symmetricMonomial _ (E.val.obj (op U)) d e

/-- The monomials of degree `d` in a family of sections `e` of `E` over `U`, as sections over `U`
of `S^d E`. -/
noncomputable def moduleSheafSymmetricPowerFrame :
    MonotoneWord ι d → (moduleSheafSymmetricPower d E).val.presheaf.obj (op U) :=
  sheafifyFamily (symmetricPowerMonomials e d)

/-- **The symmetric powers of a module with a local frame have a local frame.** If `e` is a
frame of `E` over `U`, the monomials of degree `d` in `e` form a frame of `S^d E` over `U`. -/
theorem IsLocalFrame.moduleSheafSymmetricPower {e : ι → E.val.presheaf.obj (op U)}
    (he : IsLocalFrame E U e) (d : ℕ) :
    IsLocalFrame (moduleSheafSymmetricPower d E) U (moduleSheafSymmetricPowerFrame e d) := by
  refine isLocalFrame_sheafify _ fun V h => ?_
  have hfam : presheafRestrictFamily (symmetricPowerMonomials e d) h =
      symmetricMonomial _ (E.val.obj (op V)) d
        (fun i => E.val.presheaf.map (homOfLE h).op (e i)) := by
    funext w
    exact symmetricPowerMap_symmetricMonomial d _ (E.val.restrictₛₗ (homOfLE h).op) e w
  rw [presheafFrameMap, hfam]
  exact symmetricMonomial_bijective d (he V h)

end SymmetricPowerFrame

section LocallyFree

variable {E : SheafOfModules.{u} (ringCatSheafOf R)}

/-- **Symmetric powers of a locally free module of rank `n`.** If `E` is locally free of rank `n`,
then `S^d E` is locally free of rank `C(n + d - 1, d)`. -/
theorem IsLocallyFreeOfRank.moduleSheafSymmetricPower {n : ℕ} (hE : IsLocallyFreeOfRank E n)
    (d : ℕ) : IsLocallyFreeOfRank (moduleSheafSymmetricPower d E) ((n + d - 1).choose d) := by
  apply isLocallyFreeOfRank_of_isLocalFrame
  intro x
  obtain ⟨U, e, hx, he⟩ := exists_isLocalFrame_of_isLocallyFreeOfRank hE x
  let : LinearOrder (ULift.{u} (Fin n)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have hcard : Fintype.card (ULift.{u} (Fin ((n + d - 1).choose d))) =
      Fintype.card (MonotoneWord (ULift.{u} (Fin n)) d) := by
    rw [MonotoneWord.card]
    simp
  exact ⟨U, _, hx, (he.moduleSheafSymmetricPower d).reindex (Fintype.equivOfCardEq hcard)⟩

/-- **Symmetric powers of a locally free module of finite rank are locally free of finite
rank.** -/
theorem IsFiniteLocallyFree.moduleSheafSymmetricPower (hE : IsFiniteLocallyFree E) (d : ℕ) :
    IsFiniteLocallyFree (moduleSheafSymmetricPower d E) := by
  classical
  intro x
  obtain ⟨U, hx, n, ⟨α⟩⟩ := hE x
  let : LinearOrder (ULift.{u} (Fin n)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have he := (isLocalFrame_of_over_iso α).moduleSheafSymmetricPower d
  let N := Fintype.card (MonotoneWord (ULift.{u} (Fin n)) d)
  have hcard : Fintype.card (ULift.{u} (Fin N)) =
      Fintype.card (MonotoneWord (ULift.{u} (Fin n)) d) := by simp [N]
  exact ⟨U, hx, N,
    nonempty_over_iso_free_of_isLocalFrame (he.reindex (Fintype.equivOfCardEq hcard))⟩

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_ofEpi_free_π {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {N : SheafOfModules.{u} S} {I : Type u}
    (β : SheafOfModules.free I ≅ N) :
    IsIso ((SheafOfModules.free.generatingSections I).ofEpi β.hom).π := by
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  infer_instance

/-- A module sheaf which is locally free of finite rank is of finite presentation: locally it is
a finite free module, with no relations. -/
theorem IsFiniteLocallyFree.isFinitePresentation {M : SheafOfModules.{u} (ringCatSheafOf R)}
    (hM : IsFiniteLocallyFree M) : SheafOfModules.IsFinitePresentation.{u, u, u} M := by
  choose U hxU n α using hM
  let q : M.LocalGeneratorsData :=
    { I := X
      X := U
      coversTop := by
        rw [Opens.coversTop_iff, IsOpenCover, eq_top_iff]
        exact fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
      generators := fun x =>
        (SheafOfModules.free.generatingSections (ULift.{u} (Fin (n x)))).ofEpi
          (α x).some.symm.hom }
  have : q.IsLocallyFreeData := by
    constructor
    intro x
    exact isIso_ofEpi_free_π (α x).some.symm
  have hq : q.quasiCoherentData.IsFinitePresentation := by
    constructor
    intro x
    constructor
    · exact ⟨inferInstanceAs (Finite (ULift.{u} (Fin (n x))))⟩
    · exact ⟨inferInstanceAs (Finite (ULift.{u} Empty))⟩
  exact SheafOfModules.IsFinitePresentation.mk.{u, u, u} ⟨q.quasiCoherentData, hq⟩

/-- A module sheaf which is locally free of finite rank is quasi-coherent. -/
theorem IsFiniteLocallyFree.isQuasicoherent {M : SheafOfModules.{u} (ringCatSheafOf R)}
    (hM : IsFiniteLocallyFree M) : SheafOfModules.IsQuasicoherent.{u, u, u} M :=
  have := hM.isFinitePresentation
  inferInstance

/-- **The symmetric algebra of a locally free module of finite rank is quasi-coherent.** Over an
open `U` on which `E` is free with frame `e`, each `(S^d E)|_U` is free on the monomials of degree
`d` in `e`, so `S(E)|_U = ⊕_d (S^d E)|_U` is free. -/
theorem IsFiniteLocallyFree.isQuasicoherent_moduleSheafSymmetricAlgebra
    (hE : IsFiniteLocallyFree E) :
    SheafOfModules.IsQuasicoherent.{u, u, u} (moduleSheafSymmetricAlgebra E) := by
  classical
  choose U hxU n α using hE
  have hloc : ∀ x, SheafOfModules.IsQuasicoherent.{u, u, u}
      ((moduleSheafSymmetricAlgebra E).over (U x)) := by
    intro x
    let : LinearOrder (ULift.{u} (Fin (n x))) :=
      LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
    have he := isLocalFrame_of_over_iso (α x).some
    let T : ℕ → Type u := fun d => MonotoneWord (ULift.{u} (Fin (n x))) d
    let β : ∀ d, (Hartshorne.moduleSheafSymmetricPower d E).over (U x) ≅
        SheafOfModules.free (T d) :=
      fun d => (nonempty_over_iso_free_of_isLocalFrame
        (IsLocalFrame.moduleSheafSymmetricPower he d)).some
    let G := SheafOfModules.overFunctor (ringCatSheafOf R) (U x)
    have : G.IsLeftAdjoint :=
      inferInstanceAs (SheafOfModules.pushforward (𝟙 ((ringCatSheafOf R).over (U x)))).IsLeftAdjoint
    have hG := isColimitOfPreserves G (moduleSheafSymmetricAlgebra_isColimit E)
    have hF := isColimitOfPreserves
      (SheafOfModules.freeFunctor (R := (ringCatSheafOf R).over (U x)))
      (Types.coproductColimitCocone.{0, u} T).isColimit
    let e := hG.coconePointsIsoOfNatIso hF (Discrete.natIso fun d => β d.as)
    exact (SheafOfModules.isQuasicoherent ((ringCatSheafOf R).over (U x))).prop_of_iso e.symm
      (inferInstanceAs (SheafOfModules.IsQuasicoherent.{u, u, u}
        (SheafOfModules.free (R := (ringCatSheafOf R).over (U x)) (Σ d, T d))))
  refine SheafOfModules.IsQuasicoherent.of_coversTop (moduleSheafSymmetricAlgebra E) U ?_
  rw [Opens.coversTop_iff, IsOpenCover, eq_top_iff]
  exact fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩

end LocallyFree

/-- A free module `E ≅ 𝒪_X^{⊕ I}` of finite rank has a global frame. -/
theorem exists_isLocalFrame_top_of_iso_free {E : SheafOfModules.{u} (ringCatSheafOf R)}
    {I : Type u} [Fintype I] (β : E ≅ SheafOfModules.free I) :
    ∃ e : I → E.val.presheaf.obj (op ⊤), IsLocalFrame E ⊤ e := by
  classical
  let G := SheafOfModules.overFunctor (ringCatSheafOf R) (⊤ : Opens X)
  have : G.IsLeftAdjoint :=
    inferInstanceAs (SheafOfModules.pushforward (𝟙 ((ringCatSheafOf R).over ⊤))).IsLeftAdjoint
  let γ : E.over ⊤ ≅ SheafOfModules.free I :=
    G.mapIso β ≪≫ (SheafOfModules.mapFreeIso G I (Iso.refl _)).symm
  exact ⟨_, isLocalFrame_of_over_iso γ⟩

end Ringed

section Polynomial

open SheafTensorOperations SheafAlgebraOperations

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}


variable (ι : Type u)

/-- The semilinear map `A[T_i] → B[T_i]` induced by a ring map `A → B` on coefficients. -/
noncomputable def mvPolynomialMapₛₗ {A B : Type u} [CommRing A] [CommRing B] (σ : A →+* B) :
    MvPolynomial ι A →ₛₗ[σ] MvPolynomial ι B where
  toFun := MvPolynomial.map σ
  map_add' := map_add _
  map_smul' a p := by
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]

variable (R) in
/-- The presheaf of `𝒪_X`-algebras `U ↦ 𝒪_X(U)[T_i]_{i ∈ ι}`, as a presheaf of modules. -/
noncomputable def polynomialPresheaf :
    PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
  presheafOfSemilinear
    (fun U => ModuleCat.of _ (MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U)))
    (fun i => mvPolynomialMapₛₗ ι ((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom)
    (fun U p => by
      change MvPolynomial.map _ p = p
      rw [show ((R.obj ⋙ forget₂ CommRingCat RingCat).map (𝟙 U)).hom = RingHom.id _ from
        RingHom.ext (ringMap_id_apply U), MvPolynomial.map_id])
    (fun i j p => by
      change MvPolynomial.map _ p = MvPolynomial.map _ (MvPolynomial.map _ p)
      rw [MvPolynomial.map_map]
      exact congrArg (fun φ => MvPolynomial.map φ p)
        (RingHom.ext (ringMap_comp_apply (R := R) i j)))

variable (R) in
/-- The presheaf of `𝒪_X`-algebras `U ↦ 𝒪_X(U)[T_i]_{i ∈ ι}`. -/
noncomputable def polynomialPresheafAlgebra : PresheafAlgebra (polynomialPresheaf R ι) where
  mul :=
    { app U := SheafTensorOperations.algebraMulBilinear _
        (MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U))
      naturality i a b :=
        map_mul (MvPolynomial.map ((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom)
        (show MvPolynomial ι _ from a) (show MvPolynomial ι _ from b) }
  one U := (1 : MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U))
  map_one i := map_one (MvPolynomial.map ((R.obj ⋙ forget₂ CommRingCat RingCat).map i).hom)
  mul_assoc U a b c := _root_.mul_assoc
    (G := MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U)) a b c
  one_mul U a := _root_.one_mul
    (M := MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U)) a
  mul_one U a := _root_.mul_one
    (M := MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U)) a

variable (R) in
/-- **The polynomial algebra sheaf** `𝒪_X[T_i]_{i ∈ ι}`, the sheafification of
`U ↦ 𝒪_X(U)[T_i]`; its sheaf of `𝒪_X`-algebras structure is `polynomialAlgebraSheafStructure`. -/
noncomputable def polynomialAlgebraSheaf : SheafOfModules.{u} (ringCatSheafOf R) :=
  sheafify (polynomialPresheaf R ι)

variable (R) in
/-- The sheaf of `𝒪_X`-algebras structure of `𝒪_X[T_i]`. -/
noncomputable def polynomialAlgebraSheafStructure :
    ModuleSheafAlgebra (polynomialAlgebraSheaf R ι) :=
  (polynomialPresheafAlgebra R ι).sheafification

variable {ι} [Fintype ι] {E : SheafOfModules.{u} (ringCatSheafOf R)}
  {e : ι → E.val.obj (op ⊤)}

/-- The restrictions `e_i|_V` of global sections of `E` to an open `V`. -/
noncomputable def globalSectionsRestrict (e : ι → E.val.obj (op ⊤)) (V : (Opens X)ᵒᵖ) :
    ι → E.val.obj V :=
  fun i => E.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op (e i)

/-- The basis of `E(V)` given by the restrictions of a global frame `e`. -/
noncomputable def frameBasis (he : Ringed.IsLocalFrame E ⊤ e) (V : (Opens X)ᵒᵖ) :
    Module.Basis ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj V) (E.val.obj V) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective
    (Fintype.linearCombination ((R.obj ⋙ forget₂ CommRingCat RingCat).obj V)
      (globalSectionsRestrict e V)) (he V.unop le_top)).symm

theorem frameBasis_apply (he : Ringed.IsLocalFrame E ⊤ e) (V : (Opens X)ᵒᵖ) (i : ι) :
    frameBasis he V i = globalSectionsRestrict e V i := by
  classical
  exact (congrFun (Module.Basis.coe_ofEquivFun _) i).trans
    ((Fintype.linearCombination_apply_single _ _ i 1).trans (one_smul _ _))

omit [Fintype ι] in
theorem restrict_globalSectionsRestrict {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) (i : ι) :
    E.val.map f (globalSectionsRestrict e V i) = globalSectionsRestrict e W i := by
  simp only [globalSectionsRestrict]
  rw [← PresheafOfModules.map_comp_apply]
  exact PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _

theorem restrict_frameBasis (he : Ringed.IsLocalFrame E ⊤ e) {V W : (Opens X)ᵒᵖ} (f : V ⟶ W)
    (i : ι) : E.val.restrictₛₗ f (frameBasis he V i) = frameBasis he W i := by
  rw [frameBasis_apply, frameBasis_apply]
  exact restrict_globalSectionsRestrict f i

/-- Over every open `V`, the frame `e|_V` identifies `𝒪_X(V)[T_i]` with the symmetric algebra
`S(E(V))`, `T_i ↦ e_i|_V`. -/
noncomputable def polynomialPresheafIso (he : Ringed.IsLocalFrame E ⊤ e) :
    polynomialPresheaf R ι ≅ moduleSheafSymmetricAlgebraPresheaf E :=
  PresheafOfModules.isoMk
    (fun V => (SymmetricAlgebra.equivMvPolynomial (frameBasis he V)).symm.toLinearEquiv.toModuleIso)
    (fun _ _ f => ModuleCat.hom_ext (LinearMap.ext fun p =>
      SheafTensorOperations.equivMvPolynomial_symm_map _ (E.val.restrictₛₗ f) _ _
        (restrict_frameBasis he f) p))

/-- **The symmetric algebra of a free module is a polynomial algebra.** If `E` has a global
frame `e = (e_i)_{i ∈ ι}` (that is, `E ≅ 𝒪_X^{⊕ ι}`), then `𝒪_X[T_i]_{i ∈ ι} ≅ S(E)`, `T_i ↦ e_i`,
as sheaves of `𝒪_X`-algebras (`polynomialAlgebraSymmetricAlgebraIso_mul`,
`polynomialAlgebraSymmetricAlgebraIso_one`, `polynomialAlgebraSymmetricAlgebraIso_X`). -/
noncomputable def polynomialAlgebraSymmetricAlgebraIso (he : Ringed.IsLocalFrame E ⊤ e) :
    polynomialAlgebraSheaf R ι ≅ moduleSheafSymmetricAlgebra E :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf R).obj)).mapIso (polynomialPresheafIso he)

theorem polynomialAlgebraSymmetricAlgebraIso_mul (he : Ringed.IsLocalFrame E ⊤ e) (U : (Opens X)ᵒᵖ)
    (a b : (polynomialAlgebraSheaf R ι).val.obj U) :
    (polynomialAlgebraSymmetricAlgebraIso he).hom.val.app U
        ((polynomialAlgebraSheafStructure R ι).mul.app U a b) =
      (moduleSheafSymmetricAlgebraStructure E).mul.app U
        ((polynomialAlgebraSymmetricAlgebraIso he).hom.val.app U a)
        ((polynomialAlgebraSymmetricAlgebraIso he).hom.val.app U b) :=
  PresheafAlgebra.sheafifyMap_mul _ _ _
    (fun U (a b : MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj U)) =>
      map_mul (SymmetricAlgebra.equivMvPolynomial (frameBasis he U)).symm a b) U a b

theorem polynomialAlgebraSymmetricAlgebraIso_one (he : Ringed.IsLocalFrame E ⊤ e)
    (U : (Opens X)ᵒᵖ) :
    (polynomialAlgebraSymmetricAlgebraIso he).hom.val.app U
        ((polynomialAlgebraSheafStructure R ι).one U) =
      (moduleSheafSymmetricAlgebraStructure E).one U :=
  PresheafAlgebra.sheafifyMap_one _ _ _
    (fun U => map_one (SymmetricAlgebra.equivMvPolynomial (frameBasis he U)).symm) U

/-- The isomorphism `𝒪_X[T_i] ≅ S(E)` sends the variable `T_i` to the frame section `e_i`. -/
theorem polynomialAlgebraSymmetricAlgebraIso_X (he : Ringed.IsLocalFrame E ⊤ e) (V : Opens X)
    (i : ι) :
    (polynomialAlgebraSymmetricAlgebraIso he).hom.val.app (op V)
        ((sheafifyUnit (polynomialPresheaf R ι)).app (op V)
          (MvPolynomial.X i : MvPolynomial ι ((R.obj ⋙ forget₂ CommRingCat RingCat).obj (op V)))) =
      (sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf E)).app (op V)
        (SymmetricAlgebra.ι _ _ (globalSectionsRestrict e (op V) i)) :=
  (sheafifyMap_unit _ (op V) _).trans (congrArg _
    ((SymmetricAlgebra.equivMvPolynomial_symm_X (frameBasis he (op V)) i).trans
      (congrArg _ (frameBasis_apply he (op V) i))))

/-- **The symmetric algebra of a free module of finite rank is a polynomial algebra:** if
`E ≅ 𝒪_X^{⊕ ι}`, then `S(E) ≅ 𝒪_X[T_i]_{i ∈ ι}` as sheaves of `𝒪_X`-algebras. -/
theorem exists_polynomialAlgebraSheaf_iso_symmetricAlgebra
    {E : SheafOfModules.{u} (ringCatSheafOf R)}
    {ι : Type u} [Fintype ι] (β : E ≅ SheafOfModules.free ι) :
    ∃ φ : polynomialAlgebraSheaf R ι ≅ moduleSheafSymmetricAlgebra E,
      (∀ U a b, φ.hom.val.app U ((polynomialAlgebraSheafStructure R ι).mul.app U a b) =
        (moduleSheafSymmetricAlgebraStructure E).mul.app U (φ.hom.val.app U a)
          (φ.hom.val.app U b)) ∧
      ∀ U, φ.hom.val.app U ((polynomialAlgebraSheafStructure R ι).one U) =
        (moduleSheafSymmetricAlgebraStructure E).one U := by
  obtain ⟨e, he⟩ := Ringed.exists_isLocalFrame_top_of_iso_free β
  exact ⟨polynomialAlgebraSymmetricAlgebraIso (e := e) he,
    polynomialAlgebraSymmetricAlgebraIso_mul (e := e) he,
    polynomialAlgebraSymmetricAlgebraIso_one (e := e) he⟩

/-- The degree-one inclusion `S^1 F → S(F)` sends the class of a section `m` of `F` to the image
of `m` in the symmetric algebra. -/
theorem moduleSheafSymmetricAlgebraι_one_apply (F : SheafOfModules.{u} (ringCatSheafOf R))
    (V : (Opens X)ᵒᵖ) (m : F.val.obj V) :
    (moduleSheafSymmetricAlgebraι 1 F).val.app V
        ((moduleSheafSymmetricPowerUnit 1 F).app V
          (symmetricPowerTprod _ (F.val.obj V) 1 (fun _ => m))) =
      (sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf F)).app V
        (SymmetricAlgebra.ι _ _ m) := by
  refine (sheafifyMap_unit _ V _).trans (congrArg _ ?_)
  change SymmetricAlgebra.algHom _ _ (TensorPower.toTensorAlgebra (PiTensorProduct.tprod _ _)) = _
  rw [TensorPower.toTensorAlgebra_tprod, TensorAlgebra.tprod_apply]
  simp [SymmetricAlgebra.ι]

end Polynomial

section Restriction

open SheafTensorOperations SheafAlgebraOperations AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- **Restriction of a sheaf of algebras** along an open immersion `f : Y ⟶ X`: the
multiplication and unit of `A|_Y` over `W` are those of `A` over `f(W)`. -/
noncomputable def ModuleSheafAlgebra.restrict {A : SheafOfModules.{u} (ringCatSheafOf X.sheaf)}
    (S : ModuleSheafAlgebra A) : ModuleSheafAlgebra ((restrictModule f).obj A) where
  mul :=
    { app W :=
        { toFun a :=
            { toFun b := S.mul.app (f.opensFunctor.op.obj W) a b
              map_add' b b' := map_add _ b b'
              map_smul' r b := (S.mul.app (f.opensFunctor.op.obj W) a).map_smul
                (restrictRing f W r) b }
          map_add' a a' := LinearMap.ext fun b =>
            LinearMap.congr_fun ((S.mul.app (f.opensFunctor.op.obj W)).map_add a a') b
          map_smul' r a := LinearMap.ext fun b =>
            LinearMap.congr_fun ((S.mul.app (f.opensFunctor.op.obj W)).map_smul
              (restrictRing f W r) a) b }
      naturality i a b := S.mul.naturality (f.opensFunctor.op.map i) a b }
  one W := S.one (f.opensFunctor.op.obj W)
  map_one i := S.map_one (f.opensFunctor.op.map i)
  mul_assoc W := S.mul_assoc (f.opensFunctor.op.obj W)
  one_mul W := S.one_mul (f.opensFunctor.op.obj W)
  mul_one W := S.mul_one (f.opensFunctor.op.obj W)

@[deprecated SheafTensorOperations.isIso_sheafificationRestrictHom (since := "2026-11-09")]
alias isIso_sheafificationRestrictHom := SheafTensorOperations.isIso_sheafificationRestrictHom

variable (E : SheafOfModules.{u} (ringCatSheafOf X.sheaf))

/-- Sections over `W` of the presheaf `W ↦ S(E|_Y(W))` agree with sections over `f(W)` of the
presheaf `U ↦ S(E(U))`. -/
noncomputable def symmetricAlgebraRestrictEquiv (W : (Opens Y)ᵒᵖ) :
    (moduleSheafSymmetricAlgebraPresheaf ((restrictModule f).obj E)).obj W ≃ₗ[
      (ringCatSheafOf Y.sheaf).obj.obj W]
      ((PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafSymmetricAlgebraPresheaf E)).obj W where
  toFun := symmetricAlgebraMap (restrictRing f W) (restrictSections f E W)
  map_add' := map_add _
  map_smul' := (symmetricAlgebraMap (restrictRing f W) (restrictSections f E W)).map_smulₛₗ
  invFun := symmetricAlgebraMap (restrictRingInv f W) (restrictSectionsInv f E W)
  left_inv x := (symmetricAlgebraMap_comp (fun a => (restrictRingInv_restrictRing f W a).symm)
    _ _ LinearMap.id (fun _ => rfl) x).symm.trans
      (symmetricAlgebraMap_id (fun _ => rfl) _ (fun _ => rfl) x)
  right_inv x := (symmetricAlgebraMap_comp (fun b => (restrictRing_restrictRingInv f W b).symm)
    _ _ LinearMap.id (fun _ => rfl) x).symm.trans
      (symmetricAlgebraMap_id (fun _ => rfl) _ (fun _ => rfl) x)

/-- The presheaf `W ↦ S(E|_Y(W))` is the restriction to `Y` of the presheaf `U ↦ S(E(U))`. -/
noncomputable def symmetricAlgebraPresheafRestrictIso :
    moduleSheafSymmetricAlgebraPresheaf ((restrictModule f).obj E) ≅
      (PresheafOfModules.pushforward (restrictRingHom f).hom).obj
        (moduleSheafSymmetricAlgebraPresheaf E) :=
  PresheafOfModules.isoMk (fun W => (symmetricAlgebraRestrictEquiv f E W).toModuleIso)
    (fun W W' i => by
      ext x
      exact (symmetricAlgebraMap_comp (fun a => rfl)
        (((restrictModule f).obj E).val.restrictₛₗ i)
        (restrictSections f E W') (restrictSectionsMap f E i) (fun _ => rfl) x).symm.trans
        (symmetricAlgebraMap_comp (fun a => restrictRing_naturality f i a)
          (restrictSections f E W) (E.val.restrictₛₗ (f.opensFunctor.op.map i)) _
          (fun _ => rfl) x))

/-- **The symmetric algebra commutes with restriction to open subschemes:** `S(E|_Y) ≅ S(E)|_Y`,
as sheaves of algebras (`symmetricAlgebraRestrictIso_mul`, `symmetricAlgebraRestrictIso_one`). -/
noncomputable def symmetricAlgebraRestrictIso :
    moduleSheafSymmetricAlgebra ((restrictModule f).obj E) ≅
      (restrictModule f).obj (moduleSheafSymmetricAlgebra E) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheafOf Y.sheaf).obj)).mapIso
      (symmetricAlgebraPresheafRestrictIso f E) ≪≫
    @asIso _ _ _ _ (sheafificationRestrictHom f (moduleSheafSymmetricAlgebraPresheaf E))
      (SheafTensorOperations.isIso_sheafificationRestrictHom f _)

theorem symmetricAlgebraRestrictIso_unit (W : (Opens Y)ᵒᵖ)
    (z : (moduleSheafSymmetricAlgebraPresheaf ((restrictModule f).obj E)).obj W) :
    (symmetricAlgebraRestrictIso f E).hom.val.app W
        ((sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf ((restrictModule f).obj E))).app W z) =
      (sheafifyUnit (moduleSheafSymmetricAlgebraPresheaf E)).app (f.opensFunctor.op.obj W)
        (symmetricAlgebraMap (restrictRing f W) (restrictSections f E W) z) := by
  have h1 := sheafifyMap_unit (symmetricAlgebraPresheafRestrictIso f E).hom W z
  have h2 := sheafificationRestrictHom_unit f (moduleSheafSymmetricAlgebraPresheaf E) W
    ((symmetricAlgebraPresheafRestrictIso f E).hom.app W z)
  exact (congrArg ((sheafificationRestrictHom f (moduleSheafSymmetricAlgebraPresheaf E)).val.app W)
    h1).trans h2

theorem symmetricAlgebraRestrictIso_mul (W : (Opens Y)ᵒᵖ)
    (a b : (moduleSheafSymmetricAlgebra ((restrictModule f).obj E)).val.obj W) :
    (symmetricAlgebraRestrictIso f E).hom.val.app W
        ((moduleSheafSymmetricAlgebraStructure ((restrictModule f).obj E)).mul.app W a b) =
      ((moduleSheafSymmetricAlgebraStructure E).restrict f).mul.app W
        ((symmetricAlgebraRestrictIso f E).hom.val.app W a)
        ((symmetricAlgebraRestrictIso f E).hom.val.app W b) := by
  refine PresheafAlgebra.sheafify_hom_mul _ _ _ (fun W x y => ?_) W a b
  have hu := symmetricAlgebraRestrictIso_unit f E W
  exact (hu _).trans ((congrArg _ (symmetricAlgebraMap_mul _ _ x y)).trans
    ((moduleSheafSymmetricAlgebra_mul_unit E _ _ _).symm.trans
      (congrArg₂ (fun s t => ((moduleSheafSymmetricAlgebraStructure E).restrict f).mul.app W s t)
        (hu x).symm (hu y).symm)))

theorem symmetricAlgebraRestrictIso_one (W : (Opens Y)ᵒᵖ) :
    (symmetricAlgebraRestrictIso f E).hom.val.app W
        ((moduleSheafSymmetricAlgebraStructure ((restrictModule f).obj E)).one W) =
      ((moduleSheafSymmetricAlgebraStructure E).restrict f).one W :=
  (symmetricAlgebraRestrictIso_unit f E W
    (1 : SymmetricAlgebra ((Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj W)
      (((restrictModule f).obj E).val.obj W))).trans
    (congrArg _ (map_one (symmetricAlgebraRingHom (restrictRing f W) (restrictSections f E W))))

end Restriction

end Hartshorne

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.SheafAlgebraOperations Hartshorne.SheafTensorOperations

variable {X : Scheme.{u}} (E : X.Modules)

/-- **The symmetric algebra sheaf** `Sym(E) = ⊕_d Sym^d E` of an `𝒪_X`-module `E`, with its sheaf of
graded `𝒪_X`-algebras structure `symmetricAlgebraStructure`. -/
noncomputable abbrev symmetricAlgebra : X.Modules :=
  moduleSheafSymmetricAlgebra (R := X.sheaf) E

/-- The sheaf of `𝒪_X`-algebras structure of `Sym(E)`. -/
noncomputable abbrev symmetricAlgebraStructure :
    ModuleSheafAlgebra (R := X.sheaf) E.symmetricAlgebra :=
  moduleSheafSymmetricAlgebraStructure E

/-- The homogeneous component `Sym^d E` of `Sym(E)`. -/
noncomputable abbrev symmetricPower (d : ℕ) : X.Modules :=
  moduleSheafSymmetricPower (R := X.sheaf) d E

variable {E}

private theorem isFiniteLocallyFree_of (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) : Ringed.IsFiniteLocallyFree (R := X.sheaf) E :=
  (isFiniteLocallyFree_iff E).mpr ⟨hE, hfin⟩

/-- **`Sym(E)` is a sheaf of graded commutative `𝒪_X`-algebras** `⊕_d Sym^d E`: the inclusions of
the homogeneous components exhibit `Sym(E)` as the direct sum of the `Sym^d E`, the product of
sections of degrees `r` and `s` has degree `r + s`, and the multiplication is commutative. -/
theorem symmetricAlgebra_graded (E : X.Modules) :
    Nonempty (Limits.IsColimit (Limits.Cofan.mk E.symmetricAlgebra
      fun d => moduleSheafSymmetricAlgebraι (R := X.sheaf) d E)) ∧
    (∀ (r s : ℕ) (U : (X.Opens)ᵒᵖ) (a : (E.symmetricPower r).val.obj U)
      (b : (E.symmetricPower s).val.obj U),
      E.symmetricAlgebraStructure.mul.app U ((moduleSheafSymmetricAlgebraι r E).val.app U a)
          ((moduleSheafSymmetricAlgebraι s E).val.app U b) =
        (moduleSheafSymmetricAlgebraι (r + s) E).val.app U
          ((moduleSheafSymmetricPowerMul r E s).app U a b)) ∧
    ∀ (U : (X.Opens)ᵒᵖ) (a b : E.symmetricAlgebra.val.obj U),
      E.symmetricAlgebraStructure.mul.app U a b = E.symmetricAlgebraStructure.mul.app U b a :=
  ⟨⟨moduleSheafSymmetricAlgebra_isColimit E⟩,
    fun r s U a b => moduleSheafSymmetricAlgebra_mul_ι r E s U a b,
    moduleSheafSymmetricAlgebra_mul_comm E⟩

/-- **`Sym(E)` is quasi-coherent** for a locally free `E` of finite rank. -/
theorem symmetricAlgebra_isQuasicoherent (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) :
    SheafOfModules.IsQuasicoherent.{u, u, u} E.symmetricAlgebra :=
  (isFiniteLocallyFree_of hE hfin).isQuasicoherent_moduleSheafSymmetricAlgebra

/-- **Each `Sym^d E` is locally free of finite rank** for a locally free `E` of finite rank. -/
theorem symmetricPower_isLocallyFree (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) (d : ℕ) :
    (E.symmetricPower d).IsLocallyFree ∧ ∀ x, (E.symmetricPower d).rankAt x < Cardinal.aleph0 :=
  (isFiniteLocallyFree_iff _).mp
    (Ringed.IsFiniteLocallyFree.moduleSheafSymmetricPower (isFiniteLocallyFree_of hE hfin) d)

/-- **`Sym^d` of a locally free module of rank `n` is locally free of rank `C(n + d - 1, d)`.** -/
theorem symmetricPower_isLocallyFreeOfRank {n : ℕ} (hE : E.IsLocallyFreeOfRank n) (d : ℕ) :
    (E.symmetricPower d).IsLocallyFreeOfRank ((n + d - 1).choose d) :=
  (isLocallyFreeOfRank_iff_ringed _ _).mpr
    (Ringed.IsLocallyFreeOfRank.moduleSheafSymmetricPower
      ((isLocallyFreeOfRank_iff_ringed _ _).mp hE) d)

/-- **Each `Sym^d E` is quasi-coherent** for a locally free `E` of finite rank. -/
theorem symmetricPower_isQuasicoherent (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) (d : ℕ) :
    SheafOfModules.IsQuasicoherent.{u, u, u} (E.symmetricPower d) :=
  Ringed.IsFiniteLocallyFree.isQuasicoherent
    (Ringed.IsFiniteLocallyFree.moduleSheafSymmetricPower (isFiniteLocallyFree_of hE hfin) d)

/-- **Each `Sym^d E` is coherent** on a Noetherian scheme, for a locally free `E` of finite
rank. -/
theorem symmetricPower_isCoherent [IsNoetherian X] (hE : E.IsLocallyFree)
    (hfin : ∀ x, E.rankAt x < Cardinal.aleph0) (d : ℕ) :
    IsCoherent (E.symmetricPower d) :=
  have := Ringed.IsFiniteLocallyFree.isFinitePresentation
    (Ringed.IsFiniteLocallyFree.moduleSheafSymmetricPower (isFiniteLocallyFree_of hE hfin) d)
  ((coherent_affine_local_tfae (E.symmetricPower d)).out 1 0).mp this

/-- **Locally, `Sym(E)` is a polynomial algebra.** On an open `U` where `E` is free,
`E|_U ≅ 𝒪_U^{⊕ ι}` with `ι` finite, the restriction `Sym(E)|_U` is isomorphic, as a sheaf of
graded `𝒪_U`-algebras, to the polynomial algebra `𝒪_U[T_i]_{i ∈ ι}`: the isomorphism is
multiplicative and unital, and sends each variable `T_i` into the degree-one part `Sym^1 E`. -/
theorem symmetricAlgebra_restrict_iso_polynomial {U : X.Opens} {ι : Type u} [Fintype ι]
    (β : E.restrict U.ι ≅ SheafOfModules.free ι) :
    ∃ φ : polynomialAlgebraSheaf (U : Scheme.{u}).sheaf ι ≅ E.symmetricAlgebra.restrict U.ι,
      (∀ W a b, φ.hom.val.app W
          ((polynomialAlgebraSheafStructure (U : Scheme.{u}).sheaf ι).mul.app W a b) =
        (E.symmetricAlgebraStructure.restrict U.ι).mul.app W (φ.hom.val.app W a)
          (φ.hom.val.app W b)) ∧
      (∀ W, φ.hom.val.app W ((polynomialAlgebraSheafStructure (U : Scheme.{u}).sheaf ι).one W) =
        (E.symmetricAlgebraStructure.restrict U.ι).one W) ∧
      ∀ W (i : ι), ∃ s : (E.symmetricPower 1).val.obj (U.ι.opensFunctor.op.obj W),
        φ.hom.val.app W ((sheafifyUnit (polynomialPresheaf (U : Scheme.{u}).sheaf ι)).app W
          (MvPolynomial.X i)) =
        (moduleSheafSymmetricAlgebraι (R := X.sheaf) 1 E).val.app _ s := by
  obtain ⟨e, he⟩ := Ringed.exists_isLocalFrame_top_of_iso_free (R := (U : Scheme.{u}).sheaf)
    (E := E.restrict U.ι) β
  let ψ := symmetricAlgebraRestrictIso U.ι E
  refine ⟨polynomialAlgebraSymmetricAlgebraIso (e := e) he ≪≫ ψ, fun W a b => ?_, fun W => ?_,
    fun W i => ⟨(moduleSheafSymmetricPowerMultilinear 1 E).app (U.ι.opensFunctor.op.obj W)
      (fun _ => SheafTensorOperations.restrictSections U.ι E W
        (globalSectionsRestrict (E := E.restrict U.ι) e W i)), ?_⟩⟩
  · exact (congrArg (ψ.hom.val.app W) (polynomialAlgebraSymmetricAlgebraIso_mul he W a b)).trans
      (symmetricAlgebraRestrictIso_mul U.ι E W _ _)
  · exact (congrArg (ψ.hom.val.app W) (polynomialAlgebraSymmetricAlgebraIso_one he W)).trans
      (symmetricAlgebraRestrictIso_one U.ι E W)
  · exact (congrArg (ψ.hom.val.app W) (polynomialAlgebraSymmetricAlgebraIso_X he W.unop i)).trans
      ((symmetricAlgebraRestrictIso_unit U.ι E W _).trans
        ((congrArg _ (symmetricAlgebraRingHom_ι _ _ _)).trans
          (moduleSheafSymmetricAlgebraι_one_apply E _ _).symm))

/-- **The degree-one part of `Sym(E)` is `E`.** -/
noncomputable def symmetricPowerOneIso (E : X.Modules) : E.symmetricPower 1 ≅ E :=
  moduleSheafSymmetricPowerOneIso (R := X.sheaf) E

/-- **The degree-zero part of `Sym(E)` is `𝒪_X`.** -/
noncomputable def symmetricPowerZeroIso (E : X.Modules) :
    E.symmetricPower 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  moduleSheafSymmetricPowerZeroIso (R := X.sheaf) E

/-- **`Sym^0 E = 𝒪_X` as algebras, compatibly with the unit.** Followed by the inclusion
`Sym^0 E → Sym(E)`, the identification `𝒪_X ≅ Sym^0 E` sends `1` to the unit of `Sym(E)`. -/
theorem symmetricPowerZeroIso_inv_one (E : X.Modules) (U : X.Opensᵒᵖ) :
    (moduleSheafSymmetricAlgebraι (R := X.sheaf) 0 E).val.app U
        (E.symmetricPowerZeroIso.inv.val.app U (1 : Γ(X, U.unop))) =
      E.symmetricAlgebraStructure.one U :=
  moduleSheafSymmetricAlgebraι_zero_one E U

/-- **`Sym^0 E = 𝒪_X` as algebras.** Followed by the inclusion `Sym^0 E → Sym(E)`, the
identification `𝒪_X ≅ Sym^0 E` sends products of sections of `𝒪_X` to products in `Sym(E)`. -/
theorem symmetricPowerZeroIso_inv_mul (E : X.Modules) (U : X.Opensᵒᵖ) (a b : Γ(X, U.unop)) :
    (moduleSheafSymmetricAlgebraι (R := X.sheaf) 0 E).val.app U
        (E.symmetricPowerZeroIso.inv.val.app U (a * b)) =
      E.symmetricAlgebraStructure.mul.app U
        ((moduleSheafSymmetricAlgebraι (R := X.sheaf) 0 E).val.app U
          (E.symmetricPowerZeroIso.inv.val.app U a))
        ((moduleSheafSymmetricAlgebraι (R := X.sheaf) 0 E).val.app U
          (E.symmetricPowerZeroIso.inv.val.app U b)) :=
  moduleSheafSymmetricAlgebraι_zero_mul E U a b

end AlgebraicGeometry.Scheme.Modules
