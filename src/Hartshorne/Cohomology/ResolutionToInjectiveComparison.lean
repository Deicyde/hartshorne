/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Comparison from an arbitrary resolution to an injective resolution

An augmentation `A ⟶ K•` which is a quasi-isomorphism admits an augmentation-preserving
cochain map to every injective resolution of `A`. Any two such maps are cochain-homotopic.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ResolutionToInjectiveComparison

open HomologicalComplex CochainComplex

variable {A : C} {K : CochainComplex C ℕ}
  (epsilon : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso epsilon]

include epsilon

private lemma exactAt_succ (n : ℕ) : K.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt epsilon (n + 1)
    (CochainComplex.exactAt_succ_single_obj A n)]
  infer_instance

private lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (K.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (exactAt_succ epsilon n)

private lemma exact_succ_succ (n : ℕ) :
    (ShortComplex.mk _ _ (K.d_comp_d (n + 1) (n + 2) (n + 3))).Exact := by
  simpa only [Nat.add_assoc, Nat.reduceAdd] using exact_succ epsilon (n + 1)

omit [QuasiIso epsilon] in
@[simp]
private lemma epsilon_f_succ (n : ℕ) : epsilon.f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 A (n + 1)
    (by simp)).eq_of_src _ _

omit [QuasiIso epsilon] in
@[reassoc]
private lemma epsilon_f_zero_comp_d : epsilon.f 0 ≫ K.d 0 1 = 0 := by
  rw [HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d, zero_comp]

private abbrev kernelFork : KernelFork (K.d 0 1) :=
  KernelFork.ofι (Z := A) (epsilon.f 0) (epsilon_f_zero_comp_d epsilon)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def isLimitKernelFork : IsLimit (kernelFork epsilon) := by
  refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 A).symm ≪≫
    isoOfQuasiIsoAt epsilon 0 ≪≫
    K.isoHomologyπ₀.symm) ?_
  simp [kernelFork, singleObjHomologySelfIso, singleObjCyclesSelfIso]

private lemma exact_zero :
    (ShortComplex.mk _ _ (epsilon_f_zero_comp_d epsilon)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelFork epsilon)

private instance mono_epsilon_zero : Mono (epsilon.f 0) :=
  mono_of_isLimit_fork (isLimitKernelFork epsilon)

variable (I : InjectiveResolution A)

set_option backward.isDefEq.respectTransparency false in
private def homFZero : K.X 0 ⟶ I.cocomplex.X 0 :=
  Injective.factorThru (I.ι.f 0) (epsilon.f 0)

private lemma epsilon_zero_comp_homFZero :
    epsilon.f 0 ≫ homFZero epsilon I = I.ι.f 0 := by
  apply Injective.comp_factorThru

set_option backward.isDefEq.respectTransparency false in
private def homFOne : K.X 1 ⟶ I.cocomplex.X 1 :=
  (exact_zero epsilon).descToInjective
    (homFZero epsilon I ≫ I.cocomplex.d 0 1) (by
      rw [← Category.assoc, epsilon_zero_comp_homFZero epsilon I,
        I.ι_f_zero_comp_complex_d])

@[simp]
private lemma d_comp_homFOne :
    K.d 0 1 ≫ homFOne epsilon I =
      homFZero epsilon I ≫ I.cocomplex.d 0 1 :=
  (exact_zero epsilon).comp_descToInjective _ _

private def homFSucc (n : ℕ)
    (g : K.X n ⟶ I.cocomplex.X n)
    (g' : K.X (n + 1) ⟶ I.cocomplex.X (n + 1))
    (w : K.d n (n + 1) ≫ g' = g ≫ I.cocomplex.d n (n + 1)) :
    Σ' g'' : K.X (n + 2) ⟶ I.cocomplex.X (n + 2),
      K.d (n + 1) (n + 2) ≫ g'' =
        g' ≫ I.cocomplex.d (n + 1) (n + 2) :=
  ⟨(exact_succ epsilon n).descToInjective
      (g' ≫ I.cocomplex.d (n + 1) (n + 2))
      (by simp [reassoc_of% w]),
    (exact_succ epsilon n).comp_descToInjective _ _⟩

/-- A chosen augmentation-preserving comparison cochain map. -/
noncomputable def hom : K ⟶ I.cocomplex :=
  CochainComplex.mkHom _ _ (homFZero epsilon I) (homFOne epsilon I)
    (d_comp_homFOne epsilon I).symm
    fun n ⟨g, g', w⟩ ↦
      ⟨(homFSucc epsilon I n g g' w.symm).1,
        (homFSucc epsilon I n g g' w.symm).2.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
theorem commutes : epsilon ≫ hom epsilon I = I.ι := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n
  · change epsilon.f 0 ≫ (hom epsilon I).f 0 = I.ι.f 0
    exact epsilon_zero_comp_homFZero epsilon I
  · simp only [epsilon_f_succ]

private def homotopyZeroZero
    (f : K ⟶ I.cocomplex) (comm : epsilon ≫ f = 0) :
    K.X 1 ⟶ I.cocomplex.X 0 :=
  (exact_zero epsilon).descToInjective (f.f 0)
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroZero
    (f : K ⟶ I.cocomplex) (comm : epsilon ≫ f = 0) :
    K.d 0 1 ≫ homotopyZeroZero epsilon I f comm = f.f 0 :=
  (exact_zero epsilon).comp_descToInjective _ _

private def homotopyZeroOne
    (f : K ⟶ I.cocomplex) (comm : epsilon ≫ f = 0) :
    K.X 2 ⟶ I.cocomplex.X 1 :=
  (exact_succ epsilon 0).descToInjective
    (f.f 1 - homotopyZeroZero epsilon I f comm ≫ I.cocomplex.d 0 1)
    (by rw [Preadditive.comp_sub, comp_homotopyZeroZero_assoc epsilon I f comm,
      HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroOne
    (f : K ⟶ I.cocomplex) (comm : epsilon ≫ f = 0) :
    K.d 1 2 ≫ homotopyZeroOne epsilon I f comm =
      f.f 1 - homotopyZeroZero epsilon I f comm ≫ I.cocomplex.d 0 1 :=
  (exact_succ epsilon 0).comp_descToInjective _ _

private def homotopyZeroSucc
    (f : K ⟶ I.cocomplex) (n : ℕ)
    (g : K.X (n + 1) ⟶ I.cocomplex.X n)
    (g' : K.X (n + 2) ⟶ I.cocomplex.X (n + 1))
    (w : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' +
      g ≫ I.cocomplex.d n (n + 1)) :
    K.X (n + 3) ⟶ I.cocomplex.X (n + 2) :=
  (exact_succ_succ epsilon n).descToInjective
    (f.f (n + 2) - g' ≫ I.cocomplex.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w,
        Preadditive.add_comp, Category.assoc, Category.assoc,
        I.cocomplex.d_comp_d, comp_zero, add_zero, sub_self])

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroSucc
    (f : K ⟶ I.cocomplex) (n : ℕ)
    (g : K.X (n + 1) ⟶ I.cocomplex.X n)
    (g' : K.X (n + 2) ⟶ I.cocomplex.X (n + 1))
    (w : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' +
      g ≫ I.cocomplex.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ homotopyZeroSucc epsilon I f n g g' w =
      f.f (n + 2) - g' ≫ I.cocomplex.d _ _ :=
  (exact_succ_succ epsilon n).comp_descToInjective _ _

private def homotopyZero
    (f : K ⟶ I.cocomplex) (comm : epsilon ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroZero epsilon I f comm) (by simp)
    (homotopyZeroOne epsilon I f comm) (by simp)
    (fun n ⟨g, g', w⟩ ↦
      ⟨homotopyZeroSucc epsilon I f n g g' (by simp only [w, add_comm]),
        by simp⟩)

/-- Any two augmentation-preserving comparisons are cochain-homotopic. -/
noncomputable def homotopy (f g : K ⟶ I.cocomplex)
    (hf : epsilon ≫ f = I.ι) (hg : epsilon ≫ g = I.ι) :
    Homotopy f g :=
  Homotopy.equivSubZero.invFun
    (homotopyZero epsilon I _ (by simp [hf, hg]))

end ResolutionToInjectiveComparison

/-- The type of augmentation-preserving cochain maps from a resolution to an injective
resolution. -/
abbrev ResolutionToInjectiveComparison
    {A : C} {K : CochainComplex C ℕ}
    (epsilon : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso epsilon]
    (I : InjectiveResolution A) :=
  { f : K ⟶ I.cocomplex // epsilon ≫ f = I.ι }

/-- An arbitrary resolution admits an augmentation-preserving comparison with an injective
resolution, unique up to cochain homotopy. -/
theorem resolutionToInjectiveComparison_exists_uniqueUpToHomotopy
    {A : C} {K : CochainComplex C ℕ}
    (epsilon : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso epsilon]
    (I : InjectiveResolution A) :
    Nonempty (ResolutionToInjectiveComparison epsilon I) ∧
      ∀ f g : ResolutionToInjectiveComparison epsilon I,
        Nonempty (Homotopy f.1 g.1) := by
  constructor
  · exact ⟨⟨ResolutionToInjectiveComparison.hom epsilon I,
      ResolutionToInjectiveComparison.commutes epsilon I⟩⟩
  · intro f g
    exact ⟨ResolutionToInjectiveComparison.homotopy epsilon I f.1 g.1 f.2 g.2⟩

end Hartshorne
