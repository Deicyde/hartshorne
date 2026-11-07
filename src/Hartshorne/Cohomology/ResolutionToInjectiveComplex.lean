/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Maps from a resolution to a complex of injectives

Let `A ⟶ K•` be an augmentation which is a quasi-isomorphism (so `K•` is a resolution of `A`)
and let `L•` be a cochain complex, concentrated in nonnegative degrees, of injective objects.
Every cochain map `A ⟶ L•` extends along the augmentation to a cochain map `K• ⟶ L•`, and two
cochain maps `K• ⟶ L•` agreeing on `A` are cochain-homotopic.

This is the comparison theorem of homological algebra with the target only assumed to consist of
injective objects (not to be a resolution); the construction is the usual degree-by-degree
extension, using exactness of `K•` and injectivity of the `L^n`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ResolutionToInjectiveComplex

open HomologicalComplex CochainComplex

@[simp]
private lemma single_f_succ {A : C} {L : CochainComplex C ℕ}
    (g : (CochainComplex.single₀ C).obj A ⟶ L) (n : ℕ) : g.f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 A (n + 1)
    (by simp)).eq_of_src _ _

@[reassoc]
private lemma single_f_zero_comp_d {A : C} {L : CochainComplex C ℕ}
    (g : (CochainComplex.single₀ C).obj A ⟶ L) : g.f 0 ≫ L.d 0 1 = 0 := by
  rw [HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d, zero_comp]

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

private abbrev kernelFork : KernelFork (K.d 0 1) :=
  KernelFork.ofι (Z := A) (epsilon.f 0) (single_f_zero_comp_d epsilon)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private def isLimitKernelFork : IsLimit (kernelFork epsilon) := by
  refine IsLimit.ofIsoLimit (K.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso (ComplexShape.up ℕ) 0 A).symm ≪≫
    isoOfQuasiIsoAt epsilon 0 ≪≫
    K.isoHomologyπ₀.symm) ?_
  simp [kernelFork, singleObjHomologySelfIso, singleObjCyclesSelfIso]

private lemma exact_zero :
    (ShortComplex.mk _ _ (single_f_zero_comp_d epsilon)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (isLimitKernelFork epsilon)

private instance mono_epsilon_zero : Mono (epsilon.f 0) :=
  mono_of_isLimit_fork (isLimitKernelFork epsilon)

variable {L : CochainComplex C ℕ} [∀ n, Injective (L.X n)]

section Existence

variable (g : (CochainComplex.single₀ C).obj A ⟶ L)

set_option backward.isDefEq.respectTransparency false in
private def homFZero : K.X 0 ⟶ L.X 0 :=
  Injective.factorThru (g.f 0) (epsilon.f 0)

private lemma epsilon_zero_comp_homFZero :
    epsilon.f 0 ≫ homFZero epsilon g = g.f 0 := by
  apply Injective.comp_factorThru

set_option backward.isDefEq.respectTransparency false in
private def homFOne : K.X 1 ⟶ L.X 1 :=
  (exact_zero epsilon).descToInjective
    (homFZero epsilon g ≫ L.d 0 1) (by
      rw [← Category.assoc, epsilon_zero_comp_homFZero epsilon g,
        single_f_zero_comp_d g])

@[simp]
private lemma d_comp_homFOne :
    K.d 0 1 ≫ homFOne epsilon g = homFZero epsilon g ≫ L.d 0 1 :=
  (exact_zero epsilon).comp_descToInjective _ _

private def homFSucc (n : ℕ)
    (h : K.X n ⟶ L.X n) (h' : K.X (n + 1) ⟶ L.X (n + 1))
    (w : K.d n (n + 1) ≫ h' = h ≫ L.d n (n + 1)) :
    Σ' h'' : K.X (n + 2) ⟶ L.X (n + 2),
      K.d (n + 1) (n + 2) ≫ h'' = h' ≫ L.d (n + 1) (n + 2) :=
  ⟨(exact_succ epsilon n).descToInjective
      (h' ≫ L.d (n + 1) (n + 2)) (by simp [reassoc_of% w]),
    (exact_succ epsilon n).comp_descToInjective _ _⟩

/-- A chosen cochain map `K• ⟶ L•` extending `g : A ⟶ L•` along the augmentation. -/
def extend : K ⟶ L :=
  CochainComplex.mkHom _ _ (homFZero epsilon g) (homFOne epsilon g)
    (d_comp_homFOne epsilon g).symm
    fun n ⟨h, h', w⟩ ↦
      ⟨(homFSucc epsilon n h h' w.symm).1, (homFSucc epsilon n h h' w.symm).2.symm⟩

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
theorem comp_extend : epsilon ≫ extend epsilon g = g := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n
  · change epsilon.f 0 ≫ (extend epsilon g).f 0 = g.f 0
    exact epsilon_zero_comp_homFZero epsilon g
  · simp only [single_f_succ]

end Existence

section Uniqueness

private def homotopyZeroZero (f : K ⟶ L) (comm : epsilon ≫ f = 0) : K.X 1 ⟶ L.X 0 :=
  (exact_zero epsilon).descToInjective (f.f 0)
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroZero (f : K ⟶ L) (comm : epsilon ≫ f = 0) :
    K.d 0 1 ≫ homotopyZeroZero epsilon f comm = f.f 0 :=
  (exact_zero epsilon).comp_descToInjective _ _

private def homotopyZeroOne (f : K ⟶ L) (comm : epsilon ≫ f = 0) : K.X 2 ⟶ L.X 1 :=
  (exact_succ epsilon 0).descToInjective
    (f.f 1 - homotopyZeroZero epsilon f comm ≫ L.d 0 1)
    (by rw [Preadditive.comp_sub, comp_homotopyZeroZero_assoc epsilon f comm,
      HomologicalComplex.Hom.comm, sub_self])

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroOne (f : K ⟶ L) (comm : epsilon ≫ f = 0) :
    K.d 1 2 ≫ homotopyZeroOne epsilon f comm =
      f.f 1 - homotopyZeroZero epsilon f comm ≫ L.d 0 1 :=
  (exact_succ epsilon 0).comp_descToInjective _ _

private def homotopyZeroSucc (f : K ⟶ L) (n : ℕ)
    (g : K.X (n + 1) ⟶ L.X n) (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.X (n + 3) ⟶ L.X (n + 2) :=
  (exact_succ_succ epsilon n).descToInjective
    (f.f (n + 2) - g' ≫ L.d _ _) (by
      dsimp
      rw [Preadditive.comp_sub, ← HomologicalComplex.Hom.comm, w,
        Preadditive.add_comp, Category.assoc, Category.assoc,
        L.d_comp_d, comp_zero, add_zero, sub_self])

@[reassoc (attr := simp)]
private lemma comp_homotopyZeroSucc (f : K ⟶ L) (n : ℕ)
    (g : K.X (n + 1) ⟶ L.X n) (g' : K.X (n + 2) ⟶ L.X (n + 1))
    (w : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' + g ≫ L.d n (n + 1)) :
    K.d (n + 2) (n + 3) ≫ homotopyZeroSucc epsilon f n g g' w =
      f.f (n + 2) - g' ≫ L.d _ _ :=
  (exact_succ_succ epsilon n).comp_descToInjective _ _

private def homotopyZero (f : K ⟶ L) (comm : epsilon ≫ f = 0) : Homotopy f 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroZero epsilon f comm) (by simp)
    (homotopyZeroOne epsilon f comm) (by simp)
    (fun n ⟨g, g', w⟩ ↦
      ⟨homotopyZeroSucc epsilon f n g g' (by simp only [w, add_comm]), by simp⟩)

/-- Two cochain maps `K• ⟶ L•` which agree after composing with the augmentation are
cochain-homotopic. -/
def homotopy (f g : K ⟶ L) (h : epsilon ≫ f = epsilon ≫ g) : Homotopy f g :=
  Homotopy.equivSubZero.invFun
    (homotopyZero epsilon _ (by rw [Preadditive.comp_sub, h, sub_self]))

end Uniqueness

end ResolutionToInjectiveComplex

/-- A cochain map from the object to a complex of injectives extends along a resolution of the
object, and two extensions are cochain-homotopic. -/
theorem resolutionToInjectiveComplex_exists_uniqueUpToHomotopy
    {A : C} {K L : CochainComplex C ℕ}
    (epsilon : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso epsilon]
    [∀ n, Injective (L.X n)] (g : (CochainComplex.single₀ C).obj A ⟶ L) :
    (∃ f : K ⟶ L, epsilon ≫ f = g) ∧
      ∀ f f' : K ⟶ L, epsilon ≫ f = g → epsilon ≫ f' = g → Nonempty (Homotopy f f') :=
  ⟨⟨ResolutionToInjectiveComplex.extend epsilon g,
      ResolutionToInjectiveComplex.comp_extend epsilon g⟩,
    fun f f' hf hf' ↦ ⟨ResolutionToInjectiveComplex.homotopy epsilon f f' (hf.trans hf'.symm)⟩⟩

end Hartshorne
