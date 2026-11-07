/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.EulerSequenceMaps
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The Euler sequence on projective space: local computations

Hartshorne, *Algebraic Geometry*, II.8, proof of Theorem 8.13 (pp. 176–177), for
`X = ℙ^n_A = Proj A[x_0, …, x_n]`.

* `epi_beta`: the map `β : 𝒪(-1)^{n+1} ⟶ 𝒪`, `(s_j) ↦ ∑ x_j s_j`, is an epimorphism, since on
  `D₊(x_i)` the section `1 / x_i` of the `i`-th summand maps to `1`.
* `chain_rule`: on an open subset `W` of the standard chart `D₊(x_i)`, every function `f`
  satisfies `d f = ∑_l (x_i ∂f/∂x_l) d(x_l / x_i)` in `Ω_{X/Y}`. Locally `f = r / g` with `r, g`
  homogeneous of the same degree `k`; `r / x_i^k` and `g / x_i^k` are polynomials in the
  `x_l / x_i` over `A`, for which the formula follows from the Leibniz rule, and the quotient
  rule passes it to `f`.
-/

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry HomogeneousLocalization TopologicalSpace Opposite
  Hartshorne.ProjGradedModuleSheaf

noncomputable section

namespace Hartshorne.EulerSequence

variable {A : Type u} [CommRing A] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

local notation3 "𝒜" => grading A n
local notation3 "S" => MvPolynomial (Fin (n + 1)) A

local notation3 "at " p =>
  HomogeneousLocalization.AtPrime (grading A n)
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p))

local notation3 "Mt " p =>
  HomogeneousLocalizedModule (grading A n) (gradedTwist (grading A n) (-1))
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p)).primeCompl

/-! ### Sections of `𝒪(-1)^{n+1}` -/

/-- The `j`-th component of a section of `𝒪(-1)^{n+1}`. -/
abbrev comp (j : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (s : (E A n).val.obj U) :
    (O1 A n).val.obj U :=
  (Limits.biproduct.π (fun _ : Fin (n + 1) => O1 A n) j).val.app U s

/-- The section of `𝒪(-1)^{n+1}` with a single nonzero component. -/
abbrev incl (j : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (t : (O1 A n).val.obj U) :
    (E A n).val.obj U :=
  (Limits.biproduct.ι (fun _ : Fin (n + 1) => O1 A n) j).val.app U t

theorem eq_sum_incl_comp {U : (Proj 𝒜).Opensᵒᵖ} (s : (E A n).val.obj U) :
    s = ∑ j, incl j (comp j s) := by
  have h := congrArg (fun φ : E A n ⟶ E A n => φ.val.app U s)
    (Limits.biproduct.total (f := fun _ : Fin (n + 1) => O1 A n))
  simp only at h
  rw [sum_val_app] at h
  exact h.symm

theorem E_ext {U : (Proj 𝒜).Opensᵒᵖ} {s t : (E A n).val.obj U}
    (h : ∀ j, comp j s = comp j t) : s = t := by
  rw [eq_sum_incl_comp s, eq_sum_incl_comp t]
  exact Finset.sum_congr rfl fun j _ => congrArg _ (h j)

theorem comp_incl_self (j : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (t : (O1 A n).val.obj U) :
    comp j (incl j t) = t := by
  have h := congrArg (fun φ : O1 A n ⟶ O1 A n => φ.val.app U t)
    (Limits.biproduct.ι_π_self (fun _ : Fin (n + 1) => O1 A n) j)
  exact h

theorem comp_incl_ne {j k : Fin (n + 1)} (hjk : j ≠ k) {U : (Proj 𝒜).Opensᵒᵖ}
    (t : (O1 A n).val.obj U) : comp k (incl j t) = 0 := by
  have h := congrArg (fun φ : O1 A n ⟶ O1 A n => φ.val.app U t)
    (Limits.biproduct.ι_π_ne (fun _ : Fin (n + 1) => O1 A n) hjk)
  exact h

theorem comp_alpha (j : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (ω : (Ω A n).val.obj U) :
    comp j ((alpha A n).val.app U ω) = (alphaj j).val.app U ω := by
  have h := congrArg (fun φ : Ω A n ⟶ O1 A n => φ.val.app U ω)
    (Limits.biproduct.lift_π (f := fun _ : Fin (n + 1) => O1 A n) alphaj j)
  exact h

theorem beta_app {U : (Proj 𝒜).Opensᵒᵖ} (s : (E A n).val.obj U) :
    (beta A n).val.app U s = ∑ j, secMul j U (comp j s) := by
  conv_lhs => rw [eq_sum_incl_comp s]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := congrArg (fun φ : O1 A n ⟶ O0 A n => φ.val.app U (comp j s))
    (Limits.biproduct.ι_desc (f := fun _ : Fin (n + 1) => O1 A n) mulX j)
  exact h

/-! ### Local tools -/

omit [CommRing A] in
/-- Sections of a sheaf of modules are equal if they are locally equal. -/
theorem modules_ext {X : Scheme.{u}} (N : X.Modules) {U : X.Opensᵒᵖ} {s t : N.val.obj U}
    (h : ∀ x ∈ U.unop, ∃ V, ∃ hV : V ≤ U.unop, x ∈ V ∧
      N.val.map (homOfLE hV).op s = N.val.map (homOfLE hV).op t) : s = t :=
  TopCat.Presheaf.IsSheaf.section_ext N.isSheaf h

theorem irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → S)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd p hp
  change p ∈ MvPolynomial.idealOfVars (Fin (n + 1)) A
  rw [← pow_one (MvPolynomial.idealOfVars (Fin (n + 1)) A),
    MvPolynomial.mem_pow_idealOfVars_iff]
  intro m hm
  have hhom : p.IsHomogeneous d := (MvPolynomial.mem_homogeneousSubmodule d p).1 hp
  have hdeg : (Finsupp.weight 1) m = d := hhom (MvPolynomial.mem_support_iff.1 hm)
  have hdeg' : Finsupp.degree m = d := by
    rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
    exact hdeg
  rw [hdeg']
  exact hd

/-- Every point of `ℙ^n` lies in some standard chart `D₊(x_i)`. -/
theorem exists_X_notMem (p : ProjectiveSpectrum 𝒜) :
    ∃ i : Fin (n + 1), MvPolynomial.X i ∉ p.asHomogeneousIdeal := by
  by_contra! h
  refine p.not_irrelevant_le (irrelevant_le_span_X.trans ?_)
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact h i

theorem X_mem_one (i : Fin (n + 1)) : (MvPolynomial.X i : S) ∈ 𝒜 1 :=
  MvPolynomial.isHomogeneous_X A i

theorem X_pow_mem (i : Fin (n + 1)) (k : ℕ) : (MvPolynomial.X i : S) ^ k ∈ 𝒜 k := by
  simpa using SetLike.pow_mem_graded k (X_mem_one (A := A) (n := n) i)

theorem one_mem_twist : (1 : S) ∈ gradedTwist 𝒜 (-1) ((1 : ℕ) : ℤ) :=
  (mem_gradedTwist_of_eq (k := 0) (by norm_num)).2 (SetLike.GradedOne.one_mem)

/-! ### Sections on a standard chart -/

/-- The fraction `r / x_i^k` on an open set where `x_i` does not vanish. -/
def fracSec (i : Fin (n + 1)) (k : ℕ) (r : S) (hr : r ∈ 𝒜 k) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) : (Proj 𝒜).presheaf.obj (op W) :=
  ⟨fun p => HomogeneousLocalization.mk ⟨k, ⟨r, hr⟩, ⟨MvPolynomial.X i ^ k, X_pow_mem i k⟩,
      fun h => hW p.2 (p.1.isPrime.mem_of_pow_mem k h)⟩,
    fun p => ⟨W, p.2, 𝟙 _, k, ⟨r, hr⟩, ⟨MvPolynomial.X i ^ k, X_pow_mem i k⟩,
      fun q h => hW q.2 (q.1.isPrime.mem_of_pow_mem k h), fun _ => rfl⟩⟩

theorem fracSec_val (i : Fin (n + 1)) (k : ℕ) (r : S) (hr : r ∈ 𝒜 k) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (p : ProjectiveSpectrum 𝒜) (hp : p ∈ W) :
    ((fracSec i k r hr W hW).1 ⟨p, hp⟩).val =
      Localization.mk r (⟨MvPolynomial.X i ^ k, fun h => hW hp (p.isPrime.mem_of_pow_mem k h)⟩ :
        p.asHomogeneousIdeal.toIdeal.primeCompl) :=
  rfl

/-- The unit section `1` of `𝒪`. -/
abbrev oneSec (U : (Proj 𝒜).Opensᵒᵖ) : (O0 A n).val.obj U :=
  (1 : (Proj 𝒜).ringCatSheaf.obj.obj U)

/-- The section `1 / x_i` of `𝒪(-1)` on an open set where `x_i` does not vanish. -/
def invX (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) : (O1 A n).val.obj (op W) :=
  (⟨fun p => HomogeneousLocalizedModule.mk 1 1 one_mem_twist _ (X_mem_one i) (hW p.2),
    fun p => ⟨W, p.2, 𝟙 _, 1, 1, one_mem_twist, _, X_mem_one i, fun q => hW q.2,
      fun _ => rfl⟩⟩ : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj (op W))

theorem secMul_invX (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :
    secMul i (op W) (invX i W hW) = oneSec (op W) := by
  apply O0_ext
  intro p
  apply HomogeneousLocalization.val_injective
  refine (ptMul_val i _ _).trans ?_
  change _ * toLoc _ (LocalizedModule.mk _ _) = (1 : HomogeneousLocalization 𝒜 _).val
  rw [toLoc_mk, HomogeneousLocalization.val_one, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, one_mul, mul_one]
  exact Localization.mk_self ⟨_, hW p.2⟩

/-! ### Surjectivity of `β` -/

omit [CommRing A] in
theorem app_eq_zero_of_eq_zero {X : Scheme.{u}} {M N : X.Modules} {g : M ⟶ N} (hg : g = 0)
    (U : X.Opensᵒᵖ) (x : M.val.obj U) : g.val.app U x = 0 := by
  subst hg
  rfl

theorem beta_incl_invX (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :
    (beta A n).val.app (op W) (incl i (invX i W hW)) = oneSec (op W) := by
  rw [beta_app, Finset.sum_eq_single i
    (fun j _ hj => by rw [comp_incl_ne (Ne.symm hj), map_zero]) (by simp),
    comp_incl_self]
  exact secMul_invX i W hW

/-- **`β : 𝒪(-1)^{n+1} ⟶ 𝒪` is an epimorphism**: on `D₊(x_i)` the section `1 / x_i` of the
`i`-th summand maps to `1`. -/
theorem epi_beta : Epi (beta A n) := by
  refine Preadditive.epi_of_cancel_zero _ fun {Z} h hh => ?_
  have h1 : ∀ U : (Proj 𝒜).Opensᵒᵖ, h.val.app U (oneSec U) = 0 := by
    intro U
    refine modules_ext Z fun x hx => ?_
    obtain ⟨i, hi⟩ := exists_X_notMem (x : ProjectiveSpectrum 𝒜)
    refine ⟨U.unop ⊓ Proj.basicOpen 𝒜 (MvPolynomial.X i), inf_le_left, ⟨hx, hi⟩, ?_⟩
    rw [map_zero, ← PresheafOfModules.naturality_apply]
    have e1 : (O0 A n).val.map (homOfLE inf_le_left).op (oneSec U) =
        oneSec (op (U.unop ⊓ Proj.basicOpen 𝒜 (MvPolynomial.X i))) :=
      PresheafOfModules.unit_map_one _ _
    rw [e1, ← beta_incl_invX i _ inf_le_right]
    exact app_eq_zero_of_eq_zero hh _ _
  apply (SheafOfModules.unitHomEquiv Z).injective
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  change h.val.app U (oneSec U) = (0 : O0 A n ⟶ Z).val.app U (oneSec U)
  exact (h1 U).trans (app_eq_zero_of_eq_zero rfl U _).symm

/-! ### The chain rule on a standard chart -/

/-- The canonical derivation `d : 𝒪 → Ω`. -/
abbrev dd {U : (Proj 𝒜).Opensᵒᵖ} (f : (Proj 𝒜).presheaf.obj U) : (Ω A n).val.obj U :=
  (Scheme.relativeDifferentialsDerivation (toBase A n)).d f

/-- The coefficient `x_i ∂f/∂x_l` of `d(x_l / x_i)` in `d f` on the chart `D₊(x_i)`. -/
abbrev cD (i l : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (f : (Proj 𝒜).presheaf.obj U) :
    (Proj 𝒜).ringCatSheaf.obj.obj U :=
  secMul i U (secD l U f)

/-- A function viewed as a scalar for sheaves of modules. -/
abbrev rc {U : (Proj 𝒜).Opensᵒᵖ} (f : (Proj 𝒜).presheaf.obj U) :
    (Proj 𝒜).ringCatSheaf.obj.obj U := f

/-- The coordinate function `x_l / x_i` on an open subset of `D₊(x_i)`. -/
abbrev yS (i l : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) : (Proj 𝒜).presheaf.obj (op W) :=
  fracSec i 1 (MvPolynomial.X l) (X_mem_one l) W hW

theorem cD_val (i l : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (f : (Proj 𝒜).presheaf.obj U)
    (p : ProjectiveSpectrum 𝒜) (hp : p ∈ U.unop) :
    (((cD i l f : (Proj 𝒜).presheaf.obj U)).1 ⟨p, hp⟩).val =
      algebraMap S _ (MvPolynomial.X i) * toLoc _ (pD A l (pt p) ((f.1 ⟨p, hp⟩).val)) :=
  ptMul_val i p _

theorem cD_yS (i l m : Fin (n + 1)) (hl : l ≠ i) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :
    cD i l (yS i m W hW) = if l = m then 1 else 0 := by
  by_cases hlm : l = m
  · subst hlm
    rw [if_pos rfl]
    apply Subtype.ext
    funext ⟨p, hp⟩
    apply HomogeneousLocalization.val_injective
    refine (cD_val i l _ p hp).trans ?_
    erw [fracSec_val]
    rw [pD_mk, toLoc_mk]
    simp only [pow_one, MvPolynomial.pderiv_X, Pi.single_eq_same, Pi.single_apply,
      if_neg hl.symm, mul_zero, sub_zero, mul_one]
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul]
    change _ = (1 : HomogeneousLocalization 𝒜 _).val
    rw [HomogeneousLocalization.val_one]
    exact Localization.mk_self ⟨_, mul_mem (hW hp) (hW hp)⟩
  · rw [if_neg hlm]
    apply Subtype.ext
    funext ⟨p, hp⟩
    apply HomogeneousLocalization.val_injective
    refine (cD_val i l _ p hp).trans ?_
    erw [fracSec_val]
    rw [pD_mk, toLoc_mk]
    simp only [pow_one, MvPolynomial.pderiv_X, Pi.single_apply, if_neg hl.symm,
      if_neg (Ne.symm hlm), mul_zero, sub_zero, Localization.mk_zero]
    change _ = (0 : HomogeneousLocalization 𝒜 _).val
    rw [HomogeneousLocalization.val_zero]

/-- The chain-rule property of a function `f` on an open subset `W` of `D₊(x_i)`:
`d f = ∑_l (x_i ∂f/∂x_l) d(x_l / x_i)`. -/
def PCR (i : Fin (n + 1)) (W : (Proj 𝒜).Opens) (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i))
    (f : (Proj 𝒜).presheaf.obj (op W)) : Prop :=
  dd f = ∑ l, cD i l f • dd (yS i l W hW)

theorem dd_add {U : (Proj 𝒜).Opensᵒᵖ} (f g : (Proj 𝒜).presheaf.obj U) :
    dd (f + g) = dd f + dd g :=
  map_add _ f g

theorem dd_mul {U : (Proj 𝒜).Opensᵒᵖ} (f g : (Proj 𝒜).presheaf.obj U) :
    dd (f * g) = rc f • dd g + rc g • dd f :=
  PresheafOfModules.Derivation.d_mul _ f g

theorem cD_add (i l : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (f g : (Proj 𝒜).presheaf.obj U) :
    cD i l (f + g) = cD i l f + cD i l g :=
  (congrArg (secMul i U) (map_add (secD l U) f g)).trans (map_add (secMul i U) _ _)

theorem cD_mul (i l : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (f g : (Proj 𝒜).presheaf.obj U) :
    cD i l (f * g) = rc f * cD i l g + rc g * cD i l f :=
  (congrArg (secMul i U) (secD_mul l U f g)).trans
    (((map_add (secMul i U) _ _).trans (congrArg₂ (· + ·) ((secMul i U).map_smul _ _)
      ((secMul i U).map_smul _ _))))

theorem PCR_add {i : Fin (n + 1)} {W : (Proj 𝒜).Opens}
    {hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)} {f g : (Proj 𝒜).presheaf.obj (op W)}
    (hf : PCR i W hW f) (hg : PCR i W hW g) : PCR i W hW (f + g) :=
  (dd_add f g).trans ((congrArg₂ (· + ·) hf hg).trans (Finset.sum_add_distrib.symm.trans
    (Finset.sum_congr rfl fun l _ =>
      (add_smul _ _ _).symm.trans (congrArg (· • _) (cD_add i l f g).symm))))

theorem PCR_mul {i : Fin (n + 1)} {W : (Proj 𝒜).Opens}
    {hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)} {f g : (Proj 𝒜).presheaf.obj (op W)}
    (hf : PCR i W hW f) (hg : PCR i W hW g) : PCR i W hW (f * g) :=
  (dd_mul f g).trans ((congrArg₂ (fun a b => rc f • a + rc g • b) hg hf).trans
    ((congrArg₂ (· + ·) (Finset.smul_sum ..) (Finset.smul_sum ..)).trans
      (Finset.sum_add_distrib.symm.trans (Finset.sum_congr rfl fun l _ => by
        rw [cD_mul, add_smul, mul_smul, mul_smul]))))

omit [CommRing A] in
/-- Abstract form of the quotient step of the chain rule. -/
theorem chain_div {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Fintype ι]
    (d : R → M) (c : ι → R → R) (y : ι → M)
    (hd : ∀ a b, d (a * b) = a • d b + b • d a) (hc : ∀ l a b, c l (a * b) = a * c l b + b * c l a)
    {f g : R} (hgu : IsUnit g) (hg : d g = ∑ l, c l g • y l)
    (hh : d (f * g) = ∑ l, c l (f * g) • y l) : d f = ∑ l, c l f • y l := by
  have e1 : g • d f = d (f * g) - f • d g := by
    rw [hd]
    abel
  have key : g • d f = g • ∑ l, c l f • y l := by
    rw [e1, hh, hg, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hc, add_smul, mul_smul, mul_smul]
    abel
  exact hgu.smul_left_cancel.mp key

theorem PCR_div {i : Fin (n + 1)} {W : (Proj 𝒜).Opens}
    {hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)} {f g h : (Proj 𝒜).presheaf.obj (op W)}
    (hgu : IsUnit (rc g)) (hg : PCR i W hW g) (hh : PCR i W hW h) (hfg : f * g = h) :
    PCR i W hW f := by
  subst hfg
  exact chain_div (R := (Proj 𝒜).ringCatSheaf.obj.obj (op W)) (M := (Ω A n).val.obj (op W))
    (fun a => dd (show (Proj 𝒜).presheaf.obj (op W) from a))
    (fun l a => cD i l (show (Proj 𝒜).presheaf.obj (op W) from a))
    (fun l => dd (yS i l W hW)) (fun a b => dd_mul a b) (fun l a b => cD_mul i l a b) hgu hg hh

theorem yS_self (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) : yS i i W hW = 1 := by
  apply Subtype.ext
  funext ⟨p, hp⟩
  apply HomogeneousLocalization.val_injective
  erw [fracSec_val]
  change _ = (1 : HomogeneousLocalization 𝒜 _).val
  rw [HomogeneousLocalization.val_one]
  simp only [pow_one]
  exact Localization.mk_self ⟨_, hW hp⟩

theorem dd_one {U : (Proj 𝒜).Opensᵒᵖ} : dd (1 : (Proj 𝒜).presheaf.obj U) = 0 :=
  PresheafOfModules.Derivation.d_one _ _

theorem PCR_yS (i m : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) : PCR i W hW (yS i m W hW) := by
  have hi : dd (yS i i W hW) = 0 := by rw [yS_self]; exact dd_one
  show dd (yS i m W hW) = ∑ l, cD i l (yS i m W hW) • dd (yS i l W hW)
  rw [Finset.sum_eq_single m]
  · by_cases hm : m = i
    · subst hm
      rw [hi, smul_zero]
    · rw [cD_yS i m m hm, if_pos rfl, one_smul]
  · intro l _ hlm
    by_cases hl : l = i
    · subst hl
      rw [hi, smul_zero]
    · rw [cD_yS i l m hl, if_neg hlm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ m) h

/-- The constant function `a ∈ A` on an open set. -/
def cstSec (a : A) (W : (Proj 𝒜).Opens) : (Proj 𝒜).presheaf.obj (op W) :=
  (Proj 𝒜).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op
    ((toBase A n).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))

theorem cstSec_val (a : A) (W : (Proj 𝒜).Opens) (p : ProjectiveSpectrum 𝒜) (hp : p ∈ W) :
    ((cstSec (n := n) a W).1 ⟨p, hp⟩).val = algebraMap S _ (MvPolynomial.C a) :=
  toBase_appTop_val a p

theorem dd_cstSec (a : A) (W : (Proj 𝒜).Opens) : dd (cstSec (n := n) a W) = 0 := by
  have hk : (Scheme.relativeDifferentialsDerivation (toBase A n)).d (X := op ⊤)
      ((toBase A n).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)) = 0 :=
    RelDiffLocal.kills_of_derivation (toBase A n) _ ⊤ _
  have hm := (Scheme.relativeDifferentialsDerivation (toBase A n)).d_map
    (homOfLE (le_top : W ≤ ⊤)).op
    ((toBase A n).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))
  rw [hk, map_zero] at hm
  exact hm

theorem secD_cstSec (l : Fin (n + 1)) (a : A) (W : (Proj 𝒜).Opens) :
    secD l (op W) (cstSec (n := n) a W) = 0 :=
  section_ext (U := op W) fun x => ptD_const l x.1 _ a (cstSec_val a W x.1 x.2)

theorem PCR_cst (i : Fin (n + 1)) (a : A) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) : PCR i W hW (cstSec a W) := by
  show dd (cstSec a W) = ∑ l, cD i l (cstSec a W) • dd (yS i l W hW)
  rw [dd_cstSec]
  symm
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [cD, secD_cstSec, map_zero, zero_smul]

theorem PCR_zero (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) : PCR i W hW 0 := by
  show dd 0 = ∑ l, cD i l 0 • dd (yS i l W hW)
  rw [dd, map_zero]
  symm
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [cD, map_zero, map_zero, zero_smul]

theorem fracSec_add (i : Fin (n + 1)) (k : ℕ) {r t : S} (hr : r ∈ 𝒜 k) (ht : t ∈ 𝒜 k)
    (W : (Proj 𝒜).Opens) (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :
    fracSec i k (r + t) (add_mem hr ht) W hW = fracSec i k r hr W hW + fracSec i k t ht W hW := by
  apply Subtype.ext
  funext ⟨p, hp⟩
  apply HomogeneousLocalization.val_injective
  change _ = (_ + _ : HomogeneousLocalization 𝒜 _).val
  rw [HomogeneousLocalization.val_add]
  erw [fracSec_val, fracSec_val, fracSec_val]
  rw [Localization.add_mk_self]

theorem fracSec_mul (i : Fin (n + 1)) {j k l : ℕ} (hj : j = k + l) {r t : S} (hr : r ∈ 𝒜 k)
    (ht : t ∈ 𝒜 l) (hrt : r * t ∈ 𝒜 j) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :
    fracSec i j (r * t) hrt W hW = fracSec i k r hr W hW * fracSec i l t ht W hW := by
  subst hj
  apply Subtype.ext
  funext ⟨p, hp⟩
  apply HomogeneousLocalization.val_injective
  change _ = (_ * _ : HomogeneousLocalization 𝒜 _).val
  rw [HomogeneousLocalization.val_mul]
  erw [fracSec_val, fracSec_val, fracSec_val]
  rw [Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add _ _ _)

theorem fracSec_algebraMap (i : Fin (n + 1)) (a : A) (h : algebraMap A S a ∈ 𝒜 0)
    (W : (Proj 𝒜).Opens) (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :
    fracSec i 0 (algebraMap A S a) h W hW = cstSec a W := by
  apply Subtype.ext
  funext ⟨p, hp⟩
  apply HomogeneousLocalization.val_injective
  erw [fracSec_val, cstSec_val a W p hp]
  rw [← Localization.mk_one_eq_algebraMap, MvPolynomial.algebraMap_eq]
  congr 1

theorem fracSec_smul (i : Fin (n + 1)) (a : A) {m : S} (hm : m ∈ 𝒜 1) (h : a • m ∈ 𝒜 1)
    (W : (Proj 𝒜).Opens) (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) :
    fracSec i 1 (a • m) h W hW = cstSec a W * fracSec i 1 m hm W hW := by
  apply Subtype.ext
  funext ⟨p, hp⟩
  apply HomogeneousLocalization.val_injective
  change _ = (_ * _ : HomogeneousLocalization 𝒜 _).val
  rw [HomogeneousLocalization.val_mul]
  erw [fracSec_val, fracSec_val, cstSec_val a W p hp]
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, MvPolynomial.smul_eq_C_mul]

theorem PCR_fracSec_one (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) {m : S} (hm : m ∈ 𝒜 1) :
    PCR i W hW (fracSec i 1 m hm W hW) := by
  have hspan : (𝒜 1 : Submodule A S) =
      Submodule.span A (Set.range (MvPolynomial.X : Fin (n + 1) → S)) :=
    MvPolynomial.homogeneousSubmodule_one_eq_span_X
  have hm' : m ∈ Submodule.span A (Set.range (MvPolynomial.X : Fin (n + 1) → S)) := by
    rw [← hspan]
    exact hm
  induction hm' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    exact PCR_yS i l W hW
  | zero =>
    have e : fracSec i 1 (0 : S) hm W hW = 0 := by
      apply Subtype.ext
      funext ⟨p, hp⟩
      apply HomogeneousLocalization.val_injective
      erw [fracSec_val]
      rw [Localization.mk_zero]
      change (0 : Localization _) = (0 : HomogeneousLocalization 𝒜 _).val
      rw [HomogeneousLocalization.val_zero]
    rw [e]
    exact PCR_zero i W hW
  | add x y hx hy ihx ihy =>
    have hx1 : x ∈ 𝒜 1 := by rw [hspan]; exact hx
    have hy1 : y ∈ 𝒜 1 := by rw [hspan]; exact hy
    rw [fracSec_add i 1 hx1 hy1]
    exact PCR_add (ihx hx1) (ihy hy1)
  | smul a x hx ihx =>
    have hx1 : x ∈ 𝒜 1 := by rw [hspan]; exact hx
    rw [fracSec_smul i a hx1]
    exact PCR_mul (PCR_cst i a W hW) (ihx hx1)

theorem PCR_fracSec (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) {k : ℕ} {r : S} (hr : r ∈ 𝒜 k) :
    PCR i W hW (fracSec i k r hr W hW) := by
  have hpow : ∀ j : ℕ, (𝒜 1 : Submodule A S) ^ j = 𝒜 j := fun j =>
    MvPolynomial.homogeneousSubmodule_one_pow (σ := Fin (n + 1)) (R := A) j
  have hr' : r ∈ (𝒜 1) ^ k := by
    rw [hpow]
    exact hr
  induction hr' using Submodule.pow_induction_on_left' with
  | algebraMap a =>
    rw [fracSec_algebraMap i a]
    exact PCR_cst i a W hW
  | add x y j hx hy ihx ihy =>
    have hx' : x ∈ 𝒜 j := by rw [← hpow]; exact hx
    have hy' : y ∈ 𝒜 j := by rw [← hpow]; exact hy
    rw [fracSec_add i j hx' hy']
    exact PCR_add (ihx hx') (ihy hy')
  | mem_mul m hm j x hx ihx =>
    have hx' : x ∈ 𝒜 j := by rw [← hpow]; exact hx
    rw [fracSec_mul i (by omega : j.succ = 1 + j) hm hx']
    exact PCR_mul (PCR_fracSec_one i W hW hm) (ihx hx')

theorem PCR_of_local (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (f : (Proj 𝒜).presheaf.obj (op W))
    (h : ∀ p ∈ W, ∃ (W' : (Proj 𝒜).Opens) (hW' : W' ≤ W), p ∈ W' ∧
      PCR i W' (hW'.trans hW) ((Proj 𝒜).presheaf.map (homOfLE hW').op f)) :
    PCR i W hW f := by
  show dd f = ∑ l, cD i l f • dd (yS i l W hW)
  refine modules_ext (Ω A n) fun p hp => ?_
  obtain ⟨W', hW', hpW', hP⟩ := h p hp
  refine ⟨W', hW', hpW', ?_⟩
  have hP' : dd ((Proj 𝒜).presheaf.map (homOfLE hW').op f) =
      ∑ l, cD i l ((Proj 𝒜).presheaf.map (homOfLE hW').op f) •
        dd (yS i l W' (hW'.trans hW)) := hP
  have e1 := (Scheme.relativeDifferentialsDerivation (toBase A n)).d_map (homOfLE hW').op f
  refine e1.symm.trans (hP'.trans ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [PresheafOfModules.map_smul]
  have e2 := (Scheme.relativeDifferentialsDerivation (toBase A n)).d_map (homOfLE hW').op
    (yS i l W hW)
  exact congrArg₂ (· • ·) rfl e2

/-- The inverse `x_i^k / g` of `g / x_i^k` where `g` does not vanish. -/
def invFracSec (i : Fin (n + 1)) (k : ℕ) (g : S) (hg : g ∈ 𝒜 k) (V : (Proj 𝒜).Opens)
    (hV : ∀ p ∈ V, g ∉ ProjectiveSpectrum.asHomogeneousIdeal (p : ProjectiveSpectrum 𝒜)) :
    (Proj 𝒜).presheaf.obj (op V) :=
  ⟨fun p => HomogeneousLocalization.mk ⟨k, ⟨MvPolynomial.X i ^ k, X_pow_mem i k⟩, ⟨g, hg⟩,
      hV p.1 p.2⟩,
    fun p => ⟨V, p.2, 𝟙 _, k, ⟨MvPolynomial.X i ^ k, X_pow_mem i k⟩, ⟨g, hg⟩,
      fun q => hV q.1 q.2, fun _ => rfl⟩⟩

/-- **The chain rule on `D₊(x_i)`**: for every function `f` on an open `W ⊆ D₊(x_i)`,
`d f = ∑_l (x_i ∂f/∂x_l) d(x_l / x_i)`. -/
theorem chain_rule (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (f : (Proj 𝒜).presheaf.obj (op W)) :
    PCR i W hW f := by
  refine PCR_of_local i W hW f fun p hp => ?_
  obtain ⟨V, hpV, ιVW, k, ⟨r, hr⟩, ⟨g, hg⟩, nin, w⟩ := f.2 ⟨p, hp⟩
  have hVW : V ≤ W := ιVW.le
  refine ⟨V, hVW, hpV, ?_⟩
  have hgV : ∀ q ∈ V, g ∉ ProjectiveSpectrum.asHomogeneousIdeal (q : ProjectiveSpectrum 𝒜) :=
    fun q hq => nin ⟨q, hq⟩
  refine PCR_div (g := fracSec i k g hg V (hVW.trans hW)) (h := fracSec i k r hr V (hVW.trans hW))
    ?_ (PCR_fracSec i V _ hg) (PCR_fracSec i V _ hr) ?_
  · refine IsUnit.of_mul_eq_one (rc (invFracSec i k g hg V hgV)) ?_
    apply Subtype.ext
    funext ⟨q, hq⟩
    apply HomogeneousLocalization.val_injective
    change (_ * _ : HomogeneousLocalization 𝒜 _).val = (1 : HomogeneousLocalization 𝒜 _).val
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
    erw [fracSec_val]
    change _ * (HomogeneousLocalization.mk _).val = _
    rw [HomogeneousLocalization.val_mk, Localization.mk_mul, ← Localization.mk_one,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul, mul_one]; ring⟩
  · apply Subtype.ext
    funext ⟨q, hq⟩
    apply HomogeneousLocalization.val_injective
    change (_ * _ : HomogeneousLocalization 𝒜 _).val = _
    rw [HomogeneousLocalization.val_mul]
    erw [fracSec_val, fracSec_val]
    have wq := congrArg HomogeneousLocalization.val (w ⟨q, hq⟩)
    change ((f.1 ⟨q, hVW hq⟩)).val = _ at wq
    change (f.1 ⟨q, hVW hq⟩).val * _ = _
    rw [wq, HomogeneousLocalization.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]; ring⟩

end Hartshorne.EulerSequence
