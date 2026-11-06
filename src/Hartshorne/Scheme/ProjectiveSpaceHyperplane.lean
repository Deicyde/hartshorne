/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveSpaceRegular
import Hartshorne.Scheme.ProjClosedSubschemeTruncation

/-!
# Hyperplane sections of projective space

Hartshorne, *Algebraic Geometry*, II.8, the projective-space case in the proof of
Theorem 8.18 (pp. 179–180).

Let `k` be a field, `n ≥ 1` and `S = k[x₀, …, xₙ]`, so that `ℙⁿ_k = Proj S`. A
hyperplane of `ℙⁿ_k` is the zero locus of a nonzero linear form `h ∈ S₁`; the
corresponding hyperplane section is the closed subscheme `Proj (S/(h)) ⟶ Proj S`
cut out by the homogeneous ideal `(h)`. Every such section is isomorphic to
`ℙⁿ⁻¹_k`, hence regular. The complete linear system `|H|` of hyperplanes is the
set of nonzero linear forms up to scalars, so quantifying over nonzero linear forms
says that every member of `|H|` is good.

## Proof

Some variable `x_p` occurs in `h`. After the coordinate swap `x₀ ↔ x_p` and the
identification `k[x₀, …, xₙ] ≅ k[x₁, …, xₙ][x₀]`, the linear form `h` becomes
`c • (x₀ - r)` with `c ∈ kˣ` and `r` a linear form in `x₁, …, xₙ`. Evaluating
`x₀` at `r` gives a surjective graded homomorphism `φ : S → k[y₁, …, yₙ]` whose
kernel is `(h)` (factor theorem). The induced map `S/(h) → k[y₁, …, yₙ]` is a
graded isomorphism, so the induced morphism of `Proj` schemes is an isomorphism.
Regularity then follows from the regularity of projective space over a field.

## Main results

* `Hartshorne.hyperplaneIdeal`, `Hartshorne.hyperplaneSection`,
  `Hartshorne.hyperplaneSectionι`: the hyperplane section `Proj (S/(h))` and its
  closed immersion into `ℙⁿ_k`.
* `Hartshorne.nonempty_iso_hyperplaneSection`: the hyperplane section is
  isomorphic to `ℙⁿ⁻¹_k`.
* `Hartshorne.hyperplaneSection_isRegular`: every hyperplane section is regular.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hartshorne

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A scheme isomorphic to a regular scheme is regular. -/
theorem isRegular_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (hY : Y.IsRegular) :
    X.IsRegular := by
  obtain ⟨hN, hR⟩ := hY
  refine ⟨isLocallyNoetherian_of_isOpenImmersion e.hom, fun x => ?_⟩
  have : IsRegularLocalRing (Y.presheaf.stalk (e.hom x)) := hR _
  exact IsRegularLocalRing.of_ringEquiv (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv

variable (k : Type u) [Field k] (n : ℕ)

/-- The homogeneous ideal `(h) ⊆ k[x₀, …, xₙ]` of a linear form `h`. -/
def hyperplaneIdeal (h : MvPolynomial (Fin (n + 1)) k)
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) :
    HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) :=
  ⟨Ideal.span {h}, Ideal.homogeneous_span _ _ (by rintro x rfl; exact ⟨1, hh⟩)⟩

/-- The hyperplane section `Proj (k[x₀, …, xₙ]/(h))` of `ℙⁿ_k` cut out by a linear
form `h`. -/
abbrev hyperplaneSection (h : MvPolynomial (Fin (n + 1)) k)
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) : Scheme.{u} :=
  Proj (gradedQuotient (homogeneousSubmodule (Fin (n + 1)) k) (hyperplaneIdeal k n h hh))

/-- The closed immersion of the hyperplane section `Proj (S/(h))` into `ℙⁿ_k`. -/
def hyperplaneSectionι (h : MvPolynomial (Fin (n + 1)) k)
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) :
    hyperplaneSection k n h hh ⟶ projectiveSpaceScheme k n :=
  projQuotientι _ (hyperplaneIdeal k n h hh)

instance isClosedImmersion_hyperplaneSectionι (h : MvPolynomial (Fin (n + 1)) k)
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) :
    IsClosedImmersion (hyperplaneSectionι k n h hh) :=
  isClosedImmersion_projQuotientι _

namespace HyperplaneSection

variable {k n}

/-- A nonzero linear form involves some variable. -/
theorem exists_degreeOf_pos {h : MvPolynomial (Fin (n + 1)) k}
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) (h0 : h ≠ 0) :
    ∃ p, 0 < degreeOf p h := by
  obtain ⟨m, hm⟩ := ne_zero_iff.mp h0
  have hdeg := (mem_homogeneousSubmodule _ _).mp hh hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hdeg
  obtain ⟨p, hp⟩ := Finsupp.ne_iff.mp hm0
  exact ⟨p, lt_of_lt_of_le (Nat.pos_of_ne_zero hp)
    (monomial_le_degreeOf p (mem_support_iff.mpr hm))⟩

variable (k) in
/-- The coordinate change `x₀ ↔ x_p` followed by `k[x₀, …, xₙ] ≅ k[x₁, …, xₙ][x₀]`. -/
def coordEquiv (p : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) k ≃ₐ[k] Polynomial (MvPolynomial (Fin n) k) :=
  (renameEquiv k (Equiv.swap 0 p)).trans (finSuccEquiv k n)

theorem coordEquiv_apply (p : Fin (n + 1)) (x : MvPolynomial (Fin (n + 1)) k) :
    coordEquiv k p x = finSuccEquiv k n (rename (Equiv.swap 0 p) x) := rfl

/-- After the coordinate change, a linear form involving `x_p` becomes
`c • (x₀ - r)` with `c ≠ 0` and `r` a linear form in the remaining variables. -/
theorem exists_coordEquiv_eq {h : MvPolynomial (Fin (n + 1)) k}
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) {p : Fin (n + 1)}
    (hp : 0 < degreeOf p h) :
    ∃ c : k, c ≠ 0 ∧ ∃ r : MvPolynomial (Fin n) k, r.IsHomogeneous 1 ∧
      coordEquiv k p h = Polynomial.C (C c) * (Polynomial.X - Polynomial.C r) := by
  have hh' : h.IsHomogeneous 1 := (mem_homogeneousSubmodule _ _).mp hh
  have hhom : (rename (Equiv.swap 0 p) h).IsHomogeneous 1 := hh'.rename_isHomogeneous
  set F := coordEquiv k p h with hFdef
  have hFdeg : F.natDegree = degreeOf p h := by
    rw [hFdef, coordEquiv_apply, natDegree_finSuccEquiv]
    have := degreeOf_rename_of_injective (p := h) (Equiv.swap 0 p).injective p
    rwa [Equiv.swap_apply_right] at this
  have hle : F.natDegree ≤ 1 :=
    hFdeg ▸ (degreeOf_le_totalDegree h p).trans hh'.totalDegree_le
  have hF1 : F.natDegree = 1 := by omega
  have hFeq := Polynomial.eq_X_add_C_of_natDegree_le_one hle
  have ha1 : (F.coeff 1).IsHomogeneous 0 := hhom.finSuccEquiv_coeff_isHomogeneous 1 0 rfl
  have ha0 : (F.coeff 0).IsHomogeneous 1 := hhom.finSuccEquiv_coeff_isHomogeneous 0 1 rfl
  obtain ⟨c, hc⟩ : ∃ c : k, F.coeff 1 = C c :=
    ⟨_, totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous (Fin n)).mpr ha1)⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hF0 : F ≠ 0 := by
      rintro hF
      rw [hF, Polynomial.natDegree_zero] at hF1
      exact zero_ne_one hF1
    apply Polynomial.leadingCoeff_ne_zero.mpr hF0
    rw [Polynomial.leadingCoeff, hF1, hc, C_0]
  refine ⟨c, hc0, -(C c⁻¹ * F.coeff 0), ?_, ?_⟩
  · simpa using ((isHomogeneous_C (Fin n) c⁻¹).mul ha0).neg
  · have hcr : C c * -(C c⁻¹ * F.coeff 0) = -F.coeff 0 := by
      rw [mul_neg, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul]
    conv_lhs => rw [hFeq]
    rw [hc, mul_sub, ← Polynomial.C_mul, hcr, Polynomial.C_neg, sub_neg_eq_add]

variable (p : Fin (n + 1)) (r : MvPolynomial (Fin n) k)

variable (k) in
/-- Evaluation of `x₀` at `r` after the coordinate change. -/
def evalHom : MvPolynomial (Fin (n + 1)) k →+* MvPolynomial (Fin n) k :=
  (Polynomial.evalRingHom r).comp (coordEquiv k p : MvPolynomial (Fin (n + 1)) k →+* _)

theorem evalHom_apply (x : MvPolynomial (Fin (n + 1)) k) :
    evalHom k p r x = Polynomial.eval r (coordEquiv k p x) := rfl

theorem evalHom_X_succ (i : Fin n) :
    evalHom k p r (X (Equiv.swap 0 p i.succ)) = X i := by
  simp [evalHom_apply, coordEquiv_apply, finSuccEquiv_X_succ]

theorem evalHom_X_isHomogeneous (hr : r.IsHomogeneous 1) (j : Fin (n + 1)) :
    (evalHom k p r (X j)).IsHomogeneous 1 := by
  have key : ∀ j' : Fin (n + 1),
      (Polynomial.eval r (finSuccEquiv k n (X j'))).IsHomogeneous 1 := by
    intro j'
    refine Fin.cases ?_ (fun i => ?_) j'
    · simpa [finSuccEquiv_X_zero] using hr
    · simpa [finSuccEquiv_X_succ] using isHomogeneous_X k i
  simpa [evalHom_apply, coordEquiv_apply] using key (Equiv.swap 0 p j)

theorem evalHom_eq_aeval :
    evalHom k p r = (aeval fun j => evalHom k p r (X j)).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · simp [evalHom_apply, coordEquiv_apply, finSuccEquiv_apply]
  · simp

theorem evalHom_mem (hr : r.IsHomogeneous 1) {d : ℕ} {x : MvPolynomial (Fin (n + 1)) k}
    (hx : x ∈ homogeneousSubmodule (Fin (n + 1)) k d) :
    evalHom k p r x ∈ homogeneousSubmodule (Fin n) k d := by
  rw [mem_homogeneousSubmodule] at hx ⊢
  rw [evalHom_eq_aeval]
  simpa using hx.aeval _ (evalHom_X_isHomogeneous p r hr)

theorem evalHom_rename (t : MvPolynomial (Fin n) k) :
    evalHom k p r (rename (fun i => Equiv.swap 0 p i.succ) t) = t := by
  rw [evalHom_eq_aeval]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename, Function.comp_def,
    evalHom_X_succ]
  exact aeval_X_left_apply t

/-- The kernel of `evalHom` is the ideal `(h)` (factor theorem). -/
theorem evalHom_eq_zero_iff {h : MvPolynomial (Fin (n + 1)) k} {c : k} (hc : c ≠ 0)
    (heq : coordEquiv k p h = Polynomial.C (C c) * (Polynomial.X - Polynomial.C r))
    (x : MvPolynomial (Fin (n + 1)) k) :
    evalHom k p r x = 0 ↔ x ∈ Ideal.span {h} := by
  have hu : IsUnit (Polynomial.C (C c : MvPolynomial (Fin n) k)) :=
    ((Ne.isUnit hc).map (C : k →+* MvPolynomial (Fin n) k)).map Polynomial.C
  rw [Ideal.mem_span_singleton, ← map_dvd_iff (coordEquiv k p), heq, hu.mul_left_dvd,
    Polynomial.dvd_iff_isRoot]
  rfl

variable {p r}

/-- The graded homomorphism `S/(h) → k[y₁, …, yₙ]` induced by `evalHom`. -/
def quotientHom {h : MvPolynomial (Fin (n + 1)) k}
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) (hr : r.IsHomogeneous 1)
    (hker : ∀ x, evalHom k p r x = 0 ↔ x ∈ Ideal.span {h}) :
    gradedQuotient (homogeneousSubmodule (Fin (n + 1)) k) (hyperplaneIdeal k n h hh) →+*ᵍ
      homogeneousSubmodule (Fin n) k where
  toRingHom := Ideal.Quotient.lift _ (evalHom k p r) fun a ha => (hker a).mpr ha
  map_mem := by
    intro i x hx
    obtain ⟨a, ha, rfl⟩ := mem_gradedQuotient_iff.mp hx
    exact evalHom_mem p r hr ha

theorem bijective_quotientHom {h : MvPolynomial (Fin (n + 1)) k}
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) (hr : r.IsHomogeneous 1)
    (hker : ∀ x, evalHom k p r x = 0 ↔ x ∈ Ideal.span {h}) (d : ℕ) :
    Function.Bijective ((quotientHom hh hr hker).gradedAddHom d) := by
  constructor
  · intro x y hxy
    exact Subtype.ext (RingHom.lift_injective_of_ker_le_ideal _ _
      (fun a ha => (hker a).mp ha) (congrArg Subtype.val hxy))
  · rintro ⟨t, ht⟩
    have ha : rename (fun i => Equiv.swap 0 p i.succ) t ∈
        homogeneousSubmodule (Fin (n + 1)) k d :=
      (mem_homogeneousSubmodule _ _).mpr
        (((mem_homogeneousSubmodule _ _).mp ht).rename_isHomogeneous)
    refine ⟨⟨_, mk_mem_gradedQuotient ha⟩, Subtype.ext ?_⟩
    exact evalHom_rename p r t

/-- The hyperplane section is isomorphic to `Proj k[y₁, …, yₙ]`. -/
theorem nonempty_iso_proj {h : MvPolynomial (Fin (n + 1)) k}
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) (h0 : h ≠ 0) :
    Nonempty (hyperplaneSection k n h hh ≅ Proj (homogeneousSubmodule (Fin n) k)) := by
  obtain ⟨p, hp⟩ := exists_degreeOf_pos hh h0
  obtain ⟨c, hc, r, hr, heq⟩ := exists_coordEquiv_eq hh hp
  have hb := bijective_quotientHom hh hr (evalHom_eq_zero_iff p r hc heq)
  have := isIso_projPartialMap_comp_top_of_bijective
    (f := quotientHom hh hr (evalHom_eq_zero_iff p r hc heq)) (d₀ := 0) fun d _ => hb d
  exact ⟨(@asIso _ _ _ _ _ this).symm⟩

end HyperplaneSection

variable {k n}

/-- **Hartshorne II, proof of Theorem 8.18, projective-space case.** For `n ≥ 1`, every
hyperplane section of `ℙⁿ_k` is isomorphic to `ℙⁿ⁻¹_k`. -/
theorem nonempty_iso_hyperplaneSection (hn : 1 ≤ n) (h : MvPolynomial (Fin (n + 1)) k)
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) (h0 : h ≠ 0) :
    Nonempty (hyperplaneSection k n h hh ≅ projectiveSpaceScheme k (n - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact HyperplaneSection.nonempty_iso_proj hh h0

/-- **Hartshorne II, proof of Theorem 8.18, projective-space case.** For `n ≥ 1`, every
hyperplane section of `ℙⁿ_k` is regular, so every member of the complete linear system
of hyperplanes is good. -/
theorem hyperplaneSection_isRegular (hn : 1 ≤ n) (h : MvPolynomial (Fin (n + 1)) k)
    (hh : h ∈ homogeneousSubmodule (Fin (n + 1)) k 1) (h0 : h ≠ 0) :
    (hyperplaneSection k n h hh).IsRegular :=
  isRegular_of_iso (nonempty_iso_hyperplaneSection hn h hh h0).some
    (projectiveSpaceScheme_isRegular k (n - 1))

end Hartshorne
