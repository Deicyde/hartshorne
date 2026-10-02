/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectiveSpaceHilbertPolynomial

/-!
# The Hilbert polynomial and degree of a hypersurface

Hartshorne, *Algebraic Geometry*, Proposition I.7.6(d) (p. 52).
-/

namespace Hartshorne

open Filter MvPolynomial Polynomial Set
open scoped Polynomial

noncomputable section

universe u

private theorem homogeneousComponent_mul_of_isHomogeneous
    {k : Type u} [Field k] {sigma : Type*}
    (a f : MvPolynomial sigma k) {d : Nat} (hf : f.IsHomogeneous d)
    (m : Nat) :
    homogeneousComponent (m + d) (a * f) = homogeneousComponent m a * f := by
  induction a using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, add_mul]
  | monomial e c =>
      rw [homogeneousComponent_of_mem
          ((isHomogeneous_monomial c rfl).mul hf),
        homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
      split_ifs with hleft hright
      · rfl
      · omega
      · omega
      · simp

private theorem isHomogeneous_of_mul_right_isHomogeneous
    {k : Type u} [Field k] {sigma : Type*}
    {a f : MvPolynomial sigma k} {d l : Nat}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    (haf : (a * f).IsHomogeneous l) :
    a.IsHomogeneous (l - d) := by
  intro e he
  let m := e.degree
  have hcomponent_ne : homogeneousComponent m a ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (MvPolynomial.coeff e) hzero
    simp only [MvPolynomial.coeff_homogeneousComponent, m,
      MvPolynomial.coeff_zero] at hcoeff
    exact he hcoeff
  have hdegree : m + d = l := by
    by_contra hne
    have hcomponent_zero : homogeneousComponent (m + d) (a * f) = 0 := by
      rw [homogeneousComponent_of_mem haf, if_neg hne]
    rw [homogeneousComponent_mul_of_isHomogeneous a f hf m] at hcomponent_zero
    exact (mul_ne_zero hcomponent_ne hf0) hcomponent_zero
  have he_degree : e.degree = l - d := by
    dsimp [m] at hdegree
    omega
  calc
    Finsupp.weight (1 : sigma → Nat) e =
        Finsupp.weight (fun _ : sigma ↦ (1 : Nat)) e := rfl
    _ = e.degree := congrArg (fun h : (sigma →₀ Nat) →+ Nat ↦ h e)
      (@Finsupp.degree_eq_weight_one sigma Nat _).symm
    _ = l - d := he_degree

private noncomputable def principalHomogeneousIdeal
    {k : Type u} [Field k] {sigma : Type*}
    (f : MvPolynomial sigma k) {d : Nat} (hf : f.IsHomogeneous d) :
    HomogeneousIdeal (integerHomogeneousSubmodule k sigma) :=
  ⟨Ideal.span ({f} : Set (MvPolynomial sigma k)),
    (ideal_isHomogeneous_integer_iff k sigma _).2
      (Ideal.homogeneous_span _ _ fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        subst g
        exact isHomogeneousElem_iff.mpr ⟨d, hf⟩)⟩

private def hypersurfaceMulDegree
    {k : Type u} [Field k] {sigma : Type*}
    (f : MvPolynomial sigma k) {d l : Nat} (hdl : d <= l)
    (hf : f.IsHomogeneous d) :
    ↑(gradedModuleTwist (integerHomogeneousSubmodule k sigma)
      (-(d : Int)) (l : Int)) →ₗ[k]
      integerHomogeneousSubmodule k sigma (l : Int) where
  toFun a := ⟨a * f, by
    have ha : (a : MvPolynomial sigma k).IsHomogeneous (l - d) := by
      have hindex : (l : Int) + -(d : Int) = ((l - d : Nat) : Int) := by omega
      have ha' : (a : MvPolynomial sigma k) ∈
          integerHomogeneousSubmodule k sigma ((l : Int) + -(d : Int)) := a.property
      rw [hindex] at ha'
      exact ha'
    have haf := ha.mul hf
    simpa [Nat.sub_add_cancel hdl] using haf⟩
  map_add' a b := by
    apply Subtype.ext
    change ((a : MvPolynomial sigma k) + b) * f = a * f + b * f
    exact add_mul _ _ _
  map_smul' r a := by
    apply Subtype.ext
    change (r • (a : MvPolynomial sigma k)) * f = r • ((a : MvPolynomial sigma k) * f)
    simp

private def hypersurfaceQuotientDegree
    {k : Type u} [Field k] {sigma : Type*}
    (f : MvPolynomial sigma k) {d l : Nat} (hf : f.IsHomogeneous d) :
    integerHomogeneousSubmodule k sigma (l : Int) →ₗ[k]
      quotGrading (integerHomogeneousSubmodule k sigma)
        (principalHomogeneousIdeal f hf) (l : Int) where
  toFun a := ⟨Ideal.Quotient.mk (Ideal.span ({f} : Set (MvPolynomial sigma k))) a,
    ⟨a, a.property, rfl⟩⟩
  map_add' a b := by
    apply Subtype.ext
    change Ideal.Quotient.mk _ ((a : MvPolynomial sigma k) + b) = _
    exact map_add (Ideal.Quotient.mkₐ k _)
      (a : MvPolynomial sigma k) (b : MvPolynomial sigma k)
  map_smul' r a := by
    apply Subtype.ext
    change Ideal.Quotient.mk _ (r • (a : MvPolynomial sigma k)) = _
    exact Submodule.Quotient.mk_smul _ r (a : MvPolynomial sigma k)

private theorem hypersurface_degreewise_exact
    {k : Type u} [Field k] {sigma : Type*}
    (f : MvPolynomial sigma k) {d l : Nat} (hdl : d <= l)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) :
    Function.Injective (hypersurfaceMulDegree f hdl hf) /\
      LinearMap.range (hypersurfaceMulDegree f hdl hf) =
        LinearMap.ker (hypersurfaceQuotientDegree (l := l) f hf) /\
      Function.Surjective (hypersurfaceQuotientDegree (l := l) f hf) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply mul_right_cancel₀ hf0
    exact congrArg Subtype.val hab
  · ext p
    constructor
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      change Ideal.Quotient.mk (Ideal.span ({f} : Set (MvPolynomial sigma k)))
        ((a : MvPolynomial sigma k) * f) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_span_singleton.2
          ⟨(a : MvPolynomial sigma k), mul_comm (a : MvPolynomial sigma k) f⟩)
    · intro hp
      have hp0 := congrArg Subtype.val hp
      change Ideal.Quotient.mk (Ideal.span ({f} : Set (MvPolynomial sigma k)))
        (p : MvPolynomial sigma k) = 0 at hp0
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.1 hp0)
      have hpf : (p : MvPolynomial sigma k).IsHomogeneous l := by
        simpa using p.property
      have haHom : a.IsHomogeneous (l - d) := by
        apply isHomogeneous_of_mul_right_isHomogeneous hf hf0
        rw [mul_comm, ← ha]
        exact hpf
      let a' : ↑(gradedModuleTwist (integerHomogeneousSubmodule k sigma)
          (-(d : Int)) (l : Int)) := ⟨a, by
        have hindex : (l : Int) + -(d : Int) = ((l - d : Nat) : Int) := by omega
        change a ∈ integerHomogeneousSubmodule k sigma
          ((l : Int) + -(d : Int))
        rw [hindex]
        exact haHom⟩
      refine ⟨a', ?_⟩
      apply Subtype.ext
      change a * f = (p : MvPolynomial sigma k)
      rw [mul_comm, ← ha]
  · intro q
    obtain ⟨a, ha, haq⟩ := q.property
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact haq

private theorem projZeroSet_singleton_nonempty_of_irreducible
    {k : Type u} [Field k] [IsAlgClosed k] {n d : Nat}
    (hn : 0 < n) (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f) :
    (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
  classical
  let I : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span {f}
  have hIhom : IsHomogeneousIdeal I :=
    Ideal.homogeneous_span _ _ fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      subst g
      exact isHomogeneousElem_iff.mpr ⟨d, hf⟩
  have hIprime : I.IsPrime :=
    (Ideal.span_singleton_prime hfirr.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hfirr)
  by_contra hne
  have hempty : projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k)) = ∅ := by
    rw [show I = Ideal.span ({f} : Set _) from rfl, projZeroSet_span]
    exact Set.not_nonempty_iff_eq_empty.mp hne
  have hirrle : irrelevantIdeal k (Fin (n + 1)) ≤ I := by
    have h := (projZeroSet_eq_empty_iff hIhom).1 hempty
    simpa only [hIprime.radical] using h
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  have hi : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0, i1] at hv
  have hX0 := hirrle (X_mem_irrelevantIdeal (k := k) i0)
  have hX1 := hirrle (X_mem_irrelevantIdeal (k := k) i1)
  have hdvd0 : f ∣ X i0 := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hX0
    exact ⟨a, by simpa [mul_comm] using ha⟩
  have hdvd1 : f ∣ X i1 := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hX1
    exact ⟨a, by simpa [mul_comm] using ha⟩
  have ha0 : Associated f (X i0) :=
    hfirr.associated_of_dvd (X_prime (R := k) (i := i0)).irreducible hdvd0
  have ha1 : Associated f (X i1) :=
    hfirr.associated_of_dvd (X_prime (R := k) (i := i1)).irreducible hdvd1
  obtain ⟨g, hg⟩ := (ha0.symm.trans ha1).dvd
  let v : Fin (n + 1) → k := fun j ↦ if j = i1 then 1 else 0
  have heval := congrArg (MvPolynomial.eval v) hg
  simp [v, hi] at heval

private theorem finrank_homogeneousSubmodule_hypersurface
    {k : Type u} [Field k] (n l : Nat) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k l) =
      (l + n).choose n := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank k
      (MvPolynomial.restrictSupport k
        {e : Fin (n + 1) →₀ Nat | e.degree = l}) = _
  rw [Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport k
      {e : Fin (n + 1) →₀ Nat | e.degree = l})]
  change Nat.card {e : Fin (n + 1) →₀ Nat // e.degree = l} = _
  calc
    Nat.card {e : Fin (n + 1) →₀ Nat // e.degree = l} =
        Nat.card (Sym (Fin (n + 1)) l) :=
      Nat.card_congr (Sym.equivNatSum (Fin (n + 1)) l).symm
    _ = Fintype.card (Sym (Fin (n + 1)) l) := Nat.card_eq_fintype_card
    _ = ((n + 1) + l - 1).choose l := by
      simpa using Sym.card_sym_eq_choose (α := Fin (n + 1)) l
    _ = (l + n).choose n := by
      have h : (n + 1) + l - 1 = l + n := by omega
      rw [h]
      exact Nat.choose_symm_add

private theorem hilbertFunction_hypersurface
    {k : Type u} [Field k] [IsAlgClosed k] {n d l : Nat}
    (hn : 0 < n) (hdl : d ≤ l)
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f) :
    hilbertFunction (k := k) (σ := Fin (n + 1))
        (integerHomogeneousSubmodule k (Fin (n + 1))) (l : Int) =
      hilbertFunction (k := k) (σ := Fin (n + 1))
          (integerHomogeneousSubmodule k (Fin (n + 1))) ((l - d : Nat) : Int) +
        hilbertFunction (k := k) (σ := Fin (n + 1))
          (integerProjCoordGrading
            (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k)))) (l : Int) := by
  let I : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span {f}
  have hIhom : IsHomogeneousIdeal I :=
    Ideal.homogeneous_span _ _ fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      subst g
      exact isHomogeneousElem_iff.mpr ⟨d, hf⟩
  have hIprime : I.IsPrime :=
    (Ideal.span_singleton_prime hfirr.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hfirr)
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  have hZI : projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k)) = H := by
    exact projZeroSet_span _
  have hIne : (projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
    rw [hZI]
    exact projZeroSet_singleton_nonempty_of_irreducible hn f hf hfirr
  have hJ : homogeneousVanishingIdeal H = I := by
    rw [← hZI, homogeneousVanishingIdeal_projZeroSet hIhom hIne,
      hIprime.radical]
  have hHI : integerProjVanishingIdeal H = principalHomogeneousIdeal f hf := by
    apply HomogeneousIdeal.ext
    exact hJ
  obtain ⟨hinj, hexact, hsurj⟩ :=
    hypersurface_degreewise_exact f hdl hf hfirr.ne_zero
  let _ : Module.Finite k
      ↑(gradedModuleTwist (integerHomogeneousSubmodule k (Fin (n + 1)))
        (-(d : Int)) (l : Int)) :=
    finite_gradedPiece (k := k) (σ := Fin (n + 1))
      (integerHomogeneousSubmodule k (Fin (n + 1))) ((l : Int) + -(d : Int))
  let _ : Module.Finite k
      (integerHomogeneousSubmodule k (Fin (n + 1)) (l : Int)) :=
    finite_gradedPiece (k := k) (σ := Fin (n + 1))
      (integerHomogeneousSubmodule k (Fin (n + 1))) (l : Int)
  let _ : Module.Finite k
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1)))
        (principalHomogeneousIdeal f hf) (l : Int)) :=
    Module.Finite.of_surjective (hypersurfaceQuotientDegree (l := l) f hf) hsurj
  have hadd := finrank_middle_eq_add_of_exact
    (hypersurfaceMulDegree f hdl hf)
    (hypersurfaceQuotientDegree (l := l) f hf) hinj hexact hsurj
  have hindex : (l : Int) + -(d : Int) = ((l - d : Nat) : Int) := by omega
  change Module.finrank k (integerHomogeneousSubmodule k (Fin (n + 1)) (l : Int)) =
    Module.finrank k
        (integerHomogeneousSubmodule k (Fin (n + 1)) ((l : Int) + -(d : Int))) +
      Module.finrank k
        (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1)))
          (principalHomogeneousIdeal f hf) (l : Int)) at hadd
  rw [hindex] at hadd
  change Module.finrank k (integerHomogeneousSubmodule k (Fin (n + 1)) (l : Int)) =
    Module.finrank k
        (integerHomogeneousSubmodule k (Fin (n + 1)) ((l - d : Nat) : Int)) +
      Module.finrank k
        (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1)))
          (integerProjVanishingIdeal H) (l : Int))
  rw [hHI]
  exact hadd

private theorem projectiveHilbertPolynomial_hypersurface
    {k : Type u} [Field k] [IsAlgClosed k] {n d : Nat}
    (hn : 0 < n)
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f) :
    projectiveHilbertPolynomial
        (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))) =
      projectiveHilbertPolynomial
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) -
        (projectiveHilbertPolynomial
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1))))).taylor (-(d : ℚ)) := by
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  let PS := projectiveHilbertPolynomial
    (Set.univ : Set (ProjectiveSpace k (Fin (n + 1))))
  let PH := projectiveHilbertPolynomial H
  have hPS := projectiveHilbertPolynomial_isHilbertPolynomial
    (Set.univ : Set (ProjectiveSpace k (Fin (n + 1))))
  have hPH := projectiveHilbertPolynomial_isHilbertPolynomial H
  have hnum : IsNumericalPolynomial (PS - PS.taylor (-(d : ℚ))) := by
    rw [IsNumericalPolynomial]
    exact Filter.Eventually.of_forall fun z => by
      obtain ⟨a, ha⟩ := hPS.1.integerValued z
      obtain ⟨b, hb⟩ := hPS.1.integerValued (z - d)
      change PS.eval (z : ℚ) = (a : ℚ) at ha
      change PS.eval ((z - d : Int) : ℚ) = (b : ℚ) at hb
      refine ⟨a - b, ?_⟩
      simp only [Polynomial.eval_sub, Polynomial.taylor_eval]
      push_cast at hb ⊢
      rw [ha]
      simpa only [sub_eq_add_neg] using congrArg (fun q : ℚ ↦ (a : ℚ) - q) hb
  have hPSshift : ∀ᶠ z : Int in Filter.atTop,
      PS.eval ((z - d : Int) : ℚ) =
        (hilbertFunction (σ := Fin (n + 1))
          (integerProjCoordGrading
            (Set.univ : Set (ProjectiveSpace k (Fin (n + 1))))) (z - d) : ℚ) := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hPS.2
    exact Filter.eventually_atTop.mpr ⟨N + d, fun z hz => hN (z - d) (by omega)⟩
  have hevent : ∀ᶠ z : Int in Filter.atTop,
      (PS - PS.taylor (-(d : ℚ))).eval (z : ℚ) =
        (hilbertFunction (σ := Fin (n + 1)) (integerProjCoordGrading H) z : ℚ) := by
    filter_upwards [hPS.2, hPSshift, hPH.2,
      Filter.eventually_ge_atTop (d : Int)] with z hzPS hzPSshift hzPH hzd
    obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le (le_trans (Int.natCast_nonneg d) hzd)
    have hdl : d ≤ l := by exact_mod_cast hzd
    have hfun := hilbertFunction_hypersurface hn hdl f hf hfirr
    have hraw_l : hilbertFunction (k := k) (σ := Fin (n + 1))
        (integerHomogeneousSubmodule k (Fin (n + 1))) (l : Int) =
        (l + n).choose n := by
      rw [hilbertFunction, integerHomogeneousSubmodule_ofNat,
        finrank_homogeneousSubmodule_hypersurface]
    have hraw_ld : hilbertFunction (k := k) (σ := Fin (n + 1))
        (integerHomogeneousSubmodule k (Fin (n + 1))) ((l - d : Nat) : Int) =
        (l - d + n).choose n := by
      rw [hilbertFunction, integerHomogeneousSubmodule_ofNat,
        finrank_homogeneousSubmodule_hypersurface]
    have hspace_l :=
      (projectiveSpace_hilbertPolynomial_and_degree (k := k) n).1 l
    have hspace_ld :=
      (projectiveSpace_hilbertPolynomial_and_degree (k := k) n).1 (l - d)
    simp only [Polynomial.eval_sub, Polynomial.taylor_eval]
    have hindex : (l : Int) - (d : Int) = ((l - d : Nat) : Int) := by omega
    have hqindex : (((l : Int) : ℚ) + -(d : ℚ)) =
        (((l - d : Nat) : Int) : ℚ) := by
      calc
        ((l : Int) : ℚ) + -(d : ℚ) = (((l : Int) - (d : Int)) : ℚ) := by
          push_cast
          ring
        _ = (((l - d : Nat) : Int) : ℚ) :=
          by simpa only [Int.cast_sub, Int.cast_natCast] using
            congrArg (fun z : Int ↦ (z : ℚ)) hindex
    rw [hindex] at hzPSshift
    rw [hraw_l, hraw_ld] at hfun
    rw [hzPS, hqindex, hzPSshift, hspace_l, hspace_ld]
    have hfunQ := congrArg (fun m : Nat ↦ (m : ℚ)) hfun
    push_cast at hfunQ ⊢
    linarith
  exact isHilbertPolynomial_unique (integerProjCoordGrading H) hPH ⟨hnum, hevent⟩

private theorem translatedNumericalBinomial_sub_shift_one (r : Nat) :
    (numericalBinomial (r + 1)).taylor ((r + 1 : Nat) : ℚ) -
        ((numericalBinomial (r + 1)).taylor ((r + 1 : Nat) : ℚ)).taylor (-1) =
      (numericalBinomial r).taylor (r : ℚ) := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_sub, Polynomial.taylor_eval]
  have h := congrArg (fun P : ℚ[X] ↦ P.eval (x + r))
    (polynomialForwardDifference_numericalBinomial_succ r)
  simp only [polynomialForwardDifference_eval] at h
  push_cast at h ⊢
  convert h using 1
  all_goals ring

private theorem projectiveSpace_difference_degree_leadingCoeff
    (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    let P := (numericalBinomial n).taylor (n : ℚ)
    (P - P.taylor (-(d : ℚ))).natDegree = n - 1 ∧
      (P - P.taylor (-(d : ℚ))).leadingCoeff =
        (d : ℚ) * ((n - 1).factorial : ℚ)⁻¹ := by
  let P := (numericalBinomial n).taylor (n : ℚ)
  let D : Nat → ℚ[X] := fun e ↦ P - P.taylor (-(e : ℚ))
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hD1 : D 1 = (numericalBinomial r).taylor (r : ℚ) := by
    simpa [D, P] using translatedNumericalBinomial_sub_shift_one r
  have hD1deg : (D 1).natDegree = r := by
    rw [hD1, Polynomial.natDegree_taylor, numericalBinomial_natDegree]
  have hD1lc : (D 1).leadingCoeff = (r.factorial : ℚ)⁻¹ := by
    rw [hD1, Polynomial.leadingCoeff_taylor, numericalBinomial_leadingCoeff]
  have hrec (e : Nat) : D (e + 1) = D e + (D 1).taylor (-(e : ℚ)) := by
    apply Polynomial.funext
    intro x
    simp only [D, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.taylor_eval]
    push_cast
    ring
  have hmain : ∀ e : Nat, 0 < e →
      (D e).natDegree = r ∧
        (D e).leadingCoeff = (e : ℚ) * (r.factorial : ℚ)⁻¹ := by
    intro e he
    induction e with
    | zero => omega
    | succ e ih =>
        by_cases he0 : e = 0
        · subst e
          simpa using And.intro hD1deg hD1lc
        · have ihe := ih (Nat.pos_of_ne_zero he0)
          have hAdeg : (D e).natDegree = r := ihe.1
          have hAlc : (D e).leadingCoeff =
              (e : ℚ) * (r.factorial : ℚ)⁻¹ := ihe.2
          let B := (D 1).taylor (-(e : ℚ))
          have hBdeg : B.natDegree = r := by
            change ((D 1).taylor (-(e : ℚ))).natDegree = r
            rw [Polynomial.natDegree_taylor, hD1deg]
          have hBlc : B.leadingCoeff = (r.factorial : ℚ)⁻¹ := by
            change ((D 1).taylor (-(e : ℚ))).leadingCoeff = _
            rw [Polynomial.leadingCoeff_taylor, hD1lc]
          have hcA : (D e).coeff r =
              (e : ℚ) * (r.factorial : ℚ)⁻¹ := by
            calc
              (D e).coeff r = (D e).coeff (D e).natDegree := by rw [hAdeg]
              _ = (D e).leadingCoeff := Polynomial.coeff_natDegree
              _ = _ := hAlc
          have hcB : B.coeff r = (r.factorial : ℚ)⁻¹ := by
            calc
              B.coeff r = B.coeff B.natDegree := by rw [hBdeg]
              _ = B.leadingCoeff := Polynomial.coeff_natDegree
              _ = _ := hBlc
          have hcoeff : (D e + B).coeff r =
              ((e + 1 : Nat) : ℚ) * (r.factorial : ℚ)⁻¹ := by
            rw [Polynomial.coeff_add, hcA, hcB]
            push_cast
            ring
          have hcoeff0 : (D e + B).coeff r ≠ 0 := by
            rw [hcoeff]
            positivity
          have hdeg : (D e + B).natDegree = r := by
            apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ hcoeff0
            exact (Polynomial.natDegree_add_le _ _).trans (by simp [hAdeg, hBdeg])
          have hrec' : D (e + 1) = D e + B := by
            simpa [B] using hrec e
          rw [hrec']
          refine ⟨hdeg, ?_⟩
          rw [Polynomial.leadingCoeff, hdeg, hcoeff]
  simpa [D, P] using hmain d hd

/-- **Hartshorne I.7.6(d).** Let `f` be an irreducible homogeneous polynomial
of positive degree `d` in the homogeneous coordinate ring of `P^n`, with
`n > 0`, and let `H = Z(f)`.  Multiplication by `f` gives the graded exact
sequence `0 → S(-d) → S → S/(f) → 0`; consequently the Hilbert
polynomial of `H` is the indicated difference and the projective degree of
`H` is `d`. -/
theorem hypersurface_hilbertPolynomial_and_degree
    {k : Type u} [Field k] [IsAlgClosed k] {n d : Nat}
    (hn : 0 < n) (hd : 0 < d)
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f) :
    projectiveHilbertPolynomial
        (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))) =
      projectiveHilbertPolynomial
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) -
        (projectiveHilbertPolynomial
          (Set.univ : Set (ProjectiveSpace k (Fin (n + 1))))).taylor (-(d : ℚ)) ∧
      projectiveDegree
        (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))) = (d : ℚ) := by
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  let PS := projectiveHilbertPolynomial
    (Set.univ : Set (ProjectiveSpace k (Fin (n + 1))))
  have hpoly := projectiveHilbertPolynomial_hypersurface hn f hf hfirr
  have hspace : PS = (numericalBinomial n).taylor (n : ℚ) :=
    (projectiveSpace_hilbertPolynomial_and_degree (k := k) n).2.1
  have hdata := projectiveSpace_difference_degree_leadingCoeff n d hn hd
  refine ⟨hpoly, ?_⟩
  change projectiveDegree H = (d : ℚ)
  rw [projectiveDegree, hpoly]
  change (PS - PS.taylor (-(d : ℚ))).natDegree.factorial *
      (PS - PS.taylor (-(d : ℚ))).leadingCoeff = (d : ℚ)
  rw [hspace, hdata.1, hdata.2]
  have hfac : (((n - 1).factorial : Nat) : ℚ) ≠ 0 := by positivity
  field_simp

end

end Hartshorne
