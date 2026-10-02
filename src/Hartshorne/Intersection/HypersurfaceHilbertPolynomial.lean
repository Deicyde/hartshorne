/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Intersection.ProjectiveSpaceHilbertPolynomial
import Hartshorne.Projective.PointIdeal

/-!
# Hilbert polynomials of hypersurfaces and hypersurface sections

Hartshorne, *Algebraic Geometry*, Proposition I.7.6(d) (p. 52) and the
hypersurface-section calculation in the proof of Theorem I.7.7 (p. 53).
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

private theorem integerProjVanishingIdeal_le_sup_left
    {k : Type u} [Field k] {n : Nat}
    (Y H : Set (ProjectiveSpace k (Fin (n + 1)))) :
    (integerProjVanishingIdeal Y).toIdeal ≤
      (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H).toIdeal := by
  rw [HomogeneousIdeal.toIdeal_sup]
  exact le_sup_left

/-- The ambient polynomial-ring action respects the quotient grading on the
nonreduced projective intersection module `S/(J(Y) + J(H))`. -/
instance integerProjectiveIntersectionGradingGradedSMul
    {k : Type u} [Field k] {n : Nat}
    (Y H : Set (ProjectiveSpace k (Fin (n + 1)))) :
    SetLike.GradedSMul (integerHomogeneousSubmodule k (Fin (n + 1)))
      (quotGrading (integerHomogeneousSubmodule k (Fin (n + 1)))
        (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H)) where
  smul_mem {i j a q} ha hq := by
    obtain ⟨b, hb, rfl⟩ := hq
    refine ⟨a * b, SetLike.mul_mem_graded ha hb, ?_⟩
    change Ideal.Quotient.mk
        (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H).toIdeal
        (a * b) =
      a • Ideal.Quotient.mk
        (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H).toIdeal b
    exact Submodule.Quotient.mk_smul
      (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H).toIdeal a b

/-- Multiplication by a homogeneous degree-`d` equation on every integer
graded piece of `S(Y)(-d)`. -/
noncomputable def hypersurfaceSectionMulDegreeInt
    {k : Type u} [Field k] {n d : Nat}
    (Y : Set (ProjectiveSpace k (Fin (n + 1))))
    (f : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
    (l : Int) :
    ↑(gradedModuleTwist (integerProjCoordGrading Y) (-(d : Int)) l) →ₗ[k]
      integerProjCoordGrading Y l where
  toFun a := ⟨f • a.1, by
    have hf' : f ∈ integerHomogeneousSubmodule k (Fin (n + 1)) (d : Int) := by
      simpa using hf
    have hmem := SetLike.GradedSMul.smul_mem
      (A := integerHomogeneousSubmodule k (Fin (n + 1)))
      (B := integerProjCoordGrading Y) hf' a.property
    simpa [add_assoc, add_comm, add_left_comm] using hmem⟩
  map_add' a b := by
    apply Subtype.ext
    exact smul_add f a.1 b.1
  map_smul' r a := by
    apply Subtype.ext
    exact smul_comm f r a.1

private theorem homogeneousComponent_mul_eq_zero_of_lt
    {k : Type u} [Field k] {sigma : Type*}
    (a f : MvPolynomial sigma k) {d l : Nat}
    (hf : f.IsHomogeneous d) (hld : l < d) :
    homogeneousComponent l (a * f) = 0 := by
  induction a using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, add_zero]
  | monomial e c =>
      rw [homogeneousComponent_of_mem
        ((isHomogeneous_monomial c rfl).mul hf)]
      split_ifs with h
      · omega
      · rfl

/-- Multiplication by a homogeneous hypersurface equation, restricted from
the degree-`l` piece of `S(Y)(-d)` to the degree-`l` piece of `S(Y)`. -/
noncomputable def hypersurfaceSectionMulDegree
    {k : Type u} [Field k] {n d l : Nat}
    (Y : Set (ProjectiveSpace k (Fin (n + 1))))
    (f : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
    (hdl : d ≤ l) :
    ↑(gradedModuleTwist (integerProjCoordGrading Y)
        (-(d : Int)) (l : Int)) →ₗ[k]
      integerProjCoordGrading Y (l : Int) where
  toFun a := ⟨a.1 * Ideal.Quotient.mk (homogeneousVanishingIdeal Y) f, by
    obtain ⟨g, hg, hga⟩ := a.property
    have hgHom : g.IsHomogeneous (l - d) := by
      have hindex : (l : Int) + -(d : Int) = ((l - d : Nat) : Int) := by omega
      have hg' : g ∈ integerHomogeneousSubmodule k (Fin (n + 1))
          ((l - d : Nat) : Int) := by
        rw [← hindex]
        exact hg
      simpa using hg'
    refine ⟨g * f, by simpa [Nat.sub_add_cancel hdl] using hgHom.mul hf, ?_⟩
    change Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (g * f) =
      a.1 * Ideal.Quotient.mk (homogeneousVanishingIdeal Y) f
    change Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g = a.1 at hga
    rw [← hga]
    rfl⟩
  map_add' a b := by
    apply Subtype.ext
    exact add_mul a.1 b.1 (Ideal.Quotient.mk _ f)
  map_smul' r a := by
    apply Subtype.ext
    exact smul_mul_assoc r a.1 (Ideal.Quotient.mk _ f)

/-- The quotient map from the degree-`l` piece of `S(Y)` to the corresponding
piece of the nonreduced intersection module `S/(J(Y) + J(H))`. -/
noncomputable def hypersurfaceSectionQuotientDegree
    {k : Type u} [Field k] {n : Nat}
    (Y H : Set (ProjectiveSpace k (Fin (n + 1)))) (l : Int) :
    integerProjCoordGrading Y l →ₗ[k]
      quotGrading (integerHomogeneousSubmodule k (Fin (n + 1)))
        (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H) l where
  toFun a := ⟨Ideal.Quotient.factor
      (integerProjVanishingIdeal_le_sup_left Y H) a.1, by
    obtain ⟨g, hg, hga⟩ := a.property
    refine ⟨g, hg, ?_⟩
    change Ideal.Quotient.mk
        (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H).toIdeal g =
      Ideal.Quotient.factor (integerProjVanishingIdeal_le_sup_left Y H) a.1
    rw [← hga]
    rfl⟩
  map_add' a b := by
    apply Subtype.ext
    exact map_add
      (Ideal.Quotient.factorₐ k (integerProjVanishingIdeal_le_sup_left Y H)) a.1 b.1
  map_smul' r a := by
    apply Subtype.ext
    exact map_smul
      (Ideal.Quotient.factorₐ k (integerProjVanishingIdeal_le_sup_left Y H)) r a.1

private theorem homogeneousVanishingIdeal_hypersurface
    {k : Type u} [Field k] [IsAlgClosed k] {n d : Nat}
    (hn : 0 < n) (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f) :
    homogeneousVanishingIdeal
        (projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))) =
      Ideal.span ({f} : Set (MvPolynomial (Fin (n + 1)) k)) := by
  let I : Ideal (MvPolynomial (Fin (n + 1)) k) := Ideal.span {f}
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  have hIhom : IsHomogeneousIdeal I :=
    Ideal.homogeneous_span _ _ fun g hg => by
      rw [Set.mem_singleton_iff] at hg
      subst g
      exact isHomogeneousElem_iff.mpr ⟨d, hf⟩
  have hIprime : I.IsPrime :=
    (Ideal.span_singleton_prime hfirr.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hfirr)
  have hZI : projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k)) = H :=
    projZeroSet_span _
  have hIne : (projZeroSet (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty := by
    rw [hZI]
    exact projZeroSet_singleton_nonempty_of_irreducible hn f hf hfirr
  change homogeneousVanishingIdeal H = I
  rw [← hZI, homogeneousVanishingIdeal_projZeroSet hIhom hIne,
    hIprime.radical]

/-- If `H = Z(f)` does not contain the projective variety `Y`, multiplication
by `f` followed by the quotient to `S/(J(Y) + J(H))` is short exact in every
degree at least `d`.  The quotient is the nonreduced intersection module used
by Hartshorne's intersection multiplicities. -/
theorem hypersurfaceSection_degreewise_exact
    {k : Type u} [Field k] [IsAlgClosed k] {n d l : Nat}
    (hn : 0 < n)
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) (hY : IsProjVariety Y)
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f)
    (hproper : ¬Y ⊆ projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k)))
    (hdl : d ≤ l) :
    let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
    Function.Injective (hypersurfaceSectionMulDegree Y f hf hdl) ∧
      LinearMap.range (hypersurfaceSectionMulDegree Y f hf hdl) =
        LinearMap.ker (hypersurfaceSectionQuotientDegree Y H (l : Int)) ∧
      Function.Surjective
        (hypersurfaceSectionQuotientDegree Y H (l : Int)) := by
  classical
  dsimp only
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  let JY := homogeneousVanishingIdeal Y
  have hJH : homogeneousVanishingIdeal H = Ideal.span ({f} : Set _) :=
    homogeneousVanishingIdeal_hypersurface hn f hf hfirr
  let _ : IsDomain (homogeneousCoordinateRing Y) :=
    isDomain_homogeneousCoordinateRing hY
  have hfquot : Ideal.Quotient.mk JY f ≠ 0 := by
    intro hzero
    have hfJ : f ∈ JY := Ideal.Quotient.eq_zero_iff_mem.1 hzero
    apply hproper
    intro P hPY g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact homogeneousVanish_of_mem_homogeneousVanishingIdeal hfJ hPY
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    apply mul_right_cancel₀ hfquot
    exact congrArg Subtype.val hab
  · ext x
    constructor
    · rintro ⟨a, rfl⟩
      apply Subtype.ext
      obtain ⟨g, hg, hga⟩ := a.property
      change Ideal.Quotient.factor
          (integerProjVanishingIdeal_le_sup_left Y H)
          ((hypersurfaceSectionMulDegree Y f hf hdl a).1) = 0
      have haeq : (hypersurfaceSectionMulDegree Y f hf hdl a).1 =
          Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (g * f) := by
        change a.1 * Ideal.Quotient.mk (homogeneousVanishingIdeal Y) f = _
        rw [← hga]
        rfl
      rw [haeq]
      change Ideal.Quotient.mk
          (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H).toIdeal
          (g * f) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.2
      change g * f ∈ homogeneousVanishingIdeal Y ⊔ homogeneousVanishingIdeal H
      rw [hJH]
      exact (le_sup_right : Ideal.span ({f} : Set _) ≤
        homogeneousVanishingIdeal Y ⊔ Ideal.span ({f} : Set _))
          (Ideal.mem_span_singleton.2 ⟨g, mul_comm g f⟩)
    · intro hx
      obtain ⟨p, hp, hpx⟩ := x.property
      have hxzero := congrArg Subtype.val hx
      change Ideal.Quotient.factor
          (integerProjVanishingIdeal_le_sup_left Y H) x.1 = 0 at hxzero
      rw [← hpx] at hxzero
      have hpSum : p ∈ homogeneousVanishingIdeal Y ⊔ homogeneousVanishingIdeal H := by
        apply Ideal.Quotient.eq_zero_iff_mem.1
        exact hxzero
      rw [hJH] at hpSum
      obtain ⟨j, hj, q, hq, hjq⟩ := Submodule.mem_sup.1 hpSum
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hq
      have hpaJ : p - a * f ∈ homogeneousVanishingIdeal Y := by
        rw [mul_comm a f, ← ha, ← hjq]
        simpa using hj
      have hpHom : p.IsHomogeneous l := by
        simpa using hp
      let a' := homogeneousComponent (l - d) a
      have ha'Hom : a'.IsHomogeneous (l - d) :=
        homogeneousComponent_mem (l - d) a
      have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem
        (isHomogeneousIdeal_homogeneousVanishingIdeal Y) hpaJ l
      have hcompEq : homogeneousComponent l (p - a * f) = p - a' * f := by
        rw [map_sub, homogeneousComponent_of_mem hpHom, if_pos rfl]
        have hmul : homogeneousComponent l (a * f) = a' * f := by
          change homogeneousComponent l (a * f) =
            homogeneousComponent (l - d) a * f
          simpa [Nat.sub_add_cancel hdl] using
            homogeneousComponent_mul_of_isHomogeneous a f hf (l - d)
        rw [hmul]
      have hpa'J : p - a' * f ∈ homogeneousVanishingIdeal Y := by
        rw [← hcompEq]
        exact hcomp
      have hindex : (l : Int) + -(d : Int) = ((l - d : Nat) : Int) := by omega
      let a'' : ↑(gradedModuleTwist (integerProjCoordGrading Y)
          (-(d : Int)) (l : Int)) :=
        ⟨Ideal.Quotient.mk (homogeneousVanishingIdeal Y) a', by
          refine ⟨a', ?_, rfl⟩
          rw [hindex, integerHomogeneousSubmodule_ofNat]
          exact ha'Hom⟩
      refine ⟨a'', ?_⟩
      apply Subtype.ext
      rw [← hpx]
      apply Ideal.Quotient.eq.2
      simpa only [neg_sub] using
        (homogeneousVanishingIdeal Y).neg_mem hpa'J
  · intro q
    obtain ⟨p, hp, hpq⟩ := q.property
    let x : integerProjCoordGrading Y (l : Int) :=
      ⟨Ideal.Quotient.mk (homogeneousVanishingIdeal Y) p, ⟨p, hp, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [← hpq]
    rfl

private theorem hypersurfaceSectionMulDegreeInt_ofNat
    {k : Type u} [Field k] {n d l : Nat}
    (Y : Set (ProjectiveSpace k (Fin (n + 1))))
    (f : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
    (hdl : d ≤ l) :
    hypersurfaceSectionMulDegreeInt Y f hf (l : Int) =
      hypersurfaceSectionMulDegree Y f hf hdl := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change f • a.1 = a.1 * Ideal.Quotient.mk (homogeneousVanishingIdeal Y) f
  change Ideal.Quotient.mk (homogeneousVanishingIdeal Y) f * a.1 = _
  rw [mul_comm]

/-- The multiplication/quotient sequence for a proper hypersurface section
is exact in every integer degree.  This is the degreewise content of the
graded short exact sequence
`0 → S(Y)(-d) → S(Y) → S/(J(Y)+J(H)) → 0`. -/
theorem hypersurfaceSection_degreewise_exact_int
    {k : Type u} [Field k] [IsAlgClosed k] {n d : Nat}
    (hn : 0 < n)
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) (hY : IsProjVariety Y)
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f)
    (hproper : ¬Y ⊆ projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k)))
    (l : Int) :
    let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
    Function.Injective (hypersurfaceSectionMulDegreeInt Y f hf l) ∧
      LinearMap.range (hypersurfaceSectionMulDegreeInt Y f hf l) =
        LinearMap.ker (hypersurfaceSectionQuotientDegree Y H l) ∧
      Function.Surjective (hypersurfaceSectionQuotientDegree Y H l) := by
  classical
  dsimp only
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  let JY := homogeneousVanishingIdeal Y
  have hJH : homogeneousVanishingIdeal H = Ideal.span ({f} : Set _) :=
    homogeneousVanishingIdeal_hypersurface hn f hf hfirr
  let _ : IsDomain (homogeneousCoordinateRing Y) :=
    isDomain_homogeneousCoordinateRing hY
  have hfquot : Ideal.Quotient.mk JY f ≠ 0 := by
    intro hzero
    have hfJ : f ∈ JY := Ideal.Quotient.eq_zero_iff_mem.1 hzero
    apply hproper
    intro P hPY g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    exact homogeneousVanish_of_mem_homogeneousVanishingIdeal hfJ hPY
  have hinj : Function.Injective
      (hypersurfaceSectionMulDegreeInt Y f hf l) := by
    intro a b hab
    apply Subtype.ext
    apply mul_left_cancel₀ hfquot
    have hab' := congrArg Subtype.val hab
    change f • a.1 = f • b.1 at hab'
    exact hab'
  have hsurj : Function.Surjective
      (hypersurfaceSectionQuotientDegree Y H l) := by
    intro q
    obtain ⟨p, hp, hpq⟩ := q.property
    let x : integerProjCoordGrading Y l :=
      ⟨Ideal.Quotient.mk (homogeneousVanishingIdeal Y) p, ⟨p, hp, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    rw [← hpq]
    rfl
  cases l with
  | ofNat l =>
      by_cases hdl : d ≤ l
      · have htail := hypersurfaceSection_degreewise_exact
          hn Y hY f hf hfirr hproper hdl
        rw [← hypersurfaceSectionMulDegreeInt_ofNat Y f hf hdl] at htail
        exact htail
      · refine ⟨hinj, ?_, hsurj⟩
        ext x
        constructor
        · rintro ⟨a, rfl⟩
          apply Subtype.ext
          obtain ⟨g, hg, hga⟩ := a.property
          change Ideal.Quotient.factor
              (integerProjVanishingIdeal_le_sup_left Y H)
              ((hypersurfaceSectionMulDegreeInt Y f hf (l : Int) a).1) = 0
          have haeq : (hypersurfaceSectionMulDegreeInt Y f hf (l : Int) a).1 =
              Ideal.Quotient.mk (homogeneousVanishingIdeal Y) (f * g) := by
            change f • a.1 = _
            change Ideal.Quotient.mk (homogeneousVanishingIdeal Y) g = a.1 at hga
            rw [← hga]
            rfl
          rw [haeq]
          change Ideal.Quotient.mk
              (integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H).toIdeal
              (f * g) = 0
          apply Ideal.Quotient.eq_zero_iff_mem.2
          change f * g ∈ homogeneousVanishingIdeal Y ⊔ homogeneousVanishingIdeal H
          rw [hJH]
          exact (le_sup_right : Ideal.span ({f} : Set _) ≤
            homogeneousVanishingIdeal Y ⊔ Ideal.span ({f} : Set _))
              (Ideal.mem_span_singleton.2 ⟨g, rfl⟩)
        · intro hx
          obtain ⟨p, hp, hpx⟩ := x.property
          have hxzero := congrArg Subtype.val hx
          change Ideal.Quotient.factor
              (integerProjVanishingIdeal_le_sup_left Y H) x.1 = 0 at hxzero
          rw [← hpx] at hxzero
          have hpSum : p ∈ homogeneousVanishingIdeal Y ⊔
              homogeneousVanishingIdeal H := by
            apply Ideal.Quotient.eq_zero_iff_mem.1
            exact hxzero
          rw [hJH] at hpSum
          obtain ⟨j, hj, q, hq, hjq⟩ := Submodule.mem_sup.1 hpSum
          obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hq
          have hpaJ : p - a * f ∈ homogeneousVanishingIdeal Y := by
            rw [mul_comm a f, ← ha, ← hjq]
            simpa using hj
          have hpHom : p.IsHomogeneous l := by simpa using hp
          have hcomp := MvPolynomial.homogeneousComponent_mem_of_mem
            (isHomogeneousIdeal_homogeneousVanishingIdeal Y) hpaJ l
          have hpfJ : p ∈ homogeneousVanishingIdeal Y := by
            rw [map_sub, homogeneousComponent_of_mem hpHom, if_pos rfl,
              homogeneousComponent_mul_eq_zero_of_lt a f hf (by omega), sub_zero]
              at hcomp
            exact hcomp
          have hx0 : x = 0 := by
            apply Subtype.ext
            rw [← hpx]
            exact Ideal.Quotient.eq_zero_iff_mem.2 hpfJ
          subst x
          exact ⟨0, map_zero _⟩
  | negSucc l =>
      refine ⟨hinj, ?_, hsurj⟩
      ext x
      constructor
      · intro
        apply LinearMap.mem_ker.2
        have hx0 : x = 0 := by
          obtain ⟨p, hp, hpx⟩ := x.property
          have hp0 : p = 0 := by
            simpa [integerHomogeneousSubmodule] using hp
          apply Subtype.ext
          rw [← hpx, hp0]
          rfl
        subst x
        exact map_zero _
      · intro
        have hx0 : x = 0 := by
          obtain ⟨p, hp, hpx⟩ := x.property
          have hp0 : p = 0 := by
            simpa [integerHomogeneousSubmodule] using hp
          apply Subtype.ext
          rw [← hpx, hp0]
          rfl
        subst x
        exact ⟨0, map_zero _⟩

private theorem polynomial_sub_taylor_natDegree_le
    (P : ℚ[X]) {r : ℕ} (hr : P.natDegree = r) (hr0 : 0 < r)
    (a : ℚ) :
    (P - P.taylor a).natDegree ≤ r - 1 := by
  have hP0 : P ≠ 0 := by
    intro hP
    simp [hP] at hr
    omega
  have hdegree : P.degree = (P.taylor a).degree := by
    rw [Polynomial.degree_taylor]
  have hlt : (P - P.taylor a).degree < P.degree :=
    Polynomial.degree_sub_lt_left hdegree hP0
      (Polynomial.leadingCoeff_taylor a P).symm
  by_cases hQ : P - P.taylor a = 0
  · simp [hQ]
  · have hnatlt : (P - P.taylor a).natDegree < r := by
      rw [Polynomial.degree_eq_natDegree hQ,
        Polynomial.degree_eq_natDegree hP0, hr] at hlt
      exact_mod_cast hlt
    omega

private theorem polynomial_sub_taylor_leadingCoeff
    (P : ℚ[X]) {r d : ℕ} (hr : P.natDegree = r)
    (hr0 : 0 < r) (hd : 0 < d) :
    (P - P.taylor (-(d : ℚ))).natDegree = r - 1 ∧
      (P - P.taylor (-(d : ℚ))).leadingCoeff =
        (d : ℚ) * (r : ℚ) * P.leadingCoeff := by
  let Q := P.hasseDeriv (r - 1)
  have hQdeg : Q.natDegree ≤ 1 := by
    dsimp [Q]
    have h := P.natDegree_hasseDeriv_le (r - 1)
    rw [hr] at h
    omega
  have hQeval : Q.eval (-(d : ℚ)) =
      Q.coeff 0 + Q.coeff 1 * (-(d : ℚ)) := by
    rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
    simp [Finset.sum_range_succ]
  have hrsub : r - 1 + 1 = r := by omega
  have hQcoeff0 : Q.coeff 0 = P.coeff (r - 1) := by
    simp [Q, Polynomial.hasseDeriv_coeff]
  have hQcoeff1 : Q.coeff 1 = (r : ℚ) * P.leadingCoeff := by
    rw [show Q.coeff 1 = ((1 + (r - 1)).choose (r - 1) : ℚ) *
        P.coeff (1 + (r - 1)) by
      exact Polynomial.hasseDeriv_coeff (r - 1) P 1]
    rw [show 1 + (r - 1) = r by omega]
    have hchoose : r.choose (r - 1) = r := by
      calc
        r.choose (r - 1) = ((r - 1) + 1).choose (r - 1) := by rw [hrsub]
        _ = (r - 1) + 1 := Nat.choose_succ_self_right (r - 1)
        _ = r := hrsub
    have hPcoeff : P.coeff r = P.leadingCoeff := by
      rw [← hr, Polynomial.coeff_natDegree]
    rw [hchoose, hPcoeff]
  have hcoeff : (P - P.taylor (-(d : ℚ))).coeff (r - 1) =
      (d : ℚ) * (r : ℚ) * P.leadingCoeff := by
    rw [Polynomial.coeff_sub, Polynomial.taylor_coeff, hQeval,
      hQcoeff0, hQcoeff1]
    ring
  have hPleading : P.leadingCoeff ≠ 0 := by
    exact Polynomial.leadingCoeff_ne_zero.mpr (by
      intro hP
      simp [hP] at hr
      omega)
  have hcoeff0 : (P - P.taylor (-(d : ℚ))).coeff (r - 1) ≠ 0 := by
    rw [hcoeff]
    positivity
  have hdegree := polynomial_sub_taylor_natDegree_le P hr hr0 (-(d : ℚ))
  have hnat : (P - P.taylor (-(d : ℚ))).natDegree = r - 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegree hcoeff0
  refine ⟨hnat, ?_⟩
  rw [Polynomial.leadingCoeff, hnat, hcoeff]

/-- **Hartshorne I.7.7, hypersurface-section calculation.**  If the
positive-dimensional projective variety `Y` is not contained in the
degree-`d` hypersurface `H = Z(f)`, the Hilbert polynomial of the nonreduced
intersection module `S/(J(Y) + J(H))` is
`P_Y(z) - P_Y(z-d)`.  It has degree `r - 1` and leading coefficient
`d * deg(Y) / (r - 1)!`. -/
theorem hypersurfaceSection_hilbertPolynomial_and_leadingCoeff
    {k : Type u} [Field k] [IsAlgClosed k] {n d r : Nat}
    (hd : 0 < d) (hr0 : 0 < r)
    (Y : Set (ProjectiveSpace k (Fin (n + 1)))) (hY : IsProjVariety Y)
    (hYdim : projDim Y = (r : WithBot ℕ∞))
    (f : MvPolynomial (Fin (n + 1)) k)
    (hf : f.IsHomogeneous d) (hfirr : Irreducible f)
    (hproper : ¬Y ⊆ projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))) :
    let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
    let 𝒮 := integerHomogeneousSubmodule k (Fin (n + 1))
    let I := integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H
    let ℳ := quotGrading 𝒮 I
    let PM := gradedHilbertPolynomial
      (k := k) (n := n) (M := MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) ℳ
    PM = projectiveHilbertPolynomial Y -
        (projectiveHilbertPolynomial Y).taylor (-(d : ℚ)) ∧
      PM.natDegree = r - 1 ∧
      PM.leadingCoeff = (d : ℚ) * projectiveDegree Y *
        (((r - 1).factorial : Nat) : ℚ)⁻¹ := by
  classical
  dsimp only
  let H := projZeroSet ({f} : Set (MvPolynomial (Fin (n + 1)) k))
  let 𝒮 := integerHomogeneousSubmodule k (Fin (n + 1))
  let I := integerProjVanishingIdeal Y ⊔ integerProjVanishingIdeal H
  let ℳ := quotGrading 𝒮 I
  let P := projectiveHilbertPolynomial Y
  let PM := gradedHilbertPolynomial
    (k := k) (n := n) (M := MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) ℳ
  have hn : 0 < n := by
    have hle : projDim Y ≤
        projDim (Set.univ : Set (ProjectiveSpace k (Fin (n + 1)))) :=
      (Topology.IsEmbedding.inclusion
        (Set.subset_univ Y)).isInducing.topologicalKrullDim_le
    rw [hYdim, projDim_univ_fin] at hle
    have hrn : r ≤ n := by exact_mod_cast hle
    omega
  have hP := projectiveHilbertPolynomial_isHilbertPolynomial Y
  have hPM : IsHilbertPolynomial (σ := Fin (n + 1)) ℳ PM :=
    gradedHilbertPolynomial_isHilbertPolynomial
      (k := k) (n := n) (M := MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) ℳ
  have hnum : IsNumericalPolynomial (P - P.taylor (-(d : ℚ))) := by
    rw [IsNumericalPolynomial]
    exact Filter.Eventually.of_forall fun z => by
      obtain ⟨a, ha⟩ := hP.1.integerValued z
      obtain ⟨b, hb⟩ := hP.1.integerValued (z - d)
      change P.eval (z : ℚ) = (a : ℚ) at ha
      change P.eval ((z - d : Int) : ℚ) = (b : ℚ) at hb
      refine ⟨a - b, ?_⟩
      simp only [Polynomial.eval_sub, Polynomial.taylor_eval]
      push_cast at hb ⊢
      rw [ha]
      simpa only [sub_eq_add_neg] using
        congrArg (fun q : ℚ ↦ (a : ℚ) - q) hb
  have hPshift : ∀ᶠ z : Int in Filter.atTop,
      P.eval ((z - d : Int) : ℚ) =
        (hilbertFunction (σ := Fin (n + 1))
          (integerProjCoordGrading Y) (z - d) : ℚ) := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP.2
    exact Filter.eventually_atTop.mpr
      ⟨N + d, fun z hz => hN (z - d) (by omega)⟩
  have hevent : ∀ᶠ z : Int in Filter.atTop,
      (P - P.taylor (-(d : ℚ))).eval (z : ℚ) =
        (hilbertFunction (σ := Fin (n + 1)) ℳ z : ℚ) := by
    filter_upwards [hP.2, hPshift,
      Filter.eventually_ge_atTop (d : Int)] with z hzP hzPshift hzd
    obtain ⟨l, rfl⟩ := Int.eq_ofNat_of_zero_le
      (le_trans (Int.natCast_nonneg d) hzd)
    obtain ⟨hinj, hexact, hsurj⟩ :=
      hypersurfaceSection_degreewise_exact_int
        hn Y hY f hf hfirr hproper (l : Int)
    have hfun := hilbertFunction_add_of_degreewise_exact
      (σ := Fin (n + 1))
      (gradedModuleTwist (integerProjCoordGrading Y) (-(d : Int)))
      (integerProjCoordGrading Y) ℳ (l : Int)
      (hypersurfaceSectionMulDegreeInt Y f hf (l : Int))
      (hypersurfaceSectionQuotientDegree Y H (l : Int))
      hinj hexact hsurj
    simp only [hilbertFunction_twist] at hfun
    have hindex : (l : Int) + -(d : Int) = ((l - d : Nat) : Int) := by omega
    have hindexSub : (l : Int) - (d : Int) = ((l - d : Nat) : Int) := by omega
    have hqindex : (((l : Int) : ℚ) + -(d : ℚ)) =
        (((l - d : Nat) : Int) : ℚ) := by
      calc
        ((l : Int) : ℚ) + -(d : ℚ) =
            (((l : Int) - (d : Int)) : ℚ) := by
          push_cast
          ring
        _ = (((l - d : Nat) : Int) : ℚ) := by
          simpa only [Int.cast_sub, Int.cast_natCast] using
            congrArg (fun z : Int ↦ (z : ℚ)) hindexSub
    rw [hindex] at hfun
    rw [hindexSub] at hzPshift
    simp only [Polynomial.eval_sub, Polynomial.taylor_eval]
    rw [hzP, hqindex, hzPshift]
    have hfunQ := congrArg (fun m : Nat ↦ (m : ℚ)) hfun
    push_cast at hfunQ ⊢
    linarith
  have hpolynomial : PM = P - P.taylor (-(d : ℚ)) :=
    isHilbertPolynomial_unique ℳ hPM ⟨hnum, hevent⟩
  have hPdeg : P.natDegree = r := by
    have hdeg : hilbertPolynomialDegree P = (r : WithBot ℕ∞) := by
      rw [show hilbertPolynomialDegree P = projDim Y by
        simpa [P] using projectiveHilbertPolynomial_degree hY.isProjAlgebraicSet]
      exact hYdim
    by_cases hP0 : P = 0
    · simp [hilbertPolynomialDegree, hP0] at hdeg
    · simpa [hilbertPolynomialDegree, hP0] using hdeg
  have hdata := polynomial_sub_taylor_leadingCoeff P hPdeg hr0 hd
  refine ⟨hpolynomial, ?_, ?_⟩
  · change PM.natDegree = r - 1
    rw [hpolynomial, hdata.1]
  · change PM.leadingCoeff = (d : ℚ) * projectiveDegree Y *
      (((r - 1).factorial : Nat) : ℚ)⁻¹
    rw [hpolynomial, hdata.2]
    unfold projectiveDegree
    change (d : ℚ) * (r : ℚ) * P.leadingCoeff =
      (d : ℚ) * (P.natDegree.factorial * P.leadingCoeff) *
        (((r - 1).factorial : Nat) : ℚ)⁻¹
    rw [hPdeg]
    have hfac : (((r - 1).factorial : Nat) : ℚ) ≠ 0 := by positivity
    rw [← Nat.mul_factorial_pred (Nat.ne_of_gt hr0)]
    push_cast
    field_simp

end

end Hartshorne
