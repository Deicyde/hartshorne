/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.ValuationRegularFunctions

/-!
# Regularity axioms on the valuation space

Hartshorne, *Algebraic Geometry*, I.6 (p. 42).

The residue-valued regular functions on the valuation space restrict, have
closed zero loci, are closed under division by nowhere-zero functions, and are
detected locally.  These are precisely the four regular-function fields needed
to construct a `Variety`.

The locality proof treats the empty open separately.  On a nonempty open it
chooses one rational representative, compares every other local representative
on a nonempty intersection, and uses injectivity of residue evaluation there.
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u v

namespace ValuationSpace

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Restricting the set of valuations enlarges the algebra of rational
functions regular at every point. -/
private theorem regularRationalFunctions_mono
    {U V : Set (ValuationSpace k K)} (hVU : V ⊆ U) :
    regularRationalFunctions (k := k) (K := K) U ≤
      regularRationalFunctions (k := k) (K := K) V := by
  intro f hf
  rw [mem_regularRationalFunctions_iff]
  intro R
  exact mem_regularRationalFunctions_iff.mp hf ⟨R.1, hVU R.2⟩

/-- Restriction between the algebras of rational representatives is the
identity on the ambient function field. -/
private def rationalRestriction
    {U V : Set (ValuationSpace k K)} (hVU : V ⊆ U) :
    regularRationalFunctions (k := k) (K := K) U →ₐ[k]
      regularRationalFunctions (k := k) (K := K) V :=
  Subalgebra.inclusion (regularRationalFunctions_mono hVU)

/-- Residue evaluation commutes with restriction. -/
private theorem residueEvaluation_restrict [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    {U V : Set (ValuationSpace k K)} (hVU : V ⊆ U)
    (f : regularRationalFunctions (k := k) (K := K) U) :
    residueEvaluation htrdeg V (rationalRestriction hVU f) =
      fun R : V ↦ residueEvaluation htrdeg U f ⟨R.1, hVU R.2⟩ := by
  rfl

/-- The four regular-function properties needed to construct a `Variety` on
the valuation space. -/
structure RegularFunctionsAxioms [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1) : Prop where
  /-- Regular functions restrict to smaller open subsets. -/
  regular_restrict :
    ∀ {U V : Opens (ValuationSpace k K)} (hVU : V ≤ U) {f : U → k},
      f ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K)) →
        (fun x : V ↦ f ⟨x.1, hVU x.2⟩) ∈
          regularFunctions htrdeg (V : Set (ValuationSpace k K))
  /-- The zero locus of a regular function is closed. -/
  isClosed_zeroLocus :
    ∀ {U : Opens (ValuationSpace k K)} {f : U → k},
      f ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K)) →
        IsClosed {x : U | f x = 0}
  /-- A quotient by a nowhere-zero regular function is regular. -/
  regular_div :
    ∀ {U : Opens (ValuationSpace k K)} {f g : U → k},
      f ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K)) →
      g ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K)) →
      (∀ x, g x ≠ 0) →
        (fun x ↦ f x / g x) ∈
          regularFunctions htrdeg (U : Set (ValuationSpace k K))
  /-- Regularity is local on the valuation space. -/
  regular_of_locally :
    ∀ {U : Opens (ValuationSpace k K)} {f : U → k},
      (∀ x : U, ∃ V : Opens (ValuationSpace k K), ∃ hVU : V ≤ U,
        x.1 ∈ V ∧
          (fun y : V ↦ f ⟨y.1, hVU y.2⟩) ∈
            regularFunctions htrdeg (V : Set (ValuationSpace k K))) →
      f ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K))

private theorem regularFunctions_restrict [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    {U V : Opens (ValuationSpace k K)} (hVU : V ≤ U) {f : U → k}
    (hf : f ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K))) :
    (fun x : V ↦ f ⟨x.1, hVU x.2⟩) ∈
      regularFunctions htrdeg (V : Set (ValuationSpace k K)) := by
  rw [regularFunctions, AlgHom.mem_range] at hf ⊢
  obtain ⟨a, rfl⟩ := hf
  refine ⟨rationalRestriction hVU a, ?_⟩
  exact residueEvaluation_restrict htrdeg hVU a

/-- Zero residue implies membership in the maximal ideal of the corresponding
valuation ring. -/
private theorem vanishesAt_of_residueEvaluation_eq_zero [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    {U : Set (ValuationSpace k K)}
    (f : regularRationalFunctions (k := k) (K := K) U) (R : U)
    (hzero : residueEvaluation htrdeg U f R = 0) :
    ((ValuationSpace.of k K).symm R.1).VanishesAt f.1 := by
  let V := (ValuationSpace.of k K).symm R.1
  have hfmem : f.1 ∈ V.toValuationSubring :=
    mem_regularRationalFunctions_iff.mp f.2 R
  rw [V.vanishesAt_iff_exists_mem_maximalIdeal]
  refine ⟨hfmem, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  apply (FunctionFieldDVR.residueFieldEquiv htrdeg V).injective
  simpa [FunctionFieldDVR.residueAt] using hzero

private theorem regularFunctions_isClosed_zeroLocus [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    {U : Opens (ValuationSpace k K)} {f : U → k}
    (hf : f ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K))) :
    IsClosed {x : U | f x = 0} := by
  rw [regularFunctions, AlgHom.mem_range] at hf
  obtain ⟨a, rfl⟩ := hf
  by_cases ha : (a.1 : K) = 0
  · have ha' : a = 0 := Subtype.ext ha
    subst a
    simp
  · let Z : Set (ValuationSpace k K) :=
      {R | ((ValuationSpace.of k K).symm R).VanishesAt a.1}
    have hZfinite : Z.Finite := by
      apply Set.Finite.preimage
        (s := {R : FunctionFieldDVR k K | R.VanishesAt a.1})
        (ValuationSpace.of k K).symm.injective.injOn
      exact FunctionFieldDVR.finite_vanishesAt htrdeg ha
    apply Set.Finite.isClosed
    apply (hZfinite.preimage Subtype.val_injective.injOn).subset
    intro R hR
    change ((ValuationSpace.of k K).symm R.1).VanishesAt a.1
    exact vanishesAt_of_residueEvaluation_eq_zero htrdeg a R hR

/-- An element of a function-field DVR with nonzero residue is a unit. -/
private theorem isUnit_of_residueAt_ne_zero [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (R : FunctionFieldDVR k K) (x : R.toValuationSubring)
    (hx : FunctionFieldDVR.residueAt htrdeg R x ≠ 0) : IsUnit x := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  intro hzero
  apply hx
  simp [FunctionFieldDVR.residueAt, hzero]

private theorem regularFunctions_div [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    {U : Opens (ValuationSpace k K)} {f g : U → k}
    (hf : f ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K)))
    (hg : g ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K)))
    (hgne : ∀ x, g x ≠ 0) :
    (fun x ↦ f x / g x) ∈
      regularFunctions htrdeg (U : Set (ValuationSpace k K)) := by
  rw [regularFunctions, AlgHom.mem_range] at hf hg ⊢
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  have hquotient : ∀ R : U,
      a.1 / b.1 ∈ ((ValuationSpace.of k K).symm R.1).toValuationSubring := by
    intro R
    let V := (ValuationSpace.of k K).symm R.1
    have hamem : a.1 ∈ V.toValuationSubring :=
      mem_regularRationalFunctions_iff.mp a.2 R
    have hbmem : b.1 ∈ V.toValuationSubring :=
      mem_regularRationalFunctions_iff.mp b.2 R
    have hresB := hgne R
    change FunctionFieldDVR.residueAt htrdeg
        ((ValuationSpace.of k K).symm R.1)
          ⟨b.1, mem_regularRationalFunctions_iff.mp b.2 R⟩ ≠ 0 at hresB
    change FunctionFieldDVR.residueAt htrdeg V
      (⟨b.1, hbmem⟩ : V.toValuationSubring) ≠ 0 at hresB
    have hbunit : IsUnit (⟨b.1, hbmem⟩ : V.toValuationSubring) :=
      isUnit_of_residueAt_ne_zero htrdeg V _ hresB
    rw [div_eq_mul_inv]
    exact V.toValuationSubring.mul_mem _ _ hamem
      (Submonoid.inv_mem_of_isUnit hbunit)
  let c : regularRationalFunctions (k := k) (K := K)
      (U : Set (ValuationSpace k K)) :=
    ⟨a.1 / b.1, mem_regularRationalFunctions_iff.mpr hquotient⟩
  refine ⟨c, ?_⟩
  funext R
  let V := (ValuationSpace.of k K).symm R.1
  have hamem : a.1 ∈ V.toValuationSubring :=
    mem_regularRationalFunctions_iff.mp a.2 R
  have hbmem : b.1 ∈ V.toValuationSubring :=
    mem_regularRationalFunctions_iff.mp b.2 R
  have hresB := hgne R
  change FunctionFieldDVR.residueAt htrdeg
      ((ValuationSpace.of k K).symm R.1)
        ⟨b.1, mem_regularRationalFunctions_iff.mp b.2 R⟩ ≠ 0 at hresB
  change FunctionFieldDVR.residueAt htrdeg V
    (⟨b.1, hbmem⟩ : V.toValuationSubring) ≠ 0 at hresB
  have hbunit : IsUnit (⟨b.1, hbmem⟩ : V.toValuationSubring) :=
    isUnit_of_residueAt_ne_zero htrdeg V _ hresB
  have hbzero : b.1 ≠ 0 := by
    intro hb
    apply hbunit.ne_zero
    apply Subtype.ext
    exact hb
  change FunctionFieldDVR.residueAt htrdeg V
      (⟨a.1 / b.1, hquotient R⟩ : V.toValuationSubring) =
    FunctionFieldDVR.residueAt htrdeg V ⟨a.1, hamem⟩ /
      FunctionFieldDVR.residueAt htrdeg V ⟨b.1, hbmem⟩
  rw [eq_div_iff hresB, ← map_mul]
  congr 1
  apply Subtype.ext
  exact div_mul_cancel₀ a.1 hbzero

private theorem regularFunctions_of_locally [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    {U : Opens (ValuationSpace k K)} {f : U → k}
    (hlocal : ∀ x : U,
      ∃ V : Opens (ValuationSpace k K), ∃ hVU : V ≤ U,
        x.1 ∈ V ∧
          (fun y : V ↦ f ⟨y.1, hVU y.2⟩) ∈
            regularFunctions htrdeg (V : Set (ValuationSpace k K))) :
    f ∈ regularFunctions htrdeg (U : Set (ValuationSpace k K)) := by
  by_cases hne : (U : Set (ValuationSpace k K)).Nonempty
  · let _ : IrreducibleSpace (ValuationSpace k K) :=
      ValuationSpace.irreducibleSpace_of_trdeg_eq_one htrdeg
    let x₀ : U := ⟨hne.choose, hne.choose_spec⟩
    obtain ⟨V₀, hV₀U, hx₀V₀, hfV₀⟩ := hlocal x₀
    rw [regularFunctions, AlgHom.mem_range] at hfV₀
    obtain ⟨a₀, ha₀⟩ := hfV₀
    have haU : ∀ R : U, ∃ ha : a₀.1 ∈
        ((ValuationSpace.of k K).symm R.1).toValuationSubring,
        FunctionFieldDVR.residueAt htrdeg
            ((ValuationSpace.of k K).symm R.1) ⟨a₀.1, ha⟩ = f R := by
      intro R
      obtain ⟨W, hWU, hRW, hfW⟩ := hlocal R
      rw [regularFunctions, AlgHom.mem_range] at hfW
      obtain ⟨b, hb⟩ := hfW
      let T : Opens (ValuationSpace k K) := V₀ ⊓ W
      have hTV₀ : T ≤ V₀ := inf_le_left
      have hTW : T ≤ W := inf_le_right
      have hV₀ne : (V₀ : Set (ValuationSpace k K)).Nonempty :=
        ⟨x₀.1, hx₀V₀⟩
      have hWne : (W : Set (ValuationSpace k K)).Nonempty := ⟨R.1, hRW⟩
      have hTne : (T : Set (ValuationSpace k K)).Nonempty := by
        exact nonempty_preirreducible_inter V₀.isOpen W.isOpen hV₀ne hWne
      let aT := rationalRestriction hTV₀ a₀
      let bT := rationalRestriction hTW b
      have hevalT : residueEvaluation htrdeg (T : Set (ValuationSpace k K)) aT =
          residueEvaluation htrdeg (T : Set (ValuationSpace k K)) bT := by
        funext z
        have haPoint := congrFun ha₀ ⟨z.1, hTV₀ z.2⟩
        have hbPoint := congrFun hb ⟨z.1, hTW z.2⟩
        calc
          residueEvaluation htrdeg (T : Set (ValuationSpace k K)) aT z =
              residueEvaluation htrdeg (V₀ : Set (ValuationSpace k K)) a₀
                ⟨z.1, hTV₀ z.2⟩ := by rfl
          _ = f ⟨z.1, hV₀U (hTV₀ z.2)⟩ := haPoint
          _ = f ⟨z.1, hWU (hTW z.2)⟩ := by rfl
          _ = residueEvaluation htrdeg (W : Set (ValuationSpace k K)) b
                ⟨z.1, hTW z.2⟩ := hbPoint.symm
          _ = residueEvaluation htrdeg (T : Set (ValuationSpace k K)) bT z := by
            rfl
      have habT : aT = bT :=
        residueEvaluation_injective htrdeg T.isOpen hTne hevalT
      have hab : a₀.1 = b.1 := by
        simpa [aT, bT, rationalRestriction] using congrArg Subtype.val habT
      have hbmem : b.1 ∈
          ((ValuationSpace.of k K).symm R.1).toValuationSubring :=
        mem_regularRationalFunctions_iff.mp b.2 ⟨R.1, hRW⟩
      have hamem : a₀.1 ∈
          ((ValuationSpace.of k K).symm R.1).toValuationSubring := by
        rw [hab]
        exact hbmem
      refine ⟨hamem, ?_⟩
      have hbPoint := congrFun hb ⟨R.1, hRW⟩
      change FunctionFieldDVR.residueAt htrdeg
          ((ValuationSpace.of k K).symm R.1) ⟨b.1, hbmem⟩ = f R at hbPoint
      simpa [hab] using hbPoint
    rw [regularFunctions, AlgHom.mem_range]
    let aU : regularRationalFunctions (k := k) (K := K)
        (U : Set (ValuationSpace k K)) :=
      ⟨a₀.1, mem_regularRationalFunctions_iff.mpr fun R ↦ (haU R).choose⟩
    refine ⟨aU, ?_⟩
    funext R
    change FunctionFieldDVR.residueAt htrdeg
      ((ValuationSpace.of k K).symm R.1) ⟨a₀.1, (haU R).choose⟩ = f R
    exact (haU R).choose_spec
  · rw [regularFunctions, AlgHom.mem_range]
    refine ⟨0, ?_⟩
    funext x
    exact (hne ⟨x.1, x.2⟩).elim

/-- The valuation-space regular functions satisfy all four axioms required by
`Variety`: restriction, closed zero loci, division, and locality. -/
theorem regularFunctions_axioms [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1) :
    RegularFunctionsAxioms htrdeg where
  regular_restrict := regularFunctions_restrict htrdeg
  isClosed_zeroLocus := regularFunctions_isClosed_zeroLocus htrdeg
  regular_div := regularFunctions_div htrdeg
  regular_of_locally := regularFunctions_of_locally htrdeg

end ValuationSpace

end

end Hartshorne
