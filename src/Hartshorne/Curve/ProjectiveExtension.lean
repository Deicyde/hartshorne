/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.ValuationProjectivePivot
import Hartshorne.Curve.ValuationSpaceFunctionField
import Hartshorne.Morphism.OpenSubvariety
import Hartshorne.Rational.AffineOpenBasis
import Hartshorne.Rational.MorphismAgreement
import Hartshorne.Rational.ProductVariety

/-!
# Extending a morphism from a punctured abstract curve

Hartshorne, *Algebraic Geometry*, I.6, Proposition 6.8 (pp. 43--44).
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

namespace ValuationSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable [IsAlgClosed k] [Algebra.EssFiniteType k K]

/-- The complement of one point in an abstract nonsingular curve. -/
def puncturedOpen (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (P : (abstractNonsingularCurve htrdeg U hU).carrier) :
    Opens (abstractNonsingularCurve htrdeg U hU).carrier where
  carrier := {P}ᶜ
  is_open' := by
    have hclosed : IsClosed ({P.1} : Set (ValuationSpace k K)) :=
      Set.Finite.isClosed (Set.finite_singleton P.1)
    have hpre : IsClosed
        ((fun Q : (abstractNonsingularCurve htrdeg U hU).carrier ↦ Q.1) ⁻¹'
          ({P.1} : Set (ValuationSpace k K))) :=
      hclosed.preimage continuous_subtype_val
    convert hpre.isOpen_compl using 1
    ext Q
    constructor
    · intro h hval
      exact h (Subtype.ext hval)
    · intro h hQP
      exact h (congrArg Subtype.val hQP)

@[simp]
theorem mem_puncturedOpen (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (P Q : (abstractNonsingularCurve htrdeg U hU).carrier) :
    Q ∈ puncturedOpen htrdeg U hU P ↔ Q ≠ P := by
  simp [puncturedOpen]

/-- Removing one point from an abstract nonsingular curve leaves a nonempty
open subset. -/
theorem puncturedOpen_nonempty (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (P : (abstractNonsingularCurve htrdeg U hU).carrier) :
    ((puncturedOpen htrdeg U hU P : Opens
      (abstractNonsingularCurve htrdeg U hU).carrier) :
      Set (abstractNonsingularCurve htrdeg U hU).carrier).Nonempty := by
  have hUinfinite := infinite_of_isOpen_of_nonempty htrdeg U.isOpen hU
  by_contra hempty
  apply hUinfinite
  apply (Set.finite_singleton P.1).subset
  intro Q hQU
  have hQP : (⟨Q, hQU⟩ :
      (abstractNonsingularCurve htrdeg U hU).carrier) = P := by
    by_contra hne
    apply hempty
    exact ⟨⟨Q, hQU⟩, (mem_puncturedOpen htrdeg U hU P _).mpr hne⟩
  exact Set.mem_singleton_iff.mpr (congrArg Subtype.val hQP)

/-- Unfold regularity on a restriction only once, retaining the ambient
variety rather than unfolding its own construction. -/
private theorem regular_on_push_of_restrict
    {κ : Type u} [Field κ] {X : Variety κ}
    {D : Opens X.carrier} {hD : (D : Set X.carrier).Nonempty}
    {W : Opens (X.restrict D hD).carrier} {f : W → κ}
    (hf : f ∈ (X.restrict D hD).regular W) :
    (fun z : pushOpens D W ↦ f (ofPush (U := D) z)) ∈
      X.regular (pushOpens D W) :=
  hf

/-- A regular function on an open subset of an open abstract curve is represented
by one element of the ambient function field. -/
private theorem exists_rational_of_regular_on_nested_open
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (D : Opens (abstractNonsingularCurve htrdeg U hU).carrier)
    (hD : (D : Set (abstractNonsingularCurve htrdeg U hU).carrier).Nonempty)
    (W : Opens
      ((abstractNonsingularCurve htrdeg U hU).restrict D hD).carrier)
    (f : W → k)
    (hf : f ∈ ((abstractNonsingularCurve htrdeg U hU).restrict D hD).regular W) :
    ∃ q : regularRationalFunctions (k := k) (K := K)
        (pushOpens U (pushOpens D W) : Set (ValuationSpace k K)),
      residueEvaluation htrdeg
          (pushOpens U (pushOpens D W) : Set (ValuationSpace k K)) q =
        fun z ↦ f (ofPush (ofPush z)) := by
  change (fun z : pushOpens U (pushOpens D W) ↦ f (ofPush (ofPush z))) ∈
    regularFunctions htrdeg
      (pushOpens U (pushOpens D W) : Set (ValuationSpace k K)) at hf
  rw [regularFunctions, AlgHom.mem_range] at hf
  exact hf

/-- Residue evaluation is globally regular on a restricted open subvariety
whenever the field element belongs to every valuation ring there. -/
private theorem residue_isGlobalRegular_on_restrict
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (V : Opens (abstractNonsingularCurve htrdeg U hU).carrier)
    (hV : (V : Set (abstractNonsingularCurve htrdeg U hU).carrier).Nonempty)
    (q : K)
    (hq : ∀ z : V,
      q ∈ ((ValuationSpace.of k K).symm z.1.1).toValuationSubring) :
    ((abstractNonsingularCurve htrdeg U hU).restrict V hV).IsGlobalRegular
      (fun z ↦ FunctionFieldDVR.residueAt htrdeg
        ((ValuationSpace.of k K).symm z.1.1) ⟨q, hq z⟩) := by
  change (fun z : pushOpens U (pushOpens V ⊤) ↦
      FunctionFieldDVR.residueAt htrdeg
        ((ValuationSpace.of k K).symm z.1)
          ⟨q, hq (ofPush (U := V) (ofPush (U := U) z))⟩) ∈
    regularFunctions htrdeg
      (pushOpens U (pushOpens V ⊤) : Set (ValuationSpace k K))
  rw [regularFunctions, AlgHom.mem_range]
  let a : regularRationalFunctions (k := k) (K := K)
      (pushOpens U (pushOpens V ⊤) : Set (ValuationSpace k K)) :=
    ⟨q, mem_regularRationalFunctions_iff.mpr
      (fun z ↦ hq (ofPush (U := V) (ofPush (U := U) z)))⟩
  refine ⟨a, ?_⟩
  funext z
  rfl

/-- A morphism from a nonempty open part of an abstract curve to projective
space extends over any one prescribed point on some neighbourhood of that
point.  The local extension agrees with the original morphism wherever both
are defined. -/
private theorem exists_local_extension_to_projectiveSpace
    {σ : Type u} [Finite σ] [Nonempty σ]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (D : Opens (abstractNonsingularCurve htrdeg U hU).carrier)
    (hD : (D : Set (abstractNonsingularCurve htrdeg U hU).carrier).Nonempty)
    (φ : VarietyHom
      ((abstractNonsingularCurve htrdeg U hU).restrict D hD)
      (Variety.ofQuasiProjective
        (isProjVariety_univ (k := k) (σ := σ)).isQuasiProjVariety))
    (P : (abstractNonsingularCurve htrdeg U hU).carrier) :
    ∃ (N : Opens (abstractNonsingularCurve htrdeg U hU).carrier)
      (hN : (N : Set (abstractNonsingularCurve htrdeg U hU).carrier).Nonempty),
      P ∈ N ∧
        ∃ ψ : VarietyHom
          ((abstractNonsingularCurve htrdeg U hU).restrict N hN)
          (Variety.ofQuasiProjective
            (isProjVariety_univ (k := k) (σ := σ)).isQuasiProjVariety),
          ∀ (z : (abstractNonsingularCurve htrdeg U hU).carrier)
            (hzN : z ∈ N) (hzD : z ∈ D),
            ψ ⟨z, hzN⟩ = φ ⟨z, hzD⟩ := by
  classical
  let X := abstractNonsingularCurve htrdeg U hU
  let hℙ := (isProjVariety_univ (k := k) (σ := σ)).isQuasiProjVariety
  let x₀ : (X.restrict D hD).carrier := ⟨hD.choose, hD.choose_spec⟩
  obtain ⟨j, W, hx₀W, hφW, hcoord⟩ :=
    (exists_varietyHom_iff_locally_chart_regular hℙ φ.toFun).mp ⟨φ, rfl⟩ x₀
  let T : Opens (ValuationSpace k K) := pushOpens U (pushOpens D W)
  let coordRat (l : {l : σ // l ≠ j}) :
      regularRationalFunctions (k := k) (K := K)
        (T : Set (ValuationSpace k K)) :=
    Classical.choose (exists_rational_of_regular_on_nested_open
      htrdeg U hU D hD W
      (fun z : W ↦ chartMap j (φ z).1 l) (hcoord l))
  have coordRat_spec (l : {l : σ // l ≠ j}) :
      residueEvaluation htrdeg (T : Set (ValuationSpace k K)) (coordRat l) =
        fun z ↦ chartMap j
          (φ (ofPush (U := D) (ofPush (U := U) z)).1).1 l :=
    Classical.choose_spec (exists_rational_of_regular_on_nested_open
      htrdeg U hU D hD W
      (fun z : W ↦ chartMap j (φ z).1 l) (hcoord l))
  let q : σ → K := fun i ↦ if hi : i = j then 1 else (coordRat ⟨i, hi⟩).1
  have hqT (i : σ) : q i ∈
      regularRationalFunctions (k := k) (K := K)
        (T : Set (ValuationSpace k K)) := by
    by_cases hi : i = j
    · simp [q, hi]
    · simp [q, hi]
  have hqeval (i : σ) (z : T) :
      FunctionFieldDVR.residueAt htrdeg
          ((ValuationSpace.of k K).symm z.1) ⟨q i,
            mem_regularRationalFunctions_iff.mp (hqT i) z⟩ =
        (φ (ofPush (U := D) (ofPush (U := U) z)).1).1.rep i /
          (φ (ofPush (U := D) (ofPush (U := U) z)).1).1.rep j := by
    by_cases hi : i = j
    · subst i
      have hj : (φ (ofPush (U := D) (ofPush (U := U) z)).1).1.rep j ≠ 0 :=
        rep_ne_zero_of_mem_standardChart
          (hφW (ofPush (U := D) (ofPush (U := U) z)))
      rw [div_self hj]
      have hone : (⟨q j, mem_regularRationalFunctions_iff.mp (hqT j) z⟩ :
          ((ValuationSpace.of k K).symm z.1).toValuationSubring) = 1 := by
        apply Subtype.ext
        simp [q]
      rw [hone, map_one]
    · have hs := congrFun (coordRat_spec ⟨i, hi⟩) z
      simp [q, hi, chartMap] at hs ⊢
      exact hs
  have hqne : q ≠ 0 := by
    intro hzero
    have hj := congrFun hzero j
    simp [q] at hj
  let R := (ValuationSpace.of k K).symm P.1
  obtain ⟨p, hqp, hrP, hrp⟩ :=
    FunctionFieldDVR.exists_projective_pivot R q hqne
  let r : σ → K := fun i ↦ q i / q p
  let _ := Fintype.ofFinite σ
  let domain : σ → Opens X.carrier := fun i ↦ regularDomain htrdeg U (r i)
  let N : Opens X.carrier :=
    Finset.univ.inf domain
  have hNle (i : σ) : N ≤ domain i := by
    exact Finset.inf_le (Finset.mem_univ i)
  have hPdomain (i : σ) : P ∈ domain i := by
    change ¬ r i ∉ R.toValuationSubring
    exact not_not.mpr (hrP i)
  have hPN : P ∈ N := by
    have hmem : ∀ s : Finset σ, P ∈ s.inf domain := by
      intro s
      induction s using Finset.induction_on with
      | empty => trivial
      | @insert i s hi ih =>
          have hbin : P ∈ domain i ⊓ s.inf domain := by
            change P ∈ (domain i : Set X.carrier) ∩
              ((s.inf domain : Opens X.carrier) : Set X.carrier)
            exact ⟨hPdomain i, ih⟩
          simpa [hi] using hbin
    exact hmem Finset.univ
  have hN : (N : Set X.carrier).Nonempty := ⟨P, hPN⟩
  have hrN (i : σ) (z : N) :
      r i ∈ ((ValuationSpace.of k K).symm z.1.1).toValuationSubring := by
    have hz := hNle i z.2
    change ¬ r i ∉ ((ValuationSpace.of k K).symm z.1.1).toValuationSubring at hz
    exact not_not.mp hz
  let a (z : N) (i : σ) : k :=
    FunctionFieldDVR.residueAt htrdeg
      ((ValuationSpace.of k K).symm z.1.1) ⟨r i, hrN i z⟩
  let ψfun : (X.restrict N hN).carrier →
      (Set.univ : Set (ProjectiveSpace k σ)) := fun z ↦
    ⟨chartInv p (fun l ↦ a z l.1), Set.mem_univ _⟩
  have hψ : ∃ ψ : VarietyHom (X.restrict N hN)
      (Variety.ofQuasiProjective hℙ), ψ.toFun = ψfun := by
    apply (exists_varietyHom_iff_locally_chart_regular hℙ ψfun).mpr
    intro z
    refine ⟨p, ⊤, trivial, fun _ ↦ chartInv_mem_standardChart p _, ?_⟩
    intro l
    have hreg := residue_isGlobalRegular_on_restrict
      htrdeg U hU N hN (r l.1) (hrN l.1)
    change (X.restrict N hN).IsGlobalRegular
      (fun z ↦ chartMap p (ψfun z).1 l)
    rw [show (fun z ↦ chartMap p (ψfun z).1 l) =
        fun z ↦ FunctionFieldDVR.residueAt htrdeg
          ((ValuationSpace.of k K).symm z.1.1) ⟨r l.1, hrN l.1 z⟩ by
      funext z
      simp [ψfun, a]]
    exact hreg
  let ψ : VarietyHom (X.restrict N hN)
      (Variety.ofQuasiProjective hℙ) := Classical.choose hψ
  have hψ_apply (z : (X.restrict N hN).carrier) :
      ψ z = ψfun z := congrFun (Classical.choose_spec hψ) z
  let V : Opens X.carrier := N ⊓ D
  have hV : (V : Set X.carrier).Nonempty :=
    Variety.opens_inter_nonempty hN hD
  let ψV : VarietyHom (X.restrict V hV)
      (Variety.ofQuasiProjective hℙ) :=
    ψ.comp (X.inclHomOfLE inf_le_left hV hN)
  let φV : VarietyHom (X.restrict V hV)
      (Variety.ofQuasiProjective hℙ) :=
    φ.comp (X.inclHomOfLE inf_le_right hV hD)
  let S : Opens (X.restrict V hV).carrier :=
    Opens.comap
      ⟨(X.inclHomOfLE inf_le_right hV hD).toFun,
        (X.inclHomOfLE inf_le_right hV hD).continuous_toFun⟩ W
  have hpushW : ((pushOpens D W : Opens X.carrier) : Set X.carrier).Nonempty := by
    exact ⟨x₀.1, x₀.2, fun _ ↦ hx₀W⟩
  have hNW : ((N ⊓ pushOpens D W : Opens X.carrier) : Set X.carrier).Nonempty :=
    Variety.opens_inter_nonempty hN hpushW
  have hS : (S : Set (X.restrict V hV).carrier).Nonempty := by
    obtain ⟨z, hzN, hzW⟩ := hNW
    exact ⟨⟨z, hzN, hzW.1⟩, hzW.2 hzW.1⟩
  have hagreeS : ∀ z ∈ (S : Set (X.restrict V hV).carrier), ψV z = φV z := by
    intro z hzS
    change (⟨z.1, z.2.2⟩ : D) ∈ W at hzS
    let zW : W := ⟨⟨z.1, z.2.2⟩, hzS⟩
    let zT : T := toPush (toPush zW)
    let zN : N := ⟨z.1, z.2.1⟩
    let zD : D := ⟨z.1, z.2.2⟩
    let Rz := (ValuationSpace.of k K).symm z.1.1
    have hqmem (i : σ) : q i ∈ Rz.toValuationSubring :=
      mem_regularRationalFunctions_iff.mp (hqT i) zT
    have heval (i : σ) :
        FunctionFieldDVR.residueAt htrdeg Rz ⟨q i, hqmem i⟩ =
          (φ zD).1.rep i / (φ zD).1.rep j := by
      have h := hqeval i zT
      have hpoint :
          (ofPush (U := D) (ofPush (U := U) zT)).1 = zD :=
        Subtype.ext rfl
      rw [hpoint] at h
      change FunctionFieldDVR.residueAt htrdeg
          ((ValuationSpace.of k K).symm zT.1)
            ⟨q i, mem_regularRationalFunctions_iff.mp (hqT i) zT⟩ =
        (φ zD).1.rep i / (φ zD).1.rep j
      exact h
    have hmul (i : σ) : a zN i *
        FunctionFieldDVR.residueAt htrdeg Rz ⟨q p, hqmem p⟩ =
      FunctionFieldDVR.residueAt htrdeg Rz ⟨q i, hqmem i⟩ := by
      change FunctionFieldDVR.residueAt htrdeg Rz ⟨r i, hrN i zN⟩ *
          FunctionFieldDVR.residueAt htrdeg Rz ⟨q p, hqmem p⟩ = _
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      exact div_mul_cancel₀ (q i) hqp
    have hj : (φ zD).1.rep j ≠ 0 :=
      rep_ne_zero_of_mem_standardChart (hφW zW)
    have hep : FunctionFieldDVR.residueAt htrdeg Rz ⟨q p, hqmem p⟩ ≠ 0 := by
      intro hepzero
      have hm := hmul j
      rw [hepzero, mul_zero] at hm
      have hevalj := heval j
      rw [div_self hj] at hevalj
      rw [hevalj] at hm
      exact zero_ne_one hm
    have hp : (φ zD).1.rep p ≠ 0 := by
      intro hpzero
      apply hep
      have hevalp := heval p
      rw [hpzero, zero_div] at hevalp
      exact hevalp
    have hchart : (φ zD).1 ∈ standardChart p :=
      mem_standardChart_iff.mpr hp
    have hcoords : (fun l : {l : σ // l ≠ p} ↦ a zN l.1) =
        chartMap p (φ zD).1 := by
      funext l
      have hm := hmul l.1
      rw [heval p, heval l.1] at hm
      field_simp [hj] at hm
      apply (eq_div_iff hp).mpr
      exact hm
    change ψ zN = φ zD
    rw [hψ_apply zN]
    apply Subtype.ext
    change chartInv p (fun l : {l : σ // l ≠ p} ↦ a zN l.1) = (φ zD).1
    rw [hcoords, chartInv_chartMap hchart]
  have hψVφV : ψV = φV :=
    isSeparated_ofQuasiProjective hℙ _ ψV φV S S.isOpen hS hagreeS
  refine ⟨N, hN, hPN, ψ, ?_⟩
  intro z hzN hzD
  let zV : V := ⟨z, hzN, hzD⟩
  have hz := congrArg (fun f : VarietyHom (X.restrict V hV)
      (Variety.ofQuasiProjective hℙ) ↦ f zV) hψVφV
  exact hz

/-- **Hartshorne I.6, Proposition 6.8.** A morphism from an abstract
nonsingular curve with one point removed to a projective variety extends
uniquely across that point. -/
theorem existsUnique_projective_extension
    {σ : Type u} [Finite σ] [Nonempty σ]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (P : (abstractNonsingularCurve htrdeg U hU).carrier)
    {Y : Set (ProjectiveSpace k σ)} (hY : IsProjVariety Y)
    (φ : VarietyHom
      ((abstractNonsingularCurve htrdeg U hU).restrict
        (puncturedOpen htrdeg U hU P)
        (puncturedOpen_nonempty htrdeg U hU P))
      (Variety.ofProjective hY)) :
    ∃! Φ : VarietyHom (abstractNonsingularCurve htrdeg U hU)
        (Variety.ofProjective hY),
      Φ.comp ((abstractNonsingularCurve htrdeg U hU).inclHom
        (puncturedOpen htrdeg U hU P)
        (puncturedOpen_nonempty htrdeg U hU P)) = φ := by
  classical
  let X := abstractNonsingularCurve htrdeg U hU
  let D := puncturedOpen htrdeg U hU P
  let hD := puncturedOpen_nonempty htrdeg U hU P
  let hℙ := (isProjVariety_univ (k := k) (σ := σ)).isQuasiProjVariety
  let hYq := hY.isQuasiProjVariety
  let ιY : VarietyHom (Variety.ofProjective hY)
      (Variety.ofQuasiProjective hℙ) :=
    inclHom hℙ hYq (Set.subset_univ Y)
  let φℙ : VarietyHom (X.restrict D hD)
      (Variety.ofQuasiProjective hℙ) := ιY.comp φ
  obtain ⟨N, hN, hPN, ψ, hagree⟩ :=
    exists_local_extension_to_projectiveSpace htrdeg U hU D hD φℙ P
  let pointN (z : X.carrier) (hzN : z ∈ N) :
      ((abstractNonsingularCurve htrdeg U hU).restrict N hN).carrier :=
    ⟨z, hzN⟩
  let pointD (z : X.carrier) (hzD : z ∈ D) : (X.restrict D hD).carrier :=
    ⟨z, hzD⟩
  let rawψ (z : ((abstractNonsingularCurve htrdeg U hU).restrict N hN).carrier) :
      ProjectiveSpace k σ := Subtype.val (ψ z)
  let rawφ (z : (X.restrict D hD).carrier) : ProjectiveSpace k σ :=
    Subtype.val (φℙ z)
  let Fraw : X.carrier → ProjectiveSpace k σ := fun z ↦
    if hz : z = P then
      rawψ (pointN z (hz.symm ▸ hPN))
    else
      rawφ (pointD z ((mem_puncturedOpen htrdeg U hU P z).mpr hz))
  let Ffun : X.carrier → (Set.univ : Set (ProjectiveSpace k σ)) := fun z ↦
    ⟨Fraw z, Set.mem_univ _⟩
  have Ffun_eq_φℙ (z : X.carrier) (hzD : z ∈ D) :
      Ffun z = ⟨rawφ (pointD z hzD), Set.mem_univ _⟩ := by
    have hz : z ≠ P := (mem_puncturedOpen htrdeg U hU P z).mp hzD
    apply Subtype.ext
    change Fraw z = rawφ (pointD z hzD)
    dsimp only [Fraw]
    rw [dif_neg hz]
  have Ffun_eq_ψ (z : X.carrier) (hzN : z ∈ N) :
      Ffun z = ⟨rawψ (pointN z hzN), Set.mem_univ _⟩ := by
    by_cases hz : z = P
    · subst z
      apply Subtype.ext
      change Fraw P = rawψ (pointN P hzN)
      dsimp only [Fraw]
      rw [dif_pos rfl]
    · apply Subtype.ext
      change Fraw z = rawψ (pointN z hzN)
      dsimp only [Fraw]
      rw [dif_neg hz]
      exact congrArg Subtype.val ((hagree z hzN
        ((mem_puncturedOpen htrdeg U hU P z).mpr hz)).symm)
  have hFℙ : ∃ F : VarietyHom X (Variety.ofQuasiProjective hℙ),
      F.toFun = Ffun := by
    apply (exists_varietyHom_iff_locally_chart_regular hℙ Ffun).mpr
    intro x
    by_cases hx : x = P
    · subst x
      obtain ⟨i, W, hPW, hψW, hψreg⟩ :=
        (exists_varietyHom_iff_locally_chart_regular hℙ ψ.toFun).mp
          ⟨ψ, rfl⟩ ⟨P, hPN⟩
      let V : Opens X.carrier := pushOpens N W
      refine ⟨i, V, ⟨hPN, fun _ ↦ hPW⟩, ?_, ?_⟩
      · intro z
        have hzpoint : pointN z.1 z.2.1 = (ofPush (U := N) z).1 :=
          Subtype.ext rfl
        rw [Ffun_eq_ψ z.1 z.2.1, hzpoint]
        exact hψW (ofPush z)
      · intro l
        have hreg := regular_on_push_of_restrict (hψreg l)
        rw [show (fun z : V ↦ chartMap i (Ffun z.1).1 l) =
            fun z : V ↦ chartMap i (ψ (ofPush (U := N) z).1).1 l by
          funext z
          have hzpoint : pointN z.1 z.2.1 = (ofPush (U := N) z).1 :=
            Subtype.ext rfl
          rw [Ffun_eq_ψ z.1 z.2.1, hzpoint]]
        exact hreg
    · have hxD : x ∈ D :=
        (mem_puncturedOpen htrdeg U hU P x).mpr hx
      obtain ⟨i, W, hxW, hφW, hφreg⟩ :=
        (exists_varietyHom_iff_locally_chart_regular hℙ φℙ.toFun).mp
          ⟨φℙ, rfl⟩ ⟨x, hxD⟩
      let V : Opens X.carrier := pushOpens D W
      refine ⟨i, V, ⟨hxD, fun _ ↦ hxW⟩, ?_, ?_⟩
      · intro z
        have hzpoint : pointD z.1 z.2.1 = (ofPush (U := D) z).1 :=
          Subtype.ext rfl
        rw [Ffun_eq_φℙ z.1 z.2.1, hzpoint]
        exact hφW (ofPush z)
      · intro l
        have hreg := regular_on_push_of_restrict (hφreg l)
        rw [show (fun z : V ↦ chartMap i (Ffun z.1).1 l) =
            fun z : V ↦ chartMap i (φℙ (ofPush (U := D) z).1).1 l by
          funext z
          have hzpoint : pointD z.1 z.2.1 = (ofPush (U := D) z).1 :=
            Subtype.ext rfl
          rw [Ffun_eq_φℙ z.1 z.2.1, hzpoint]]
        exact hreg
  let Fℙ : VarietyHom X (Variety.ofQuasiProjective hℙ) := Classical.choose hFℙ
  have hFℙ_apply (z : X.carrier) : Fℙ z = Ffun z :=
    congrFun (Classical.choose_spec hFℙ) z
  have hFmem (z : X.carrier) : (Fℙ z).1 ∈ Y := by
    let Z : Set X.carrier := {x | (Fℙ x).1 ∈ Y}
    have hZclosed : IsClosed Z :=
      hY.2.preimage (continuous_subtype_val.comp Fℙ.continuous_toFun)
    have hDZ : (D : Set X.carrier) ⊆ Z := by
      intro x hxD
      change (Fℙ x).1 ∈ Y
      rw [hFℙ_apply, Ffun_eq_φℙ x hxD]
      change (φ (pointD x hxD)).1 ∈ Y
      exact (φ (pointD x hxD)).2
    have hclosure : closure (D : Set X.carrier) ⊆ Z :=
      hZclosed.closure_subset_iff.mpr hDZ
    apply hclosure
    rw [(Variety.dense_of_isOpen_of_nonempty D.isOpen hD).closure_eq]
    exact Set.mem_univ z
  let FtoY : X.carrier → Y := fun z ↦ ⟨(Fℙ z).1, hFmem z⟩
  have hF : ∃ F : VarietyHom X (Variety.ofQuasiProjective hYq),
      F.toFun = FtoY := by
    apply (exists_varietyHom_iff_locally_chart_regular hYq FtoY).mpr
    intro x
    obtain ⟨i, V, hxV, hFV, hFreg⟩ :=
      (exists_varietyHom_iff_locally_chart_regular hℙ Fℙ.toFun).mp
        ⟨Fℙ, rfl⟩ x
    exact ⟨i, V, hxV, hFV, hFreg⟩
  let F : VarietyHom X (Variety.ofProjective hY) := Classical.choose hF
  have hF_apply (z : X.carrier) : F z = FtoY z :=
    congrFun (Classical.choose_spec hF) z
  have hFextends : F.comp (X.inclHom D hD) = φ := by
    apply VarietyHom.ext
    funext z
    rw [VarietyHom.comp_apply, hF_apply]
    apply Subtype.ext
    change (Fℙ z.1).1 = (φ z).1
    rw [hFℙ_apply, Ffun_eq_φℙ z.1 z.2]
    change (φ z).1 = (φ z).1
    rfl
  refine ⟨F, hFextends, ?_⟩
  intro G hG
  apply isSeparated_ofQuasiProjective hYq X G F D D.isOpen hD
  intro z hzD
  let zD : (X.restrict D hD).carrier := ⟨z, hzD⟩
  have hGz := congrArg
    (fun H : VarietyHom (X.restrict D hD) (Variety.ofProjective hY) ↦ H zD) hG
  have hFz := congrArg
    (fun H : VarietyHom (X.restrict D hD) (Variety.ofProjective hY) ↦ H zD) hFextends
  exact hGz.trans hFz.symm

/-- Inclusion between abstract curves cut out by nested ambient valuation-space
opens. -/
private noncomputable def abstractCurveInclHom
    (htrdeg : Algebra.trdeg k K = 1)
    {V U : Opens (ValuationSpace k K)} (hVU : V ≤ U)
    (hV : (V : Set (ValuationSpace k K)).Nonempty)
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    VarietyHom (abstractNonsingularCurve htrdeg V hV)
      (abstractNonsingularCurve htrdeg U hU) := by
  change VarietyHom
    ((abstractNonsingularCurveAmbient htrdeg).restrict V hV)
    ((abstractNonsingularCurveAmbient htrdeg).restrict U hU)
  exact (abstractNonsingularCurveAmbient htrdeg).inclHomOfLE hVU hV hU

/-- Flatten an open restriction of an abstract curve back to an abstract curve
on the corresponding ambient valuation-space open. -/
private noncomputable def abstractCurveFlattenHom
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (D : Opens (abstractNonsingularCurve htrdeg U hU).carrier)
    (hD : (D : Set (abstractNonsingularCurve htrdeg U hU).carrier).Nonempty) :
    VarietyHom
      ((abstractNonsingularCurve htrdeg U hU).restrict D hD)
      (abstractNonsingularCurve htrdeg (pushOpens U D)
        (Variety.pushOpens_nonempty
          (X := abstractNonsingularCurveAmbient htrdeg)
          (U := U) (hU := hU) hD)) := by
  change VarietyHom
    (((abstractNonsingularCurveAmbient htrdeg).restrict U hU).restrict D hD)
    ((abstractNonsingularCurveAmbient htrdeg).restrict (pushOpens U D)
      (Variety.pushOpens_nonempty
        (X := abstractNonsingularCurveAmbient htrdeg)
        (U := U) (hU := hU) hD))
  exact Variety.flattenRestrictHom
    (X := abstractNonsingularCurveAmbient htrdeg) U hU D hD

/-- Unflatten an abstract curve on a pushed open into the corresponding open
restriction. -/
private noncomputable def abstractCurveUnflattenHom
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (D : Opens (abstractNonsingularCurve htrdeg U hU).carrier)
    (hD : (D : Set (abstractNonsingularCurve htrdeg U hU).carrier).Nonempty) :
    VarietyHom
      (abstractNonsingularCurve htrdeg (pushOpens U D)
        (Variety.pushOpens_nonempty
          (X := abstractNonsingularCurveAmbient htrdeg)
          (U := U) (hU := hU) hD))
      ((abstractNonsingularCurve htrdeg U hU).restrict D hD) := by
  change VarietyHom
    ((abstractNonsingularCurveAmbient htrdeg).restrict (pushOpens U D)
      (Variety.pushOpens_nonempty
        (X := abstractNonsingularCurveAmbient htrdeg)
        (U := U) (hU := hU) hD))
    (((abstractNonsingularCurveAmbient htrdeg).restrict U hU).restrict D hD)
  exact Variety.unflattenRestrictHom
    (X := abstractNonsingularCurveAmbient htrdeg) U hU D hD

/-- Existence of an extension between two ambient opens.  The explicit finite
set is an induction parameter recording the points still missing from the
domain. -/
private theorem exists_projective_extension_between_ambient_opens_aux
    {τ : Type u} [Finite τ] [Nonempty τ]
    (htrdeg : Algebra.trdeg k K = 1)
    {Z : Set (ProjectiveSpace k τ)} (hZ : IsProjVariety Z)
    (S : Set (ValuationSpace k K)) (hS : S.Finite) :
    ∀ (U V : Opens (ValuationSpace k K))
      (hU : (U : Set (ValuationSpace k K)).Nonempty)
      (hV : (V : Set (ValuationSpace k K)).Nonempty)
      (hVU : V ≤ U),
      (U : Set (ValuationSpace k K)) \ (V : Set (ValuationSpace k K)) = S →
      ∀ φ : VarietyHom (abstractNonsingularCurve htrdeg V hV)
          (Variety.ofProjective hZ),
        ∃ Φ : VarietyHom (abstractNonsingularCurve htrdeg U hU)
            (Variety.ofProjective hZ),
          ∀ (x : ValuationSpace k K) (hx : x ∈ V),
            Φ ⟨x, hVU hx⟩ = φ ⟨x, hx⟩ := by
  classical
  refine Set.Finite.induction_on
    (motive := fun S _ =>
      ∀ (U V : Opens (ValuationSpace k K))
        (hU : (U : Set (ValuationSpace k K)).Nonempty)
        (hV : (V : Set (ValuationSpace k K)).Nonempty)
        (hVU : V ≤ U),
        (U : Set (ValuationSpace k K)) \ (V : Set (ValuationSpace k K)) = S →
        ∀ φ : VarietyHom (abstractNonsingularCurve htrdeg V hV)
            (Variety.ofProjective hZ),
          ∃ Φ : VarietyHom (abstractNonsingularCurve htrdeg U hU)
              (Variety.ofProjective hZ),
            ∀ (x : ValuationSpace k K) (hx : x ∈ V),
              Φ ⟨x, hVU hx⟩ = φ ⟨x, hx⟩)
    S hS ?_ ?_
  · intro U V hU hV hVU hdiff φ
    have hUV : U ≤ V := by
      intro x hxU
      by_contra hxV
      have hx : x ∈ (U : Set (ValuationSpace k K)) \
          (V : Set (ValuationSpace k K)) := ⟨hxU, hxV⟩
      rw [hdiff] at hx
      exact hx
    let j : VarietyHom (abstractNonsingularCurve htrdeg U hU)
        (abstractNonsingularCurve htrdeg V hV) :=
      abstractCurveInclHom htrdeg hUV hU hV
    refine ⟨φ.comp j, ?_⟩
    intro x hxV
    change φ (j ⟨x, hVU hxV⟩) = φ ⟨x, hxV⟩
    apply congrArg φ
    apply Subtype.ext
    rfl
  · intro p S hp hS ih U V hU hV hVU hdiff φ
    have hpDiff : p ∈ (U : Set (ValuationSpace k K)) \
        (V : Set (ValuationSpace k K)) := by
      rw [hdiff]
      simp
    have hpU : p ∈ U := hpDiff.1
    have hpV : p ∉ V := hpDiff.2
    let A := abstractNonsingularCurve htrdeg U hU
    let P : A.carrier := ⟨p, hpU⟩
    let D : Opens A.carrier := puncturedOpen htrdeg U hU P
    let hD : (D : Set A.carrier).Nonempty :=
      puncturedOpen_nonempty htrdeg U hU P
    let U' : Opens (ValuationSpace k K) := pushOpens U D
    let hU' : (U' : Set (ValuationSpace k K)).Nonempty :=
      Variety.pushOpens_nonempty
        (X := abstractNonsingularCurveAmbient htrdeg)
        (U := U) (hU := hU) hD
    have hU'_mem (x : ValuationSpace k K) : x ∈ U' ↔ x ∈ U ∧ x ≠ p := by
      constructor
      · intro hx
        refine ⟨hx.1, ?_⟩
        intro hxp
        have hne := (mem_puncturedOpen htrdeg U hU P ⟨x, hx.1⟩).mp
          (hx.2 hx.1)
        apply hne
        apply Subtype.ext
        exact hxp
      · rintro ⟨hxU, hxp⟩
        refine ⟨hxU, fun hxU' =>
          (mem_puncturedOpen htrdeg U hU P ⟨x, hxU'⟩).mpr ?_⟩
        intro heq
        exact hxp (congrArg Subtype.val heq)
    have hVU' : V ≤ U' := by
      intro x hxV
      apply (hU'_mem x).mpr
      refine ⟨hVU hxV, ?_⟩
      intro hxp
      apply hpV
      simpa [hxp] using hxV
    have hdiff' : (U' : Set (ValuationSpace k K)) \
        (V : Set (ValuationSpace k K)) = S := by
      ext x
      constructor
      · intro hx
        have hxDiff : x ∈ (U : Set (ValuationSpace k K)) \
            (V : Set (ValuationSpace k K)) := ⟨((hU'_mem x).mp hx.1).1, hx.2⟩
        have hxInsert : x = p ∨ x ∈ S := by
          rw [hdiff] at hxDiff
          simpa only [Set.mem_insert_iff] using hxDiff
        exact hxInsert.resolve_left ((hU'_mem x).mp hx.1).2
      · intro hxS
        have hxInsert : x ∈ insert p S := Set.mem_insert_of_mem p hxS
        have hxDiff : x ∈ (U : Set (ValuationSpace k K)) \
            (V : Set (ValuationSpace k K)) := by
          rw [hdiff]
          exact hxInsert
        have hxp : x ≠ p := by
          intro hxp
          apply hp
          simpa [hxp] using hxS
        exact ⟨(hU'_mem x).mpr ⟨hxDiff.1, hxp⟩, hxDiff.2⟩
    obtain ⟨ψ, hψ⟩ := ih U' V hU' hV hVU' hdiff' φ
    let φD : VarietyHom (A.restrict D hD) (Variety.ofProjective hZ) :=
      ψ.comp (abstractCurveFlattenHom htrdeg U hU D hD)
    obtain ⟨Φ, hΦ, _⟩ :=
      existsUnique_projective_extension htrdeg U hU P hZ φD
    refine ⟨Φ, ?_⟩
    intro x hxV
    have hxU : x ∈ U := hVU hxV
    have hxU' : x ∈ U' := hVU' hxV
    have hxD : (⟨x, hxU⟩ : A.carrier) ∈ D := by
      exact (mem_puncturedOpen htrdeg U hU P ⟨x, hxU⟩).mpr
        (fun heq => hpV (by
          have hxp : x = p := congrArg Subtype.val heq
          simpa [hxp] using hxV))
    let xD : (A.restrict D hD).carrier := ⟨⟨x, hxU⟩, hxD⟩
    have hΦx := congrArg
      (fun q : VarietyHom (A.restrict D hD) (Variety.ofProjective hZ) => q xD) hΦ
    change Φ ((A.inclHom D hD) xD) = φD xD at hΦx
    calc
      Φ ⟨x, hxU⟩ = Φ ((A.inclHom D hD) xD) := by
        apply congrArg Φ
        rfl
      _ = φD xD := hΦx
      _ = ψ ⟨x, hxU'⟩ := by rfl
      _ = φ ⟨x, hxV⟩ := hψ x hxV

/-- A morphism from any nonempty open part of an abstract nonsingular curve to
a projective variety extends uniquely to the whole abstract curve. -/
theorem existsUnique_projective_extension_of_open
    {τ : Type u} [Finite τ] [Nonempty τ]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (D : Opens (abstractNonsingularCurve htrdeg U hU).carrier)
    (hD : (D : Set (abstractNonsingularCurve htrdeg U hU).carrier).Nonempty)
    {Z : Set (ProjectiveSpace k τ)} (hZ : IsProjVariety Z)
    (φ : VarietyHom
      ((abstractNonsingularCurve htrdeg U hU).restrict D hD)
      (Variety.ofProjective hZ)) :
    ∃! Φ : VarietyHom (abstractNonsingularCurve htrdeg U hU)
        (Variety.ofProjective hZ),
      Φ.comp ((abstractNonsingularCurve htrdeg U hU).inclHom D hD) = φ := by
  classical
  let V : Opens (ValuationSpace k K) := pushOpens U D
  let hV : (V : Set (ValuationSpace k K)).Nonempty :=
    Variety.pushOpens_nonempty
      (X := abstractNonsingularCurveAmbient htrdeg)
      (U := U) (hU := hU) hD
  let φV : VarietyHom (abstractNonsingularCurve htrdeg V hV)
      (Variety.ofProjective hZ) :=
    φ.comp (abstractCurveUnflattenHom htrdeg U hU D hD)
  have hfinite : ((V : Set (ValuationSpace k K))ᶜ).Finite :=
    (isOpen_iff_nonempty_imp_compl_finite k K).mp V.isOpen hV
  have hdiff : ((U : Set (ValuationSpace k K)) \
      (V : Set (ValuationSpace k K))).Finite :=
    hfinite.subset (fun _ hx => hx.2)
  obtain ⟨Φ, hΦ⟩ := exists_projective_extension_between_ambient_opens_aux
    htrdeg hZ ((U : Set (ValuationSpace k K)) \ (V : Set (ValuationSpace k K)))
      hdiff U V hU hV pushOpens_le rfl φV
  have hΦcomp : Φ.comp
      ((abstractNonsingularCurve htrdeg U hU).inclHom D hD) = φ := by
    apply VarietyHom.ext
    funext x
    let xV : V := toPush x
    have hx := hΦ x.1.1 xV.2
    have hxleft :
        (⟨x.1.1, pushOpens_le xV.2⟩ :
          (abstractNonsingularCurve htrdeg U hU).carrier) = x.1 := by
      apply Subtype.ext
      rfl
    have hxright : abstractCurveUnflattenHom htrdeg U hU D hD xV = x := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    calc
      Φ x.1 = Φ ⟨x.1.1, pushOpens_le xV.2⟩ := congrArg Φ hxleft.symm
      _ = φV xV := hx
      _ = φ (abstractCurveUnflattenHom htrdeg U hU D hD xV) := rfl
      _ = φ x := congrArg φ hxright
  refine ⟨Φ, hΦcomp, ?_⟩
  intro Ψ hΨ
  apply isSeparated_ofQuasiProjective hZ.isQuasiProjVariety
    (abstractNonsingularCurve htrdeg U hU) Ψ Φ (D : Set _)
    D.isOpen hD
  intro x hxD
  let xD : (abstractNonsingularCurve htrdeg U hU).restrict D hD := ⟨x, hxD⟩
  have hΨx := congrArg
    (fun q : VarietyHom
      ((abstractNonsingularCurve htrdeg U hU).restrict D hD)
      (Variety.ofProjective hZ) => q xD) hΨ
  have hΦx := congrArg
    (fun q : VarietyHom
      ((abstractNonsingularCurve htrdeg U hU).restrict D hD)
      (Variety.ofProjective hZ) => q xD) hΦcomp
  exact hΨx.trans hΦx.symm

end ValuationSpace

end

end Hartshorne
