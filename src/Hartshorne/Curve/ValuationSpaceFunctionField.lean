/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.AbstractNonsingularCurve
import Hartshorne.Morphism.VarietyFunctionFieldStructure
import Hartshorne.Morphism.GlobalLocalIntersection
import Hartshorne.Nonsingular.IntrinsicNonsingular

/-!
# The function field of an abstract nonsingular curve

Hartshorne, *Algebraic Geometry*, I.6 (p. 42).

If `U` is a nonempty open subset of the valuation space of a one-dimensional
function field `K / k`, then the function field of the associated abstract
nonsingular curve is canonically isomorphic to `K`.  An element of `K` is
represented on its maximal pole-free open subset of `U`; conversely, the
definition of regular functions on the valuation space supplies a unique
ambient element of `K` for every rational representative.
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u v

namespace ValuationSpace

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- The poles of an element of `K`, regarded as a subset of the valuation
space. -/
private def poleSet (x : K) : Set (ValuationSpace k K) :=
  {R | ((ValuationSpace.of k K).symm R).HasPoleAt x}

private theorem poleSet_finite [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) (x : K) :
    (poleSet (k := k) x).Finite := by
  apply Set.Finite.preimage
    (s := {R : FunctionFieldDVR k K | R.HasPoleAt x})
    (ValuationSpace.of k K).symm.injective.injOn
  exact FunctionFieldDVR.finite_hasPoleAt htrdeg x

/-- The maximal open subset of `U` on which `x : K` belongs to every
valuation ring. -/
def regularDomain [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K)) (x : K) : Opens U where
  carrier := (Subtype.val : U → ValuationSpace k K) ⁻¹' (poleSet (k := k) x)ᶜ
  is_open' := by
    change IsOpen (((Subtype.val : U → ValuationSpace k K) ⁻¹'
      poleSet (k := k) x)ᶜ)
    exact ((poleSet_finite htrdeg x).preimage
      Subtype.val_injective.injOn).isClosed.isOpen_compl

private theorem mem_valuationSubring_of_mem_regularDomain
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K)) (x : K) {R : U}
    (hR : R ∈ regularDomain htrdeg U x) :
    x ∈ ((ValuationSpace.of k K).symm R.1).toValuationSubring := by
  classical
  change ¬ (x ∉ ((ValuationSpace.of k K).symm R.1).toValuationSubring) at hR
  exact not_not.mp hR

/-- An element of a one-dimensional function field belongs to a given
valuation ring exactly when it is regular on some open neighbourhood of that
valuation. -/
theorem mem_valuationSubring_iff_exists_regular_neighborhood
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (R : FunctionFieldDVR k K) (q : K) :
    q ∈ R.toValuationSubring ↔
      ∃ U : Opens (ValuationSpace k K),
        ValuationSpace.of k K R ∈ U ∧
          q ∈ regularRationalFunctions (k := k) (K := K)
            (U : Set (ValuationSpace k K)) := by
  classical
  constructor
  · intro hq
    let T : Opens (ValuationSpace k K) := ⊤
    let V : Opens T := regularDomain htrdeg T q
    let U : Opens (ValuationSpace k K) := pushOpens T V
    refine ⟨U, ?_, ?_⟩
    · refine ⟨Set.mem_univ _, ?_⟩
      intro _
      change ¬ q ∉ R.toValuationSubring
      exact not_not.mpr hq
    · rw [mem_regularRationalFunctions_iff]
      intro S
      exact mem_valuationSubring_of_mem_regularDomain
        htrdeg T q (ofPush S).2
  · rintro ⟨U, hRU, hqU⟩
    have hqR := mem_regularRationalFunctions_iff.mp hqU
      (⟨ValuationSpace.of k K R, hRU⟩ : U)
    simpa using hqR

private theorem regularDomain_nonempty [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) (x : K) :
    ((regularDomain htrdeg U x : Opens U) : Set U).Nonempty := by
  have hUinfinite : (U : Set (ValuationSpace k K)).Infinite :=
    ValuationSpace.infinite_of_isOpen_of_nonempty htrdeg U.isOpen hU
  by_contra hdomain
  apply hUinfinite
  apply (poleSet_finite htrdeg x).subset
  intro R hRU
  by_contra hRpole
  apply hdomain
  exact ⟨⟨R, hRU⟩, hRpole⟩

/-- Residue evaluation of `x` on its maximal pole-free open domain. -/
noncomputable def regularValue [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K)) (x : K)
    (R : regularDomain htrdeg U x) : k :=
  FunctionFieldDVR.residueAt htrdeg
    ((ValuationSpace.of k K).symm R.1.1)
    ⟨x, mem_valuationSubring_of_mem_regularDomain htrdeg U x R.2⟩

/-- An ambient rational function, represented by residue evaluation on its
maximal pole-free open subset of `U`. -/
noncomputable def rationalRepOfElement [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) (x : K) :
    Variety.RationalRep (abstractNonsingularCurve htrdeg U hU) where
  U := regularDomain htrdeg U x
  nonempty_U := regularDomain_nonempty htrdeg U hU x
  toFun := regularValue htrdeg U x
  regular := by
    change (fun w : pushOpens U (regularDomain htrdeg U x) ↦
      regularValue htrdeg U x (ofPush w)) ∈
        regularFunctions htrdeg
          (pushOpens U (regularDomain htrdeg U x) : Set (ValuationSpace k K))
    rw [regularFunctions, AlgHom.mem_range]
    let a : regularRationalFunctions (k := k) (K := K)
        (pushOpens U (regularDomain htrdeg U x) : Set (ValuationSpace k K)) :=
      ⟨x, by
        rw [mem_regularRationalFunctions_iff]
        intro R
        exact mem_valuationSubring_of_mem_regularDomain htrdeg U x (ofPush R).2⟩
    refine ⟨a, ?_⟩
    funext R
    rfl

private theorem rationalRepOfElement_add_rel [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) (x y : K) :
    (rationalRepOfElement htrdeg U hU (x + y)).Rel
      ((rationalRepOfElement htrdeg U hU x).add
        (rationalRepOfElement htrdeg U hU y)) := by
  intro R hsum hxy
  let V := (ValuationSpace.of k K).symm R.1
  have hx : x ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U x hxy.1
  have hy : y ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U y hxy.2
  have hsum' : x + y ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U (x + y) hsum
  change FunctionFieldDVR.residueAt htrdeg V ⟨x + y, hsum'⟩ =
    FunctionFieldDVR.residueAt htrdeg V ⟨x, hx⟩ +
      FunctionFieldDVR.residueAt htrdeg V ⟨y, hy⟩
  calc
    _ = FunctionFieldDVR.residueAt htrdeg V
        ((⟨x, hx⟩ : V.toValuationSubring) + ⟨y, hy⟩) := by
      congr 1
    _ = _ := map_add (FunctionFieldDVR.residueAt htrdeg V)
      (⟨x, hx⟩ : V.toValuationSubring) ⟨y, hy⟩

private theorem rationalRepOfElement_mul_rel [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) (x y : K) :
    (rationalRepOfElement htrdeg U hU (x * y)).Rel
      ((rationalRepOfElement htrdeg U hU x).mul
        (rationalRepOfElement htrdeg U hU y)) := by
  intro R hprod hxy
  let V := (ValuationSpace.of k K).symm R.1
  have hx : x ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U x hxy.1
  have hy : y ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U y hxy.2
  have hprod' : x * y ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U (x * y) hprod
  change FunctionFieldDVR.residueAt htrdeg V ⟨x * y, hprod'⟩ =
    FunctionFieldDVR.residueAt htrdeg V ⟨x, hx⟩ *
      FunctionFieldDVR.residueAt htrdeg V ⟨y, hy⟩
  calc
    _ = FunctionFieldDVR.residueAt htrdeg V
        ((⟨x, hx⟩ : V.toValuationSubring) * ⟨y, hy⟩) := by
      congr 1
    _ = _ := map_mul (FunctionFieldDVR.residueAt htrdeg V)
      (⟨x, hx⟩ : V.toValuationSubring) ⟨y, hy⟩

private theorem rationalRepOfElement_zero_rel [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    (rationalRepOfElement htrdeg U hU (0 : K)).Rel
      (Variety.RationalRep.const
        (abstractNonsingularCurve htrdeg U hU) 0) := by
  intro R hR _
  let V := (ValuationSpace.of k K).symm R.1
  have hzero : (0 : K) ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U 0 hR
  change FunctionFieldDVR.residueAt htrdeg V ⟨0, hzero⟩ = 0
  calc
    _ = FunctionFieldDVR.residueAt htrdeg V
        (0 : V.toValuationSubring) := by congr 1
    _ = 0 := map_zero (FunctionFieldDVR.residueAt htrdeg V)

private theorem rationalRepOfElement_one_rel [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    (rationalRepOfElement htrdeg U hU (1 : K)).Rel
      (Variety.RationalRep.const
        (abstractNonsingularCurve htrdeg U hU) 1) := by
  intro R hR _
  let V := (ValuationSpace.of k K).symm R.1
  have hone : (1 : K) ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U 1 hR
  change FunctionFieldDVR.residueAt htrdeg V ⟨1, hone⟩ = 1
  calc
    _ = FunctionFieldDVR.residueAt htrdeg V
        (1 : V.toValuationSubring) := by congr 1
    _ = 1 := map_one (FunctionFieldDVR.residueAt htrdeg V)

private theorem rationalRepOfElement_algebraMap_rel [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) (c : k) :
    (rationalRepOfElement htrdeg U hU (algebraMap k K c)).Rel
      (Variety.RationalRep.const
        (abstractNonsingularCurve htrdeg U hU) c) := by
  intro R hR _
  let V := (ValuationSpace.of k K).symm R.1
  have hc : algebraMap k K c ∈ V.toValuationSubring :=
    mem_valuationSubring_of_mem_regularDomain htrdeg U (algebraMap k K c) hR
  change FunctionFieldDVR.residueAt htrdeg V ⟨algebraMap k K c, hc⟩ = c
  calc
    _ = FunctionFieldDVR.residueAt htrdeg V
        (algebraMap k V.toValuationSubring c) := by congr 1
    _ = c := FunctionFieldDVR.residueAt_algebraMap htrdeg V c

/-- The canonical map from the ambient field to the function field of an
abstract nonsingular curve.  It sends an element to residue evaluation on its
maximal pole-free open domain. -/
noncomputable def abstractNonsingularCurveToFunctionFieldAlgHom
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    K →ₐ[k] (abstractNonsingularCurve htrdeg U hU).FunctionField where
  toFun x := Quotient.mk _ (rationalRepOfElement htrdeg U hU x)
  map_one' := Quotient.sound (rationalRepOfElement_one_rel htrdeg U hU)
  map_mul' x y := Quotient.sound (rationalRepOfElement_mul_rel htrdeg U hU x y)
  map_zero' := Quotient.sound (rationalRepOfElement_zero_rel htrdeg U hU)
  map_add' x y := Quotient.sound (rationalRepOfElement_add_rel htrdeg U hU x y)
  commutes' c := Quotient.sound
    (rationalRepOfElement_algebraMap_rel htrdeg U hU c)

private theorem abstractNonsingularCurveToFunctionFieldAlgHom_surjective
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    Function.Surjective
      (abstractNonsingularCurveToFunctionFieldAlgHom htrdeg U hU) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro r
  have hr := r.regular
  change (fun w : pushOpens U r.U ↦ r.toFun (ofPush w)) ∈
    regularFunctions htrdeg
      (pushOpens U r.U : Set (ValuationSpace k K)) at hr
  rw [regularFunctions, AlgHom.mem_range] at hr
  obtain ⟨a, ha⟩ := hr
  refine ⟨a.1, Quotient.sound ?_⟩
  intro R haDomain hrDomain
  have hpoint := congrFun ha (toPush (⟨R, hrDomain⟩ : r.U))
  change regularValue htrdeg U a.1 ⟨R, haDomain⟩ =
    r.toFun ⟨R, hrDomain⟩
  change FunctionFieldDVR.residueAt htrdeg
      ((ValuationSpace.of k K).symm R.1)
        ⟨a.1, mem_valuationSubring_of_mem_regularDomain
          htrdeg U a.1 haDomain⟩ = r.toFun ⟨R, hrDomain⟩
  change FunctionFieldDVR.residueAt htrdeg
      ((ValuationSpace.of k K).symm R.1) ⟨a.1, _⟩ =
        r.toFun ⟨R, hrDomain⟩ at hpoint
  exact hpoint

/-- The canonical map from `K` to the function field of the associated
abstract nonsingular curve is bijective. -/
theorem abstractNonsingularCurveToFunctionFieldAlgHom_bijective
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    Function.Bijective
      (abstractNonsingularCurveToFunctionFieldAlgHom htrdeg U hU) :=
  ⟨(abstractNonsingularCurveToFunctionFieldAlgHom htrdeg U hU).toRingHom.injective,
    abstractNonsingularCurveToFunctionFieldAlgHom_surjective htrdeg U hU⟩

/-- **Hartshorne I.6.** The function field of the abstract nonsingular curve
associated to a nonempty open `U ⊆ C_K` is canonically `K`, as a
`k`-algebra. -/
noncomputable def abstractNonsingularCurveFunctionFieldAlgEquiv
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    K ≃ₐ[k] (abstractNonsingularCurve htrdeg U hU).FunctionField :=
  AlgEquiv.ofBijective
    (abstractNonsingularCurveToFunctionFieldAlgHom htrdeg U hU)
    (abstractNonsingularCurveToFunctionFieldAlgHom_bijective htrdeg U hU)

private noncomputable def abstractCurveLocalToAmbientAlgHom
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (P : (abstractNonsingularCurve htrdeg U hU).carrier) :
    (abstractNonsingularCurve htrdeg U hU).LocalRingAt P →ₐ[k] K :=
  (abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU).symm.toAlgHom.comp
    ((abstractNonsingularCurve htrdeg U hU).localToFunctionFieldAlgHom P)

private theorem abstractCurveLocalToAmbientAlgHom_mem
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (P : (abstractNonsingularCurve htrdeg U hU).carrier)
    (a : (abstractNonsingularCurve htrdeg U hU).LocalRingAt P) :
    abstractCurveLocalToAmbientAlgHom htrdeg U hU P a ∈
      ((ValuationSpace.of k K).symm P.1).toValuationSubring := by
  let X := abstractNonsingularCurve htrdeg U hU
  let R := (ValuationSpace.of k K).symm P.1
  change abstractCurveLocalToAmbientAlgHom htrdeg U hU P a ∈
    R.toValuationSubring
  refine Quotient.inductionOn a ?_
  intro r
  have hr := r.regular
  change (fun w : pushOpens U r.U ↦ r.toFun (ofPush w)) ∈
    regularFunctions htrdeg
      (pushOpens U r.U : Set (ValuationSpace k K)) at hr
  rw [regularFunctions, AlgHom.mem_range] at hr
  obtain ⟨q, hq⟩ := hr
  have hfield :
      abstractNonsingularCurveToFunctionFieldAlgHom htrdeg U hU q.1 =
        X.localToFunctionFieldAlgHom P
          (Quotient.mk (Variety.germSetoid X P) r) := by
    apply Quotient.sound
    intro S hSq hrS
    have hpoint := congrFun hq (toPush (⟨S, hrS⟩ : r.U))
    change regularValue htrdeg U q.1 ⟨S, hSq⟩ = r.toFun ⟨S, hrS⟩
    change FunctionFieldDVR.residueAt htrdeg
        ((ValuationSpace.of k K).symm S.1) ⟨q.1, _⟩ = r.toFun ⟨S, hrS⟩
    change FunctionFieldDVR.residueAt htrdeg
        ((ValuationSpace.of k K).symm S.1) ⟨q.1, _⟩ =
          r.toFun ⟨S, hrS⟩ at hpoint
    exact hpoint
  have htoK :
      (abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU).symm
          (X.localToFunctionFieldAlgHom P
            (Quotient.mk (Variety.germSetoid X P) r)) = q.1 := by
    rw [← hfield]
    exact (abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU).symm_apply_apply q.1
  change (abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU).symm
      (X.localToFunctionFieldAlgHom P
        (Quotient.mk (Variety.germSetoid X P) r)) ∈ R.toValuationSubring
  rw [htoK]
  apply (mem_valuationSubring_iff_exists_regular_neighborhood htrdeg R q.1).mpr
  refine ⟨pushOpens U r.U, ?_, q.2⟩
  have hP : P.1 ∈ pushOpens U r.U := (toPush (⟨P, r.mem_U⟩ : r.U)).2
  have hR : ValuationSpace.of k K R = P.1 :=
    ValuationSpace.of_apply_symm_apply k K P.1
  rwa [hR]

/-- **Hartshorne I.6.** The local ring at a point of an abstract nonsingular
curve is canonically the valuation ring represented by that point. -/
noncomputable def abstractNonsingularCurveLocalRingAlgEquiv
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (P : (abstractNonsingularCurve htrdeg U hU).carrier) :
    (abstractNonsingularCurve htrdeg U hU).LocalRingAt P ≃ₐ[k]
      ((ValuationSpace.of k K).symm P.1).toValuationSubring := by
  let X := abstractNonsingularCurve htrdeg U hU
  let eK := abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU
  let toK := abstractCurveLocalToAmbientAlgHom htrdeg U hU P
  let R := (ValuationSpace.of k K).symm P.1
  let f : X.LocalRingAt P →ₐ[k] R.toValuationSubring := {
    toFun := fun a ↦ ⟨toK a, abstractCurveLocalToAmbientAlgHom_mem htrdeg U hU P a⟩
    map_one' := Subtype.ext (map_one toK)
    map_mul' := fun a b ↦ Subtype.ext (map_mul toK a b)
    map_zero' := Subtype.ext (map_zero toK)
    map_add' := fun a b ↦ Subtype.ext (map_add toK a b)
    commutes' := fun c ↦ Subtype.ext (toK.commutes c)
  }
  refine AlgEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    apply X.localToFunctionFieldAlgHom_injective P
    apply eK.symm.injective
    exact congrArg Subtype.val hab
  · intro z
    let rr := rationalRepOfElement htrdeg U hU z.1
    have hPdomain : P ∈ rr.U := by
      change ¬ z.1 ∉ R.toValuationSubring
      exact not_not.mpr z.2
    let r : X.GermRep P := {
      U := rr.U
      mem_U := hPdomain
      toFun := rr.toFun
      regular := rr.regular
    }
    let a : X.LocalRingAt P := Quotient.mk (Variety.germSetoid X P) r
    refine ⟨a, Subtype.ext ?_⟩
    change (abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU).symm
      (X.localToFunctionFieldAlgHom P a) = z.1
    calc
      _ = (abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU).symm
          ((abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU) z.1) := by
        congr 1
      _ = z.1 := (abstractNonsingularCurveFunctionFieldAlgEquiv
        htrdeg U hU).symm_apply_apply z.1

/-- The canonical local-ring equivalence commutes with the two embeddings into
the ambient function field `K`. -/
@[simp]
theorem abstractNonsingularCurveLocalRingAlgEquiv_coe
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty)
    (P : (abstractNonsingularCurve htrdeg U hU).carrier)
    (a : (abstractNonsingularCurve htrdeg U hU).LocalRingAt P) :
    (((abstractNonsingularCurveLocalRingAlgEquiv htrdeg U hU P) a :
        ((ValuationSpace.of k K).symm P.1).toValuationSubring) : K) =
      (abstractNonsingularCurveFunctionFieldAlgEquiv htrdeg U hU).symm
        ((abstractNonsingularCurve htrdeg U hU).localToFunctionFieldAlgHom P a) := by
  unfold abstractNonsingularCurveLocalRingAlgEquiv
  rfl

/-- Abstract curves obtained from one-dimensional function fields are
nonsingular because all of their local rings are the represented DVRs. -/
theorem abstractNonsingularCurve_nonsingular
    [IsAlgClosed k] [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1)
    (U : Opens (ValuationSpace k K))
    (hU : (U : Set (ValuationSpace k K)).Nonempty) :
    (abstractNonsingularCurve htrdeg U hU).Nonsingular := by
  intro P
  exact (isRegularLocalRing_iff_of_ringEquiv
    (abstractNonsingularCurveLocalRingAlgEquiv htrdeg U hU P).toRingEquiv).mpr
      inferInstance

end ValuationSpace

end

end Hartshorne
