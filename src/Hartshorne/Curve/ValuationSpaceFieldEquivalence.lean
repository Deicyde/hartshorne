/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.AbstractNonsingularCurve

/-!
# Valuation curves and equivalent function fields

Hartshorne, *Algebraic Geometry*, I.6, Theorem 6.9 (p. 44).

An equivalence of one-dimensional function fields transports their discrete
valuation rings.  On the associated cofinite spaces this is a homeomorphism,
and compatibility of the canonical residue maps makes it an isomorphism of
the corresponding abstract nonsingular curves.
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u v

namespace ValuationSpace

variable {k : Type u} {K L : Type v}
  [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]

/-- Push a valuation subring forward along a field equivalence. -/
private def pushValuationSubring (e : K ≃ₐ[k] L) (R : ValuationSubring K) :
    ValuationSubring L where
  toSubring := R.toSubring.comap e.symm.toRingHom
  mem_or_inv_mem' x := by
    change e.symm x ∈ R ∨ e.symm (x⁻¹) ∈ R
    rw [map_inv₀]
    exact R.mem_or_inv_mem (e.symm x)

@[simp]
private theorem mem_pushValuationSubring (e : K ≃ₐ[k] L)
    (R : ValuationSubring K) (x : L) :
    x ∈ pushValuationSubring e R ↔ e.symm x ∈ R :=
  Iff.rfl

/-- The source valuation ring and its transported copy are isomorphic. -/
private def pushValuationSubringRingEquiv (e : K ≃ₐ[k] L)
    (R : ValuationSubring K) : R ≃+* pushValuationSubring e R where
  toFun x := ⟨e (x : K), by
    change e.symm (e (x : K)) ∈ R
    simp⟩
  invFun y := ⟨e.symm y, y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add e (x : K) (y : K))

/-- Transport a function-field DVR along an equivalence of its ambient field. -/
def transportDVR (e : K ≃ₐ[k] L) (R : FunctionFieldDVR k K) :
    FunctionFieldDVR k L := by
  refine ⟨pushValuationSubring e R.toValuationSubring, ?_, ?_⟩
  · exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (pushValuationSubringRingEquiv e R.toValuationSubring)
  · intro c
    change e.symm (algebraMap k L c) ∈ R.toValuationSubring
    rw [e.symm.commutes]
    exact R.algebraMap_mem c

@[simp]
theorem mem_transportDVR (e : K ≃ₐ[k] L)
    (R : FunctionFieldDVR k K) (x : L) :
    x ∈ (transportDVR e R).toValuationSubring ↔
      e.symm x ∈ R.toValuationSubring :=
  Iff.rfl

@[simp]
theorem transportDVR_apply_mem (e : K ≃ₐ[k] L)
    (R : FunctionFieldDVR k K) (x : K) :
    e x ∈ (transportDVR e R).toValuationSubring ↔
      x ∈ R.toValuationSubring := by
  change e.symm (e x) ∈ R.toValuationSubring ↔ x ∈ R.toValuationSubring
  simp

/-- The transported valuation ring is a `k`-algebra equivalent copy of the
source valuation ring. -/
def transportDVRAlgEquiv (e : K ≃ₐ[k] L)
    (R : FunctionFieldDVR k K) :
    R.toValuationSubring ≃ₐ[k] (transportDVR e R).toValuationSubring where
  toFun x := ⟨e (x : K), (transportDVR_apply_mem e R x).2 x.2⟩
  invFun y := ⟨e.symm y, y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add e (x : K) (y : K))
  commutes' c := Subtype.ext (e.commutes c)

@[simp]
private theorem transportDVR_symm_transportDVR (e : K ≃ₐ[k] L)
    (R : FunctionFieldDVR k K) :
    transportDVR e.symm (transportDVR e R) = R := by
  apply FunctionFieldDVR.ext
  intro x
  change e.symm (e x) ∈ R.toValuationSubring ↔ x ∈ R.toValuationSubring
  simp

@[simp]
private theorem transportDVR_transportDVR_symm (e : K ≃ₐ[k] L)
    (R : FunctionFieldDVR k L) :
    transportDVR e (transportDVR e.symm R) = R := by
  apply FunctionFieldDVR.ext
  intro x
  change e (e.symm x) ∈ R.toValuationSubring ↔ x ∈ R.toValuationSubring
  simp

/-- Function-field DVRs are transported bijectively by a field equivalence. -/
private def dvrEquiv (e : K ≃ₐ[k] L) :
    FunctionFieldDVR k K ≃ FunctionFieldDVR k L where
  toFun := transportDVR e
  invFun := transportDVR e.symm
  left_inv := transportDVR_symm_transportDVR e
  right_inv := transportDVR_transportDVR_symm e

/-- The induced equivalence of valuation spaces. -/
private def valuationSpaceEquiv (e : K ≃ₐ[k] L) :
    ValuationSpace k K ≃ ValuationSpace k L :=
  (ValuationSpace.of k K).symm.trans ((dvrEquiv e).trans (ValuationSpace.of k L))

private theorem continuous_valuationSpaceEquiv (e : K ≃ₐ[k] L) :
    Continuous (valuationSpaceEquiv e) := by
  rw [continuous_def]
  intro U hU
  rw [ValuationSpace.isOpen_iff] at hU ⊢
  rcases hU with rfl | hU
  · exact Or.inl (preimage_empty)
  · right
    rw [← preimage_compl]
    exact hU.preimage (valuationSpaceEquiv e).injective.injOn

/-- The induced homeomorphism of cofinite valuation spaces. -/
def valuationSpaceHomeomorph (e : K ≃ₐ[k] L) :
    ValuationSpace k K ≃ₜ ValuationSpace k L where
  __ := valuationSpaceEquiv e
  continuous_toFun := continuous_valuationSpaceEquiv e
  continuous_invFun := by
    convert continuous_valuationSpaceEquiv e.symm using 1
    ext R
    rfl

/-- On points, the valuation-space homeomorphism is exactly transport of the
underlying function-field DVR. -/
@[simp]
theorem valuationSpaceHomeomorph_apply (e : K ≃ₐ[k] L)
    (R : ValuationSpace k K) :
    (ValuationSpace.of k L).symm (valuationSpaceHomeomorph e R) =
      transportDVR e ((ValuationSpace.of k K).symm R) :=
  rfl

/-- Two morphisms from a local `k`-algebra to the algebraically closed base
field coincide. -/
private theorem algHom_to_baseField_unique
    {R : Type*} [CommRing R] [Algebra k R] [IsLocalRing R]
    (f g : R →ₐ[k] k) : f = g := by
  have hf : Function.Surjective f := fun c ↦
    ⟨algebraMap k R c, f.commutes c⟩
  have hg : Function.Surjective g := fun c ↦
    ⟨algebraMap k R c, g.commutes c⟩
  have hker : RingHom.ker f.toRingHom = RingHom.ker g.toRingHom :=
    (IsLocalRing.ker_eq_maximalIdeal f.toRingHom hf).trans
      (IsLocalRing.ker_eq_maximalIdeal g.toRingHom hg).symm
  ext x
  have hx : x - algebraMap k R (g x) ∈ RingHom.ker g.toRingHom := by
    rw [RingHom.mem_ker]
    simp
  rw [← hker, RingHom.mem_ker] at hx
  exact sub_eq_zero.mp (by simpa using hx)

/-- Canonical residue evaluation commutes with transport of a DVR. -/
private theorem residueAt_transportDVR [IsAlgClosed k]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType k L]
    (hK : Algebra.trdeg k K = 1) (hL : Algebra.trdeg k L = 1)
    (e : K ≃ₐ[k] L) (R : FunctionFieldDVR k K)
    (x : R.toValuationSubring) :
    FunctionFieldDVR.residueAt hL (transportDVR e R)
        (transportDVRAlgEquiv e R x) =
      FunctionFieldDVR.residueAt hK R x := by
  let f : R.toValuationSubring →ₐ[k] k :=
    (FunctionFieldDVR.residueAt hL (transportDVR e R)).comp
      (transportDVRAlgEquiv e R).toAlgHom
  have h := algHom_to_baseField_unique f
    (FunctionFieldDVR.residueAt hK R)
  exact DFunLike.congr_fun h x

private theorem valuationSpace_univ_nonempty [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (hK : Algebra.trdeg k K = 1) :
    ((⊤ : Opens (ValuationSpace k K)) : Set (ValuationSpace k K)).Nonempty := by
  let _ : Infinite (FunctionFieldDVR k K) :=
    FunctionFieldDVR.infinite_of_trdeg_eq_one hK
  exact Set.univ_nonempty

/-- The abstract nonsingular curve carried by the entire valuation space of a
one-dimensional function field. -/
noncomputable def abstractNonsingularCurveOfFunctionField [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (hK : Algebra.trdeg k K = 1) : Variety k :=
  abstractNonsingularCurve hK (⊤ : Opens (ValuationSpace k K))
    (valuationSpace_univ_nonempty hK)

/-- The homeomorphism on valuation spaces, restricted to their top opens. -/
private def abstractCurveTopHomeomorph [IsAlgClosed k]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType k L]
    (hK : Algebra.trdeg k K = 1) (hL : Algebra.trdeg k L = 1)
    (e : K ≃ₐ[k] L) :
    (abstractNonsingularCurveOfFunctionField hK).carrier ≃ₜ
      (abstractNonsingularCurveOfFunctionField hL).carrier := by
  change (↥(⊤ : Opens (ValuationSpace k K))) ≃ₜ
    ↥(⊤ : Opens (ValuationSpace k L))
  let h := valuationSpaceHomeomorph e
  exact {
    toFun := fun R ↦ ⟨h R.1, trivial⟩
    invFun := fun R ↦ ⟨h.symm R.1, trivial⟩
    left_inv := fun R ↦ Subtype.ext (h.symm_apply_apply R.1)
    right_inv := fun R ↦ Subtype.ext (h.apply_symm_apply R.1)
    continuous_toFun := (h.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (h.symm.continuous.comp continuous_subtype_val).subtype_mk _
  }

/-- An equivalence of function fields induces a morphism between their full
abstract valuation curves.  The proof of regularity transports the representing
rational function through the inverse field equivalence and uses compatibility
of the canonical residue maps. -/
noncomputable def abstractNonsingularCurveHomOfAlgEquiv [IsAlgClosed k]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType k L]
    (hK : Algebra.trdeg k K = 1) (hL : Algebra.trdeg k L = 1)
    (e : K ≃ₐ[k] L) :
    VarietyHom
      (abstractNonsingularCurveOfFunctionField hK)
      (abstractNonsingularCurveOfFunctionField hL) := by
  let h := abstractCurveTopHomeomorph hK hL e
  refine {
    toFun := h
    continuous_toFun := h.continuous
    regular_comp := ?_
  }
  intro V g hg
  change (fun w : pushOpens (⊤ : Opens (ValuationSpace k L)) V ↦
      g (ofPush w)) ∈
    regularFunctions hL
      (pushOpens (⊤ : Opens (ValuationSpace k L)) V :
        Set (ValuationSpace k L)) at hg
  change (fun w : pushOpens (⊤ : Opens (ValuationSpace k K))
      (Opens.comap ⟨h, h.continuous⟩ V) ↦
        g ⟨h (ofPush w).1, (ofPush w).2⟩) ∈
    regularFunctions hK
      (pushOpens (⊤ : Opens (ValuationSpace k K))
        (Opens.comap ⟨h, h.continuous⟩ V) : Set (ValuationSpace k K))
  rw [regularFunctions, AlgHom.mem_range] at hg ⊢
  obtain ⟨q, hq⟩ := hg
  let W : Opens
      (abstractNonsingularCurveOfFunctionField hK).carrier :=
    Opens.comap ⟨h, h.continuous⟩ V
  let p : regularRationalFunctions (k := k) (K := K)
      (pushOpens (⊤ : Opens (ValuationSpace k K)) W) :=
    ⟨e.symm q.1, by
      rw [mem_regularRationalFunctions_iff]
      intro R
      let x : W := ofPush R
      let z : V := ⟨h x.1, x.2⟩
      let S : pushOpens (⊤ : Opens (ValuationSpace k L)) V := toPush z
      have hqS := mem_regularRationalFunctions_iff.mp q.2 S
      change q.1 ∈ (transportDVR e
        ((ValuationSpace.of k K).symm R.1)).toValuationSubring at hqS
      exact (mem_transportDVR e ((ValuationSpace.of k K).symm R.1) q.1).mp hqS⟩
  refine ⟨p, ?_⟩
  funext R
  let x : W := ofPush R
  let z : V := ⟨h x.1, x.2⟩
  let S : pushOpens (⊤ : Opens (ValuationSpace k L)) V := toPush z
  let R₀ : FunctionFieldDVR k K := (ValuationSpace.of k K).symm R.1
  have hp : e.symm q.1 ∈ R₀.toValuationSubring :=
    mem_regularRationalFunctions_iff.mp p.2 R
  have hqS : q.1 ∈ (transportDVR e R₀).toValuationSubring :=
    (mem_transportDVR e R₀ q.1).2 hp
  have heq : transportDVRAlgEquiv e R₀ ⟨e.symm q.1, hp⟩ =
      ⟨q.1, hqS⟩ := by
    apply Subtype.ext
    exact e.apply_symm_apply q.1
  calc
    residueEvaluation hK
        (pushOpens (⊤ : Opens (ValuationSpace k K)) W :
          Set (ValuationSpace k K)) p R =
        FunctionFieldDVR.residueAt hK R₀ ⟨e.symm q.1, hp⟩ := rfl
    _ = FunctionFieldDVR.residueAt hL (transportDVR e R₀)
        (transportDVRAlgEquiv e R₀ ⟨e.symm q.1, hp⟩) :=
      (residueAt_transportDVR hK hL e R₀ ⟨e.symm q.1, hp⟩).symm
    _ = FunctionFieldDVR.residueAt hL (transportDVR e R₀) ⟨q.1, hqS⟩ := by
      rw [heq]
    _ = residueEvaluation hL
        (pushOpens (⊤ : Opens (ValuationSpace k L)) V :
          Set (ValuationSpace k L)) q S := rfl
    _ = g z := congrFun hq S

/-- The underlying valuation-space point of the induced curve morphism is the
homeomorphic transport of the source point. -/
@[simp]
theorem abstractNonsingularCurveHomOfAlgEquiv_apply [IsAlgClosed k]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType k L]
    (hK : Algebra.trdeg k K = 1) (hL : Algebra.trdeg k L = 1)
    (e : K ≃ₐ[k] L)
    (R : (abstractNonsingularCurveOfFunctionField hK).carrier) :
    (abstractNonsingularCurveHomOfAlgEquiv hK hL e R).1 =
      valuationSpaceHomeomorph e R.1 :=
  rfl

/-- **Field-equivalence invariance of the abstract valuation curve.**

The displayed morphism is an isomorphism of varieties, hence pulls regular
functions back in both directions.  The two further conclusions expose the
underlying transport needed by Theorem 6.9: membership in the transported DVR
is detected by applying `e.symm`, and canonical residue evaluation commutes
with the resulting local-ring equivalence. -/
theorem abstractNonsingularCurveIsoOfAlgEquiv [IsAlgClosed k]
    [Algebra.EssFiniteType k K] [Algebra.EssFiniteType k L]
    (hK : Algebra.trdeg k K = 1) (hL : Algebra.trdeg k L = 1)
    (e : K ≃ₐ[k] L) :
    (abstractNonsingularCurveHomOfAlgEquiv hK hL e).IsIso ∧
      (∀ (R : (abstractNonsingularCurveOfFunctionField hK).carrier) (x : K),
        e x ∈ ((ValuationSpace.of k L).symm
            ((abstractNonsingularCurveHomOfAlgEquiv hK hL e R).1)).toValuationSubring ↔
          x ∈ ((ValuationSpace.of k K).symm R.1).toValuationSubring) ∧
      (∀ (R : (abstractNonsingularCurveOfFunctionField hK).carrier) (x : K)
          (hx : x ∈ ((ValuationSpace.of k K).symm R.1).toValuationSubring)
          (hy : e x ∈ ((ValuationSpace.of k L).symm
            ((abstractNonsingularCurveHomOfAlgEquiv hK hL e R).1)).toValuationSubring),
        FunctionFieldDVR.residueAt hL
            ((ValuationSpace.of k L).symm
              ((abstractNonsingularCurveHomOfAlgEquiv hK hL e R).1))
            ⟨e x, hy⟩ =
          FunctionFieldDVR.residueAt hK
            ((ValuationSpace.of k K).symm R.1) ⟨x, hx⟩) := by
  let f := abstractNonsingularCurveHomOfAlgEquiv hK hL e
  let g := abstractNonsingularCurveHomOfAlgEquiv hL hK e.symm
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨g, ?_, ?_⟩
    · apply VarietyHom.ext
      funext R
      apply Subtype.ext
      change valuationSpaceEquiv e.symm (valuationSpaceEquiv e R.1) = R.1
      change ValuationSpace.of k K
          (transportDVR e.symm
            ((ValuationSpace.of k L).symm
              (ValuationSpace.of k L
                (transportDVR e ((ValuationSpace.of k K).symm R.1))))) = R.1
      rw [ValuationSpace.of_symm_apply_apply,
        transportDVR_symm_transportDVR]
      rfl
    · apply VarietyHom.ext
      funext R
      apply Subtype.ext
      change valuationSpaceEquiv e (valuationSpaceEquiv e.symm R.1) = R.1
      change ValuationSpace.of k L
          (transportDVR e
            ((ValuationSpace.of k K).symm
              (ValuationSpace.of k K
                (transportDVR e.symm ((ValuationSpace.of k L).symm R.1))))) = R.1
      rw [ValuationSpace.of_symm_apply_apply,
        transportDVR_transportDVR_symm]
      rfl
  · intro R x
    change e x ∈ (transportDVR e
        ((ValuationSpace.of k K).symm R.1)).toValuationSubring ↔
      x ∈ ((ValuationSpace.of k K).symm R.1).toValuationSubring
    exact transportDVR_apply_mem e _ x
  · intro R x hx hy
    let R₀ : FunctionFieldDVR k K := (ValuationSpace.of k K).symm R.1
    change FunctionFieldDVR.residueAt hL (transportDVR e R₀) ⟨e x, hy⟩ =
      FunctionFieldDVR.residueAt hK R₀ ⟨x, hx⟩
    have hres := residueAt_transportDVR hK hL e R₀ (⟨x, hx⟩ : R₀.toValuationSubring)
    calc
      FunctionFieldDVR.residueAt hL (transportDVR e R₀) ⟨e x, hy⟩ =
          FunctionFieldDVR.residueAt hL (transportDVR e R₀)
            (transportDVRAlgEquiv e R₀ ⟨x, hx⟩) := by
        apply congrArg (FunctionFieldDVR.residueAt hL (transportDVR e R₀))
        apply Subtype.ext
        rfl
      _ = FunctionFieldDVR.residueAt hK R₀ ⟨x, hx⟩ := hres

end ValuationSpace

end

end Hartshorne
