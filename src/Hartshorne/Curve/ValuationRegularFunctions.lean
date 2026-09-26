/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.FinitePoles
import Hartshorne.Curve.ValuationResidueField
import Hartshorne.Curve.ValuationSpaceInfinitude
import Mathlib.Algebra.Algebra.Pi

/-!
# Regular functions on the valuation space

Hartshorne, *Algebraic Geometry*, I.6 (p. 42).

A rational function is regular on a subset of the valuation space when it
belongs to every valuation ring over that subset.  Taking its residue at each
point gives a function to the constant field.  We define regular functions to
be the image of this residue-evaluation map.

On a nonempty open subset the map is injective: a nonzero difference cannot
vanish at every point, since its zero set is finite whereas the open set is
infinite.  On the empty subset the rational-function algebra is all of `K` and
the image is the full algebra of functions on the empty type.
-/

namespace Hartshorne

open Set TopologicalSpace

noncomputable section

universe u v

namespace ValuationSpace

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Rational functions belonging to every valuation ring over `U`. -/
abbrev regularRationalFunctions (U : Set (ValuationSpace k K)) :
    Subalgebra k K :=
  ⨅ R : U, ((ValuationSpace.of k K).symm R.1).toSubalgebra

/-- Membership in the intersection algebra means membership in every
valuation ring over `U`. -/
theorem mem_regularRationalFunctions_iff
    {U : Set (ValuationSpace k K)} {x : K} :
    x ∈ regularRationalFunctions (k := k) (K := K) U ↔
      ∀ R : U, x ∈ ((ValuationSpace.of k K).symm R.1).toValuationSubring := by
  simp [regularRationalFunctions, FunctionFieldDVR.toSubalgebra]

/-- Inclusion of the intersection algebra into the valuation ring at one
point. -/
private def regularRationalFunctionsToValuationSubring
    (U : Set (ValuationSpace k K)) (R : U) :
    regularRationalFunctions (k := k) (K := K) U →ₐ[k]
      ((ValuationSpace.of k K).symm R.1).toValuationSubring where
  toFun f := ⟨f.1, mem_regularRationalFunctions_iff.mp f.2 R⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    apply Subtype.ext
    exact ((ValuationSpace.of k K).symm R.1).coe_algebraMap c

/-- Evaluate a rational function regular on `U` by taking its residue at every
valuation ring in `U`. -/
noncomputable def residueEvaluation [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Set (ValuationSpace k K)) :
    regularRationalFunctions (k := k) (K := K) U →ₐ[k] (U → k) :=
  AlgHom.pi fun R ↦
    (FunctionFieldDVR.residueAt htrdeg
      ((ValuationSpace.of k K).symm R.1)).comp
        (regularRationalFunctionsToValuationSubring U R)

@[simp]
theorem residueEvaluation_apply [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Set (ValuationSpace k K))
    (f : regularRationalFunctions (k := k) (K := K) U) (R : U) :
    residueEvaluation htrdeg U f R =
      FunctionFieldDVR.residueAt htrdeg
        ((ValuationSpace.of k K).symm R.1)
        ⟨f.1, mem_regularRationalFunctions_iff.mp f.2 R⟩ :=
  rfl

/-- The `k`-algebra of regular functions on `U`, realized as the image of
residue evaluation inside the function algebra `U → k`. -/
noncomputable def regularFunctions [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    (U : Set (ValuationSpace k K)) : Subalgebra k (U → k) :=
  (residueEvaluation htrdeg U).range

/-- Residue evaluation is injective on every nonempty open subset of the
valuation space. -/
theorem residueEvaluation_injective [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1)
    {U : Set (ValuationSpace k K)} (hU : IsOpen U) (hne : U.Nonempty) :
    Function.Injective (residueEvaluation htrdeg U) := by
  intro f g heval
  apply Subtype.ext
  by_contra hfg
  have hdiff : (f.1 - g.1 : K) ≠ 0 := sub_ne_zero.mpr hfg
  let Z : Set (ValuationSpace k K) :=
    {R | ((ValuationSpace.of k K).symm R).VanishesAt (f.1 - g.1)}
  have hZfinite : Z.Finite := by
    apply Set.Finite.preimage
      (s := {R : FunctionFieldDVR k K | R.VanishesAt (f.1 - g.1)})
      (ValuationSpace.of k K).symm.injective.injOn
    exact FunctionFieldDVR.finite_vanishesAt htrdeg hdiff
  have hUZ : U ⊆ Z := by
    intro R hRU
    let R' : U := ⟨R, hRU⟩
    let V := (ValuationSpace.of k K).symm R
    have hfmem : f.1 ∈ V.toValuationSubring :=
      mem_regularRationalFunctions_iff.mp f.2 R'
    have hgmem : g.1 ∈ V.toValuationSubring :=
      mem_regularRationalFunctions_iff.mp g.2 R'
    have hresidue : FunctionFieldDVR.residueAt htrdeg V
        (⟨f.1 - g.1, V.toValuationSubring.sub_mem hfmem hgmem⟩ :
          V.toValuationSubring) = 0 := by
      change FunctionFieldDVR.residueAt htrdeg V
          (⟨f.1, hfmem⟩ - ⟨g.1, hgmem⟩) = 0
      rw [map_sub]
      have hpoint := congrFun heval R'
      change FunctionFieldDVR.residueAt htrdeg V ⟨f.1, hfmem⟩ =
        FunctionFieldDVR.residueAt htrdeg V ⟨g.1, hgmem⟩ at hpoint
      rw [hpoint, sub_self]
    change V.VanishesAt (f.1 - g.1)
    rw [V.vanishesAt_iff_exists_mem_maximalIdeal]
    refine ⟨V.toValuationSubring.sub_mem hfmem hgmem, ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff]
    apply (FunctionFieldDVR.residueFieldEquiv htrdeg V).injective
    simpa [FunctionFieldDVR.residueAt] using hresidue
  have hUfinite : U.Finite := hZfinite.subset hUZ
  exact (ValuationSpace.infinite_of_isOpen_of_nonempty htrdeg hU hne) hUfinite

/-- On the empty subset, the intersection of the valuation rings is the whole
function field. -/
theorem regularRationalFunctions_empty :
    regularRationalFunctions (k := k) (K := K) ∅ = ⊤ := by
  simp [regularRationalFunctions]

/-- On the empty subset, every function to `k` is regular. -/
theorem regularFunctions_empty [IsAlgClosed k]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1) :
    regularFunctions htrdeg ∅ = ⊤ := by
  apply top_unique
  intro f _
  rw [regularFunctions, AlgHom.mem_range]
  refine ⟨0, ?_⟩
  funext R
  exact R.2.elim

end ValuationSpace

end

end Hartshorne
