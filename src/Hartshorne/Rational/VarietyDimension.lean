/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.RationalMapFunctionFieldEquivalence
import Mathlib.Topology.KrullDimension

/-!
# Dimension and the function field of an abstract variety

For a variety with an affine-open basis, its topological dimension equals the
transcendence degree of its function field.  This extends the affine form of
Hartshorne I.3, Theorem 3.2(d), to the abstract variety interface used for
rational maps.

The key point is that every finite chain of irreducible closed subsets meets a
suitable affine neighbourhood of a point in its smallest member.  Thus an
affine-open basis controls the dimension of the whole variety.

## Main results

* `Hartshorne.Variety.HasAffineOpenBasis.exists_dimension_eq_trdeg`
* `Hartshorne.Variety.HasAffineOpenBasis.trdeg_eq_of_topologicalKrullDim_eq`
-/

namespace Hartshorne

open TopologicalSpace Topology

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace VarietyHom.IsIso

omit [IsAlgClosed k] in
/-- Isomorphic varieties have the same topological dimension. -/
theorem topologicalKrullDim_eq {X Y : Variety k} {f : VarietyHom X Y}
    (hf : f.IsIso) :
    topologicalKrullDim X.carrier = topologicalKrullDim Y.carrier := by
  obtain ⟨g, hgf, hfg⟩ := hf
  let e : X.carrier ≃ₜ Y.carrier := Homeomorph.mk
    { toFun := f
      invFun := g
      left_inv := fun x => by
        have h := congrArg (fun q : VarietyHom X X => q x) hgf
        simpa using h
      right_inv := fun y => by
        have h := congrArg (fun q : VarietyHom Y Y => q y) hfg
        simpa using h }
    f.continuous_toFun g.continuous_toFun
  exact IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph

end VarietyHom.IsIso

namespace Variety

/-- An affine presentation computes both the dimension of a variety and the
transcendence degree of its function field by the same natural number. -/
theorem IsAffine.exists_dimension_eq_trdeg {X : Variety k} (hX : X.IsAffine) :
    ∃ r : ℕ, topologicalKrullDim X.carrier = r ∧
      Algebra.trdeg k X.FunctionField = r := by
  obtain ⟨σ, hσ, Z, hZ, f, hf⟩ := hX
  let _ : Finite σ := hσ
  let _ : IsDomain (coordinateRing Z) := isDomain_coordinateRing hZ
  let _ : IsFractionRing (coordinateRing Z)
      (Hartshorne.FunctionField hZ.isIrreducible) :=
    isFractionRing_functionField hZ.isIrreducible
  let _ : Field (Hartshorne.FunctionField hZ.isIrreducible) :=
    IsFractionRing.toField (coordinateRing Z)
  obtain ⟨r, hdim, htr⟩ := exists_ringKrullDim_eq_trdeg k
    (coordinateRing Z) (Hartshorne.FunctionField hZ.isIrreducible)
  have hdimZ : dim Z = r := by
    rw [dim_eq_ringKrullDim_coordinateRing hZ.isAlgebraicSet, hdim]
  let e : Hartshorne.FunctionField hZ.isIrreducible ≃ₐ[k] X.FunctionField :=
    (RationalMapFunctionField.functionFieldAlgEquivAffine
      hZ.isQuasiAffineVariety).symm.trans
      (RationalMapFunctionField.functionFieldAlgEquivOfIsIso f hf)
  have htrX : Algebra.trdeg k X.FunctionField = r :=
    e.trdeg_eq.symm.trans htr
  refine ⟨r, ?_, htrX⟩
  exact (hf.topologicalKrullDim_eq.trans (dim_def Z).symm).trans hdimZ

omit [IsAlgClosed k] in
/-- Irreducible closed subsets of an open subspace are the irreducible closed
subsets of the ambient space that meet that open. -/
theorem topologicalKrullDim_open_eq_krullDim_meeting {X : Variety k}
    (U : Opens X.carrier) :
    topologicalKrullDim U =
      Order.krullDim {V : IrreducibleCloseds X.carrier |
        ((fun z : U => (z : X.carrier)) ⁻¹' (V : Set X.carrier)).Nonempty} :=
  Order.krullDim_eq_of_orderIso
    (IrreducibleCloseds.orderIsoOfIsOpenEmbedding
      (fun x : U => x.1) U.isOpen.isOpenEmbedding_subtypeVal)

/-- A variety with an affine-open basis has finite dimension, and that
dimension equals the transcendence degree of its function field. -/
theorem HasAffineOpenBasis.exists_dimension_eq_trdeg {X : Variety k}
    (hX : X.HasAffineOpenBasis) :
    ∃ r : ℕ, topologicalKrullDim X.carrier = r ∧
      Algebra.trdeg k X.FunctionField = r := by
  let x : X.carrier := X.nonempty.some
  obtain ⟨U, hU, -, -, hUaff⟩ := hX ⊤ x trivial
  obtain ⟨r, hUdim, hUtr⟩ := hUaff.exists_dimension_eq_trdeg
  let eU := RationalMapFunctionField.openFunctionFieldAlgEquiv X U hU
  have hXtr : Algebra.trdeg k X.FunctionField = r :=
    eU.trdeg_eq.trans hUtr
  refine ⟨r, ?_, hXtr⟩
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim]
    refine iSup_le fun l => ?_
    obtain ⟨p, hp⟩ := (l 0).isIrreducible.nonempty
    obtain ⟨W, hW, hpW, -, hWaff⟩ := hX ⊤ p trivial
    obtain ⟨d, hWdim, hWtr⟩ := hWaff.exists_dimension_eq_trdeg
    let eW := RationalMapFunctionField.openFunctionFieldAlgEquiv X W hW
    have hdr : d = r := by
      have hcard : (d : Cardinal) = r :=
        hWtr.symm.trans (eW.trdeg_eq.symm.trans hXtr)
      exact_mod_cast hcard
    have hmeet : ∀ m,
        ((fun z : W => z.1) ⁻¹' (l m : Set X.carrier)).Nonempty := by
      intro m
      refine ⟨⟨p, hpW⟩, ?_⟩
      exact l.monotone (Fin.zero_le m) hp
    have hchain : (l.length : WithBot ℕ∞) ≤ topologicalKrullDim W := by
      rw [topologicalKrullDim_open_eq_krullDim_meeting W]
      exact Order.LTSeries.length_le_krullDim
        ⟨l.length, fun m => ⟨l m, hmeet m⟩, fun m => l.step m⟩
    change topologicalKrullDim W = (d : WithBot ℕ∞) at hWdim
    rw [hWdim, hdr] at hchain
    exact hchain
  · rw [← hUdim]
    exact IsInducing.subtypeVal.topologicalKrullDim_le

/-- If a variety with an affine-open basis has dimension `r`, then its
function field has transcendence degree `r`. -/
theorem HasAffineOpenBasis.trdeg_eq_of_topologicalKrullDim_eq
    {X : Variety k} (hX : X.HasAffineOpenBasis) {r : ℕ}
    (hdim : topologicalKrullDim X.carrier = (r : WithBot ℕ∞)) :
    Algebra.trdeg k X.FunctionField = (r : Cardinal) := by
  obtain ⟨d, hd, htr⟩ := hX.exists_dimension_eq_trdeg
  have hdr : d = r := by
    exact_mod_cast hd.symm.trans hdim
  simpa [hdr] using htr

end Variety

end Hartshorne
