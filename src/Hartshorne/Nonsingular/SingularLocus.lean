/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Nonsingular.HypersurfaceSingularLocus
import Hartshorne.Nonsingular.SingularLocusClosed
import Hartshorne.Rational.BirationalHypersurface

/-!
# The singular locus is proper and closed

Hartshorne, *Algebraic Geometry*, I.5, Theorem 5.3 (p. 33).

For a separated variety with an affine-open basis, the singular locus is a
proper closed subset.  Closedness is local on the affine-open basis.  For
properness, the variety is replaced birationally by a projective hypersurface.
The hypersurface has a nonsingular point on its standard affine chart, and its
nonsingular locus is open.  Irreducibility makes that locus meet the open set
on which the birational equivalence is an isomorphism, allowing nonsingularity
to be transported back to the original variety.
-/

namespace Hartshorne

open TopologicalSpace

variable {k : Type} [Field k] [IsAlgClosed k]

namespace SeparatedVariety

/-- A separated variety with an affine-open basis has a nonsingular point. -/
theorem exists_nonsingularAt (X : SeparatedVariety.{0, 0} k)
    (hX : X.toVariety.HasAffineOpenBasis) :
    ∃ P : X.toVariety.carrier, X.toVariety.NonsingularAt P := by
  classical
  obtain ⟨r, hdim, -⟩ := hX.exists_dimension_eq_trdeg
  obtain ⟨f, hZ, hf, hH, -, -, hHdim, hbir⟩ :=
    exists_birational_projective_hypersurface X hX r hdim
  let Z := zeroSet ({f} : Set
    (MvPolynomial {j : Fin (r + 2) // j ≠ 0} k))
  let H := projectiveClosure (0 : Fin (r + 2)) Z
  let PH : Variety k := Variety.ofProjective hH
  let SH : SeparatedVariety k :=
    ⟨PH, isSeparated_ofQuasiProjective hH.isQuasiProjVariety⟩

  have hPHNonsingularOpen :
      IsOpen {P : PH.carrier | PH.NonsingularAt P} := by
    have hPHclosed : IsClosed PH.SingularLocus :=
      (Variety.hasAffineOpenBasis_ofProjective hH).isClosed_singularLocus
    simpa only [Variety.SingularLocus, Set.compl_ofPred, not_not] using
      hPHclosed.isOpen_compl

  have hPHNonsingularNonempty :
      Set.Nonempty {P : PH.carrier | PH.NonsingularAt P} := by
    let A : Variety k := Variety.ofQuasiAffine hZ.isQuasiAffineVariety
    have hdimZ : dim Z = (r : WithBot ℕ∞) :=
      (projDim_projectiveClosure (0 : Fin (r + 2)) hZ).symm.trans hHdim
    obtain ⟨q, hq⟩ :=
      exists_nonsingularAt_of_eq_zeroSet_irreducible_of_dim
        hZ rfl hf hdimZ (by simp)
    let hchart : (H ∩ standardChart (0 : Fin (r + 2))).Nonempty :=
      projectiveClosure_inter_standardChart_nonempty (0 : Fin (r + 2)) hZ
    let C : Opens PH.carrier :=
      projectiveChartOpen hH.isQuasiProjVariety (0 : Fin (r + 2))
    let hC : (C : Set PH.carrier).Nonempty :=
      projectiveChartOpen_nonempty hH.isQuasiProjVariety
        (0 : Fin (r + 2)) hchart
    let c : VarietyHom (PH.restrict C hC) A :=
      (projectiveClosureChartToAffineHom (0 : Fin (r + 2)) hZ).comp
        (restrictChartHom hH.isQuasiProjVariety
          (0 : Fin (r + 2)) hchart)
    have hc : c.IsIso :=
      (projectiveClosureChartToAffineHom_isIso
        (0 : Fin (r + 2)) hZ).comp
        (isIso_restrictChartHom hH.isQuasiProjVariety
          (0 : Fin (r + 2)) hchart)
    obtain ⟨p, hp⟩ := hc.bijective.surjective q
    have hpC : (PH.restrict C hC).NonsingularAt p := by
      apply (Variety.nonsingularAt_iff_of_isIso hc p).2
      rw [hp]
      exact hq
    exact ⟨p.1, (Variety.nonsingularAt_restrict_iff p).1 hpC⟩

  obtain ⟨U, hU, V, hV, g, hg⟩ :=
    (birational_iff_hasIsomorphicOpenSubsets X SH).1 hbir
  let N : Opens PH.carrier :=
    ⟨{P : PH.carrier | PH.NonsingularAt P}, hPHNonsingularOpen⟩
  have hN : (N : Set PH.carrier).Nonempty := hPHNonsingularNonempty
  obtain ⟨q, hq⟩ := Variety.opens_inter_nonempty hV hN
  have hqV : q ∈ V := hq.1
  have hqN : PH.NonsingularAt q := hq.2
  let qV : (PH.restrict V hV).carrier := ⟨q, hqV⟩
  obtain ⟨p, hp⟩ := hg.bijective.surjective qV
  have hqVnonsingular : (PH.restrict V hV).NonsingularAt qV :=
    (Variety.nonsingularAt_restrict_iff qV).2 hqN
  have hpUnonsingular : (X.toVariety.restrict U hU).NonsingularAt p := by
    apply (Variety.nonsingularAt_iff_of_isIso hg p).2
    simpa only [hp] using hqVnonsingular
  exact ⟨p.1, (Variety.nonsingularAt_restrict_iff p).1 hpUnonsingular⟩

/-- **Hartshorne I.5, Theorem 5.3.** The singular locus of a separated variety
with an affine-open basis is a proper closed subset; equivalently, the
nonsingular locus is nonempty and open. -/
theorem singularLocus_isProper (X : SeparatedVariety.{0, 0} k)
    (hX : X.toVariety.HasAffineOpenBasis) :
    IsClosed X.toVariety.SingularLocus ∧
      X.toVariety.SingularLocus ⊂ Set.univ ∧
      IsOpen {P | X.toVariety.NonsingularAt P} ∧
      Set.Nonempty {P | X.toVariety.NonsingularAt P} := by
  classical
  have hclosed : IsClosed X.toVariety.SingularLocus :=
    hX.isClosed_singularLocus
  obtain ⟨P, hP⟩ := X.exists_nonsingularAt hX
  have hproper : X.toVariety.SingularLocus ⊂ Set.univ := by
    rw [Set.ssubset_univ_iff]
    intro heq
    have hPSingular : P ∈ X.toVariety.SingularLocus := by
      rw [heq]
      exact Set.mem_univ P
    exact hPSingular hP
  have hopen : IsOpen {P | X.toVariety.NonsingularAt P} := by
    simpa only [Variety.SingularLocus, Set.compl_ofPred, not_not] using
      hclosed.isOpen_compl
  exact ⟨hclosed, hproper, hopen, ⟨P, hP⟩⟩

end SeparatedVariety

/-- Theorem 5.3 phrased directly for an abstract variety equipped with the two
structure witnesses used by the development. -/
theorem Variety.HasAffineOpenBasis.singularLocus_isProper
    {X : Variety.{0, 0} k} (hX : X.HasAffineOpenBasis)
    (hsep : X.IsSeparated) :
    IsClosed X.SingularLocus ∧
      X.SingularLocus ⊂ Set.univ ∧
      IsOpen {P | X.NonsingularAt P} ∧
      Set.Nonempty {P | X.NonsingularAt P} :=
  SeparatedVariety.singularLocus_isProper ⟨X, hsep⟩ hX

end Hartshorne
