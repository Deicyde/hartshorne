/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Nonsingular.AffineSingularLocus
import Hartshorne.Nonsingular.LocalRingOpen

/-!
# Closedness of the singular locus

Hartshorne, *Algebraic Geometry*, I.5, proof of Theorem 5.3 (p. 33).

The singular locus is closed on every variety carrying an affine-open-basis
witness.  On an affine chart, closedness is transported from a concrete affine
presentation along a variety isomorphism.  The chartwise results glue because
closedness can be checked after pulling back along an open cover, and local
rings are unchanged on restriction to an open neighbourhood.
-/

namespace Hartshorne

open TopologicalSpace

universe u

variable {k : Type u} [Field k]

namespace Variety

/-- Closedness of the singular locus transports backward along a variety
isomorphism. -/
theorem isClosed_singularLocus_of_isIso {X Z : Variety k}
    {f : VarietyHom X Z} (hf : f.IsIso)
    (hZ : IsClosed Z.SingularLocus) : IsClosed X.SingularLocus := by
  have heq : X.SingularLocus = f ⁻¹' Z.SingularLocus := by
    ext P
    simp only [SingularLocus, Set.mem_ofPred_eq, Set.mem_preimage]
    exact not_congr (nonsingularAt_iff_of_isIso hf P)
  rw [heq]
  exact hZ.preimage f.continuous_toFun

/-- A variety isomorphic to a concrete affine variety has closed singular
locus. -/
theorem IsAffine.isClosed_singularLocus {X : Variety k} [IsAlgClosed k]
    (hX : X.IsAffine) : IsClosed X.SingularLocus := by
  obtain ⟨σ, hσ, Z, hZ, φ, hφ⟩ := hX
  let _ : Finite σ := hσ
  exact isClosed_singularLocus_of_isIso hφ (isClosed_affineSingularLocus hZ)

/-- If affine opens form a basis on a variety, then its singular locus is
closed. -/
theorem HasAffineOpenBasis.isClosed_singularLocus
    {X : Variety k} [IsAlgClosed k] (hX : X.HasAffineOpenBasis) :
    IsClosed X.SingularLocus := by
  classical
  choose V hV hPV _hVU hAff using fun x => hX ⊤ x trivial
  have hcover : IsOpenCover V := by
    apply IsOpenCover.of_sets (fun x => (V x).isOpen)
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x, hPV x⟩
  apply hcover.isClosed_iff_coe_preimage.mpr
  intro x
  have heq :
      ((↑) ⁻¹' X.SingularLocus : Set (V x)) =
        (X.restrict (V x) (hV x)).SingularLocus := by
    ext P
    change (¬ X.NonsingularAt P.1) ↔
      ¬ (X.restrict (V x) (hV x)).NonsingularAt P
    exact not_congr (nonsingularAt_restrict_iff P).symm
  rw [heq]
  exact (hAff x).isClosed_singularLocus

end Variety

end Hartshorne
