/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.StandardSmoothFieldDimension
import Hartshorne.Scheme.Regular
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The dense nonsingular locus

Hartshorne, *Algebraic Geometry*, II.8, Corollary 8.16 (p. 178): if `X` is a variety over an
algebraically closed field `k`, then the regular points of `X` contain a nonempty open dense
subset.

We prove this for an integral scheme locally of finite type over a perfect field. The set of
points at which `X → Spec k` is smooth is open and dense (Mathlib), and contains the generic
point. A scheme smooth over a field is regular at every point, since its local rings are
localizations of standard smooth algebras over the field.
-/

namespace Hartshorne

open AlgebraicGeometry CategoryTheory

universe u

/-- Every point of a scheme smooth over a field is regular. -/
theorem isRegularAt_of_smooth {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [Smooth g] (y : Y) : Y.IsRegularAt y := by
  obtain ⟨U, -, V, hV, hyV, e, hf⟩ := Smooth.exists_isStandardSmooth g y
  obtain rfl : U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = g y := Subsingleton.elim _ _
    rw [this]
    exact e hyV
  have hfield : IsField Γ(Spec (.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  let : Field Γ(Spec (.of k), ⊤) := hfield.toField
  let := (g.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Spec (.of k), ⊤) Γ(Y, V) := hf
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
  set t := hV.primeIdealOf ⟨y, hyV⟩
  have hreg := SubmersivePresentation.isRegularLocalRing_localization P t.asIdeal
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hyV⟩
  have := hV.isLocalization_stalk ⟨y, hyV⟩
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv t.asIdeal.primeCompl
    (Localization.AtPrime t.asIdeal) (Y.presheaf.stalk y)).toRingEquiv

/-- **Hartshorne II, Corollary 8.16.** If `X` is an integral scheme locally of finite type over a
perfect field `k`, then the regular points of `X` contain a nonempty open dense subset.
Hartshorne states this for a variety over an algebraically closed field; separatedness and
finite type beyond local finite type are not used, and perfectness of `k` suffices. -/
theorem exists_nonempty_dense_isRegularAt {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ Dense (U : Set X) ∧ ∀ x ∈ U, X.IsRegularAt x := by
  refine ⟨f.smoothLocus, ⟨_, f.genericPoint_mem_smoothLocus_of_perfectField⟩,
    f.dense_smoothLocus_of_perfectField, fun x hx ↦ ?_⟩
  have : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact Scheme.Opens.ι_preimage_self _
  have : IsRegularLocalRing (f.smoothLocus.toScheme.presheaf.stalk ⟨x, hx⟩) :=
    isRegularAt_of_smooth (f.smoothLocus.ι ≫ f) ⟨x, hx⟩
  exact IsRegularLocalRing.of_ringEquiv
    (Scheme.Opens.stalkIso f.smoothLocus ⟨x, hx⟩).commRingCatIsoToRingEquiv

end Hartshorne
