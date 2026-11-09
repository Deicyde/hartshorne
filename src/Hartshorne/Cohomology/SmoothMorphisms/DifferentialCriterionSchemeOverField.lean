/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.FlatFamilies.FlatEquidimensional
import Hartshorne.Scheme.Differentials.DifferentialCriterionField
import Hartshorne.Scheme.Differentials.RelativeDifferentialsAffineFibre
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The differential criterion for a scheme over a field

Let `Z` be a scheme of finite type over a field `K` and `n ∈ ℕ`. If every irreducible component
of `Z` has dimension `n` and every fibre `(Ω_{Z/K})_z ⊗ k(z)` has dimension at most `n`, then
`Z → Spec K` is smooth.

Smoothness is local on `Z`, so it suffices to show that `T = Γ(Z, V)` is smooth over `K` for every
affine open `V`. For a prime `q` of `T` with point `z ∈ Z`, equidimensionality and catenarity of
finite-type `K`-schemes give `dim 𝒪_{Z,z} + dim \overline{\{z\}} = n`, that is
`dim T_q + dim T ⧸ q = n`; and the fibre of `Ω_{Z/K}` at `z` is `κ(q) ⊗_T Ω_{T/K}`. The affine
differential criterion (`Hartshorne.smooth_of_forall_finrank_le`) then applies.

## Main result

* `Hartshorne.smooth_of_forall_topologicalKrullDim_eq_of_finrank_fibre_le`
-/

open AlgebraicGeometry CategoryTheory TensorProduct IsLocalRing Module Order

namespace Hartshorne

universe u

open FlatEquidimensional

/-- **The differential criterion for a scheme over a field.** Let `Z` be a scheme of finite type
over a field `K` and `n ∈ ℕ`. If every irreducible component of `Z` has dimension `n` and
`dim_{k(z)} ((Ω_{Z/K})_z ⊗ k(z)) ≤ n` for every `z ∈ Z`, then `Z → Spec K` is smooth. -/
theorem smooth_of_forall_topologicalKrullDim_eq_of_finrank_fibre_le {K : Type u} [Field K]
    {Z : Scheme.{u}} (s : Z ⟶ Spec (.of K)) (hs : FiniteType s) (n : ℕ)
    (hC : ∀ C ∈ irreducibleComponents Z, topologicalKrullDim C = n)
    (hΩ : ∀ z : Z, finrank (ResidueField (Z.presheaf.stalk z))
      (ResidueField (Z.presheaf.stalk z) ⊗[Z.presheaf.stalk z]
        (Scheme.relativeDifferentials s).presheaf.stalk z) ≤ n) :
    Smooth s := by
  have : LocallyOfFiniteType s := hs.1
  let eA := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  let : Field Γ(Spec (.of K), ⊤) := (eA.toMulEquiv.isField (Field.toIsField K)).toField
  let W : (Spec (.of K)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  refine HasRingHomProperty.of_iSup_eq_top (P := @Smooth) (fun V : Z.affineOpens => V)
    (iSup_affineOpens_eq_top Z) fun V => ?_
  let := (s.appLE ⊤ V le_top).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of K), ⊤) Γ(Z, (V : Z.Opens)) :=
    s.finiteType_appLE W.2 V.2 le_top
  change Algebra.Smooth _ _
  refine smooth_of_forall_finrank_le n fun q _ => ⟨?_, ?_⟩
  · rw [← finrank_fibre_relativeDifferentials_affine s V W le_top ⟨q, ‹_›⟩]
    exact hΩ _
  · let y : Spec Γ(Z, (V : Z.Opens)) := ⟨q, ‹_›⟩
    let z := V.2.fromSpec y
    have hsum := coheight_add_height_eq_of_equidim (catenaryAt_of_finiteType s hs)
      (exists_le_height_eq hC) z
    have : IsOpenImmersion V.2.fromSpec := V.2.isOpenImmersion_fromSpec
    have h1 : ringKrullDim (Γ(Z, (V : Z.Opens)) ⧸ q) = height z := by
      rw [height_apply_of_isOpenImmersion s hs V.2.fromSpec y]
      exact (height_spec_eq _ y).symm
    have hzV : z ∈ (V : Z.Opens) := V.2.range_fromSpec.le ⟨y, rfl⟩
    have h2 : ringKrullDim (Localization.AtPrime q) = coheight z := by
      let := TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨z, hzV⟩
      have : IsLocalization.AtPrime (Z.presheaf.stalk z) q := V.2.isLocalization_stalk' y hzV
      rw [← ringKrullDim_stalk_eq_coheight]
      exact ringKrullDim_eq_of_ringEquiv
        (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
          (Z.presheaf.stalk z)).toRingEquiv
    rw [h1, h2, ← WithBot.coe_add, hsum]
    rfl

end Hartshorne
