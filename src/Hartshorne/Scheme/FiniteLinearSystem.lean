/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LinearSystemBase
import Hartshorne.Scheme.EffectiveCartierDivisor

/-!
# Finite-dimensional linear systems on an arbitrary scheme over a field

The setting of Hartshorne, *Algebraic Geometry*, III, Remark 10.9.2 (p. 275): a
finite-dimensional linear system `V ⊆ Γ(X, L)` of an invertible sheaf `L` on a scheme `X` over a
field `k`, with `X` not assumed projective. `V` is given by a spanning family `s₀, …, sₙ`
(a basis, when `ℙ(V)` is identified with `ℙⁿ_k`): `V = linearSystem q s` is the set of
combinations `∑ aᵢ sᵢ = linearSystemSection q s a`, `a ∈ kⁿ⁺¹`, where `q : X ⟶ Spec k` is the
structure morphism.

## Main definitions and results

The zero schemes `invertibleZeroIdeal hL s`, the base locus `baseLocusIdeal hL S` and the open
`linearSystemDomain hL s = X - B`, on which the `sᵢ` generate `L`, are set up in
`Hartshorne.Scheme.LinearSystemBase` (Hartshorne II.7). Here:

* `linearSystemMorphism q hL s : X - B ⟶ ℙⁿ_k`: the morphism defined (Hartshorne II,
  Theorem 7.1) by the `sᵢ|_{X - B}` (`existsUnique_linearSystemMorphism`,
  `linearSystemMorphism_spec`).
* `comap_invertibleZeroIdeal_linearSystemSection`: on `X - B`, the zero scheme of `∑ aᵢ sᵢ` is
  the pullback of the hyperplane `∑ aᵢ xᵢ = 0`.
* `isLocallyPrincipalNonZeroDivisor_invertibleZeroIdeal`,
  `exists_isEffective_idealSheafData_eq_invertibleZeroIdeal`: on an integral scheme the zero
  scheme of a nonzero section is an effective Cartier divisor. Nonsingularity is not needed, and
  on an integral scheme a section vanishing identically on a component is zero.

## Proof

The hyperplane clause follows from `Z(f^* t) = f⁻¹ Z(t)`: the isomorphism
`φ^* 𝒪(1) ≅ L|_{X - B}` of Theorem 7.1 carries `φ^*(∑ aᵢ xᵢ)` to `(∑ aᵢ sᵢ)|_{X - B}`. For the
Cartier clause, write `s = g e` on an affine open `U` on which `e` trivializes `L`, so that the
ideal of `Z(s)` over `U` is `(g)`. On an integral scheme `Γ(U, 𝒪_X)` is a domain for nonempty
`U`, and `g ≠ 0` because otherwise the open nonvanishing locus of `s` would miss the nonempty
open `U`, hence be empty, forcing `s = 0`.
-/
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

variable {X : Scheme.{u}} {L : X.Modules}

section LinearSystem

variable {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k)) {n : ℕ}

variable (hL : L.IsInvertible)

/-- Theorem 7.1(b) for the sections `sᵢ|_U` of `L|_U`. -/
theorem existsUnique_linearSystemMorphism (s : Fin (n + 1) → Γ(L, ⊤)) :
    ∃! φ : (linearSystemDomain hL s).toScheme ⟶
        projectiveSpaceOverScheme n (Spec (CommRingCat.of k)),
      φ ≫ projectiveSpaceOverSchemeProjection n _ = (linearSystemDomain hL s).ι ≫ q ∧
      ∃ e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅
          linearSystemTwist hL s,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) =
          linearSystemSections hL s i :=
  existsUnique_morphism_of_isGeneratedBySections _ (hL.pullback _)
    (linearSystemSections hL s) (isGeneratedBySections_linearSystemSections hL s)

/-- **The morphism `X - B ⟶ ℙⁿ_k` defined by the linear system** with spanning family
`s₀, …, sₙ` (Hartshorne II, Theorem 7.1): the unique `k`-morphism pulling `𝒪(1)` back to `L|_U`
with `xᵢ ↦ sᵢ|_U`. -/
def linearSystemMorphism (s : Fin (n + 1) → Γ(L, ⊤)) :
    (linearSystemDomain hL s).toScheme ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)) :=
  (existsUnique_linearSystemMorphism q hL s).exists.choose

/-- The defining property of `linearSystemMorphism`. -/
theorem linearSystemMorphism_spec (s : Fin (n + 1) → Γ(L, ⊤)) :
    linearSystemMorphism q hL s ≫ projectiveSpaceOverSchemeProjection n _ =
        (linearSystemDomain hL s).ι ≫ q ∧
      ∃ e : (Scheme.Modules.pullback (linearSystemMorphism q hL s)).obj
          (projectiveSpaceTwistingSheaf n _ 1) ≅ linearSystemTwist hL s,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (linearSystemMorphism q hL s)
          (projectiveSpaceCoordinate n _ i)) = linearSystemSections hL s i :=
  (existsUnique_linearSystemMorphism q hL s).exists.choose_spec

/-- **The zero scheme of `∑ aᵢ sᵢ` is the pullback of the hyperplane `∑ aᵢ xᵢ = 0`.** On
`U = X - B`, the zero scheme of the section `∑ aᵢ sᵢ` of `L` (restricted to `U`) equals, as a
closed subscheme of `U`, the preimage under `φ : U ⟶ ℙⁿ_k` of the zero scheme of the linear form
`∑ aᵢ xᵢ ∈ Γ(ℙⁿ_k, 𝒪(1))`. -/
theorem comap_invertibleZeroIdeal_linearSystemSection (s : Fin (n + 1) → Γ(L, ⊤))
    (a : Fin (n + 1) → k) :
    (invertibleZeroIdeal hL (linearSystemSection q s a)).comap (linearSystemDomain hL s).ι =
      (invertibleZeroIdeal (isInvertible_projectiveSpaceTwistingSheaf n _ 1)
        (linearSection k n a)).comap (linearSystemMorphism q hL s) := by
  obtain ⟨hφ, e, he⟩ := linearSystemMorphism_spec q hL s
  rw [← invertibleZeroIdeal_pullbackGlobalSection, ← invertibleZeroIdeal_pullbackGlobalSection,
    ← invertibleZeroIdeal_map_iso _ (hL.pullback _) e, iso_app_linearSection hφ e he,
    linearSystemSection, pullbackGlobalSection_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pullbackGlobalSection_smul, appTop_kConst]

end LinearSystem

section Cartier

variable (hL : L.IsInvertible)

/-- **On an integral scheme a nonzero section has an effective Cartier zero scheme**: its zero
ideal is locally generated by a single non-zero-divisor. -/
theorem isLocallyPrincipalNonZeroDivisor_invertibleZeroIdeal [IsIntegral X] {s : Γ(L, ⊤)}
    (hs : s ≠ 0) : (invertibleZeroIdeal hL s).IsLocallyPrincipalNonZeroDivisor := by
  intro x
  obtain ⟨U, e, hxU, hU, he⟩ := exists_isAffineOpen_isTrivializingSection hL x
  obtain ⟨g, hg⟩ := he.exists_eq_smul s
  refine ⟨⟨U, hU⟩, hxU, g, ?_, invertibleZeroIdeal_ideal_eq_span hL (U := ⟨U, hU⟩) he hg⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  apply hs
  refine eq_zero_of_forall_notMem_nonvanishingLocus hL fun y hy => ?_
  have h1 := he.nonvanishingLocus_inter_eq hg
  rw [X.basicOpen_zero] at h1
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (isOpen_nonvanishingLocus hL s) U.isOpen
    ⟨y, hy⟩ ⟨x, hxU⟩
  rw [h1] at hz
  exact hz

/-- **The zero scheme of a nonzero section on an integral scheme is an effective Cartier
divisor.** -/
theorem exists_isEffective_idealSheafData_eq_invertibleZeroIdeal [IsIntegral X] {s : Γ(L, ⊤)}
    (hs : s ≠ 0) :
    ∃ (D : X.CartierDivisor) (hD : D.IsEffective),
      Scheme.CartierDivisor.idealSheafData hD = invertibleZeroIdeal hL s :=
  Scheme.CartierDivisor.exists_idealSheafData_eq
    (isLocallyPrincipalNonZeroDivisor_invertibleZeroIdeal hL hs)

end Cartier

end Hartshorne
