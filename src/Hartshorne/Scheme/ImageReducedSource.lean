/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ReducedInducedSmallest

/-!
# The scheme-theoretic image of a reduced source

Hartshorne, *Algebraic Geometry*, II, Exercise 3.11(d) (p. 92), reduced-source clause.

Let `f : Z ⟶ X` be a morphism of schemes with `Z` reduced. The scheme-theoretic image of `f`
(Mathlib's `AlgebraicGeometry.Scheme.Hom.image`, the closed subscheme cut out by the kernel
ideal sheaf `f.ker`) is the reduced induced closed subscheme on the closure of `f(Z)`.

* `Hartshorne.ker_eq_vanishingIdeal_closure_range`: the kernel ideal sheaf of `f` is the
  vanishing ideal sheaf of the closure of the range of `f`.
* `Hartshorne.exists_image_iso_reducedInducedSubscheme`: the scheme-theoretic image is
  isomorphic over `X` to the reduced induced closed subscheme on that closure.

No quasi-compactness hypothesis is needed. The inclusion of the kernel in the vanishing ideal
holds for every morphism, since the range of `f` lies in the (closed) support of `f.ker`.
Conversely, a section `s` of `𝒪_X` over an affine open `U` vanishing on the closure of `f(Z)`
pulls back to a section of `𝒪_Z` over `f⁻¹(U)` whose basic open is empty; as `Z` is reduced,
the pullback is zero, so `s` lies in the kernel.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hartshorne

universe u

variable {Z X : Scheme.{u}}

/-- **Hartshorne II, Exercise 3.11(d)** (reduced source, ideal form). If `Z` is reduced, the
kernel ideal sheaf of `f : Z ⟶ X`, which defines its scheme-theoretic image, is the vanishing
ideal sheaf of the closure of `f(Z)`. -/
theorem ker_eq_vanishingIdeal_closure_range [IsReduced Z] (f : Z ⟶ X) :
    f.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range f), isClosed_closure⟩ := by
  apply le_antisymm
  · rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
    exact closure_minimal f.range_subset_ker_support f.ker.support.isClosed
  · refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U s hs => ?_
    rw [RingHom.mem_ker, ← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen,
      eq_bot_iff]
    intro z hz
    have hzU : f z ∈ (U : X.Opens) := X.basicOpen_le s hz
    have hmem : f z ∈ ((Scheme.IdealSheafData.vanishingIdeal
        ⟨closure (Set.range f), isClosed_closure⟩).support : Set X) ∩ (U : X.Opens) := by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact ⟨subset_closure ⟨z, rfl⟩, hzU⟩
    rw [Scheme.IdealSheafData.coe_support_inter] at hmem
    exact ((Scheme.mem_zeroLocus_iff _ _ _).mp hmem.1 s hs hz).elim

/-- **Hartshorne II, Exercise 3.11(d)** (reduced source). If `Z` is reduced, the
scheme-theoretic image of `f : Z ⟶ X` is, as a closed subscheme of `X`, the reduced induced
closed subscheme on the closure of `f(Z)`: there is an isomorphism between them commuting with
the closed immersions into `X`. -/
theorem exists_image_iso_reducedInducedSubscheme [IsReduced Z] (f : Z ⟶ X) :
    ∃ e : f.image ≅ reducedInducedSubscheme ⟨closure (Set.range f), isClosed_closure⟩,
      e.hom ≫ reducedInducedSubschemeι _ = f.imageι := by
  have h := ker_eq_vanishingIdeal_closure_range f
  refine ⟨⟨Scheme.IdealSheafData.inclusion h.ge, Scheme.IdealSheafData.inclusion h.le,
    (Scheme.IdealSheafData.inclusion_comp _ _).trans (Scheme.IdealSheafData.inclusion_id _),
    (Scheme.IdealSheafData.inclusion_comp _ _).trans (Scheme.IdealSheafData.inclusion_id _)⟩, ?_⟩
  exact Scheme.IdealSheafData.inclusion_subschemeι h.ge

end Hartshorne
