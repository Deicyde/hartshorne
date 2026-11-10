/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SectionsWithSupport

/-!
# Quasi-coherence of sections with support

Hartshorne, *Algebraic Geometry*, II, Exercise 5.6(e) (p. 124).

Let `X` be a Noetherian scheme and `Z ⊆ X` closed. If `F` is quasi-coherent, the sheaf `Γ_Z(F)` of
sections supported in `Z` is quasi-coherent (`Hartshorne.isQuasicoherent_sectionsWithSupport`);
if `F` is coherent, so is `Γ_Z(F)` (`Hartshorne.isCoherent_sectionsWithSupport`).

## Proof

Quasi-coherence is checked with the criterion `isQuasicoherent_of_pow_smul` on affine opens `U`
and basic opens `D(g) ⊆ U`. A supported section of `F` over `D(g)` times some `gᵐ` extends to a
section `u` of `F` over `U` (`F` is quasi-coherent), whose restriction to `D(g)` is supported in
`Z`. Some `gᵏ u` is then supported in `Z` (`exists_pow_smul_isSupportedIn`): every point of
`U \ Z` has a basic neighbourhood `D(c) ⊆ U \ Z` on which `u` vanishes after restriction to
`D(c) ∩ D(g)`, so some power of `g` kills `u|_{D(c)}`. Since `U \ Z` is quasi-compact (`X` is
Noetherian), finitely many such `D(c)` cover it, and one power of `g` works for all of them.

Coherence follows because `Γ_Z(F)` is a quasi-coherent submodule sheaf of the coherent `F`
(`isCoherent_of_le`).
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

open ArtinReesKernelSheaf

variable {X : Scheme.{u}} {F : X.Modules} {Z : Set X}

/-- If the restriction of `u ∈ F(U)` to `D(g)` is supported in the closed set `Z`, every point
`x ∈ U \ Z` has a basic neighbourhood `D(c) ⊆ U \ Z` on which some `gᵏ u` vanishes. -/
theorem exists_basicOpen_pow_smul_res_eq_zero [F.IsQuasicoherent] (hZ : IsClosed Z)
    (U : X.affineOpens) (g : Γ(X, U)) (u : Γ(F, U))
    (hu : IsSupportedIn F Z (res F (X.basicOpen_le g) u)) (x : X) (hxU : x ∈ (U : X.Opens))
    (hxZ : x ∉ Z) :
    ∃ (c : Γ(X, U)) (k : ℕ), x ∈ X.basicOpen c ∧ (X.basicOpen c : Set X) ⊆ Zᶜ ∧
      res F (X.basicOpen_le c) (g ^ k • u) = 0 := by
  obtain ⟨c, hcZ, hxc⟩ := U.2.exists_basicOpen_le (V := ⟨Zᶜ, hZ.isOpen_compl⟩) ⟨x, hxZ⟩ hxU
  let g' : Γ(X, X.basicOpen c) := X.presheaf.map (homOfLE (X.basicOpen_le c)).op g
  have h0 : res F (X.basicOpen_le g') (res F (X.basicOpen_le c) u) = 0 := by
    refine TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ _ _ _ fun y hy => ?_
    rw [map_zero]
    have hyc : y ∈ X.basicOpen c := X.basicOpen_le g' hy
    have hyg : y ∈ X.basicOpen g := by
      have h := hy
      rw [Scheme.basicOpen_res] at h
      exact h.2
    have h1 := (isSupportedIn_iff _).1 hu y hyg (hcZ hyc)
    rw [res_apply, TopCat.Presheaf.germ_res_apply] at h1
    rw [res_res, res_apply, TopCat.Presheaf.germ_res_apply]
    exact h1
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero_of_isAffineOpen F (X.affineBasicOpen c).2 g' _ h0
  refine ⟨c, k, hxc, hcZ, ?_⟩
  rw [LinearMap.map_smulₛₗ, map_pow]
  exact hk

/-- On a Noetherian scheme, if the restriction of `u ∈ F(U)` to a basic open `D(g)` of the affine
open `U` is supported in the closed set `Z`, then some `gᵏ u` is supported in `Z`. -/
theorem exists_pow_smul_isSupportedIn [IsNoetherian X] [F.IsQuasicoherent] (hZ : IsClosed Z)
    (U : X.affineOpens) (g : Γ(X, U)) (u : Γ(F, U))
    (hu : IsSupportedIn F Z (res F (X.basicOpen_le g) u)) :
    ∃ k : ℕ, IsSupportedIn F Z (g ^ k • u) := by
  let S : Set X := ((U : X.Opens) : Set X) \ Z
  choose c k hxc _ hk using fun x : S =>
    exists_basicOpen_pow_smul_res_eq_zero hZ U g u hu x.1 x.2.1 x.2.2
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact S).elim_finite_subcover
    (fun x : S => (X.basicOpen (c x) : Set X)) (fun _ => (X.basicOpen _).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxc ⟨x, hx⟩⟩)
  refine ⟨t.sup k, (isSupportedIn_iff _).2 fun x hx hxZ => ?_⟩
  obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, x ∈ X.basicOpen (c i) := by
    simpa using ht (show x ∈ S from ⟨hx, hxZ⟩)
  have hle : k i ≤ t.sup k := Finset.le_sup hi
  have h0 : F.presheaf.germ (U : X.Opens) x hx (g ^ k i • u) = 0 := by
    rw [← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (X.basicOpen_le (c i))) x hxi]
    exact (congrArg (F.presheaf.germ _ x hxi) (hk i)).trans (map_zero _)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, schemeModules_germ_smul, h0]
  exact smul_zero _

variable (F)

/-- **Sections with support are quasi-coherent** (Hartshorne II, Exercise 5.6(e)). On a
Noetherian scheme `X`, for a closed subset `Z` and a quasi-coherent `𝒪_X`-module `F`, the sheaf
`Γ_Z(F)` of sections of `F` supported in `Z` is quasi-coherent. -/
theorem isQuasicoherent_sectionsWithSupport [IsNoetherian X] [F.IsQuasicoherent]
    (hZ : IsClosed Z) : (sectionsWithSupport F Z).IsQuasicoherent := by
  refine isQuasicoherent_of_pow_smul _ (fun U g s hs => ?_) (fun U g t => ?_)
  · let s' : (supportSubmodule F Z).obj (op (U : X.Opens)) := s
    have hs' := congrArg (fun x : (supportSubmodule F Z).obj (op (X.basicOpen g)) => x.1) hs
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_isAffineOpen F U.2 g s'.1 hs'
    exact ⟨m, Subtype.ext hm⟩
  · let t' : (supportSubmodule F Z).obj (op (X.basicOpen g)) := t
    obtain ⟨m, u, hu⟩ := exists_pow_smul_extension_of_isAffineOpen F U.2 g t'.1
    have hsupp : IsSupportedIn F Z (res F (X.basicOpen_le g) u) := by
      rw [res_apply, hu]
      exact t'.2.smul _
    obtain ⟨k, hk⟩ := exists_pow_smul_isSupportedIn hZ U g u hsupp
    refine ⟨k + m, (⟨g ^ k • u, hk⟩ : (supportSubmodule F Z).obj (op (U : X.Opens))),
      Subtype.ext ((LinearMap.map_smulₛₗ (res F (X.basicOpen_le g)) _ u).trans ?_)⟩
    rw [map_pow, res_apply, hu]
    exact (smul_smul _ _ _).trans
      (congrArg (fun r => r • @id Γ(F, X.basicOpen g) t'.1) (pow_add _ k m).symm)

/-- **Sections with support are coherent** (Hartshorne II, Exercise 5.6(e)). On a Noetherian
scheme `X`, for a closed subset `Z` and a coherent `𝒪_X`-module `F`, the sheaf `Γ_Z(F)` of
sections of `F` supported in `Z` is coherent. -/
theorem isCoherent_sectionsWithSupport [IsNoetherian X] (hF : IsCoherent F) (hZ : IsClosed Z) :
    IsCoherent (sectionsWithSupport F Z) := by
  have h4F := ((coherent_affine_local_tfae F).out 0 3).mp hF
  have : F.IsQuasicoherent := ((quasicoherent_affine_local_tfae _).out 2 0).mp fun U =>
    (h4F U).2
  have : (toModules (supportSubmodule F Z) (isLocal_supportSubmodule F Z)).IsQuasicoherent :=
    isQuasicoherent_sectionsWithSupport F hZ
  exact isCoherent_of_le (isLocal_supportSubmodule F Z) isLocal_top le_top (isCoherent_top hF)

end Hartshorne
