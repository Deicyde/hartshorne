/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SectionsWithSupport
import Hartshorne.Cohomology.InjectiveLocalization
import Hartshorne.Cohomology.IdealPowerTorsionInjective
import Mathlib.Topology.Sheaves.Flasque

/-!
# The sheaf of an injective module is flasque

Hartshorne, *Algebraic Geometry*, III, Proposition 3.4 (pp. 214–215).

Let `A` be a Noetherian ring and `I` an injective `A`-module. Then `Ĩ` is flasque on `Spec A`
(`Hartshorne.tilde_isFlasque`).

Every section `s` of `Ĩ` over an open `U` extends to `Spec A`
(`Hartshorne.exists_extension_of_isSupportedIn`). The proof is by Noetherian induction on a
closed set `Y` containing the support of `s`. If `Y` meets `U`, choose `D(f) ⊆ U` meeting `Y`
and let `a` be the ideal of `Y`. The sections of `Ĩ` over `D(f)` supported in `Y` are the
localization `Γ_a(I)_f` of the supported global sections `Γ_a(I)`, and `Γ_a(I)` is injective,
so `Γ_a(I) → Γ_a(I)_f` is surjective (`Hartshorne.supportRestrict_basicOpen_surjective`). Hence
some global section `t` supported in `Y` agrees with `s` on `D(f)`, and `s - t|_U` is supported
in the smaller closed set `Y ∩ V(f)`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

open ArtinReesKernelSheaf

universe u

variable {R : CommRingCat.{u}} [IsNoetherianRing R] (I : ModuleCat.{u} R) [Module.Injective R I]

/-- Over a Noetherian ring, for an injective module `I`, every section of `Ĩ` over `D(f)`
supported in `V(a)` is the restriction of a global section supported in `V(a)`. -/
theorem supportRestrict_basicOpen_surjective (a : Ideal R) (f : R) :
    Function.Surjective (supportRestrict I a (PrimeSpectrum.basicOpen f)) := by
  have hJ : Module.Injective R (Ideal.primaryComponent I a) :=
    idealPowerTorsion_injective a inferInstance
  have hloc := isLocalizedModule_sectionsWithSupport_basicOpen I a f
  have hsurj := injectiveLocalizationMap_surjective R (Ideal.primaryComponent I a) f
  intro y
  obtain ⟨z, hz⟩ := (IsLocalizedModule.iso (Submonoid.powers f)
    (supportRestrict I a (PrimeSpectrum.basicOpen f) ∘ₗ
      (primaryComponentEquivSupport I a).toLinearMap)).surjective y
  obtain ⟨m, rfl⟩ := hsurj z
  refine ⟨primaryComponentEquivSupport I a m, ?_⟩
  rw [← hz, LocalizedModule.mkLinearMap_apply, IsLocalizedModule.iso_mk_one]
  rfl

/-- **Sections of `Ĩ` extend.** Over a Noetherian ring, for an injective module `I`, every
section of `Ĩ` over an open `U` supported in a closed set `Y` is the restriction of a global
section. -/
theorem exists_extension_of_isSupportedIn (Y : Closeds (Spec R)) :
    ∀ (U : (Spec R).Opens) (s : Γ(tilde I, U)), IsSupportedIn (tilde I) (Y : Set (Spec R)) s →
      ∃ t : Γ(tilde I, ⊤), res (tilde I) le_top t = s := by
  induction Y using WellFoundedLT.induction with
  | _ Y ih =>
  intro U s hs
  by_cases hYU : ∃ x ∈ (Y : Set (Spec R)), x ∈ U
  · obtain ⟨x, hxY, hxU⟩ := hYU
    obtain ⟨_, ⟨f, rfl⟩, hxf, hfU⟩ :=
      (Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hxU
    set a : Ideal R :=
      PrimeSpectrum.vanishingIdeal (show Set (PrimeSpectrum R) from (Y : Set (Spec R)))
    have hZ : PrimeSpectrum.zeroLocus (a : Set R) = (Y : Set (Spec R)) := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact Y.isClosed.closure_eq
    have hsf : res (tilde I) hfU s ∈ supportRSubmodule (M := I) a (PrimeSpectrum.basicOpen f) := by
      change IsSupportedIn _ _ _
      rw [hZ]
      exact hs.res hfU
    obtain ⟨⟨t, ht⟩, htf⟩ := supportRestrict_basicOpen_surjective I a f ⟨_, hsf⟩
    have htf' : res (tilde I) le_top t = res (tilde I) hfU s := congrArg Subtype.val htf
    have htY : IsSupportedIn (tilde I) (Y : Set (Spec R)) t := by
      rw [← hZ]
      exact ht
    let Y' : Closeds (Spec R) := ⟨(Y : Set (Spec R)) ∩ PrimeSpectrum.zeroLocus {f},
      Y.isClosed.inter (PrimeSpectrum.isClosed_zeroLocus _)⟩
    have hY' : Y' < Y := by
      refine lt_of_le_of_ne (fun y hy => hy.1) fun h => ?_
      have hx' : x ∈ (Y' : Set (Spec R)) := by rw [h]; exact hxY
      exact hxf (hx'.2 (Set.mem_singleton f))
    have hs' : IsSupportedIn (tilde I) (Y' : Set (Spec R)) (s - res (tilde I) le_top t) := by
      rw [isSupportedIn_iff]
      intro y hy hyY'
      rw [map_sub, sub_eq_zero]
      by_cases hyY : y ∈ (Y : Set (Spec R))
      · have hyf : y ∈ PrimeSpectrum.basicOpen f := fun h =>
          hyY' ⟨hyY, (PrimeSpectrum.mem_zeroLocus _ _).2 (Set.singleton_subset_iff.2 h)⟩
        have e := congrArg ((tilde I).presheaf.germ _ y hyf) htf'
        have e1 := TopCat.Presheaf.germ_res_apply (tilde I).presheaf
          (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)) y hyf t
        have e2 := TopCat.Presheaf.germ_res_apply (tilde I).presheaf (homOfLE hfU) y hyf s
        have e3 := TopCat.Presheaf.germ_res_apply (tilde I).presheaf
          (homOfLE (le_top : U ≤ ⊤)) y hy t
        exact e2.symm.trans (e.symm.trans (e1.trans e3.symm))
      · rw [(isSupportedIn_iff s).1 hs y hy hyY,
          (isSupportedIn_iff _).1 (htY.res (le_top : U ≤ ⊤)) y hy hyY]
    obtain ⟨t', ht'⟩ := ih Y' hY' U _ hs'
    refine ⟨(show Γ(tilde I, ⊤) from t) + t', ?_⟩
    rw [map_add, ht', add_sub_cancel]
  · simp only [not_exists, not_and] at hYU
    have hs0 : s = 0 := by
      refine TopCat.Presheaf.section_ext ⟨(tilde I).presheaf, (tilde I).isSheaf⟩ U s 0
        fun y hy => ?_
      rw [map_zero]
      exact (isSupportedIn_iff s).1 hs y hy fun hyY => hYU y hyY hy
    exact ⟨0, by rw [hs0, map_zero]⟩

/-- **Hartshorne III, Proposition 3.4.** Let `A` be a Noetherian ring and `I` an injective
`A`-module. Then the sheaf `Ĩ` on `Spec A` is flasque. -/
theorem tilde_isFlasque : TopCat.Presheaf.IsFlasque (tilde I).presheaf where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    obtain ⟨t, ht⟩ := exists_extension_of_isSupportedIn I ⊤ V.unop s
      ((isSupportedIn_iff s).2 fun _ _ h => absurd trivial h)
    refine ⟨res (tilde I) (le_top : U.unop ≤ ⊤) t, ?_⟩
    rw [← ht, res_apply, res_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

end Hartshorne
