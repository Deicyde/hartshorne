/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.Flatness.ModuleSheafFlatOverBase
import Hartshorne.Cohomology.Flatness.FiniteFlatLocalModuleFree
import Hartshorne.Scheme.CoherentFreeLocus

/-!
# Coherent sheaves flat over themselves are locally free

Hartshorne, *Algebraic Geometry*, III.9, Proposition 9.2(e) (p. 254).

Let `X` be a Noetherian scheme and `F` a coherent `𝒪_X`-module. Then `F` is flat over `X`
through the identity morphism if and only if `F` is locally free of finite rank, where finite
rank means `Scheme.Modules.rankAt F x < ℵ₀` at every point.

* Flatness over `X` via `𝟙 X` at `x` is flatness of the stalk `F_x` over `𝒪_{X,x}` with its
  usual module structure (`flatOverAt_id_iff`), since the stalk map of the identity is the
  identity.
* Stalks of a coherent sheaf are finite modules over the local rings (`finite_stalk_of_isCoherent`),
  being localizations of finite modules of sections on affine opens.
* Over the Noetherian local ring `𝒪_{X,x}` a finite module is flat iff free, and a coherent
  sheaf is locally free iff all its stalks are free (Hartshorne II, Exercise 5.7(b)).
* The rank of a locally free coherent sheaf is finite (`rankAt_lt_aleph0_of_isCoherent`): on an
  affine open `Spec A` where `F ≅ 𝒪^(⊕ I)`, the sections `A^(⊕ I)` form a finite `A`-module.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Hartshorne

open AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- Flatness of `F` over `X` through the identity at `x` is flatness of the stalk `F_x` over the
local ring `𝒪_{X,x}`. -/
theorem flatOverAt_id_iff (F : X.Modules) (x : X) :
    F.FlatOverAt (𝟙 X) x ↔ Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  unfold Scheme.Modules.FlatOverAt
  dsimp only
  have h : (Module.compHom (F.presheaf.stalk x) ((𝟙 X : X ⟶ X).stalkMap x).hom :
      Module (X.presheaf.stalk x) (F.presheaf.stalk x)) = schemeModulesStalkModule F x := by
    refine Module.ext' _ _ fun r m ↦ ?_
    rw [Scheme.Hom.stalkMap_id]
  exact Iff.of_eq (congrArg (fun inst ↦ @Module.Flat _ _ _ _ inst) h)

open FreeLocusAux in
attribute [local instance] freeLocusStalkAlgebra freeLocus_asIdeal_isPrime
  freeLocus_stalk_isLocalization freeLocusStalkModule freeLocus_stalk_isScalarTower in
/-- The stalks of a coherent sheaf are finite modules over the local rings. -/
theorem finite_stalk_of_isCoherent (F : X.Modules) (hF : IsCoherent F) (x : X) :
    Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let Va : X.affineOpens := ⟨V, hV⟩
  let R := Γ(X, V)
  obtain ⟨hfin, hiso⟩ := forall_affine_finite_of_isCoherent F hF Va
  let G := specRestriction F Va
  have : Module.Finite R Γ(G, ⊤) := (finite_specRestriction_iff F Va).mpr hfin
  have hloc : IsLocalizing (modulesSpecToSheaf.obj G) :=
    (isIso_fromTildeΓ_iff_isLocalizing G).mp hiso
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  obtain ⟨y, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have := isLocalizedModule_germTopLinear G hloc y
  have : Module.Finite ((Spec R).presheaf.stalk y) (G.presheaf.stalk y) :=
    Module.Finite.of_isLocalizedModule y.asIdeal.primeCompl (germTopLinear G y)
  exact (CoherentAux.finite_iff_of_ringEquiv_addEquiv (stalkRingEquiv hV.fromSpec y).symm
    (restrictStalkIso hV.fromSpec F y).addCommGroupIsoToAddEquiv
    (restrictStalkIso_hom_smul hV.fromSpec F y)).mp this

/-- A locally free coherent sheaf has finite rank at every point. -/
theorem rankAt_lt_aleph0_of_isCoherent (F : X.Modules) (hF : IsCoherent F)
    (hlf : F.IsLocallyFree) (x : X) : F.rankAt x < Cardinal.aleph0 := by
  obtain ⟨U, hxU, I, ⟨α⟩⟩ := hlf x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  replace hVU : V ≤ U := hVU
  let Va : X.affineOpens := ⟨V, hV⟩
  let R := Γ(X, V)
  let j : Spec R ⟶ U := hV.isoSpec.inv ≫ X.homOfLE hVU
  have hj : j ≫ U.ι = hV.fromSpec := by simp [j]; rfl
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let β : F.restrict hV.fromSpec ≅ SheafOfModules.free I :=
    (Scheme.Modules.restrictFunctorCongr hj).symm.app F ≪≫
      (Scheme.Modules.restrictFunctorComp j U.ι).app F ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso α ≪≫ Scheme.Modules.restrictFreeIso j I
  let G := specRestriction F Va
  have : Module.Finite R Γ(G, ⊤) :=
    (finite_specRestriction_iff F Va).mpr (forall_affine_finite_of_isCoherent F hF Va).1
  let e : Γ(G, ⊤) ≃ₗ[R] (I →₀ R) :=
    (moduleSpecΓFunctor.mapIso (β ≪≫ (tildeFinsupp I).symm) ≪≫
      (tilde.toTildeΓNatIso.app (ModuleCat.of R (I →₀ R))).symm).toLinearEquiv
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nontrivial R := Scheme.component_nontrivial X V
  have : Finite I := Module.Finite.finite_basis (Module.Basis.ofRepr e)
  rw [F.rankAt_eq α hxU]
  exact Cardinal.mk_lt_aleph0

/-- **Hartshorne III, Proposition 9.2(e).** Let `X` be a Noetherian scheme and `F` a coherent
`𝒪_X`-module. Then `F` is flat over `X` (through the identity morphism) if and only if `F` is
locally free of finite rank. -/
theorem coherent_flatOver_id_iff_isLocallyFree [IsNoetherian X] (F : X.Modules)
    (hF : IsCoherent F) :
    F.FlatOver (𝟙 X) ↔ F.IsLocallyFree ∧ ∀ x : X, F.rankAt x < Cardinal.aleph0 := by
  have hfree : F.FlatOver (𝟙 X) ↔ F.IsLocallyFree := by
    rw [isLocallyFree_iff_forall_free_stalk F hF]
    refine forall_congr' fun x ↦ ?_
    have := finite_stalk_of_isCoherent F hF x
    rw [flatOverAt_id_iff, finiteFlat_iff_free]
  rw [hfree]
  exact ⟨fun h ↦ ⟨h, rankAt_lt_aleph0_of_isCoherent F hF h⟩, And.left⟩

end

end Hartshorne
