/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentExtensionAffine
import Hartshorne.Scheme.CoherentFreeLocus
import Hartshorne.Scheme.FinitePushforwardCoherent
import Hartshorne.Scheme.LocallyFreeInvertible
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Hartshorne.Scheme.ClosedImmersionIdealSheaf

/-!
# A generic finite-module frame

Hartshorne, *Algebraic Geometry*, III, Exercise 4.2(a) (p. 222).

Let `f : X ⟶ Y` be a finite surjective morphism of Noetherian schemes, with `Y` integral. There
are a coherent `𝒪_X`-module `M`, an integer `r > 0` and a morphism `𝒪_Y^r ⟶ f_* M` which is an
isomorphism at the generic point of `Y` (`Hartshorne.exists_genericFiniteModuleFrame`).

## Proof

The coherent sheaf `f_* 𝒪_X` has a free stalk at the generic point `η` of `Y` (a vector space
over the function field), so it is free on an affine open `W = Spec A ∋ η`. Let
`B = Γ(f⁻¹ W, 𝒪_X)`, a free `A`-module with a basis `b₁, …, b_r`; `r > 0` as `f⁻¹ W ≠ ∅`.

The `bᵢ` are global sections of the quasi-coherent sheaf `E = j_* (𝒪_X|_{f⁻¹ W})`, where `j` is
the inclusion of `f⁻¹ W`. Their span `M ⊆ E` is coherent (`isCoherent_spanSheaf`), and has the
`bᵢ` as global sections; they give `α : 𝒪_Y^r ⟶ f_* M`. Over `W`, the sections of `f_* M` are
`M(f⁻¹ W) ⊆ E(f⁻¹ W) = B`. This inclusion is onto since it contains the basis, so the `bᵢ` form
an `A`-basis of `Γ(W, f_* M)`. A morphism from a free sheaf on `Spec A` to a quasi-coherent sheaf
given by a basis of the global sections is an isomorphism
(`Scheme.Modules.isIso_freeHomEquiv_symm_of_basis`). Hence `α|_W` is an isomorphism, and so is
its stalk at `η`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

namespace Hartshorne

namespace ChevalleyFrame

/-! ### A free affine chart for `f_* 𝒪_X` -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `f_* 𝒪_X`. -/
noncomputable abbrev pushStructure : Y.Modules :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

/-- For a finite morphism to an integral Noetherian scheme, `f_* 𝒪_X` has finite free sections
over some affine open containing the generic point. -/
theorem exists_affine_free [IsFinite f] [IsIntegral Y] [IsNoetherian Y] :
    ∃ W : Y.affineOpens, genericPoint Y ∈ (W : Y.Opens) ∧
      Module.Free Γ(Y, (W : Y.Opens)) Γ(specRestriction (pushStructure f) W, ⊤) ∧
      Module.Finite Γ(Y, (W : Y.Opens)) Γ(specRestriction (pushStructure f) W, ⊤) := by
  have hF : IsCoherent (pushStructure f) :=
    isCoherent_pushforward_of_isFinite f (isCoherent_structureSheafModule X)
  have hx : Module.Free (Y.presheaf.stalk (genericPoint Y))
      ((pushStructure f).presheaf.stalk (genericPoint Y)) := by
    exact Module.Free.of_divisionRing Y.functionField _
  obtain ⟨V0, hη, I, ⟨β⟩⟩ := exists_isFree_restrict_of_free_stalk _ hF _ hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, hVV0⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hη V0.2
  replace hVV0 : V ≤ V0 := hVV0
  let W : Y.affineOpens := ⟨V, hV⟩
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  let j : Spec Γ(Y, V) ⟶ V0 := hV.isoSpec.inv ≫ Y.homOfLE hVV0
  have hj : j ≫ V0.ι = hV.fromSpec := by simp [j]; rfl
  let β' : (pushStructure f).restrict hV.fromSpec ≅ SheafOfModules.free I :=
    (Scheme.Modules.restrictFunctorCongr hj).symm.app _ ≪≫
      (Scheme.Modules.restrictFunctorComp j V0.ι).app _ ≪≫
      (Scheme.Modules.restrictFunctor j).mapIso β ≪≫ Scheme.Modules.restrictFreeIso j I
  let e : Γ(specRestriction (pushStructure f) W, ⊤) ≃ₗ[Γ(Y, V)] (I →₀ Γ(Y, V)) :=
    (moduleSpecΓFunctor.mapIso (β' ≪≫ (tildeFinsupp I).symm) ≪≫
      (tilde.toTildeΓNatIso.app (ModuleCat.of Γ(Y, V) (I →₀ Γ(Y, V)))).symm).toLinearEquiv
  refine ⟨W, hηV, Module.Free.of_equiv e.symm, ?_⟩
  exact (finite_specRestriction_iff _ W).mpr (forall_affine_finite_of_isCoherent _ hF W).1

/-! ### The coherent module `M` -/

open ArtinReesKernelSheaf

/-- `E = j_* (𝒪_X|_U)` for an open `U` with inclusion `j`. -/
noncomputable abbrev chartSheaf (U : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward U.ι).obj
    (Scheme.Modules.restrict (SheafOfModules.unit X.ringCatSheaf) U.ι)

theorem image_preimage_top_le (U : X.Opens) : U.ι ''ᵁ (U.ι ⁻¹ᵁ ⊤) ≤ U :=
  (U.ι.image_le_opensRange _).trans (Scheme.Opens.opensRange_ι U).le

theorem le_image_preimage_self (U : X.Opens) : U ≤ U.ι ''ᵁ (U.ι ⁻¹ᵁ U) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_idem]

/-- The global section of `E = j_* (𝒪_X|_U)` given by a function on `U`. -/
noncomputable def chartSection (U : X.Opens) (b : Γ(X, U)) : Γ(chartSheaf U, ⊤) :=
  X.presheaf.map (homOfLE (image_preimage_top_le U)).op b

/-- The global sections `chartSection U (c i)` of `E`. -/
def frameSet {U : X.Opens} {ι : Type u} (c : ι → Γ(X, U)) : Set Γ(chartSheaf U, ⊤) :=
  Set.range fun i => chartSection U (c i)

/-- The submodule of `E` spanned by the `chartSection U (c i)`. -/
noncomputable abbrev frameModule {U : X.Opens} {ι : Type u} (c : ι → Γ(X, U)) : X.Modules :=
  toModules (spanSheaf (frameSet c)) (isLocal_spanSheaf _)

theorem chartSection_mem {U : X.Opens} {ι : Type u} (c : ι → Γ(X, U)) (i : ι) :
    chartSection U (c i) ∈ sub (spanSheaf (frameSet c)) ⊤ := fun x _ => by
  obtain ⟨V, -, hxV⟩ := exists_affine_le (U := ⊤) (x := x) trivial
  exact ⟨V, le_top, hxV, Submodule.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩⟩

/-- The global section of a module sheaf given by a section over `⊤`. -/
noncomputable def globalSection (M : X.Modules) (m : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk (fun V => res M (le_top : V.unop ≤ ⊤) m)
    (fun _ _ i => res_res M le_top (leOfHom i.unop) m)

/-- The global section of `f_* M` given by `c i`. -/
noncomputable def frameSection {U : X.Opens} {ι : Type u} (c : ι → Γ(X, U)) (i : ι) :
    ((Scheme.Modules.pushforward f).obj (frameModule c)).sections :=
  SheafOfModules.pushforwardSections f.toRingCatSheafHom
    (globalSection (frameModule c) ⟨chartSection U (c i), chartSection_mem c i⟩)

/-- The frame `𝒪_Y^{(ι)} ⟶ f_* M`, sending the `i`-th basis section to `c i`. -/
noncomputable def frameMap {U : X.Opens} {ι : Type u} (c : ι → Γ(X, U)) :
    (SheafOfModules.free ι : Y.Modules) ⟶ (Scheme.Modules.pushforward f).obj (frameModule c) :=
  ((Scheme.Modules.pushforward f).obj (frameModule c)).freeHomEquiv.symm (frameSection f c)

theorem isQuasicoherent_chartSheaf [IsNoetherian X] (U : X.Opens) :
    (chartSheaf U).IsQuasicoherent := by
  have := ClosedImmersionIdeal.isQuasicoherent_unit X
  have := Scheme.Modules.isQuasicoherent_restrictFunctor U.ι
    (SheafOfModules.unit X.ringCatSheaf : X.Modules)
  exact isQuasicoherent_pushforward U.ι (Or.inr ⟨inferInstance, inferInstance⟩) _

theorem isCoherent_frameModule [IsNoetherian X] {U : X.Opens} {ι : Type u} [Finite ι]
    (c : ι → Γ(X, U)) : IsCoherent (frameModule c) := by
  have := isQuasicoherent_chartSheaf U
  exact isCoherent_spanSheaf _ (Set.finite_range _)

/-! ### The frame is an isomorphism over the chart -/

/-- `f⁻¹ W`, written as the preimage of the image of `Spec Γ(Y, W) ⟶ Y`. -/
noncomputable abbrev chartPreimage (W : Y.affineOpens) : X.Opens :=
  haveI := W.2.isOpenImmersion_fromSpec
  f ⁻¹ᵁ (W.2.fromSpec ''ᵁ ⊤)

theorem presheaf_map_appIso_inv_app (U : X.Opens) (r : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_image_preimage_self U)).op
      ((U.ι.appIso (U.ι ⁻¹ᵁ U)).inv (U.ι.app U r)) = r := by
  rw [← ConcreteCategory.comp_apply (U.ι.app U), Scheme.Hom.app_appIso_inv]
  exact (TopCat.Presheaf.map_map_apply X.presheaf _ _ (𝟙 _) r).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

/-- Over the affine chart `W` (with `U = f⁻¹ W`), the sections `Γ(W, f_* M) = M(U)` of the span
`M`, as a submodule of `E(U)`, compared with `B = Γ(U, 𝒪_X)` by restriction. -/
noncomputable def chartSectionsMap (W : Y.affineOpens) {ι : Type u}
    (c : ι → Γ(X, chartPreimage f W)) :
    haveI := W.2.isOpenImmersion_fromSpec
    (moduleSpecΓFunctor (R := Γ(Y, (W : Y.Opens)))).obj
        (((Scheme.Modules.pushforward f).obj (frameModule c)).restrict W.2.fromSpec) →ₗ[
      Γ(Y, (W : Y.Opens))] Γ(specRestriction (pushStructure f) W, ⊤) :=
  haveI := W.2.isOpenImmersion_fromSpec
  let U := chartPreimage f W
  let A := Γ(Y, (W : Y.Opens))
  let h := homOfLE (le_image_preimage_self U)
  let ψ : A → Γ(X, U) := fun a =>
    f.app (W.2.fromSpec ''ᵁ ⊤) ((W.2.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a))
  { toFun := fun n => X.presheaf.map h.op (@id Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ U))
      (n : ↥(sub (spanSheaf (frameSet c)) U)).1)
    map_add' := fun x y => map_add (X.presheaf.map h.op).hom _ _
    map_smul' := fun a x => by
      have smulN : @id Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ U))
          ((a • x : (moduleSpecΓFunctor (R := A)).obj
            (((Scheme.Modules.pushforward f).obj (frameModule c)).restrict W.2.fromSpec)) :
            ↥(sub (spanSheaf (frameSet c)) U)).1 =
          (U.ι.appIso (U.ι ⁻¹ᵁ U)).inv (U.ι.app U (ψ a)) *
            @id Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ U)) (x : ↥(sub (spanSheaf (frameSet c)) U)).1 := rfl
      have smulB : ∀ b : Γ(specRestriction (pushStructure f) W, ⊤),
          @id Γ(X, U) (a • b) = ψ a * @id Γ(X, U) b := fun _ => rfl
      refine (congrArg (fun z => X.presheaf.map h.op z) smulN).trans ?_
      refine (map_mul (X.presheaf.map h.op).hom _ _).trans ?_
      rw [presheaf_map_appIso_inv_app]
      exact (smulB _).symm }

theorem chartSectionsMap_injective (W : Y.affineOpens) {ι : Type u}
    (c : ι → Γ(X, chartPreimage f W)) : Function.Injective (chartSectionsMap f W c) := by
  have : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  let U := chartPreimage f W
  intro x y hxy
  have key : ∀ n, X.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op
      (chartSectionsMap f W c n) =
      @id Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ U)) (n : ↥(sub (spanSheaf (frameSet c)) U)).1 := fun n =>
    (TopCat.Presheaf.map_map_apply X.presheaf _ _ (𝟙 _) _).trans
      (by rw [CategoryTheory.Functor.map_id]; rfl)
  have := congrArg (X.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op) hxy
  rw [key, key] at this
  exact Subtype.ext this

theorem chartSectionsMap_frameSection (W : Y.affineOpens) {ι : Type u}
    (c : ι → Γ(X, chartPreimage f W)) (i : ι) :
    haveI := W.2.isOpenImmersion_fromSpec
    chartSectionsMap f W c
      ((Scheme.Modules.restrictSection W.2.fromSpec _ (frameSection f c i)).val (op ⊤)) =
      c i :=
  (TopCat.Presheaf.map_map_map_apply X.presheaf _ _ _ (𝟙 _) (c i)).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

/-- Over the affine chart `W`, the frame given by a basis of `Γ(f⁻¹ W, 𝒪_X)` is an
isomorphism. -/
theorem isIso_restrict_frameMap [IsFinite f] [IsNoetherian X] (W : Y.affineOpens) {ι : Type u}
    [Finite ι]
    (bas : Module.Basis ι Γ(Y, (W : Y.Opens)) Γ(specRestriction (pushStructure f) W, ⊤)) :
    haveI := W.2.isOpenImmersion_fromSpec
    IsIso ((Scheme.Modules.restrictFunctor W.2.fromSpec).map
      (frameMap f (U := chartPreimage f W) (fun i => bas i))) := by
  have : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  let c : ι → Γ(X, chartPreimage f W) := fun i => bas i
  have hT2 := Scheme.Modules.restrictFreeIso_inv_comp_map_freeHomEquiv_symm
    W.2.fromSpec ((Scheme.Modules.pushforward f).obj (frameModule c)) (frameSection f c)
  let P := ((Scheme.Modules.pushforward f).obj (frameModule c)).restrict W.2.fromSpec
  let t := fun i => Scheme.Modules.restrictSection W.2.fromSpec _ (frameSection f c i)
  have hPM := isCoherent_pushforward_of_isFinite f (isCoherent_frameModule c)
  have : IsIso P.fromTildeΓ := (forall_affine_finite_of_isCoherent _ hPM W).2
  let Φ := chartSectionsMap f W c
  have hsurj : Function.Surjective Φ := by
    intro b
    have := Fintype.ofFinite ι
    refine ⟨∑ i, bas.repr b i • @id ((moduleSpecΓFunctor (R := Γ(Y, (W : Y.Opens)))).obj P)
      ((t i).val (op ⊤)), ?_⟩
    rw [map_sum]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (bas.sum_repr b)
    exact (Φ.map_smul _ _).trans (congrArg _ (chartSectionsMap_frameSection f W c i))
  let Φe := LinearEquiv.ofBijective Φ ⟨chartSectionsMap_injective f W c, hsurj⟩
  have hb' : ∀ i, bas.map Φe.symm i = (t i).val (op ⊤) := fun i =>
    (Module.Basis.map_apply _ _ _).trans
      (Φe.symm_apply_eq.mpr (chartSectionsMap_frameSection f W c i).symm)
  have hiso := Scheme.Modules.isIso_freeHomEquiv_symm_of_basis P t _ hb'
  have hcomp : IsIso ((Scheme.Modules.restrictFreeIso W.2.fromSpec ι).inv ≫
      (Scheme.Modules.restrictFunctor W.2.fromSpec).map (frameMap f c)) := by
    rw [frameMap, hT2]
    exact hiso
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (Scheme.Modules.restrictFreeIso W.2.fromSpec ι).inv _
    (Iso.isIso_inv _) hcomp

end ChevalleyFrame

/-- **A generic finite-module frame** (Hartshorne III, Exercise 4.2(a)). Let `f : X ⟶ Y` be a
finite surjective morphism of Noetherian schemes, with `Y` integral. There are a coherent
`𝒪_X`-module `M`, an integer `r > 0` and a morphism `𝒪_Y^r ⟶ f_* M` which is an isomorphism at
the generic point of `Y`. Hartshorne assumes `X` integral too; the proof does not use it. -/
theorem exists_genericFiniteModuleFrame {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] [IsIntegral Y] [IsNoetherian Y] [IsNoetherian X] :
    ∃ (M : X.Modules) (_ : IsCoherent M) (r : ℕ) (_ : 0 < r)
      (α : (SheafOfModules.free (ULift.{u} (Fin r)) : Y.Modules) ⟶
        (Scheme.Modules.pushforward f).obj M),
      IsIso ((Scheme.Modules.toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (genericPoint Y)).map α) := by
  obtain ⟨W, hηW, hfree, hfin⟩ := ChevalleyFrame.exists_affine_free f
  have : IsOpenImmersion W.2.fromSpec := W.2.isOpenImmersion_fromSpec
  let A := Γ(Y, (W : Y.Opens))
  let B := Γ(specRestriction (ChevalleyFrame.pushStructure f) W, ⊤)
  have : Nonempty (W : Y.Opens) := ⟨⟨_, hηW⟩⟩
  have : Nontrivial A := Scheme.component_nontrivial Y _
  let r := Module.finrank A B
  let bas : Module.Basis (ULift.{u} (Fin r)) A B :=
    (Module.finBasis A B).reindex Equiv.ulift.symm
  have hηT : genericPoint Y ∈ W.2.fromSpec ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, W.2.opensRange_fromSpec]
    exact hηW
  have hr : 0 < r := by
    obtain ⟨x, hx⟩ := f.surjective (genericPoint Y)
    have : Nonempty (ChevalleyFrame.chartPreimage f W) :=
      ⟨⟨x, show f x ∈ W.2.fromSpec ''ᵁ ⊤ from hx ▸ hηT⟩⟩
    have : Nontrivial B := Scheme.component_nontrivial X (ChevalleyFrame.chartPreimage f W)
    exact Module.finrank_pos
  refine ⟨_, ChevalleyFrame.isCoherent_frameModule
    (U := ChevalleyFrame.chartPreimage f W) (fun i => bas i), r, hr,
    ChevalleyFrame.frameMap f (U := ChevalleyFrame.chartPreimage f W) (fun i => bas i), ?_⟩
  have hiso := ChevalleyFrame.isIso_restrict_frameMap f W bas
  obtain ⟨y, hy⟩ : genericPoint Y ∈ Set.range W.2.fromSpec := by rwa [W.2.range_fromSpec]
  have h1 : IsIso ((Scheme.Modules.restrictFunctor W.2.fromSpec ⋙ Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (ChevalleyFrame.frameMap f (U := ChevalleyFrame.chartPreimage f W) (fun i => bas i))) :=
    Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y) _
  have h2 := (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso W.2.fromSpec y) _).mp h1
  rw [← hy]
  exact h2

end Hartshorne
