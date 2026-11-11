/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.AffineQuasicoherentAcyclic
import Hartshorne.Cohomology.RightDerivedLongExactSequence
import Hartshorne.Scheme.ModuleIdealSheafData
import Hartshorne.Scheme.QuasicoherentAbelianClosure
import Hartshorne.Scheme.AffineGlobalSectionsExact

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace SerreAffineness

variable {X : Scheme.{u}}

/-- A short complex of `𝒪_X`-modules, as a short complex in `SheafOfModules`. -/
abbrev toSOM (S : ShortComplex X.Modules) : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) :=
  S

/-- The underlying short complex of abelian sheaves. -/
abbrev Sab (S : ShortComplex X.Modules) : ShortComplex (X.toTopCat.Sheaf AddCommGrpCat.{u}) :=
  (toSOM S).map (ModuleCohomology.toTopSheaf X.ringCatSheaf)

/-- The structure sheaf `𝒪_X` as an `𝒪_X`-module. -/
abbrev unitMod (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- `H^i(X, F)` for an `𝒪_X`-module `F`: cohomology of the underlying abelian sheaf. -/
abbrev H (i : ℕ) (F : X.Modules) : AddCommGrpCat.{u} :=
  (sheafCohomology X.toTopCat i).obj ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)

theorem sab_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) : (Sab S).ShortExact :=
  (show (toSOM S).ShortExact from hS).map_of_exact _

set_option hygiene false in
local notation "Γ₀" => sheafSectionsOver (X := X.toTopCat) ⊤

/-- If `H^1(X, S.X₁) = 0` for a short exact sequence `S` of `𝒪_X`-modules, then
`Γ(X, S.X₂) ⟶ Γ(X, S.X₃)` is surjective. -/
theorem surjective_app_top {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h : IsZero (H 1 S.X₁)) : Function.Surjective (S.g.app ⊤) := by
  have hT := sab_shortExact hS
  have hδ : rightDerivedδ Γ₀ hT 0 = 0 := h.eq_of_tgt _ _
  have hepi0 : Epi (((Γ₀).rightDerived 0).map (Sab S).g) :=
    (rightDerived_exact₃ Γ₀ hT 0).epi_f hδ
  have hnat := ((Γ₀).rightDerivedZeroIsoSelf).hom.naturality (Sab S).g
  have e : (Γ₀).map (Sab S).g = ((Γ₀).rightDerivedZeroIsoSelf).inv.app (Sab S).X₂ ≫
      ((Γ₀).rightDerived 0).map (Sab S).g ≫ ((Γ₀).rightDerivedZeroIsoSelf).hom.app (Sab S).X₃ := by
    rw [hnat, Iso.inv_hom_id_app_assoc]
  have hepi : Epi ((Γ₀).map (Sab S).g) := by rw [e]; infer_instance
  exact (AddCommGrpCat.epi_iff_surjective _).1 hepi

/-- `H^1` vanishes on the middle term of a short exact sequence whose outer terms have
vanishing `H^1`. -/
theorem isZero_H1_of_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : IsZero (H 1 S.X₁)) (h₃ : IsZero (H 1 S.X₃)) : IsZero (H 1 S.X₂) :=
  (rightDerived_exact₂ Γ₀ (sab_shortExact hS) 1).isZero_of_both_zeros (h₁.eq_of_src _ _)
    (h₃.eq_of_tgt _ _)

/-! ### Ideal sheaves from monomorphisms into `𝒪_X` -/

section IdealOfMono

open ArtinReesKernelSheaf

variable {M : X.Modules} (ι : M ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) [Mono ι]

/-- The image of a monomorphism `M ⟶ 𝒪_X`, as a family of ideals. -/
def rangeSubmodule : (SheafOfModules.unit X.ringCatSheaf : X.Modules).val.Submodule where
  obj U := LinearMap.range (ι.val.app U).hom
  map i := by
    rintro _ ⟨s, rfl⟩
    exact ⟨M.val.map i s, PresheafOfModules.naturality_apply _ _ _⟩

/-- `M` corestricted to the image of `ι`. -/
def toRange : M.val ⟶ (rangeSubmodule ι).toPresheafOfModules :=
  PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun s := ⟨ι.val.app U s, s, rfl⟩
          map_zero' := Subtype.ext (ι.val.app U).hom.map_zero
          map_add' a b := Subtype.ext ((ι.val.app U).hom.map_add a b) }
      naturality U V i := by
        ext s
        exact Subtype.ext (PresheafOfModules.naturality_apply ι.val i s) }
    fun U r m => Subtype.ext ((ι.val.app U).hom.map_smul r m)

theorem isIso_toRange : IsIso (toRange ι) := by
  have : Mono (toRange ι) := PresheafOfModules.mono_of_injective fun U a b h =>
    modules_app_injective ι U.unop (congrArg Subtype.val h)
  have : Epi (toRange ι) := PresheafOfModules.epi_of_surjective fun U t => by
    obtain ⟨_, s, rfl⟩ := t
    exact ⟨s, rfl⟩
  exact isIso_of_mono_of_epi _

theorem isLocal_rangeSubmodule : IsLocal (rangeSubmodule ι) :=
  isLocal_of_isSheaf _ ((Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf _).mapIso (@asIso _ _ _ _ (toRange ι) (isIso_toRange ι)))).1
      M.isSheaf)

/-- `M` is isomorphic to the image of `ι`. -/
def rangeIso : M ≅ toModules (rangeSubmodule ι) (isLocal_rangeSubmodule ι) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (@asIso _ _ _ _ (toRange ι) (isIso_toRange ι))

/-- The quasi-coherent ideal subsheaf of `𝒪_X` given by a monomorphism from a quasi-coherent
module. -/
def idealOfMono [M.IsQuasicoherent] : QuasicoherentIdealSubsheaf X where
  carrier := rangeSubmodule ι
  isLocal := isLocal_rangeSubmodule ι
  isQuasicoherent := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (rangeIso ι)
    inferInstance

/-- `M` is isomorphic to the module of its ideal subsheaf. -/
def idealOfMonoIso [M.IsQuasicoherent] : M ≅ (idealOfMono ι).toModules := rangeIso ι

end IdealOfMono

/-- On a locally Noetherian scheme every quasi-coherent ideal subsheaf of `𝒪_X` is coherent. -/
theorem isCoherent_toModules [IsLocallyNoetherian X] (J : QuasicoherentIdealSubsheaf X) :
    IsCoherent J.toModules := by
  have := J.isQuasicoherent
  have hiso := ((quasicoherent_affine_local_tfae J.toModules).out 0 2).mp J.isQuasicoherent
  refine ((coherent_affine_local_tfae J.toModules).out 3 0).mp ?_
  intro U
  refine ⟨?_, hiso U⟩
  have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherian Γ(X, (U : X.Opens)) Γ(unitMod X, (U : X.Opens)) :=
    inferInstanceAs (IsNoetherian Γ(X, (U : X.Opens)) Γ(X, (U : X.Opens)))
  change Module.Finite Γ(X, (U : X.Opens)) (ArtinReesKernelSheaf.sub J.carrier (U : X.Opens))
  infer_instance

/-- **Combination step** (Hartshorne III.3.7, end of the proof, via Ex. II.2.17): if every closed
point of a Noetherian scheme has an affine neighbourhood `X_f`, and every finite family `f_i`
with `⋃ X_{f_i} = X` generates the unit ideal of `Γ(X, 𝒪_X)`, then `X` is affine. -/
theorem isAffine_of_local_of_generation [IsNoetherian X]
    (hA : ∀ P : X, IsClosed ({P} : Set X) →
      ∃ f : Γ(X, ⊤), P ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f))
    (hB : ∀ t : Finset Γ(X, ⊤), (∀ x : X, ∃ f ∈ t, x ∈ X.basicOpen f) →
      Ideal.span (t : Set Γ(X, ⊤)) = ⊤) :
    IsAffine X := by
  let S : Set Γ(X, ⊤) := {f | IsAffineOpen (X.basicOpen f)}
  have hcover : (Set.univ : Set X) ⊆ ⋃ f : S, (X.basicOpen f.1 : Set X) := by
    intro x _
    obtain ⟨P, hP, hPc⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
    obtain ⟨f, hPf, hf⟩ := hA P hPc
    have hxP : x ⤳ P := specializes_iff_mem_closure.mpr hP
    exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxP.mem_open (X.basicOpen f).isOpen hPf⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun f : S => (X.basicOpen f.1).isOpen)
    hcover
  classical
  let t' : Finset Γ(X, ⊤) := t.image Subtype.val
  have hspan : Ideal.span (t' : Set Γ(X, ⊤)) = ⊤ := by
    refine hB t' fun x => ?_
    obtain ⟨f, hft, hxf⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨f.1, Finset.mem_image_of_mem _ hft, hxf⟩
  refine isAffine_of_isAffineOpen_basicOpen (t' : Set Γ(X, ⊤)) hspan fun f hf => ?_
  obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hf
  exact g.2

end SerreAffineness

end Hartshorne
