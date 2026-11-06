/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjTailIsomorphism
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A graded quotient induces a closed immersion of Proj

Hartshorne, *Algebraic Geometry*, II, Exercise 3.12(a).

Let `φ : S →+*ᵍ T` be a surjective degree-preserving homomorphism of `ℕ`-graded
rings. Then the natural domain `U = {𝔭 ∈ Proj T | 𝔭 ⊉ φ(S₊)}` of the partial
Proj morphism is all of `Proj T`, and the induced morphism `Proj T ⟶ Proj S` is
a closed immersion.

Every homogeneous element of `T` has a homogeneous preimage of the same degree.
A relevant homogeneous prime of `T` misses some homogeneous `t` of positive
degree, hence misses `φ(s)` for a homogeneous preimage `s`, so it lies in `U`.
For homogeneous `r ∈ S` of positive degree the map of degree-zero localizations
`S_(r) → T_(φ r)` is surjective, so over `D₊(r)` the partial morphism is,
up to isomorphisms, `Spec T_(φ r) ⟶ Spec S_(r)`, a closed immersion. These
`D₊(r)` cover `Proj S` and being a closed immersion is local on the target.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomogeneousIdeal HomogeneousLocalization TopologicalSpace
open AlgebraicGeometry

universe u

namespace Hartshorne

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] {f : 𝒜 →+*ᵍ ℬ}

namespace ProjSurjection

/-- A surjective graded homomorphism has homogeneous preimages of the same degree. -/
theorem exists_homogeneous_preimage (hf : Function.Surjective f) {d : ℕ} {b : B}
    (hb : b ∈ ℬ d) : ∃ a ∈ 𝒜 d, f a = b := by
  obtain ⟨c, rfl⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 c d, SetLike.coe_mem _, ?_⟩
  rw [GradedRingHom.map_directSumDecompose, DirectSum.decompose_of_mem_same _ hb]

/-- For `r` homogeneous of positive degree, the map of degree-zero localizations
`S_(r) → T_(φ r)` induced by a surjective graded homomorphism is surjective. -/
theorem surjective_awayMap (hf : Function.Surjective f) {i : ℕ} {r : A} (hr : r ∈ 𝒜 i) :
    Function.Surjective (Away.map f r) := by
  intro w
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hr) w
  obtain ⟨a, ha, rfl⟩ := exists_homogeneous_preimage hf hb
  exact ⟨Away.mk 𝒜 hr n a ha, Away.map_mk f r hr n a ha⟩

/-- The standard opens `D₊(r)` with `r` homogeneous of positive degree cover
`Proj S`. -/
theorem iSup_basicOpen_eq_top :
    ⨆ r : ProjPartialIndex 𝒜, Proj.basicOpen 𝒜 r.2.1 = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨e, t, he, ht, htx⟩ := ProjTail.exists_homogeneous_not_mem x
  exact Opens.mem_iSup.mpr ⟨⟨e, t, he, ht⟩, (Proj.mem_basicOpen _ _ _).mpr htx⟩

/-- The inclusion of `U ∩ D₊(φ r)` into `D₊(φ r)` is an isomorphism. -/
theorem isIso_resLE {i : ℕ} {r : A} (hr : r ∈ 𝒜 i) (hi : 0 < i) :
    IsIso ((projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r))
      ((projPartialDomain f).ι ⁻¹ᵁ Proj.basicOpen ℬ (f r)) le_rfl) := by
  set W := (projPartialDomain f).ι ⁻¹ᵁ Proj.basicOpen ℬ (f r)
  have : IsOpenImmersion ((projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl ≫
      (Proj.basicOpen ℬ (f r)).ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  have : IsOpenImmersion ((projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl) :=
    IsOpenImmersion.of_comp _ (Proj.basicOpen ℬ (f r)).ι
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun y => ?_⟩⟩
  have hyU : y.1 ∈ projPartialDomain f :=
    basicOpen_le_projPartialDomain f hi hr y.2
  refine ⟨⟨⟨y.1, hyU⟩, y.2⟩, ?_⟩
  apply (Proj.basicOpen ℬ (f r)).ι.isOpenEmbedding.injective
  change ((projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl ≫
    (Proj.basicOpen ℬ (f r)).ι) _ = _
  rw [Scheme.Hom.resLE_comp_ι]
  rfl

/-- Over a standard open `D₊(r)`, the partial Proj morphism of a surjective graded
homomorphism is a closed immersion. -/
theorem isClosedImmersion_morphismRestrict (hf : Function.Surjective f) {i : ℕ} {r : A}
    (hr : r ∈ 𝒜 i) (hi : 0 < i) :
    IsClosedImmersion (projPartialMap f ∣_ Proj.basicOpen 𝒜 r) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f r))) :=
    IsClosedImmersion.spec_of_surjective _ (surjective_awayMap hf hr)
  have := isIso_resLE (f := f) hr hi
  set W := (projPartialDomain f).ι ⁻¹ᵁ Proj.basicOpen ℬ (f r)
  have hW : projPartialMap f ⁻¹ᵁ Proj.basicOpen 𝒜 r = W := projPartialMap_preimage_basicOpen f r
  have key : projPartialMap f ∣_ Proj.basicOpen 𝒜 r =
      (Scheme.isoOfEq _ hW).hom ≫
        (projPartialDomain f).ι.resLE (Proj.basicOpen ℬ (f r)) W le_rfl ≫
        (Proj.basicOpenIsoSpec ℬ (f r) (f.map_mem hr) hi).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map f r)) ≫
        (Proj.basicOpenIsoSpec 𝒜 r hr hi).inv := by
    rw [← cancel_mono (Proj.basicOpen 𝒜 r).ι, morphismRestrict_ι,
      ← Scheme.isoOfEq_hom_ι _ hW, Category.assoc]
    simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι, Proj.basicOpenIsoSpec_hom]
    congr 1
    exact projPartialCover_f_projPartialMap f r hr hi
  rw [key]
  infer_instance

end ProjSurjection

open ProjSurjection

/-- **Hartshorne II, Exercise 3.12(a), domain.** For a surjective graded
homomorphism `φ : S → T`, the natural domain of the partial Proj morphism is all
of `Proj T`. -/
theorem projPartialDomain_eq_top_of_surjective (hf : Function.Surjective f) :
    projPartialDomain f = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨e, t, he, ht, htx⟩ := ProjTail.exists_homogeneous_not_mem x
  obtain ⟨a, ha, rfl⟩ := exists_homogeneous_preimage hf ht
  rw [mem_projPartialDomain_iff]
  intro h
  exact htx (h ⟨a, mem_irrelevant_of_mem 𝒜 he ha, rfl⟩)

/-- **Hartshorne II, Exercise 3.12(a), closed immersion.** For a surjective graded
homomorphism, the partial Proj morphism `U ⟶ Proj S` is a closed immersion (and
`U = Proj T` by `projPartialDomain_eq_top_of_surjective`). -/
theorem isClosedImmersion_projPartialMap_of_surjective (hf : Function.Surjective f) :
    IsClosedImmersion (projPartialMap f) := by
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (f := projPartialMap f) _ (iSup_basicOpen_eq_top (𝒜 := 𝒜))).mpr ?_
  rintro ⟨i, r, hi, hr⟩
  exact isClosedImmersion_morphismRestrict hf hr hi

/-- **Hartshorne II, Exercise 3.12(a).** A surjective graded homomorphism
`φ : S → T` induces a morphism `Proj T ⟶ Proj S`, namely the partial Proj
morphism on its natural domain, which is all of `Proj T`; this morphism is a
closed immersion. -/
theorem isClosedImmersion_projPartialMap_comp_top_of_surjective
    (hf : Function.Surjective f) :
    IsClosedImmersion ((Proj ℬ).topIso.inv ≫
      (Proj ℬ).homOfLE (projPartialDomain_eq_top_of_surjective hf).ge ≫ projPartialMap f) := by
  have := isClosedImmersion_projPartialMap_of_surjective hf
  have : ∀ (V : (Proj ℬ).Opens) (h : ⊤ ≤ V), IsIso ((Proj ℬ).homOfLE h) := by
    intro V h
    obtain rfl : V = ⊤ := top_le_iff.mp h
    rw [Scheme.homOfLE_rfl]
    infer_instance
  have := this _ (projPartialDomain_eq_top_of_surjective hf).ge
  infer_instance

end Hartshorne
