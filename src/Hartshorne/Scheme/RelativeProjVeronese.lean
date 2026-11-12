/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeProjDesc
import Hartshorne.Scheme.VeroneseDuple

/-!
# Veronese subalgebras of a quasi-coherent graded algebra

For a quasi-coherent graded `𝒪_X`-algebra `S` and `d > 0`, the Veronese subalgebra
`S^{(d)} = ⨁_m S_{md}` is again a quasi-coherent graded `𝒪_X`-algebra
(`QuasiCoherentGradedAlgebra.veronese`), and `Proj_X S^{(d)} ≅ Proj_X S` over `X`
(`QuasiCoherentGradedAlgebra.relProjVeroneseIso`), glued from the affine isomorphisms
`Proj S(U) ≅ Proj S(U)^{(d)}` (Hartshorne II, Exercise 5.13, `Veronese.projIso`). This is the
operation "replace `L` by `L^d`" of the proof of Hartshorne II, Theorem 7.17, Step 2.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Graded

universe u

namespace Hartshorne

section Algebra

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (d : ℕ) [NeZero d]
  (φ : 𝒜 →+*ᵍ ℬ) {s : A} (hs : s ∈ 𝒜 0) [Algebra A B] [IsLocalization.Away s B]
  (hφ : ∀ a, φ a = algebraMap A B a)

/-- A degree-zero element as an element of the Veronese subring. -/
private def veroneseOfZero {a : A} (ha : a ∈ 𝒜 0) : veroneseSubring 𝒜 d :=
  Veronese.ofMem (n := 0) (by rwa [zero_mul])

include hs hφ in
/-- **The Veronese subring commutes with localization at a degree-zero element.** If
`B = A[1/s]` with `s` of degree zero, then `B^{(d)} = A^{(d)}[1/s]`. -/
theorem veronese_isLocalizationAway :
    letI := (Veronese.veroneseMap d φ).toRingHom.toAlgebra
    IsLocalization.Away (veroneseOfZero d hs) (veroneseSubring ℬ d) := by
  let := (Veronese.veroneseMap d φ).toRingHom.toAlgebra
  obtain ⟨v, hv0, hv⟩ := exists_mem_zero_mul_eq_one_of_isUnit (map_mem φ hs)
    (by rw [hφ s]; exact IsLocalization.Away.algebraMap_isUnit s)
  have hmap : ∀ y : veroneseSubring 𝒜 d,
      ((algebraMap (veroneseSubring 𝒜 d) (veroneseSubring ℬ d) y : veroneseSubring ℬ d) : B) =
        φ (y : A) := fun _ => rfl
  constructor; constructor
  · rintro ⟨_, n, rfl⟩
    change IsUnit (algebraMap _ _ (veroneseOfZero d hs ^ n))
    rw [map_pow]
    refine IsUnit.pow n (isUnit_iff_exists_inv.mpr ⟨veroneseOfZero d hv0, ?_⟩)
    apply Subtype.ext
    rw [Subring.coe_mul, hmap]
    exact hv
  · intro z
    -- The set of elements of `B^{(d)}` with a numerator in `A^{(d)}` is an additive subgroup
    -- containing the homogeneous elements.
    let P : Set (veroneseSubring ℬ d) := {z | ∃ (a : veroneseSubring 𝒜 d) (k : ℕ),
      z * algebraMap _ _ (veroneseOfZero d hs) ^ k = algebraMap _ _ a}
    have hP : z ∈ P := by
      induction z using DirectSum.Decomposition.inductionOn (veronese ℬ d) with
      | zero => exact ⟨0, 0, by simp⟩
      | @homogeneous n b =>
        obtain ⟨b, hb⟩ := b
        obtain ⟨a, ha, k, h⟩ := exists_mem_mul_pow_eq_of_isLocalizationAway φ hs hφ
          (Veronese.mem_veronese_iff.mp hb)
        refine ⟨Veronese.ofMem ha, k, Subtype.ext ?_⟩
        simp only [Subring.coe_mul, SubmonoidClass.coe_pow, hmap]
        exact h
      | add x y hx hy =>
        obtain ⟨a, k, hk⟩ := hx
        obtain ⟨a', k', hk'⟩ := hy
        refine ⟨a * veroneseOfZero d hs ^ k' + a' * veroneseOfZero d hs ^ k, k + k', ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hk, ← hk', pow_add]
        ring
    obtain ⟨a, k, hk⟩ := hP
    exact ⟨⟨a, ⟨_, k, rfl⟩⟩, by simp only [map_pow]; exact hk⟩
  · intro x y e
    have e' : algebraMap A B x = algebraMap A B y := by
      rw [← hφ, ← hφ]
      exact congrArg Subtype.val e
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers s) e'
    refine ⟨⟨_, n, rfl⟩, Subtype.ext ?_⟩
    simpa [veroneseOfZero] using hn

end Algebra

namespace QuasiCoherentGradedAlgebra

open Scheme.AffineZariskiSite

variable {X : Scheme.{u}} (S : QuasiCoherentGradedAlgebra X) (d : ℕ) [NeZero d]

omit [NeZero d] in
/-- The structure map lands in the Veronese subring. -/
private theorem structureMap_mem_veroneseSubring (U : X.AffineZariskiSite) (r : Γ(X, U.1)) :
    S.structureMap.app (.op U) r ∈ veroneseSubring (S.grading U) d :=
  Veronese.mem_veroneseSubring_of_mem (n := 0) (by rw [zero_mul]; exact S.structureMap_mem U r)

/-- The functor `U ↦ S(U)^{(d)}`. -/
private abbrev veroneseObj : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (veroneseSubring (S.grading U.unop) d)
  map f := CommRingCat.ofHom (Veronese.veroneseMap d (S.restrict f.unop)).toRingHom
  map_id U := by
    ext x
    change S.obj.map (𝟙 _) (x : S.obj.obj U) = x
    rw [S.obj.map_id]
    rfl
  map_comp f g := by
    ext x
    change S.obj.map (f ≫ g) (x : S.obj.obj _) = S.obj.map g (S.obj.map f x)
    rw [S.obj.map_comp]
    rfl

/-- **The Veronese subalgebra `S^{(d)} = ⨁_m S_{md}`** of a quasi-coherent graded
`𝒪_X`-algebra, graded by `m`. -/
abbrev veronese : QuasiCoherentGradedAlgebra X where
  obj := S.veroneseObj d
  structureMap :=
    { app U := CommRingCat.ofHom ((S.structureMap.app U).hom.codRestrict _
        (S.structureMap_mem_veroneseSubring d U.unop))
      naturality U V f := by
        ext r
        exact congr($(S.structureMap.naturality f) r) }
  coequifibered := by
    rw [coequifibered_iff_forall_isLocalizationAway]
    intro U r
    let := (S.obj.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
    have := S.isLocalizationAway U r
    exact veronese_isLocalizationAway d (S.restrict (homOfLE (U.basicOpen_le r)))
      (S.structureMap_mem U r) (fun _ => rfl)
  grading U := Hartshorne.veronese (S.grading U) d
  gradedRing _ := Veronese.gradedRing
  map_mem f _ _ hx := (Veronese.veroneseMap d (S.restrict f)).map_mem hx
  structureMap_mem U r := by
    change S.structureMap.app (.op U) r ∈ S.grading U (0 * d)
    rw [zero_mul]
    exact S.structureMap_mem U r

theorem veronese_restrict {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    (S.veronese d).restrict f = Veronese.veroneseMap d (S.restrict f) :=
  rfl

/-- The structure maps of `S^{(d)}` and `S` agree under `S^{(d)}_0 = S_0`. -/
theorem veronese_toZero_zeroEquiv (U : X.AffineZariskiSite) :
    (S.veronese d).toZero U ≫ CommRingCat.ofHom (Veronese.zeroEquiv (S.grading U) d).toRingHom =
      S.toZero U :=
  rfl

/-- `S^{(d)}_0 = S_0`: if `S₀ = 𝒪_X` then `S^{(d)}_0 = 𝒪_X`. -/
theorem DegreeZeroIsStructureSheaf.veronese (h : S.DegreeZeroIsStructureSheaf) :
    (S.veronese d).DegreeZeroIsStructureSheaf := by
  intro U
  have e : ⇑((S.veronese d).toZero U) =
      (Veronese.zeroEquiv (S.grading U) d).symm ∘ ⇑(S.toZero U) := by
    funext a
    rfl
  rw [e]
  exact (Veronese.zeroEquiv (S.grading U) d).symm.bijective.comp (h U)

/-- `Proj S(U)^{(d)} ≅ Proj S(U)` lies over `U`. -/
theorem projIso_inv_projToOpen (U : X.AffineZariskiSite) :
    (Veronese.projIso (S.grading U) d).inv ≫ S.projToOpen U = (S.veronese d).projToOpen U := by
  rw [← cancel_mono U.1.ι, Category.assoc, projToOpen_ι, projToOpen_ι, Iso.inv_comp_eq,
    Veronese.projIso_hom, reassoc_of% Veronese.toProj_comp_toSpecZero, ← Spec.map_comp_assoc,
    veronese_toZero_zeroEquiv]

/-- The compatible open immersions `Proj S(U)^{(d)} ≅ Proj S(U) ⟶ Proj_X S`. -/
private def veroneseToRelProj (U : X.AffineZariskiSite) :
    Proj ((S.veronese d).grading U) ⟶ S.relProj :=
  (Veronese.projIso (S.grading U) d).inv ≫ S.projι U

private theorem veroneseToRelProj_map {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    Proj.map ((S.veronese d).restrict f) ((S.veronese d).irrelevant_le f) ≫
      S.veroneseToRelProj d V = S.veroneseToRelProj d U := by
  have hw : Proj.map (S.restrict f) (S.irrelevant_le f) ≫ S.projι V = S.projι U :=
    colimit.w S.relativeGluingData.functor f
  have h := Veronese.map_comp_toProj d (S.restrict f) (S.irrelevant_le f)
    ((S.veronese d).irrelevant_le f)
  have h' : Proj.map (Veronese.veroneseMap d (S.restrict f)) ((S.veronese d).irrelevant_le f) ≫
      inv (Veronese.toProj (𝒜 := S.grading V) d) =
        inv (Veronese.toProj (𝒜 := S.grading U) d) ≫
          Proj.map (S.restrict f) (S.irrelevant_le f) := by
    rw [IsIso.comp_inv_eq, Category.assoc, h, IsIso.inv_hom_id_assoc]
  show Proj.map (Veronese.veroneseMap d (S.restrict f)) ((S.veronese d).irrelevant_le f) ≫
      inv (Veronese.toProj d) ≫ S.projι V = inv (Veronese.toProj d) ≫ S.projι U
  rw [reassoc_of% h', hw]

private instance (U : X.AffineZariskiSite) : IsOpenImmersion (S.veroneseToRelProj d U) :=
  inferInstanceAs (IsOpenImmersion ((Veronese.projIso (S.grading U) d).inv ≫ S.projι U))

private theorem veroneseToRelProj_base (U : X.AffineZariskiSite) :
    S.veroneseToRelProj d U ≫ S.relProjToBase = (S.veronese d).projToOpen U ≫ U.1.ι := by
  rw [veroneseToRelProj, Category.assoc, projι_relProjToBase, ← Category.assoc,
    projIso_inv_projToOpen]

private theorem veroneseToRelProj_range (U : X.AffineZariskiSite) :
    S.relProjToBase ⁻¹ᵁ U.1 = (S.veroneseToRelProj d U).opensRange := by
  change _ = ((Veronese.projIso (S.grading U) d).inv ≫ S.projι U).opensRange
  rw [Scheme.Hom.opensRange_comp_of_isIso, relProjToBase_preimage]

/-- **`Proj_X S^{(d)} ≅ Proj_X S`** (cf. Hartshorne II, Exercise 5.13, relative version), glued
from the isomorphisms `Proj S(U)^{(d)} ≅ Proj S(U)` over the affine opens `U ⊆ X`. -/
def relProjVeroneseIso : (S.veronese d).relProj ≅ S.relProj :=
  (S.veronese d).relProjIsoOfProj (S.veroneseToRelProj d) (fun f => S.veroneseToRelProj_map d f)
    S.relProjToBase (S.veroneseToRelProj_base d) (S.veroneseToRelProj_range d)

/-- The isomorphism `Proj_X S^{(d)} ≅ Proj_X S` lies over `X`. -/
@[reassoc]
theorem relProjVeroneseIso_hom_relProjToBase :
    (S.relProjVeroneseIso d).hom ≫ S.relProjToBase = (S.veronese d).relProjToBase :=
  (S.veronese d).relProjDesc_comp (S.veroneseToRelProj d) (fun f => S.veroneseToRelProj_map d f)
    S.relProjToBase (S.veroneseToRelProj_base d)

end QuasiCoherentGradedAlgebra

end Hartshorne
