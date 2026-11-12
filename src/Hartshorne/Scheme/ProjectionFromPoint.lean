/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoordinateNonvanishingOpen
import Hartshorne.RingedSpace.PicardGroup
import Hartshorne.Scheme.Differentials.RelativeDifferentialsBaseChange

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

section Functoriality

variable {X' X Y : Scheme.{u}}

theorem pullbackSection_eq_unit (f : X ⟶ Y) {N : Y.Modules} {W : Y.Opens} (e : Γ(N, W)) :
    pullbackSection f e =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app W e := rfl

/-- `f^* (g^* e)` goes to `(g ∘ f)^* e` under `f^* g^* ≅ (g ∘ f)^*`. -/
theorem pullbackComp_hom_pullbackGlobalSection (f : X' ⟶ X) (g : X ⟶ Y) {N : Y.Modules}
    (e : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app N).app ⊤
        (pullbackGlobalSection f (pullbackGlobalSection g e)) =
      pullbackGlobalSection (f ≫ g) e := by
  have hle : (⊤ : X'.Opens) ≤ f ⁻¹ᵁ g ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]
  have h1 : pullbackGlobalSection f (pullbackGlobalSection g e) =
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)).presheaf.map
        (homOfLE hle).op (pullbackSection f (pullbackSection g e)) := by
    rw [pullbackGlobalSection, pullbackGlobalSection, pullbackSection_restrict,
      Scheme.Modules.map_map_homOfLE]
  have h2 := hom_app_map ((Scheme.Modules.pullbackComp f g).hom.app N) hle
    (pullbackSection f (pullbackSection g e))
  rw [h1]
  refine h2.trans ?_
  exact congrArg (fun t => ((Scheme.Modules.pullback (f ≫ g)).obj N).presheaf.map
    (homOfLE hle).op t) (Scheme.Modules.pullbackComp_hom_unit f g N ⊤ e)

/-- `(g ∘ f)^* e` goes to `f^* (g^* e)` under `(g ∘ f)^* ≅ f^* g^*`. -/
theorem pullbackComp_inv_pullbackGlobalSection (f : X' ⟶ X) (g : X ⟶ Y) {N : Y.Modules}
    (e : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app N).app ⊤ (pullbackGlobalSection (f ≫ g) e) =
      pullbackGlobalSection f (pullbackGlobalSection g e) := by
  rw [← pullbackComp_hom_pullbackGlobalSection]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤)
      ((Scheme.Modules.pullbackComp f g).hom_inv_id_app N)) _

/-- Pulling back a morphism `α` sends `f^* t` to `f^* (α t)`. -/
theorem pullback_map_pullbackGlobalSection (f : X ⟶ Y) {M N : Y.Modules} (α : M ⟶ N)
    (t : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).map α).app ⊤ (pullbackGlobalSection f t) =
      pullbackGlobalSection f (α.app ⊤ t) := by
  rw [pullbackGlobalSection, pullbackGlobalSection, hom_app_map, pullbackSection_eq_unit,
    pullbackSection_eq_unit, Scheme.Modules.pullback_map_unit]

end Functoriality

/-! ### Morphisms defined by sections, under composition -/

section Data

variable {n : ℕ} {X' X Y : Scheme.{u}}

/-- Restricting a global section to `⊤` does nothing. -/
theorem map_homOfLE_top (L : X.Modules) (t : Γ(L, ⊤)) :
    L.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op t = t := by
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **Composition with the morphism defined by sections.** If `φ : X ⟶ ℙⁿ_Y` is defined by the
sections `sᵢ` of `L` (that is, `φ^* 𝒪(1) ≅ L` carrying each `φ^* xᵢ` to `sᵢ`) and `f : X' ⟶ X`,
then `f ≫ φ` is defined by the sections `f^* sᵢ` of `f^* L`. -/
theorem exists_iso_of_comp (f : X' ⟶ X) (φ : X ⟶ projectiveSpaceOverScheme n Y)
    {ψ : X' ⟶ projectiveSpaceOverScheme n Y} (hψ : f ≫ φ = ψ) {L : X.Modules}
    {s : Fin (n + 1) → Γ(L, ⊤)}
    (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅ L)
    (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n Y i)) = s i) :
    ∃ e' : (Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅
        (Scheme.Modules.pullback f).obj L,
      ∀ i, e'.hom.app ⊤ (pullbackGlobalSection ψ (projectiveSpaceCoordinate n Y i)) =
        pullbackGlobalSection f (s i) := by
  subst hψ
  refine ⟨((Scheme.Modules.pullbackComp f φ).app _).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e, fun i => ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackComp_inv_pullbackGlobalSection, pullback_map_pullbackGlobalSection, he]

/-- Sections generate an `𝒪_X`-module if near every point one of them trivializes it. -/
theorem isGeneratedBySections_of_isTrivializingSection {L : X.Modules} {ι : Type u}
    (s : ι → Γ(L, ⊤))
    (h : ∀ x, ∃ i, ∃ W : X.Opens, x ∈ W ∧
      IsTrivializingSection L W (L.presheaf.map (homOfLE le_top).op (s i))) :
    L.IsGeneratedBySections s := by
  intro x
  obtain ⟨i, W, hx, he⟩ := h x
  refine top_unique fun z _ => ?_
  obtain ⟨b, rfl⟩ := he.exists_smul_germ_eq hx z
  rw [TopCat.Presheaf.germ_res_apply]
  exact Submodule.smul_mem _ b (Submodule.subset_span ⟨i, rfl⟩)

/-- The zero section vanishes everywhere. -/
theorem nonvanishingLocus_zero (L : X.Modules) : nonvanishingLocus L 0 = ∅ := by
  ext x
  simp only [nonvanishingLocus, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not,
    map_zero]
  exact Submodule.zero_mem _

end Data

/-! ### The structure sheaf as a module -/

section Unit

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X`, as an `𝒪_X`-module. -/
abbrev structureModule : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- A function `r ∈ Γ(U, 𝒪_X)`, as a section of the `𝒪_X`-module `𝒪_X`. -/
def unitSection {U : X.Opens} (r : Γ(X, U)) : Γ(structureModule X, U) := r

theorem isInvertible_structureModule : (structureModule X).IsInvertible :=
  (Scheme.Modules.isInvertible_iff_ringed _).mpr (Ringed.structureModule_isInvertible (R := X.sheaf))

theorem isTrivializingSection_unitSection_one :
    IsTrivializingSection (structureModule X) ⊤ (unitSection X 1) :=
  IsTrivializingSection.of_isLocalFrame (ι := ULift.{u} (Fin 1))
    (Ringed.structureModule_isLocalFrame (R := X.sheaf))

variable {X}

theorem unitSection_eq_smul {U : X.Opens} (r : Γ(X, U)) :
    unitSection X r = r • unitSection X 1 := by
  change r = r * 1
  rw [mul_one]

theorem isTrivializingSection_unitSection {r : Γ(X, ⊤)} (hr : IsUnit r) :
    IsTrivializingSection (structureModule X) ⊤ (unitSection X r) := by
  rw [unitSection_eq_smul]
  exact (isTrivializingSection_unitSection_one X).unit_smul hr

end Unit

/-! ### Rational points in homogeneous coordinates -/

section RationalPoints

variable (k : Type u) [Field k]

/-- The constant function `c` on `Spec k`. -/
def specConst (c : k) : Γ(Spec (CommRingCat.of k), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv c

theorem isUnit_specConst {c : k} (hc : c ≠ 0) : IsUnit (specConst k c) :=
  (IsUnit.mk0 c hc).map _

theorem specConst_zero : specConst k 0 = 0 :=
  map_zero _

/-- The constants `aᵢ`, as global sections of `𝒪_{Spec k}`. -/
abbrev pointSections {m : ℕ} (a : Fin (m + 1) → k) :
    Fin (m + 1) → Γ(structureModule (Spec (CommRingCat.of k)), ⊤) :=
  fun i => unitSection _ (specConst k (a i))

theorem isGeneratedBySections_pointSections {m : ℕ} {a : Fin (m + 1) → k} (ha : a ≠ 0) :
    (structureModule (Spec (CommRingCat.of k))).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (m + 1)) => pointSections k a i.down) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  refine isGeneratedBySections_of_isTrivializingSection _ fun x => ⟨⟨j⟩, ⊤, trivial, ?_⟩
  rw [map_homOfLE_top]
  exact isTrivializingSection_unitSection (isUnit_specConst k hj)

theorem existsUnique_projectivePoint {m : ℕ} (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    ∃! φ : Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme m (Spec (CommRingCat.of k)),
      φ ≫ projectiveSpaceOverSchemeProjection m _ = 𝟙 _ ∧
      ∃ e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf m _ 1) ≅
          structureModule (Spec (CommRingCat.of k)),
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate m _ i)) =
          pointSections k a i :=
  existsUnique_morphism_of_isGeneratedBySections (𝟙 _) (isInvertible_structureModule _)
    (pointSections k a) (isGeneratedBySections_pointSections k ha)

/-- **The `k`-rational point `(a₀ : ⋯ : a_m)` of `ℙᵐ_k`**, for `a ≠ 0`: the `k`-morphism
`Spec k ⟶ ℙᵐ_k` defined (Hartshorne II, Theorem 7.1) by the global sections `a₀, …, a_m` of
`𝒪_{Spec k}`. -/
def projectivePoint {m : ℕ} (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme m (Spec (CommRingCat.of k)) :=
  (existsUnique_projectivePoint k a ha).exists.choose

theorem projectivePoint_spec {m : ℕ} (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    projectivePoint k a ha ≫ projectiveSpaceOverSchemeProjection m _ = 𝟙 _ ∧
      ∃ e : (Scheme.Modules.pullback (projectivePoint k a ha)).obj
          (projectiveSpaceTwistingSheaf m _ 1) ≅ structureModule (Spec (CommRingCat.of k)),
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (projectivePoint k a ha)
          (projectiveSpaceCoordinate m _ i)) = pointSections k a i :=
  (existsUnique_projectivePoint k a ha).exists.choose_spec

variable {k}

theorem eq_projectivePoint {m : ℕ} {a : Fin (m + 1) → k} (ha : a ≠ 0)
    {φ : Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme m (Spec (CommRingCat.of k))}
    (hφ : φ ≫ projectiveSpaceOverSchemeProjection m _ = 𝟙 _)
    (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf m _ 1) ≅
      structureModule (Spec (CommRingCat.of k)))
    (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate m _ i)) =
      pointSections k a i) :
    φ = projectivePoint k a ha :=
  (existsUnique_projectivePoint k a ha).unique ⟨hφ, e, he⟩ (projectivePoint_spec k a ha)

/-- The point `(a₀ : ⋯ : a_m)` lies in the standard open `D₊(xᵢ)` exactly when `aᵢ ≠ 0`. -/
theorem projectivePoint_mem_projectiveSpaceChart_iff {m : ℕ} {a : Fin (m + 1) → k} (ha : a ≠ 0)
    (i : Fin (m + 1)) (y : Spec (CommRingCat.of k)) :
    projectivePoint k a ha y ∈ projectiveSpaceChart m _ i ↔ a i ≠ 0 := by
  obtain ⟨-, e, he⟩ := projectivePoint_spec k a ha
  have h := preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens
    (isInvertible_structureModule _) (pointSections k a) _ e he i
  change y ∈ projectivePoint k a ha ⁻¹ᵁ projectiveSpaceChart m _ i ↔ _
  rw [h]
  change y ∈ nonvanishingLocus _ _ ↔ _
  by_cases hai : a i = 0
  · simp only [hai, ne_eq, not_true_eq_false, iff_false]
    rw [show pointSections k a i = 0 by
      change unitSection _ (specConst k (a i)) = 0
      rw [hai, specConst_zero]
      rfl, nonvanishingLocus_zero]
    exact Set.notMem_empty y
  · simp only [ne_eq, hai, not_false_eq_true, iff_true]
    have he' := isTrivializingSection_unitSection (isUnit_specConst k hai)
    rw [(he'.mem_nonvanishingLocus_iff (g := 1) (by rw [map_homOfLE_top, one_smul]) trivial),
      Scheme.basicOpen_one]
    trivial

end RationalPoints

/-! ### The projection -/

section Projection

variable (n : ℕ) (Y : Scheme.{u})

/-- The open subset `U = D₊(x₀) ∪ ⋯ ∪ D₊(xₙ)` of `ℙⁿ⁺¹_Y` where one of the first `n + 1`
homogeneous coordinates `x₀, …, xₙ` does not vanish. Over a field it is the complement of the
coordinate point `(0 : ⋯ : 0 : 1)` (`projectionDomain_eq_compl_range`). -/
def projectionDomain : (projectiveSpaceOverScheme (n + 1) Y).Opens :=
  ⨆ i : Fin (n + 1), projectiveSpaceChart (n + 1) Y i.castSucc

/-- The restriction `𝒪(1)|_U` of `𝒪(1)` on `ℙⁿ⁺¹_Y` to `U`. -/
abbrev projectionDomainTwist : (projectionDomain n Y).toScheme.Modules :=
  (Scheme.Modules.pullback (projectionDomain n Y).ι).obj (projectiveSpaceTwistingSheaf (n + 1) Y 1)

/-- The restrictions to `U` of the remaining homogeneous coordinates `x₀, …, xₙ`. -/
abbrev projectionSections (i : Fin (n + 1)) : Γ(projectionDomainTwist n Y, ⊤) :=
  pullbackGlobalSection (projectionDomain n Y).ι (projectiveSpaceCoordinate (n + 1) Y i.castSucc)

/-- On `U`, the remaining coordinates `x₀, …, xₙ` generate `𝒪(1)|_U`: they have no common zero
on `U`. -/
theorem isGeneratedBySections_projectionSections :
    (projectionDomainTwist n Y).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (n + 1)) => projectionSections n Y i.down) := by
  refine isGeneratedBySections_of_isTrivializingSection _ fun y => ?_
  have hy : (projectionDomain n Y).ι y ∈ projectionDomain n Y :=
    y.2
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨⟨i⟩, (projectionDomain n Y).ι ⁻¹ᵁ projectiveSpaceChart (n + 1) Y i.castSucc, hi, ?_⟩
  rw [pullbackGlobalSection_restrict]
  exact IsTrivializingSection.pullback _ (isTrivializingSection_projectiveSpaceChart _ _ _)

theorem existsUnique_projection :
    ∃! π : (projectionDomain n Y).toScheme ⟶ projectiveSpaceOverScheme n Y,
      π ≫ projectiveSpaceOverSchemeProjection n Y =
        (projectionDomain n Y).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) Y ∧
      ∃ e : (Scheme.Modules.pullback π).obj (projectiveSpaceTwistingSheaf n Y 1) ≅
          projectionDomainTwist n Y,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection π (projectiveSpaceCoordinate n Y i)) =
          projectionSections n Y i :=
  existsUnique_morphism_of_isGeneratedBySections _
    (Scheme.Modules.IsInvertible.pullback _ (isInvertible_projectiveSpaceTwistingSheaf _ _ _))
    (projectionSections n Y) (isGeneratedBySections_projectionSections n Y)

/-- **Projection from the coordinate point.** The morphism `U ⟶ ℙⁿ_Y` defined (Hartshorne II,
Theorem 7.1) by the remaining homogeneous coordinates `x₀, …, xₙ` of `ℙⁿ⁺¹_Y`, restricted to the
open `U` where they have no common zero. -/
def projectionFromPoint : (projectionDomain n Y).toScheme ⟶ projectiveSpaceOverScheme n Y :=
  (existsUnique_projection n Y).exists.choose

theorem projectionFromPoint_spec :
    projectionFromPoint n Y ≫ projectiveSpaceOverSchemeProjection n Y =
        (projectionDomain n Y).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) Y ∧
      ∃ e : (Scheme.Modules.pullback (projectionFromPoint n Y)).obj
          (projectiveSpaceTwistingSheaf n Y 1) ≅ projectionDomainTwist n Y,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (projectionFromPoint n Y)
          (projectiveSpaceCoordinate n Y i)) = projectionSections n Y i :=
  (existsUnique_projection n Y).exists.choose_spec

end Projection

end Hartshorne
