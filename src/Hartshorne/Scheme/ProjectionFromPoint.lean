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

/-! ### The domain is the complement of the coordinate point -/

section CoordinatePoint

variable (k : Type u) [Field k] (n : ℕ)

theorem pullbackGlobalSection_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) :
    pullbackGlobalSection f (0 : Γ(N, ⊤)) = 0 := by
  have h := pullbackSection_smul f (0 : Γ(Y, ⊤)) (0 : Γ(N, ⊤))
  rw [zero_smul, map_zero, zero_smul] at h
  rw [pullbackGlobalSection, h, map_zero]

theorem single_last_ne_zero : (Pi.single (Fin.last (n + 1)) (1 : k) : Fin (n + 2) → k) ≠ 0 := by
  intro h
  simpa using congrFun h (Fin.last _)

/-- **The coordinate point `P = (0 : ⋯ : 0 : 1)` of `ℙⁿ⁺¹_k`**, as a `k`-rational point. -/
def coordinatePoint :
    Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k)) :=
  projectivePoint k (Pi.single (Fin.last (n + 1)) 1) (single_last_ne_zero k n)

theorem coordinatePoint_notMem_projectionDomain (y : Spec (CommRingCat.of k)) :
    coordinatePoint k n y ∉ projectionDomain n (Spec (CommRingCat.of k)) := by
  intro h
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h
  rw [coordinatePoint, projectivePoint_mem_projectiveSpaceChart_iff] at hi
  exact hi (Pi.single_eq_of_ne (Fin.castSucc_ne_last i) _)

/-- A morphism from a reduced scheme to `ℙⁿ⁺¹_k` whose image avoids `U` (so `x₀, …, xₙ` vanish
on its image) factors through the coordinate point `P`: by Theorem 7.1 it is defined by the
pulled-back coordinates, of which only the last is nonzero. -/
theorem eq_comp_coordinatePoint {T : Scheme.{u}} [IsReduced T]
    (g : T ⟶ projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k)))
    (hg : ∀ y, g y ∉ projectionDomain n (Spec (CommRingCat.of k))) :
    g = (g ≫ projectiveSpaceOverSchemeProjection (n + 1) _) ≫ coordinatePoint k n := by
  set c := g ≫ projectiveSpaceOverSchemeProjection (n + 1) (Spec (CommRingCat.of k))
  set M := (Scheme.Modules.pullback g).obj (projectiveSpaceTwistingSheaf (n + 1) _ 1)
  set t : Fin (n + 2) → Γ(M, ⊤) := fun i =>
    pullbackGlobalSection g (projectiveSpaceCoordinate (n + 1) _ i)
  have hM : M.IsInvertible := isInvertible_pullback_projectiveSpaceTwistingSheaf g
  have ht : M.IsGeneratedBySections (fun i : ULift.{u} (Fin (n + 2)) => t i.down) :=
    isGeneratedBySections_pullback_projectiveSpaceCoordinate g
  have hpre : ∀ i, g ⁻¹ᵁ projectiveSpaceChart (n + 1) _ i = nonvanishingLocusOpens hM (t i) :=
    fun i => preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hM t g (Iso.refl _)
      (fun _ => rfl) i
  -- `x₀, …, xₙ` vanish on `T`
  have hzero : ∀ (i : Fin (n + 1)) y, y ∉ nonvanishingLocus M (t i.castSucc) := by
    intro i y hy
    have hy' : y ∈ g ⁻¹ᵁ projectiveSpaceChart (n + 1) _ i.castSucc := by
      rw [hpre]
      exact hy
    exact hg y (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hy'⟩)
  have hlast : ∀ y, y ∈ nonvanishingLocus M (t (Fin.last _)) := by
    intro y
    obtain ⟨⟨j⟩, hj⟩ := exists_mem_nonvanishingLocus_of_isGeneratedBySections hM ht y
    induction j using Fin.lastCases with
    | last => exact hj
    | cast i => exact absurd hj (hzero i y)
  -- so `x_{n+1}` trivializes the pullback of `𝒪(1)` and the other coordinates are zero
  have htriv : IsTrivializingSection M ⊤ (t (Fin.last _)) :=
    IsTrivializingSection.of_local fun y _ => ⟨nonvanishingLocusOpens hM (t (Fin.last _)),
      le_top, hlast y, isTrivializingSection_nonvanishingLocusOpens hM _⟩
  have ht0 : ∀ i : Fin (n + 1), t i.castSucc = 0 := by
    intro i
    obtain ⟨r, hr⟩ := htriv.exists_eq_smul (t i.castSucc)
    have hb := htriv.nonvanishingLocus_inter_eq hr
    have hr0 : r = 0 := by
      rw [← basicOpen_eq_bot_iff]
      refine SetLike.coe_injective (hb.symm.trans ?_)
      ext y
      simp only [Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false,
        iff_false, not_and]
      exact fun h _ => hzero i y h
    rw [map_homOfLE_top, hr0, zero_smul] at hr
    exact hr
  -- the corresponding data for `c ≫ P`
  have hu : IsTrivializingSection ((Scheme.Modules.pullback c).obj (structureModule _)) ⊤
      (pullbackGlobalSection c (unitSection _ 1)) :=
    (IsTrivializingSection.pullback c (isTrivializingSection_unitSection_one _)).restrict
      (Scheme.Hom.preimage_top c).ge
  have σ : PUnit.{u + 1} ≃ ULift.{u} (Fin 1) := Equiv.ofUnique _ _
  obtain ⟨α, hα⟩ := Ringed.exists_iso_of_frames (R := T.sheaf)
    (fun _ : PUnit.{u + 1} => ⊤) (le_iSup (fun _ : PUnit.{u + 1} => ⊤) PUnit.unit)
    (A := M) (B := (Scheme.Modules.pullback c).obj (structureModule _))
    (fun _ => t (Fin.last _)) (fun _ => pullbackGlobalSection c (unitSection _ 1))
    (fun _ => (isLocalFrame_of_isTrivializingSection htriv).reindex σ)
    (fun _ => (isLocalFrame_of_isTrivializingSection hu).reindex σ)
    (fun _ _ => ⟨1, by rw [one_smul], by rw [one_smul]⟩)
  let α' : M ≅ (Scheme.Modules.pullback c).obj (structureModule _) := α
  have hα' : α'.hom.app ⊤ (t (Fin.last _)) = pullbackGlobalSection c (unitSection _ 1) :=
    hα PUnit.unit
  have hsec : ∀ i, pullbackGlobalSection c (pointSections k (Pi.single (Fin.last (n + 1)) 1) i) =
      α'.hom.app ⊤ (t i) := by
    intro i
    induction i using Fin.lastCases with
    | last =>
      refine Eq.trans ?_ hα'.symm
      simp only [pointSections, Pi.single_eq_same]
      rw [show specConst k 1 = 1 from map_one _]
    | cast i =>
      rw [ht0 i, map_zero]
      simp only [pointSections, Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]
      rw [specConst_zero]
      exact pullbackGlobalSection_zero c _
  obtain ⟨-, e, he⟩ := projectivePoint_spec k (Pi.single (Fin.last (n + 1)) 1)
    (single_last_ne_zero k n)
  obtain ⟨e', he'⟩ := exists_iso_of_comp c _ rfl e he
  have hgen : ((Scheme.Modules.pullback c).obj (structureModule _)).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (n + 2)) =>
        pullbackGlobalSection c (pointSections k (Pi.single (Fin.last (n + 1)) 1) i.down)) := by
    refine isGeneratedBySections_of_isTrivializingSection _ fun y =>
      ⟨⟨Fin.last _⟩, ⊤, trivial, ?_⟩
    rw [map_homOfLE_top, hsec, hα']
    exact hu
  have hc : (c ≫ coordinatePoint k n) ≫ projectiveSpaceOverSchemeProjection (n + 1) _ = c := by
    rw [Category.assoc, coordinatePoint, (projectivePoint_spec k _ _).1, Category.comp_id]
  exact (existsUnique_morphism_of_isGeneratedBySections c
    (Scheme.Modules.IsInvertible.pullback c (isInvertible_structureModule _))
    (fun i => pullbackGlobalSection c (pointSections k (Pi.single (Fin.last (n + 1)) 1) i))
    hgen).unique
    (y₁ := g) (y₂ := c ≫ coordinatePoint k n) ⟨rfl, α', fun i => (hsec i).symm⟩ ⟨hc, e', he'⟩

/-- A point of `ℙⁿ⁺¹_k` at which `x₀, …, xₙ` all vanish is the coordinate point: apply
`eq_comp_coordinatePoint` to `Spec κ(x) ⟶ ℙⁿ⁺¹_k`. -/
theorem mem_range_coordinatePoint {x : projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k))}
    (hx : x ∉ projectionDomain n (Spec (CommRingCat.of k))) :
    x ∈ Set.range (coordinatePoint k n) := by
  have hgx : ∀ y, Scheme.fromSpecResidueField _ x y = x := fun y =>
    Scheme.fromSpecResidueField_apply x y
  have h := eq_comp_coordinatePoint k n (Scheme.fromSpecResidueField _ x)
    (fun y => (hgx y).symm ▸ hx)
  refine ⟨(Scheme.fromSpecResidueField _ x ≫
    projectiveSpaceOverSchemeProjection (n + 1) _) default, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← h]
  exact hgx default

/-- **`U` is `ℙⁿ⁺¹_k` minus the coordinate point `P = (0 : ⋯ : 0 : 1)`.** -/
theorem projectionDomain_eq_compl_range :
    (projectionDomain n (Spec (CommRingCat.of k)) : Set _) =
      (Set.range (coordinatePoint k n))ᶜ := by
  ext x
  refine ⟨fun hx ⟨y, hy⟩ => coordinatePoint_notMem_projectionDomain k n y (hy ▸ hx), fun hx => ?_⟩
  by_contra h
  exact hx (mem_range_coordinatePoint k n h)

end CoordinatePoint

/-! ### The hyperplane `x_{n+1} = 0` -/

section Hyperplane

variable (n : ℕ) (Y : Scheme.{u})

/-- The sections `x₀, …, xₙ, 0` of `𝒪(1)` on `ℙⁿ_Y`. -/
abbrev hyperplaneSections : Fin (n + 2) → Γ(projectiveSpaceTwistingSheaf n Y 1, ⊤) :=
  Fin.lastCases 0 (projectiveSpaceCoordinate n Y)

theorem isGeneratedBySections_hyperplaneSections :
    (projectiveSpaceTwistingSheaf n Y 1).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (n + 2)) => hyperplaneSections n Y i.down) := by
  refine isGeneratedBySections_of_isTrivializingSection _ fun y => ?_
  obtain ⟨i, hi⟩ := exists_mem_chartPreimage (𝟙 (projectiveSpaceOverScheme n Y)) y
  refine ⟨⟨i.castSucc⟩, projectiveSpaceChart n Y i, hi, ?_⟩
  simp only [hyperplaneSections, Fin.lastCases_castSucc]
  exact isTrivializingSection_projectiveSpaceChart n Y i

theorem existsUnique_hyperplaneInclusion :
    ∃! j : projectiveSpaceOverScheme n Y ⟶ projectiveSpaceOverScheme (n + 1) Y,
      j ≫ projectiveSpaceOverSchemeProjection (n + 1) Y = projectiveSpaceOverSchemeProjection n Y ∧
      ∃ e : (Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf (n + 1) Y 1) ≅
          projectiveSpaceTwistingSheaf n Y 1,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection j (projectiveSpaceCoordinate (n + 1) Y i)) =
          hyperplaneSections n Y i :=
  existsUnique_morphism_of_isGeneratedBySections _ (isInvertible_projectiveSpaceTwistingSheaf _ _ _)
    (hyperplaneSections n Y) (isGeneratedBySections_hyperplaneSections n Y)

/-- **The coordinate hyperplane `H ≅ ℙⁿ_Y`**: the morphism `ℙⁿ_Y ⟶ ℙⁿ⁺¹_Y`,
`(x₀ : ⋯ : xₙ) ↦ (x₀ : ⋯ : xₙ : 0)`, defined (Hartshorne II, Theorem 7.1) by the sections
`x₀, …, xₙ, 0` of `𝒪(1)` on `ℙⁿ_Y`. Its image lies in the hyperplane `x_{n+1} = 0`
(`hyperplaneInclusion_notMem_projectiveSpaceChart_last`). -/
def hyperplaneInclusion : projectiveSpaceOverScheme n Y ⟶ projectiveSpaceOverScheme (n + 1) Y :=
  (existsUnique_hyperplaneInclusion n Y).exists.choose

theorem hyperplaneInclusion_spec :
    hyperplaneInclusion n Y ≫ projectiveSpaceOverSchemeProjection (n + 1) Y =
        projectiveSpaceOverSchemeProjection n Y ∧
      ∃ e : (Scheme.Modules.pullback (hyperplaneInclusion n Y)).obj
          (projectiveSpaceTwistingSheaf (n + 1) Y 1) ≅ projectiveSpaceTwistingSheaf n Y 1,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (hyperplaneInclusion n Y)
          (projectiveSpaceCoordinate (n + 1) Y i)) = hyperplaneSections n Y i :=
  (existsUnique_hyperplaneInclusion n Y).exists.choose_spec

/-- The image of `ℙⁿ_Y` lies in the hyperplane `H = {x_{n+1} = 0}` of `ℙⁿ⁺¹_Y`. -/
theorem hyperplaneInclusion_notMem_projectiveSpaceChart_last (y : projectiveSpaceOverScheme n Y) :
    hyperplaneInclusion n Y y ∉ projectiveSpaceChart (n + 1) Y (Fin.last (n + 1)) := by
  obtain ⟨-, e, he⟩ := hyperplaneInclusion_spec n Y
  have h := preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens
    (isInvertible_projectiveSpaceTwistingSheaf _ _ _) (hyperplaneSections n Y) _ e he
    (Fin.last (n + 1))
  intro hy
  change y ∈ hyperplaneInclusion n Y ⁻¹ᵁ projectiveSpaceChart (n + 1) Y (Fin.last (n + 1)) at hy
  rw [h] at hy
  change y ∈ nonvanishingLocus _ _ at hy
  simp only [hyperplaneSections, Fin.lastCases_last] at hy
  rw [nonvanishingLocus_zero] at hy
  exact hy

end Hyperplane

/-! ### Projection of rational points -/

section RationalProjection

variable {k : Type u} [Field k] {n : ℕ}

theorem Scheme.Modules.inv_app_eq_of_hom_app_eq {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    {U : X.Opens} {s : Γ(M, U)} {t : Γ(N, U)} (h : e.hom.app U s = t) : e.inv.app U t = s := by
  rw [← h]
  exact ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U) e.hom_inv_id) s

theorem ne_zero_of_comp_castSucc_ne_zero {a : Fin (n + 2) → k}
    (ha : (fun i : Fin (n + 1) => a i.castSucc) ≠ 0) : a ≠ 0 := by
  rintro rfl
  exact ha rfl

theorem projectivePoint_congr {m : ℕ} {a b : Fin (m + 1) → k} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a = b) : projectivePoint k a ha = projectivePoint k b hb := by
  subst h
  rfl

/-- The hyperplane inclusion sends `(b₀ : ⋯ : bₙ)` to `(b₀ : ⋯ : bₙ : 0)`. -/
theorem projectivePoint_comp_hyperplaneInclusion {b : Fin (n + 1) → k} (hb : b ≠ 0)
    (hb' : (Fin.lastCases 0 b : Fin (n + 2) → k) ≠ 0) :
    projectivePoint k b hb ≫ hyperplaneInclusion n _ = projectivePoint k (Fin.lastCases 0 b) hb' := by
  obtain ⟨hp, eb, heb⟩ := projectivePoint_spec k b hb
  obtain ⟨hj, ej, hej⟩ := hyperplaneInclusion_spec n (Spec (CommRingCat.of k))
  obtain ⟨e', he'⟩ := exists_iso_of_comp (projectivePoint k b hb) _ rfl ej hej
  refine eq_projectivePoint hb' (by rw [Category.assoc, hj, hp]) (e' ≪≫ eb) fun i => ?_
  rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, he']
  induction i using Fin.lastCases with
  | last =>
    simp only [hyperplaneSections, Fin.lastCases_last, pointSections]
    rw [pullbackGlobalSection_zero, map_zero, specConst_zero]
    rfl
  | cast i =>
    simp only [hyperplaneSections, Fin.lastCases_castSucc]
    rw [heb]
    simp only [pointSections, Fin.lastCases_castSucc]

/-- The rational point `Q = (a₀ : ⋯ : a_{n+1})` lies in `U` (i.e. `Q ≠ P`) when
`(a₀, …, aₙ) ≠ 0`, and then the projection sends it to `(a₀ : ⋯ : aₙ)`. -/
theorem exists_lift_projectivePoint_comp_projectionFromPoint {a : Fin (n + 2) → k}
    (ha : (fun i : Fin (n + 1) => a i.castSucc) ≠ 0) :
    ∃ Q : Spec (CommRingCat.of k) ⟶ (projectionDomain n (Spec (CommRingCat.of k))).toScheme,
      Q ≫ (projectionDomain n _).ι = projectivePoint k a (ne_zero_of_comp_castSucc_ne_zero ha) ∧
      Q ≫ projectionFromPoint n _ = projectivePoint k (fun i : Fin (n + 1) => a i.castSucc) ha := by
  have ha0 := ne_zero_of_comp_castSucc_ne_zero ha
  have hrange : Set.range (projectivePoint k a ha0) ⊆
      Set.range (projectionDomain n (Spec (CommRingCat.of k))).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨j, (projectivePoint_mem_projectiveSpaceChart_iff ha0 _ y).mpr hj⟩
  set Q := IsOpenImmersion.lift _ _ hrange
  have hQ : Q ≫ (projectionDomain n _).ι = projectivePoint k a ha0 := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Q, hQ, ?_⟩
  obtain ⟨hpa, ea, hea⟩ := projectivePoint_spec k a ha0
  obtain ⟨hπ, eπ, heπ⟩ := projectionFromPoint_spec n (Spec (CommRingCat.of k))
  obtain ⟨e1, he1⟩ := exists_iso_of_comp Q _ hQ (Iso.refl (projectionDomainTwist n _))
    (s := fun i => pullbackGlobalSection (projectionDomain n _).ι
      (projectiveSpaceCoordinate (n + 1) _ i)) (fun _ => rfl)
  obtain ⟨e2, he2⟩ := exists_iso_of_comp Q _ rfl eπ heπ
  refine eq_projectivePoint ha (by rw [Category.assoc, hπ, ← Category.assoc, hQ, hpa])
    (e2 ≪≫ e1.symm ≪≫ ea) fun i => ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [he2, Scheme.Modules.inv_app_eq_of_hom_app_eq e1 (he1 i.castSucc), hea]

/-- **Projection of a rational point is the intersection of a line with `H`.** For
`Q = (a₀ : ⋯ : a_{n+1}) ≠ P = (0 : ⋯ : 0 : 1)`, the image of `π(Q)` in `H` is the point
`(a₀ : ⋯ : aₙ : 0) = Q − a_{n+1} P`: it lies on the line through `P` and `Q`, and on
`H = {x_{n+1} = 0}`. -/
theorem exists_lift_projectivePoint_comp_projectionFromPoint_hyperplaneInclusion
    {a : Fin (n + 2) → k} (ha : (fun i : Fin (n + 1) => a i.castSucc) ≠ 0)
    (ha' : a - a (Fin.last (n + 1)) • Pi.single (Fin.last (n + 1)) 1 ≠ 0) :
    ∃ Q : Spec (CommRingCat.of k) ⟶ (projectionDomain n (Spec (CommRingCat.of k))).toScheme,
      Q ≫ (projectionDomain n _).ι = projectivePoint k a (ne_zero_of_comp_castSucc_ne_zero ha) ∧
      Q ≫ projectionFromPoint n _ ≫ hyperplaneInclusion n _ =
        projectivePoint k (a - a (Fin.last (n + 1)) • Pi.single (Fin.last (n + 1)) 1) ha' := by
  obtain ⟨Q, hQ, hπ⟩ := exists_lift_projectivePoint_comp_projectionFromPoint ha
  have hv : (Fin.lastCases 0 (fun i : Fin (n + 1) => a i.castSucc) : Fin (n + 2) → k) =
      a - a (Fin.last (n + 1)) • Pi.single (Fin.last (n + 1)) 1 := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  refine ⟨Q, hQ, ?_⟩
  rw [← Category.assoc, hπ, projectivePoint_comp_hyperplaneInclusion ha (hv ▸ ha')]
  exact projectivePoint_congr _ _ hv

end RationalProjection

end Hartshorne
