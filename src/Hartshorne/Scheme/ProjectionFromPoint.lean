/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoordinateNonvanishingOpen
import Hartshorne.RingedSpace.PicardGroup
import Hartshorne.Scheme.Differentials.RelativeDifferentialsBaseChange

/-!
# Projection from a point

Hartshorne, *Algebraic Geometry*, I, Exercise 3.14(a) (p. 22), in scheme form.

Let `H ≅ ℙⁿ_k` be a hyperplane in `ℙⁿ⁺¹_k` and `P ∉ H` a point. Projection from `P` sends
`Q ≠ P` to the intersection of the line `PQ` with `H`. In projective coordinates with
`P = (0 : ⋯ : 0 : 1)` and `H = {x_{n+1} = 0}`, identified with `ℙⁿ_k` by
`(x₀ : ⋯ : xₙ) ↦ (x₀ : ⋯ : xₙ : 0)`, it is the morphism defined by the remaining homogeneous
coordinates `x₀, …, xₙ`.

## Main definitions

* `Hartshorne.projectivePoint k a`: the `k`-rational point `(a₀ : ⋯ : a_m)` of `ℙᵐ_k`, the
  morphism `Spec k ⟶ ℙᵐ_k` defined (Hartshorne II, Theorem 7.1) by the sections `aᵢ` of
  `𝒪_{Spec k}`.
* `Hartshorne.linearSection k m v`: the linear form `∑ vⱼ xⱼ`, a global section of `𝒪(1)`.
* `Hartshorne.pointProjectionDomain k p h`, `Hartshorne.pointProjection k p h`: for
  `P = (p₀ : ⋯ : p_{n+1})` and `H = {h = 0}`, the open `U_P` where the sections
  `sᵢ = h(P) xᵢ − pᵢ h` of `𝒪(1)` have no common zero, and the morphism `U_P ⟶ ℙⁿ⁺¹_k` they
  define.
* The coordinate case `P = (0 : ⋯ : 0 : 1)`, `H = {x_{n+1} = 0}`:
  `Hartshorne.projectionDomain n Y = D₊(x₀) ∪ ⋯ ∪ D₊(xₙ)`,
  `Hartshorne.projectionFromPoint n Y : U ⟶ ℙⁿ_Y` defined by `x₀, …, xₙ`,
  `Hartshorne.coordinatePoint k n = P`, and
  `Hartshorne.hyperplaneInclusion n Y : ℙⁿ_Y ⟶ ℙⁿ⁺¹_Y`, `(x₀ : ⋯ : xₙ) ↦ (x₀ : ⋯ : xₙ : 0)`.

## Main results

* `Hartshorne.pointProjection_isProjection`: for `h(P) ≠ 0`, `U_P = ℙⁿ⁺¹_k − {P}`; the projection
  is the morphism defined by the `sᵢ`; it pulls `h` back to `0`, so maps into `H`; and it sends
  a rational point `Q ≠ P` to `h(P) Q − h(Q) P`, the intersection of the line `PQ` with `H`.
* `Hartshorne.projectionFromPoint_isProjection`: the coordinate case, where the projection is
  the morphism to `ℙⁿ_k` defined by the remaining coordinates, and its comparison
  `pointProjection_single_last` with the general projection.

That `hyperplaneInclusion` is a closed immersion onto `H` (so that `H ≅ ℙⁿ_k`) is not proved
here.

## Proof

Off `P` some `sᵢ` is nonzero, so the `sᵢ` generate `𝒪(1)|_{U_P}` and Theorem 7.1(b) gives the
morphism. A point `x` outside `U_P` is `P`: on `Spec κ(x)` (reduced) the pulled-back `sᵢ`
vanish, so the pulled-back coordinates are `xᵢ = (pᵢ / h(P)) h` and, by the uniqueness in
Theorem 7.1, `Spec κ(x) ⟶ ℙⁿ⁺¹_k` factors through `P`. Since `∑ hᵢ sᵢ = 0`, the projection
pulls `h` back to `0`. Values on rational points are computed with the uniqueness in
Theorem 7.1, using that a composite `f ≫ φ` is defined by the pulled-back sections
(`exists_iso_of_comp`).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

section Functoriality

variable {X' X Y : Scheme.{u}}

/-- `pullbackSection f e` is the adjunction unit applied to `e`. -/
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

/-- The isomorphism of `exists_iso_of_comp` on an arbitrary global section of `𝒪(1)`: it sends
`(f ≫ φ)^* t` to `f^* (e (φ^* t))`. -/
theorem exists_iso_of_comp_all (f : X' ⟶ X) (φ : X ⟶ projectiveSpaceOverScheme n Y)
    {ψ : X' ⟶ projectiveSpaceOverScheme n Y} (hψ : f ≫ φ = ψ) {L : X.Modules}
    (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅ L) :
    ∃ e' : (Scheme.Modules.pullback ψ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅
        (Scheme.Modules.pullback f).obj L,
      ∀ t, e'.hom.app ⊤ (pullbackGlobalSection ψ t) =
        pullbackGlobalSection f (e.hom.app ⊤ (pullbackGlobalSection φ t)) := by
  subst hψ
  refine ⟨((Scheme.Modules.pullbackComp f φ).app _).symm ≪≫
    (Scheme.Modules.pullback f).mapIso e, fun t => ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackComp_inv_pullbackGlobalSection, pullback_map_pullbackGlobalSection]

/-- Sections generate an `𝒪_X`-module if near every point one of them trivializes it. -/
theorem isGeneratedBySections_of_forall_isTrivializingSection {L : X.Modules} {ι : Type u}
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
abbrev structureModuleOf : X.Modules := SheafOfModules.unit X.ringCatSheaf

/-- A function `r ∈ Γ(U, 𝒪_X)`, as a section of the `𝒪_X`-module `𝒪_X`. -/
def structureModuleSection {U : X.Opens} (r : Γ(X, U)) : Γ(structureModuleOf X, U) := r

/-- `𝒪_X` is invertible. -/
theorem isInvertible_structureModuleOf : (structureModuleOf X).IsInvertible :=
  (Scheme.Modules.isInvertible_iff_ringed _).mpr
    (Ringed.structureModule_isInvertible (R := X.sheaf))

/-- The section `1` trivializes `𝒪_X`. -/
theorem isTrivializingSection_structureModuleSection_one :
    IsTrivializingSection (structureModuleOf X) ⊤ (structureModuleSection X 1) :=
  IsTrivializingSection.of_isLocalFrame (ι := ULift.{u} (Fin 1))
    (Ringed.structureModule_isLocalFrame (R := X.sheaf))

variable {X}

/-- A function `r`, as a section of `𝒪_X`, is `r • 1`. -/
theorem structureModuleSection_eq_smul {U : X.Opens} (r : Γ(X, U)) :
    structureModuleSection X r = r • structureModuleSection X 1 := by
  change r = r * 1
  rw [mul_one]

/-- A unit trivializes `𝒪_X`. -/
theorem isTrivializingSection_structureModuleSection {r : Γ(X, ⊤)} (hr : IsUnit r) :
    IsTrivializingSection (structureModuleOf X) ⊤ (structureModuleSection X r) := by
  rw [structureModuleSection_eq_smul]
  exact (isTrivializingSection_structureModuleSection_one X).unit_smul hr

end Unit

/-! ### Rational points in homogeneous coordinates -/

section RationalPoints

variable (k : Type u) [Field k]

/-- The constant function `c` on `Spec k`. -/
def specConst (c : k) : Γ(Spec (CommRingCat.of k), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv c

/-- A nonzero constant is a unit. -/
theorem isUnit_specConst {c : k} (hc : c ≠ 0) : IsUnit (specConst k c) :=
  (IsUnit.mk0 c hc).map _

/-- The constant `0` is `0`. -/
theorem specConst_zero : specConst k 0 = 0 :=
  map_zero _

/-- The constants `aᵢ`, as global sections of `𝒪_{Spec k}`. -/
abbrev pointSections {m : ℕ} (a : Fin (m + 1) → k) :
    Fin (m + 1) → Γ(structureModuleOf (Spec (CommRingCat.of k)), ⊤) :=
  fun i => structureModuleSection _ (specConst k (a i))

/-- For `a ≠ 0`, the constants `a₀, …, a_m` generate `𝒪_{Spec k}`. -/
theorem isGeneratedBySections_pointSections {m : ℕ} {a : Fin (m + 1) → k} (ha : a ≠ 0) :
    (structureModuleOf (Spec (CommRingCat.of k))).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (m + 1)) => pointSections k a i.down) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  refine isGeneratedBySections_of_forall_isTrivializingSection _ fun x => ⟨⟨j⟩, ⊤, trivial, ?_⟩
  rw [map_homOfLE_top]
  exact isTrivializingSection_structureModuleSection (isUnit_specConst k hj)

/-- Theorem 7.1(b) for the sections `a₀, …, a_m` of `𝒪_{Spec k}`. -/
theorem existsUnique_projectivePoint {m : ℕ} (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    ∃! φ : Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme m (Spec (CommRingCat.of k)),
      φ ≫ projectiveSpaceOverSchemeProjection m _ = 𝟙 _ ∧
      ∃ e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf m _ 1) ≅
          structureModuleOf (Spec (CommRingCat.of k)),
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate m _ i)) =
          pointSections k a i :=
  existsUnique_morphism_of_isGeneratedBySections (𝟙 _) (isInvertible_structureModuleOf _)
    (pointSections k a) (isGeneratedBySections_pointSections k ha)

/-- **The `k`-rational point `(a₀ : ⋯ : a_m)` of `ℙᵐ_k`**, for `a ≠ 0`: the `k`-morphism
`Spec k ⟶ ℙᵐ_k` defined (Hartshorne II, Theorem 7.1) by the global sections `a₀, …, a_m` of
`𝒪_{Spec k}`. -/
def projectivePoint {m : ℕ} (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme m (Spec (CommRingCat.of k)) :=
  (existsUnique_projectivePoint k a ha).exists.choose

/-- The defining property of `projectivePoint`. -/
theorem projectivePoint_spec {m : ℕ} (a : Fin (m + 1) → k) (ha : a ≠ 0) :
    projectivePoint k a ha ≫ projectiveSpaceOverSchemeProjection m _ = 𝟙 _ ∧
      ∃ e : (Scheme.Modules.pullback (projectivePoint k a ha)).obj
          (projectiveSpaceTwistingSheaf m _ 1) ≅ structureModuleOf (Spec (CommRingCat.of k)),
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (projectivePoint k a ha)
          (projectiveSpaceCoordinate m _ i)) = pointSections k a i :=
  (existsUnique_projectivePoint k a ha).exists.choose_spec

variable {k}

/-- A `k`-morphism `Spec k ⟶ ℙᵐ_k` pulling `𝒪(1)` back to `𝒪_{Spec k}` with `xᵢ ↦ aᵢ` is
`(a₀ : ⋯ : a_m)`. -/
theorem eq_projectivePoint {m : ℕ} {a : Fin (m + 1) → k} (ha : a ≠ 0)
    {φ : Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme m (Spec (CommRingCat.of k))}
    (hφ : φ ≫ projectiveSpaceOverSchemeProjection m _ = 𝟙 _)
    (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf m _ 1) ≅
      structureModuleOf (Spec (CommRingCat.of k)))
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
    (isInvertible_structureModuleOf _) (pointSections k a) _ e he i
  change y ∈ projectivePoint k a ha ⁻¹ᵁ projectiveSpaceChart m _ i ↔ _
  rw [h]
  change y ∈ nonvanishingLocus _ _ ↔ _
  by_cases hai : a i = 0
  · simp only [hai, ne_eq, not_true_eq_false, iff_false]
    rw [show pointSections k a i = 0 by
      change structureModuleSection _ (specConst k (a i)) = 0
      rw [hai, specConst_zero]
      rfl, nonvanishingLocus_zero]
    exact Set.notMem_empty y
  · simp only [ne_eq, hai, not_false_eq_true, iff_true]
    have he' := isTrivializingSection_structureModuleSection (isUnit_specConst k hai)
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
  refine isGeneratedBySections_of_forall_isTrivializingSection _ fun y => ?_
  have hy : (projectionDomain n Y).ι y ∈ projectionDomain n Y :=
    y.2
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨⟨i⟩, (projectionDomain n Y).ι ⁻¹ᵁ projectiveSpaceChart (n + 1) Y i.castSucc, hi, ?_⟩
  rw [pullbackGlobalSection_restrict]
  exact IsTrivializingSection.pullback _ (isTrivializingSection_projectiveSpaceChart _ _ _)

/-- Theorem 7.1(b) for the sections `x₀, …, xₙ` of `𝒪(1)|_U`. -/
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

/-- The defining property of `projectionFromPoint`. -/
theorem projectionFromPoint_spec :
    projectionFromPoint n Y ≫ projectiveSpaceOverSchemeProjection n Y =
        (projectionDomain n Y).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) Y ∧
      ∃ e : (Scheme.Modules.pullback (projectionFromPoint n Y)).obj
          (projectiveSpaceTwistingSheaf n Y 1) ≅ projectionDomainTwist n Y,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (projectionFromPoint n Y)
          (projectiveSpaceCoordinate n Y i)) = projectionSections n Y i :=
  (existsUnique_projection n Y).exists.choose_spec

/-- `projectionFromPoint` is the unique `Y`-morphism `U ⟶ ℙⁿ_Y` defined by the remaining
coordinates: the one pulling `𝒪(1)` back to `𝒪(1)|_U` with each `xᵢ` going to `xᵢ|_U`. -/
theorem eq_projectionFromPoint_iff
    (π : (projectionDomain n Y).toScheme ⟶ projectiveSpaceOverScheme n Y) :
    (π ≫ projectiveSpaceOverSchemeProjection n Y =
        (projectionDomain n Y).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) Y ∧
      ∃ e : (Scheme.Modules.pullback π).obj (projectiveSpaceTwistingSheaf n Y 1) ≅
          projectionDomainTwist n Y,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection π (projectiveSpaceCoordinate n Y i)) =
          projectionSections n Y i) ↔ π = projectionFromPoint n Y :=
  ⟨fun h => (existsUnique_projection n Y).unique h (projectionFromPoint_spec n Y),
    fun h => h ▸ projectionFromPoint_spec n Y⟩

end Projection

/-! ### The domain is the complement of the coordinate point -/

section CoordinatePoint

variable (k : Type u) [Field k] (n : ℕ)

/-- The pullback of the zero section is zero. -/
theorem pullbackGlobalSection_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) :
    pullbackGlobalSection f (0 : Γ(N, ⊤)) = 0 := by
  have h := pullbackSection_smul f (0 : Γ(Y, ⊤)) (0 : Γ(N, ⊤))
  rw [zero_smul, map_zero, zero_smul] at h
  rw [pullbackGlobalSection, h, map_zero]

/-- The coordinate vector `(0, …, 0, 1)` is nonzero. -/
theorem single_last_ne_zero : (Pi.single (Fin.last (n + 1)) (1 : k) : Fin (n + 2) → k) ≠ 0 := by
  intro h
  simpa using congrFun h (Fin.last _)

/-- **The coordinate point `P = (0 : ⋯ : 0 : 1)` of `ℙⁿ⁺¹_k`**, as a `k`-rational point. -/
def coordinatePoint :
    Spec (CommRingCat.of k) ⟶ projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k)) :=
  projectivePoint k (Pi.single (Fin.last (n + 1)) 1) (single_last_ne_zero k n)

/-- The coordinate point `P` does not lie in `U`. -/
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
  have hu : IsTrivializingSection ((Scheme.Modules.pullback c).obj (structureModuleOf _)) ⊤
      (pullbackGlobalSection c (structureModuleSection _ 1)) :=
    (IsTrivializingSection.pullback c (isTrivializingSection_structureModuleSection_one _)).restrict
      (Scheme.Hom.preimage_top c).ge
  have σ : PUnit.{u + 1} ≃ ULift.{u} (Fin 1) := Equiv.ofUnique _ _
  obtain ⟨α, hα⟩ := Ringed.exists_iso_of_frames (R := T.sheaf)
    (fun _ : PUnit.{u + 1} => ⊤) (le_iSup (fun _ : PUnit.{u + 1} => ⊤) PUnit.unit)
    (A := M) (B := (Scheme.Modules.pullback c).obj (structureModuleOf _))
    (fun _ => t (Fin.last _)) (fun _ => pullbackGlobalSection c (structureModuleSection _ 1))
    (fun _ => (isLocalFrame_of_isTrivializingSection htriv).reindex σ)
    (fun _ => (isLocalFrame_of_isTrivializingSection hu).reindex σ)
    (fun _ _ => ⟨1, by rw [one_smul], by rw [one_smul]⟩)
  let α' : M ≅ (Scheme.Modules.pullback c).obj (structureModuleOf _) := α
  have hα' : α'.hom.app ⊤ (t (Fin.last _)) = pullbackGlobalSection c (structureModuleSection _ 1) :=
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
  have hgen : ((Scheme.Modules.pullback c).obj (structureModuleOf _)).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (n + 2)) =>
        pullbackGlobalSection c (pointSections k (Pi.single (Fin.last (n + 1)) 1) i.down)) := by
    refine isGeneratedBySections_of_forall_isTrivializingSection _ fun y =>
      ⟨⟨Fin.last _⟩, ⊤, trivial, ?_⟩
    rw [map_homOfLE_top, hsec, hα']
    exact hu
  have hc : (c ≫ coordinatePoint k n) ≫ projectiveSpaceOverSchemeProjection (n + 1) _ = c := by
    rw [Category.assoc, coordinatePoint, (projectivePoint_spec k _ _).1, Category.comp_id]
  exact (existsUnique_morphism_of_isGeneratedBySections c
    (Scheme.Modules.IsInvertible.pullback c (isInvertible_structureModuleOf _))
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

/-- The sections `x₀, …, xₙ, 0` generate `𝒪(1)` on `ℙⁿ_Y`. -/
theorem isGeneratedBySections_hyperplaneSections :
    (projectiveSpaceTwistingSheaf n Y 1).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (n + 2)) => hyperplaneSections n Y i.down) := by
  refine isGeneratedBySections_of_forall_isTrivializingSection _ fun y => ?_
  obtain ⟨i, hi⟩ := exists_mem_chartPreimage (𝟙 (projectiveSpaceOverScheme n Y)) y
  refine ⟨⟨i.castSucc⟩, projectiveSpaceChart n Y i, hi, ?_⟩
  simp only [hyperplaneSections, Fin.lastCases_castSucc]
  exact isTrivializingSection_projectiveSpaceChart n Y i

/-- Theorem 7.1(b) for the sections `x₀, …, xₙ, 0` of `𝒪(1)` on `ℙⁿ_Y`. -/
theorem existsUnique_hyperplaneInclusion :
    ∃! j : projectiveSpaceOverScheme n Y ⟶ projectiveSpaceOverScheme (n + 1) Y,
      j ≫ projectiveSpaceOverSchemeProjection (n + 1) Y = projectiveSpaceOverSchemeProjection n Y ∧
      ∃ e : (Scheme.Modules.pullback j).obj (projectiveSpaceTwistingSheaf (n + 1) Y 1) ≅
          projectiveSpaceTwistingSheaf n Y 1,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection j (projectiveSpaceCoordinate (n + 1) Y i)) =
          hyperplaneSections n Y i :=
  existsUnique_morphism_of_isGeneratedBySections _ (isInvertible_projectiveSpaceTwistingSheaf _ _ _)
    (hyperplaneSections n Y) (isGeneratedBySections_hyperplaneSections n Y)

/-- **The coordinate hyperplane embedding `ℙⁿ_Y ⟶ ℙⁿ⁺¹_Y`**:
`(x₀ : ⋯ : xₙ) ↦ (x₀ : ⋯ : xₙ : 0)`, defined (Hartshorne II, Theorem 7.1) by the sections
`x₀, …, xₙ, 0` of `𝒪(1)` on `ℙⁿ_Y`. Its image lies in the hyperplane `x_{n+1} = 0`
(`hyperplaneInclusion_notMem_projectiveSpaceChart_last`); that it is a closed immersion onto
`x_{n+1} = 0` is not proved here. -/
def hyperplaneInclusion : projectiveSpaceOverScheme n Y ⟶ projectiveSpaceOverScheme (n + 1) Y :=
  (existsUnique_hyperplaneInclusion n Y).exists.choose

/-- The defining property of `hyperplaneInclusion`. -/
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

/-- If an isomorphism sends `s` to `t`, its inverse sends `t` to `s`. -/
private theorem iso_inv_app_eq_of_hom_app_eq {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    {U : X.Opens} {s : Γ(M, U)} {t : Γ(N, U)} (h : e.hom.app U s = t) : e.inv.app U t = s := by
  rw [← h]
  exact ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ U) e.hom_inv_id) s

/-- If `(a₀, …, aₙ) ≠ 0` then `(a₀, …, a_{n+1}) ≠ 0`. -/
theorem ne_zero_of_comp_castSucc_ne_zero {a : Fin (n + 2) → k}
    (ha : (fun i : Fin (n + 1) => a i.castSucc) ≠ 0) : a ≠ 0 := by
  rintro rfl
  exact ha rfl

/-- If `(a₀, …, aₙ) ≠ 0` then `(a₀, …, aₙ, 0) ≠ 0`. -/
theorem sub_smul_single_last_ne_zero {a : Fin (n + 2) → k}
    (ha : (fun i : Fin (n + 1) => a i.castSucc) ≠ 0) :
    a - a (Fin.last (n + 1)) • Pi.single (Fin.last (n + 1)) 1 ≠ 0 := by
  intro h
  refine ha (funext fun i => ?_)
  simpa [Pi.single_eq_of_ne (Fin.castSucc_ne_last i)] using congrFun h i.castSucc

/-- Equal coordinate vectors give equal points. -/
theorem projectivePoint_congr {m : ℕ} {a b : Fin (m + 1) → k} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a = b) : projectivePoint k a ha = projectivePoint k b hb := by
  subst h
  rfl

/-- The hyperplane inclusion sends `(b₀ : ⋯ : bₙ)` to `(b₀ : ⋯ : bₙ : 0)`. -/
theorem projectivePoint_comp_hyperplaneInclusion {b : Fin (n + 1) → k} (hb : b ≠ 0)
    (hb' : (Fin.lastCases 0 b : Fin (n + 2) → k) ≠ 0) :
    projectivePoint k b hb ≫ hyperplaneInclusion n _ =
      projectivePoint k (Fin.lastCases 0 b) hb' := by
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
  rw [he2, iso_inv_app_eq_of_hom_app_eq e1 (he1 i.castSucc), hea]

/-- **Projection of a rational point is the intersection of a line with `H`.** For
`Q = (a₀ : ⋯ : a_{n+1}) ≠ P = (0 : ⋯ : 0 : 1)`, the image of `π(Q)` in `H` is the point
`(a₀ : ⋯ : aₙ : 0) = Q − a_{n+1} P`: it lies on the line through `P` and `Q`, and on
`H = {x_{n+1} = 0}`. -/
theorem exists_lift_projectivePoint_comp_projectionFromPoint_hyperplaneInclusion
    {a : Fin (n + 2) → k} (ha : (fun i : Fin (n + 1) => a i.castSucc) ≠ 0) :
    ∃ Q : Spec (CommRingCat.of k) ⟶ (projectionDomain n (Spec (CommRingCat.of k))).toScheme,
      Q ≫ (projectionDomain n _).ι = projectivePoint k a (ne_zero_of_comp_castSucc_ne_zero ha) ∧
      Q ≫ projectionFromPoint n _ ≫ hyperplaneInclusion n _ =
        projectivePoint k (a - a (Fin.last (n + 1)) • Pi.single (Fin.last (n + 1)) 1)
          (sub_smul_single_last_ne_zero ha) := by
  obtain ⟨Q, hQ, hπ⟩ := exists_lift_projectivePoint_comp_projectionFromPoint ha
  have hv : (Fin.lastCases 0 (fun i : Fin (n + 1) => a i.castSucc) : Fin (n + 2) → k) =
      a - a (Fin.last (n + 1)) • Pi.single (Fin.last (n + 1)) 1 := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp
  refine ⟨Q, hQ, ?_⟩
  rw [← Category.assoc, hπ,
    projectivePoint_comp_hyperplaneInclusion ha (hv ▸ sub_smul_single_last_ne_zero ha)]
  exact projectivePoint_congr _ _ hv

end RationalProjection

/-! ### Linear forms as sections of `𝒪(1)` -/

section Linear

variable {X Y : Scheme.{u}}

/-- `f^*` is additive on global sections. -/
theorem pullbackGlobalSection_add (f : X ⟶ Y) {N : Y.Modules} (a b : Γ(N, ⊤)) :
    pullbackGlobalSection f (a + b) = pullbackGlobalSection f a + pullbackGlobalSection f b := by
  have h : pullbackSection f (a + b) = pullbackSection f a + pullbackSection f b :=
    Ringed.etaSec_add (φ := f.toRingCatSheafHom) a b
  rw [pullbackGlobalSection, h, map_add]
  rfl

/-- `f^*`, as an additive map on global sections. -/
def pullbackGlobalSectionAddHom (f : X ⟶ Y) (N : Y.Modules) :
    Γ(N, ⊤) →+ Γ((Scheme.Modules.pullback f).obj N, ⊤) :=
  AddMonoidHom.mk' (pullbackGlobalSection f) (pullbackGlobalSection_add f)

/-- `f^*` commutes with finite sums of global sections. -/
theorem pullbackGlobalSection_sum (f : X ⟶ Y) {N : Y.Modules} {ι : Type*} (S : Finset ι)
    (g : ι → Γ(N, ⊤)) :
    pullbackGlobalSection f (∑ i ∈ S, g i) = ∑ i ∈ S, pullbackGlobalSection f (g i) :=
  map_sum (pullbackGlobalSectionAddHom f N) g S

/-- `f^*` commutes with differences of global sections. -/
theorem pullbackGlobalSection_sub (f : X ⟶ Y) {N : Y.Modules} (a b : Γ(N, ⊤)) :
    pullbackGlobalSection f (a - b) = pullbackGlobalSection f a - pullbackGlobalSection f b :=
  map_sub (pullbackGlobalSectionAddHom f N) a b

/-- `f^* (r t) = f^#(r) f^* t` for a global function `r`. -/
theorem pullbackGlobalSection_smul (f : X ⟶ Y) {N : Y.Modules} (r : Γ(Y, ⊤)) (t : Γ(N, ⊤)) :
    pullbackGlobalSection f (r • t) = f.appTop r • pullbackGlobalSection f t := by
  rw [pullbackGlobalSection, pullbackSection_smul, Scheme.Modules.map_smul]
  congr 1
  rw [show (homOfLE (Scheme.Hom.preimage_top f).ge : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ ⊤) = 𝟙 _ from rfl]
  erw [op_id, X.presheaf.map_id]
  rfl

variable {k : Type u} [Field k]

/-- The constant `c ∈ k` as a function on a scheme `X` over `Spec k` (structure morphism `q`). -/
def kConst (q : X ⟶ Spec (CommRingCat.of k)) : k →+* Γ(X, ⊤) :=
  q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

/-- `kConst q c` is the pullback along `q` of the constant `c` on `Spec k`. -/
theorem kConst_apply (q : X ⟶ Spec (CommRingCat.of k)) (c : k) :
    kConst q c = q.appTop (specConst k c) := rfl

/-- Constants pull back to constants. -/
theorem appTop_kConst (f : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of k)) (c : k) :
    f.appTop (kConst q c) = kConst (f ≫ q) c := by
  rw [kConst_apply, kConst_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- On `Spec k`, `kConst` is `specConst`. -/
theorem kConst_id (c : k) : kConst (𝟙 (Spec (CommRingCat.of k))) c = specConst k c := rfl

variable (k) in
/-- The linear form `v₀ x₀ + ⋯ + v_m x_m`, a global section of `𝒪(1)` on `ℙᵐ_k`. -/
def linearSection (m : ℕ) (v : Fin (m + 1) → k) :
    Γ(projectiveSpaceTwistingSheaf m (Spec (CommRingCat.of k)) 1, ⊤) :=
  ∑ j, kConst (projectiveSpaceOverSchemeProjection m _) (v j) •
    projectiveSpaceCoordinate m _ j

/-- The linear form of a difference. -/
theorem linearSection_sub {m : ℕ} (v w : Fin (m + 1) → k) :
    linearSection k m (v - w) = linearSection k m v - linearSection k m w := by
  simp only [linearSection, Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]

/-- The linear form of a scalar multiple. -/
theorem linearSection_smul {m : ℕ} (a : k) (v : Fin (m + 1) → k) :
    linearSection k m (a • v) =
      kConst (projectiveSpaceOverSchemeProjection m _) a • linearSection k m v := by
  simp only [linearSection, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]

/-- The linear form of `eᵢ` is the coordinate `xᵢ`. -/
theorem linearSection_single {m : ℕ} (i : Fin (m + 1)) :
    linearSection k m (Pi.single i 1) = projectiveSpaceCoordinate m _ i := by
  rw [linearSection, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, map_one, one_smul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, map_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Evaluating a linear form along a morphism defined by sections.** If `φ : X ⟶ ℙᵐ_k` over
`r : X ⟶ Spec k` is defined by the sections `sⱼ` of `L`, it pulls the linear form `∑ vⱼ xⱼ` back
to `∑ vⱼ sⱼ`. -/
theorem iso_app_linearSection {m : ℕ}
    {φ : X ⟶ projectiveSpaceOverScheme m (Spec (CommRingCat.of k))}
    {r : X ⟶ Spec (CommRingCat.of k)} (hφ : φ ≫ projectiveSpaceOverSchemeProjection m _ = r)
    {L : X.Modules} {s : Fin (m + 1) → Γ(L, ⊤)}
    (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf m _ 1) ≅ L)
    (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate m _ i)) = s i)
    (v : Fin (m + 1) → k) :
    e.hom.app ⊤ (pullbackGlobalSection φ (linearSection k m v)) = ∑ j, kConst r (v j) • s j := by
  rw [linearSection, pullbackGlobalSection_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pullbackGlobalSection_smul, Scheme.Modules.Hom.app_smul, he, appTop_kConst, hφ]

end Linear

/-! ### Nonvanishing loci under pullback -/

section Loci

variable {X Y : Scheme.{u}}

private theorem germ_smul' (F : X.Modules) {U : X.Opens} (x : X) (hx : x ∈ U) (r : Γ(X, U))
    (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  PresheafOfModules.germ_smul M x U hx r m

/-- If `t = r • s` for global sections, `t` vanishes wherever `s` does. -/
theorem nonvanishingLocus_smul_subset (L : X.Modules) (r : Γ(X, ⊤)) (s : Γ(L, ⊤)) :
    nonvanishingLocus L (r • s) ⊆ nonvanishingLocus L s := by
  intro x hx hs
  apply hx
  convert Submodule.smul_mem _ (X.presheaf.germ ⊤ x trivial r) hs using 1
  exact germ_smul' L (U := ⊤) x trivial r s

/-- **The nonvanishing locus of a pulled-back section is the preimage of the nonvanishing
locus.** -/
theorem mem_nonvanishingLocus_pullbackGlobalSection_iff (f : X ⟶ Y) {L : Y.Modules}
    (hL : L.IsInvertible) (s : Γ(L, ⊤)) (x : X) :
    x ∈ nonvanishingLocus ((Scheme.Modules.pullback f).obj L) (pullbackGlobalSection f s) ↔
      f x ∈ nonvanishingLocus L s := by
  obtain ⟨W, e, hxW, he⟩ := exists_isTrivializingSection hL (f x)
  obtain ⟨g, hg⟩ := he.exists_eq_smul s
  have hg' : ((Scheme.Modules.pullback f).obj L).presheaf.map
      (homOfLE (le_top : f ⁻¹ᵁ W ≤ ⊤)).op (pullbackGlobalSection f s) =
      f.app W g • pullbackSection f e := by
    rw [pullbackGlobalSection_restrict, hg, pullbackSection_smul]
  rw [(he.pullback f).mem_nonvanishingLocus_iff hg' (show x ∈ f ⁻¹ᵁ W from hxW),
    he.mem_nonvanishingLocus_iff hg hxW, ← Scheme.preimage_basicOpen]
  rfl

/-- On a reduced scheme, a section of an invertible sheaf vanishing at every point is zero. -/
theorem eq_zero_of_forall_notMem_nonvanishingLocus [IsReduced X] {L : X.Modules}
    (hL : L.IsInvertible) {s : Γ(L, ⊤)} (hs : ∀ x, x ∉ nonvanishingLocus L s) : s = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext L.isSheaf fun x _ => ?_
  obtain ⟨W, e, hxW, he⟩ := exists_isTrivializingSection hL x
  obtain ⟨g, hg⟩ := he.exists_eq_smul s
  have hg0 : g = 0 := by
    rw [← basicOpen_eq_bot_iff]
    refine SetLike.coe_injective ((he.nonvanishingLocus_inter_eq hg).symm.trans ?_)
    ext y
    simp only [Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false,
      iff_false, not_and]
    exact fun h _ => hs y h
  refine ⟨W, le_top, hxW, ?_⟩
  rw [hg, hg0, zero_smul, map_zero]

end Loci

/-! ### Projection from an arbitrary rational point to an arbitrary hyperplane -/

section General

open Matrix

variable (k : Type u) [Field k] {n : ℕ}

/-- The coefficient vector `h(P) eᵢ − pᵢ h` of the linear form `h(P) xᵢ − pᵢ h`. -/
def projectionVector (p h : Fin (n + 2) → k) (i : Fin (n + 2)) : Fin (n + 2) → k :=
  (h ⬝ᵥ p) • Pi.single i 1 - p i • h

/-- The sections `sᵢ = h(P) xᵢ − pᵢ h` of `𝒪(1)` on `ℙⁿ⁺¹_k`, where `P = (p₀ : ⋯ : p_{n+1})` and
`h = ∑ hⱼ xⱼ`. At a point `Q`, `(s₀(Q) : ⋯ : s_{n+1}(Q)) = h(P) Q − h(Q) P`. -/
def projectionLinearSections (p h : Fin (n + 2) → k) (i : Fin (n + 2)) :
    Γ(projectiveSpaceTwistingSheaf (n + 1) (Spec (CommRingCat.of k)) 1, ⊤) :=
  linearSection k (n + 1) (projectionVector k p h i)

/-- The open `U_P` of `ℙⁿ⁺¹_k` where the sections `sᵢ` have no common zero. When
`h(P) ≠ 0` it is `ℙⁿ⁺¹_k − {P}` (`pointProjectionDomain_eq_compl_range`). -/
def pointProjectionDomain (p h : Fin (n + 2) → k) :
    (projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k))).Opens :=
  ⨆ i, nonvanishingLocusOpens (isInvertible_projectiveSpaceTwistingSheaf _ _ 1)
    (projectionLinearSections k p h i)

/-- `𝒪(1)|_{U_P}`. -/
abbrev pointProjectionTwist (p h : Fin (n + 2) → k) :
    (pointProjectionDomain k p h).toScheme.Modules :=
  (Scheme.Modules.pullback (pointProjectionDomain k p h).ι).obj
    (projectiveSpaceTwistingSheaf (n + 1) _ 1)

/-- The restrictions of the `sᵢ` to `U_P`. -/
abbrev pointProjectionSections (p h : Fin (n + 2) → k) (i : Fin (n + 2)) :
    Γ(pointProjectionTwist k p h, ⊤) :=
  pullbackGlobalSection (pointProjectionDomain k p h).ι (projectionLinearSections k p h i)

/-- The `sᵢ` generate `𝒪(1)|_{U_P}`: each trivializes it where it does not vanish. -/
theorem isGeneratedBySections_pointProjectionSections (p h : Fin (n + 2) → k) :
    (pointProjectionTwist k p h).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (n + 2)) => pointProjectionSections k p h i.down) := by
  refine isGeneratedBySections_of_forall_isTrivializingSection _ fun y => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp y.2
  refine ⟨⟨i⟩, (pointProjectionDomain k p h).ι ⁻¹ᵁ nonvanishingLocusOpens
    (isInvertible_projectiveSpaceTwistingSheaf _ _ 1) (projectionLinearSections k p h i), hi, ?_⟩
  rw [pullbackGlobalSection_restrict]
  exact IsTrivializingSection.pullback _ (isTrivializingSection_nonvanishingLocusOpens _ _)

/-- Theorem 7.1(b) for the sections `sᵢ` of `𝒪(1)|_{U_P}`. -/
theorem existsUnique_pointProjection (p h : Fin (n + 2) → k) :
    ∃! π : (pointProjectionDomain k p h).toScheme ⟶
        projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k)),
      π ≫ projectiveSpaceOverSchemeProjection (n + 1) _ =
        (pointProjectionDomain k p h).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) _ ∧
      ∃ e : (Scheme.Modules.pullback π).obj (projectiveSpaceTwistingSheaf (n + 1) _ 1) ≅
          pointProjectionTwist k p h,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection π (projectiveSpaceCoordinate (n + 1) _ i)) =
          pointProjectionSections k p h i :=
  existsUnique_morphism_of_isGeneratedBySections _
    (Scheme.Modules.IsInvertible.pullback _ (isInvertible_projectiveSpaceTwistingSheaf _ _ _))
    (pointProjectionSections k p h) (isGeneratedBySections_pointProjectionSections k p h)

/-- **Projection from the point `P = (p₀ : ⋯ : p_{n+1})` to the hyperplane `H = {h = 0}`**: the
morphism `U_P ⟶ ℙⁿ⁺¹_k` defined (Hartshorne II, Theorem 7.1) by the sections
`sᵢ = h(P) xᵢ − pᵢ h`, sending `Q` to `h(P) Q − h(Q) P`. -/
def pointProjection (p h : Fin (n + 2) → k) :
    (pointProjectionDomain k p h).toScheme ⟶
      projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k)) :=
  (existsUnique_pointProjection k p h).exists.choose

/-- The defining property of `pointProjection`. -/
theorem pointProjection_spec (p h : Fin (n + 2) → k) :
    pointProjection k p h ≫ projectiveSpaceOverSchemeProjection (n + 1) _ =
        (pointProjectionDomain k p h).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) _ ∧
      ∃ e : (Scheme.Modules.pullback (pointProjection k p h)).obj
          (projectiveSpaceTwistingSheaf (n + 1) _ 1) ≅ pointProjectionTwist k p h,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (pointProjection k p h)
          (projectiveSpaceCoordinate (n + 1) _ i)) = pointProjectionSections k p h i :=
  (existsUnique_pointProjection k p h).exists.choose_spec

/-- `pointProjection` is the unique `k`-morphism `U_P ⟶ ℙⁿ⁺¹_k` pulling `𝒪(1)` back to
`𝒪(1)|_{U_P}` with `xᵢ ↦ sᵢ|_{U_P}`. -/
theorem eq_pointProjection_iff (p h : Fin (n + 2) → k)
    (π : (pointProjectionDomain k p h).toScheme ⟶
      projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k))) :
    (π ≫ projectiveSpaceOverSchemeProjection (n + 1) _ =
        (pointProjectionDomain k p h).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) _ ∧
      ∃ e : (Scheme.Modules.pullback π).obj (projectiveSpaceTwistingSheaf (n + 1) _ 1) ≅
          pointProjectionTwist k p h,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection π (projectiveSpaceCoordinate (n + 1) _ i)) =
          pointProjectionSections k p h i) ↔ π = pointProjection k p h :=
  ⟨fun hπ => (existsUnique_pointProjection k p h).unique hπ (pointProjection_spec k p h),
    fun hπ => hπ ▸ pointProjection_spec k p h⟩

variable {k}

/-- If `h(P) ≠ 0` then `p ≠ 0`. -/
theorem ne_zero_of_dotProduct_ne_zero {p h : Fin (n + 2) → k} (hph : h ⬝ᵥ p ≠ 0) : p ≠ 0 := by
  rintro rfl
  exact hph (dotProduct_zero h)

/-- `h(P) xᵢ − pᵢ h`, written with the constant functions on `ℙⁿ⁺¹_k`. -/
theorem projectionLinearSections_eq (p h : Fin (n + 2) → k) (i : Fin (n + 2)) :
    projectionLinearSections k p h i =
      kConst (projectiveSpaceOverSchemeProjection (n + 1) _) (h ⬝ᵥ p) •
          projectiveSpaceCoordinate (n + 1) _ i -
        kConst (projectiveSpaceOverSchemeProjection (n + 1) _) (p i) •
          linearSection k (n + 1) h := by
  rw [projectionLinearSections, projectionVector, linearSection_sub, linearSection_smul,
    linearSection_smul, linearSection_single]

/-- `∑ hᵢ sᵢ = 0`: the sections `sᵢ` satisfy the equation of `H`. -/
theorem sum_smul_projectionLinearSections (p h : Fin (n + 2) → k) :
    ∑ i, kConst (projectiveSpaceOverSchemeProjection (n + 1) _) (h i) •
      projectionLinearSections k p h i = 0 := by
  simp only [projectionLinearSections_eq, smul_sub, Finset.sum_sub_distrib, smul_smul, ← map_mul]
  rw [sub_eq_zero, ← Finset.sum_smul, ← map_sum]
  simp only [mul_comm (h _) (h ⬝ᵥ p), map_mul, ← smul_smul, ← Finset.smul_sum]
  rfl

end General

/-! ### Properties of the general projection -/

section GeneralProperties

open Matrix

variable {k : Type u} [Field k] {n : ℕ}

/-- `specConst` is multiplicative. -/
theorem specConst_mul (a b : k) : specConst k (a * b) = specConst k a * specConst k b :=
  map_mul (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a b

/-- `specConst` commutes with finite sums. -/
theorem specConst_sum {ι : Type*} (S : Finset ι) (g : ι → k) :
    specConst k (∑ i ∈ S, g i) = ∑ i ∈ S, specConst k (g i) :=
  map_sum (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom g S

/-- `r s`, as a section of `𝒪_X`, is `r • s`. -/
theorem structureModuleSection_mul {X : Scheme.{u}} (r s : Γ(X, ⊤)) :
    structureModuleSection X (r * s) = r • structureModuleSection X s := rfl

/-- `structureModuleSection` commutes with finite sums. -/
theorem structureModuleSection_sum {X : Scheme.{u}} {ι : Type*} (S : Finset ι) (g : ι → Γ(X, ⊤)) :
    structureModuleSection X (∑ i ∈ S, g i) = ∑ i ∈ S, structureModuleSection X (g i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

/-- At the rational point `(a₀ : ⋯ : a_m)`, the linear form `∑ vⱼ xⱼ` takes the value
`∑ vⱼ aⱼ`. -/
theorem iso_app_linearSection_projectivePoint {m : ℕ} {a : Fin (m + 1) → k} (ha : a ≠ 0)
    {e : (Scheme.Modules.pullback (projectivePoint k a ha)).obj
      (projectiveSpaceTwistingSheaf m _ 1) ≅ structureModuleOf (Spec (CommRingCat.of k))}
    (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection (projectivePoint k a ha)
      (projectiveSpaceCoordinate m _ i)) = pointSections k a i) (v : Fin (m + 1) → k) :
    e.hom.app ⊤ (pullbackGlobalSection (projectivePoint k a ha) (linearSection k m v)) =
      structureModuleSection _ (specConst k (v ⬝ᵥ a)) := by
  rw [iso_app_linearSection (projectivePoint_spec k a ha).1 e he v, dotProduct, specConst_sum,
    structureModuleSection_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [kConst_id, specConst_mul, structureModuleSection_mul]

/-- The rational point `(a₀ : ⋯ : a_m)` lies off the hyperplane `∑ vⱼ xⱼ = 0` exactly when
`∑ vⱼ aⱼ ≠ 0`. -/
theorem projectivePoint_mem_nonvanishingLocus_linearSection_iff {m : ℕ} {a : Fin (m + 1) → k}
    (ha : a ≠ 0) (v : Fin (m + 1) → k) (y : Spec (CommRingCat.of k)) :
    projectivePoint k a ha y ∈ nonvanishingLocus _ (linearSection k m v) ↔ v ⬝ᵥ a ≠ 0 := by
  obtain ⟨-, e, he⟩ := projectivePoint_spec k a ha
  rw [← mem_nonvanishingLocus_pullbackGlobalSection_iff _
    (isInvertible_projectiveSpaceTwistingSheaf _ _ _)]
  rw [← iso_inv_app_eq_of_hom_app_eq e (iso_app_linearSection_projectivePoint ha he v)]
  by_cases hz : v ⬝ᵥ a = 0
  · rw [hz, specConst_zero,
      show structureModuleSection (Spec (CommRingCat.of k)) 0 = 0 from rfl, map_zero,
      nonvanishingLocus_zero]
    simp
  · simp only [ne_eq, hz, not_false_eq_true, iff_true]
    have ht : IsTrivializingSection _ ⊤
        (e.inv.app ⊤ (structureModuleSection _ (specConst k (v ⬝ᵥ a)))) :=
      (isTrivializingSection_structureModuleSection (isUnit_specConst k hz)).map_iso e.symm
    rw [(ht.mem_nonvanishingLocus_iff (g := 1) (by rw [map_homOfLE_top, one_smul]) trivial),
      Scheme.basicOpen_one]
    trivial

/-- The value of `sᵢ` at `Q` is the `i`-th coordinate of `h(P) Q − h(Q) P`. -/
theorem projectionVector_dotProduct (p h q : Fin (n + 2) → k) (i : Fin (n + 2)) :
    projectionVector k p h i ⬝ᵥ q = ((h ⬝ᵥ p) • q - (h ⬝ᵥ q) • p) i := by
  simp only [projectionVector, sub_dotProduct, smul_dotProduct, single_dotProduct, one_mul,
    smul_eq_mul, Pi.sub_apply, Pi.smul_apply]
  ring

/-- `𝒪_{Spec k}` pulled back along `c` is generated by the pulled-back constants `aᵢ`, `a ≠ 0`. -/
theorem isGeneratedBySections_pullback_pointSections {T : Scheme.{u}}
    (c : T ⟶ Spec (CommRingCat.of k)) {m : ℕ} {a : Fin (m + 1) → k} (ha : a ≠ 0) :
    ((Scheme.Modules.pullback c).obj (structureModuleOf _)).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (m + 1)) => pullbackGlobalSection c (pointSections k a i.down)) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  refine isGeneratedBySections_of_forall_isTrivializingSection _ fun y => ⟨⟨j⟩, ⊤, trivial, ?_⟩
  rw [map_homOfLE_top]
  exact (IsTrivializingSection.pullback c (isTrivializingSection_structureModuleSection
    (isUnit_specConst k hj))).restrict (Scheme.Hom.preimage_top c).ge

/-- A morphism from a reduced scheme to `ℙⁿ⁺¹_k` whose image avoids `U_P` factors through `P`:
the pulled-back `sᵢ = h(P) xᵢ − pᵢ h` vanish, so the pulled-back coordinates are
`xᵢ = (pᵢ / h(P)) h`, and Theorem 7.1 identifies the morphism with the one through `P`. -/
theorem eq_comp_projectivePoint_of_notMem {p h : Fin (n + 2) → k} (hph : h ⬝ᵥ p ≠ 0)
    {T : Scheme.{u}} [IsReduced T]
    (g : T ⟶ projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k)))
    (hg : ∀ y, g y ∉ pointProjectionDomain k p h) :
    g = (g ≫ projectiveSpaceOverSchemeProjection (n + 1) _) ≫
      projectivePoint k p (ne_zero_of_dotProduct_ne_zero hph) := by
  have hp := ne_zero_of_dotProduct_ne_zero hph
  have hO := isInvertible_projectiveSpaceTwistingSheaf (n + 1) (Spec (CommRingCat.of k)) 1
  set c := g ≫ projectiveSpaceOverSchemeProjection (n + 1) (Spec (CommRingCat.of k)) with hcdef
  set M := (Scheme.Modules.pullback g).obj (projectiveSpaceTwistingSheaf (n + 1) _ 1)
  set t : Fin (n + 2) → Γ(M, ⊤) := fun i =>
    pullbackGlobalSection g (projectiveSpaceCoordinate (n + 1) _ i)
  set τ : Γ(M, ⊤) := pullbackGlobalSection g (linearSection k (n + 1) h)
  have hM : M.IsInvertible := isInvertible_pullback_projectiveSpaceTwistingSheaf g
  have hgen : M.IsGeneratedBySections (fun i : ULift.{u} (Fin (n + 2)) => t i.down) :=
    isGeneratedBySections_pullback_projectiveSpaceCoordinate g
  -- the pulled-back `sᵢ` vanish
  have hs0 : ∀ i, pullbackGlobalSection g (projectionLinearSections k p h i) = 0 := fun i =>
    eq_zero_of_forall_notMem_nonvanishingLocus hM fun y hy =>
      hg y (TopologicalSpace.Opens.mem_iSup.mpr
        ⟨i, (mem_nonvanishingLocus_pullbackGlobalSection_iff g hO _ y).mp hy⟩)
  have ht : ∀ j, t j = kConst c (p j / (h ⬝ᵥ p)) • τ := by
    intro j
    have h0 := hs0 j
    rw [projectionLinearSections_eq, pullbackGlobalSection_sub, pullbackGlobalSection_smul,
      pullbackGlobalSection_smul, appTop_kConst, appTop_kConst, sub_eq_zero, ← hcdef] at h0
    have h1 := congrArg (kConst c (h ⬝ᵥ p)⁻¹ • ·) h0
    simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hph, map_one, one_smul] at h1
    exact h1.trans (by rw [div_eq_inv_mul])
  -- `τ = h` pulled back vanishes nowhere, so it trivializes `M`
  have hτ : ∀ y, y ∈ nonvanishingLocus M τ := by
    intro y
    obtain ⟨⟨j⟩, hj⟩ := exists_mem_nonvanishingLocus_of_isGeneratedBySections hM hgen y
    have hj' : y ∈ nonvanishingLocus M (t j) := hj
    rw [ht j] at hj'
    exact nonvanishingLocus_smul_subset M _ τ hj'
  have htriv : IsTrivializingSection M ⊤ τ :=
    IsTrivializingSection.of_local fun y _ => ⟨nonvanishingLocusOpens hM τ, le_top, hτ y,
      isTrivializingSection_nonvanishingLocusOpens hM τ⟩
  -- the matching frame of `c^* 𝒪_{Spec k}`
  set u := pullbackGlobalSection c (structureModuleSection _ (specConst k (h ⬝ᵥ p)))
  have hu : IsTrivializingSection ((Scheme.Modules.pullback c).obj (structureModuleOf _)) ⊤ u :=
    (IsTrivializingSection.pullback c (isTrivializingSection_structureModuleSection
      (isUnit_specConst k hph))).restrict (Scheme.Hom.preimage_top c).ge
  have σ : PUnit.{u + 1} ≃ ULift.{u} (Fin 1) := Equiv.ofUnique _ _
  obtain ⟨α, hα⟩ := Ringed.exists_iso_of_frames (R := T.sheaf)
    (fun _ : PUnit.{u + 1} => ⊤) (le_iSup (fun _ : PUnit.{u + 1} => ⊤) PUnit.unit)
    (A := M) (B := (Scheme.Modules.pullback c).obj (structureModuleOf _))
    (fun _ => τ) (fun _ => u)
    (fun _ => (isLocalFrame_of_isTrivializingSection htriv).reindex σ)
    (fun _ => (isLocalFrame_of_isTrivializingSection hu).reindex σ)
    (fun _ _ => ⟨1, by rw [one_smul], by rw [one_smul]⟩)
  let α' : M ≅ (Scheme.Modules.pullback c).obj (structureModuleOf _) := α
  have hα' : α'.hom.app ⊤ τ = u := hα PUnit.unit
  have hsec : ∀ j, α'.hom.app ⊤ (t j) = pullbackGlobalSection c (pointSections k p j) := by
    intro j
    rw [ht j, Scheme.Modules.Hom.app_smul, hα', kConst_apply, ← pullbackGlobalSection_smul,
      ← structureModuleSection_mul, ← specConst_mul, div_mul_cancel₀ _ hph]
  obtain ⟨-, eP, heP⟩ := projectivePoint_spec k p hp
  obtain ⟨e', he'⟩ := exists_iso_of_comp c _ rfl eP heP
  have hc : (c ≫ projectivePoint k p hp) ≫ projectiveSpaceOverSchemeProjection (n + 1) _ = c := by
    rw [Category.assoc, (projectivePoint_spec k _ _).1, Category.comp_id]
  exact (existsUnique_morphism_of_isGeneratedBySections c
    (Scheme.Modules.IsInvertible.pullback c (isInvertible_structureModuleOf _))
    (fun i => pullbackGlobalSection c (pointSections k p i))
    (isGeneratedBySections_pullback_pointSections c hp)).unique
    (y₁ := g) (y₂ := c ≫ projectivePoint k p hp) ⟨rfl, α', hsec⟩ ⟨hc, e', he'⟩

/-- **`U_P = ℙⁿ⁺¹_k − {P}`** when `P` is not on `H`. -/
theorem pointProjectionDomain_eq_compl_range {p h : Fin (n + 2) → k} (hph : h ⬝ᵥ p ≠ 0) :
    (pointProjectionDomain k p h : Set _) =
      (Set.range (projectivePoint k p (ne_zero_of_dotProduct_ne_zero hph)))ᶜ := by
  have hp := ne_zero_of_dotProduct_ne_zero hph
  ext x
  refine ⟨fun hx ⟨y, hy⟩ => ?_, fun hx => ?_⟩
  · subst hy
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hi' := (projectivePoint_mem_nonvanishingLocus_linearSection_iff hp _ y).mp hi
    apply hi'
    rw [projectionVector_dotProduct]
    simp [mul_comm]
  · by_contra hxU
    apply hx
    have hgx : ∀ y, Scheme.fromSpecResidueField _ x y = x := fun y =>
      Scheme.fromSpecResidueField_apply x y
    have h' := eq_comp_projectivePoint_of_notMem hph (Scheme.fromSpecResidueField _ x)
      (fun y => (hgx y).symm ▸ hxU)
    refine ⟨(Scheme.fromSpecResidueField _ x ≫
      projectiveSpaceOverSchemeProjection (n + 1) _) default, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← h']
    exact hgx default

/-- **The projection lands in `H`**, scheme-theoretically: it pulls the equation `h` of `H` back
to zero. -/
theorem pullbackGlobalSection_pointProjection_linearSection (p h : Fin (n + 2) → k) :
    pullbackGlobalSection (pointProjection k p h) (linearSection k (n + 1) h) = 0 := by
  obtain ⟨hπ, eπ, heπ⟩ := pointProjection_spec k p h
  refine (iso_inv_app_eq_of_hom_app_eq eπ ?_).symm.trans (map_zero _)
  rw [iso_app_linearSection hπ eπ heπ h]
  simp only [pointProjectionSections, ← appTop_kConst, ← pullbackGlobalSection_smul,
    ← pullbackGlobalSection_sum, sum_smul_projectionLinearSections]
  exact pullbackGlobalSection_zero _ _

/-- **The projection lands in `H`**, on points: no point of the image lies off `H = {h = 0}`. -/
theorem pointProjection_notMem_nonvanishingLocus (p h : Fin (n + 2) → k)
    (y : (pointProjectionDomain k p h).toScheme) :
    pointProjection k p h y ∉ nonvanishingLocus _ (linearSection k (n + 1) h) := by
  rw [← mem_nonvanishingLocus_pullbackGlobalSection_iff _
    (isInvertible_projectiveSpaceTwistingSheaf _ _ _),
    pullbackGlobalSection_pointProjection_linearSection, nonvanishingLocus_zero]
  exact Set.notMem_empty _

/-- If `h(P) Q − h(Q) P ≠ 0` then `q ≠ 0`. -/
theorem ne_zero_of_projection_ne_zero {p h q : Fin (n + 2) → k}
    (hq : (h ⬝ᵥ p) • q - (h ⬝ᵥ q) • p ≠ 0) : q ≠ 0 := by
  rintro rfl
  simp at hq

/-- `h(P) Q − h(Q) P = 0` exactly when `Q` is a multiple of `P`, i.e. the point `Q` is `P`. -/
theorem projection_eq_zero_iff {p h q : Fin (n + 2) → k} (hph : h ⬝ᵥ p ≠ 0) :
    (h ⬝ᵥ p) • q - (h ⬝ᵥ q) • p = 0 ↔ ∃ t : k, q = t • p := by
  constructor
  · intro hz
    refine ⟨(h ⬝ᵥ q) / (h ⬝ᵥ p), ?_⟩
    rw [sub_eq_zero] at hz
    rw [div_eq_inv_mul, mul_smul, ← hz, smul_smul, inv_mul_cancel₀ hph, one_smul]
  · rintro ⟨t, rfl⟩
    rw [dotProduct_smul, smul_smul, smul_eq_mul, mul_comm, sub_self]

/-- **Projection of a rational point is the intersection of a line with `H`.** For a rational
point `Q = (q₀ : ⋯ : q_{n+1}) ≠ P` (`h(P) q − h(q) p ≠ 0`), `Q` lies in `U_P` and the projection
sends it to `h(P) Q − h(Q) P`, which lies on the line `PQ` and on `H`. -/
theorem exists_lift_projectivePoint_comp_pointProjection {p h q : Fin (n + 2) → k}
    (hq : (h ⬝ᵥ p) • q - (h ⬝ᵥ q) • p ≠ 0) :
    ∃ Q : Spec (CommRingCat.of k) ⟶ (pointProjectionDomain k p h).toScheme,
      Q ≫ (pointProjectionDomain k p h).ι =
          projectivePoint k q (ne_zero_of_projection_ne_zero hq) ∧
        Q ≫ pointProjection k p h = projectivePoint k _ hq := by
  have hq0 := ne_zero_of_projection_ne_zero hq
  have hrange : Set.range (projectivePoint k q hq0) ⊆
      Set.range (pointProjectionDomain k p h).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hq
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    exact (projectivePoint_mem_nonvanishingLocus_linearSection_iff hq0 _ y).mpr
      (by rw [projectionVector_dotProduct]; exact hi)
  set Q := IsOpenImmersion.lift _ _ hrange
  have hQ : Q ≫ (pointProjectionDomain k p h).ι = projectivePoint k q hq0 :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨Q, hQ, ?_⟩
  obtain ⟨hπ, eπ, heπ⟩ := pointProjection_spec k p h
  obtain ⟨hqp, eq, heq⟩ := projectivePoint_spec k q hq0
  obtain ⟨e2, he2⟩ := exists_iso_of_comp Q _ rfl eπ heπ
  obtain ⟨e1, he1⟩ := exists_iso_of_comp_all Q _ hQ (Iso.refl (pointProjectionTwist k p h))
  refine eq_projectivePoint hq (by rw [Category.assoc, hπ, ← Category.assoc, hQ, hqp])
    (e2 ≪≫ e1.symm ≪≫ eq) fun i => ?_
  have h1 : e1.hom.app ⊤ (pullbackGlobalSection (projectivePoint k q hq0)
      (projectionLinearSections k p h i)) =
      pullbackGlobalSection Q (pointProjectionSections k p h i) := he1 _
  simp only [Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [he2, iso_inv_app_eq_of_hom_app_eq e1 h1, projectionLinearSections,
    iso_app_linearSection_projectivePoint hq0 heq, projectionVector_dotProduct]

end GeneralProperties

/-! ### The coordinate case -/

section CoordinateCase

open Matrix

variable (k : Type u) [Field k] (n : ℕ)

/-- The coordinate point `(0 : ⋯ : 0 : 1)` is off `x_{n+1} = 0`. -/
theorem single_last_dotProduct_ne_zero :
    (Pi.single (Fin.last (n + 1)) (1 : k) : Fin (n + 2) → k) ⬝ᵥ Pi.single (Fin.last (n + 1)) 1 ≠
      0 := by
  simp

/-- For `P = (0 : ⋯ : 0 : 1)` and `H = {x_{n+1} = 0}`, `U_P` is `U = D₊(x₀) ∪ ⋯ ∪ D₊(xₙ)`. -/
theorem pointProjectionDomain_single_last :
    pointProjectionDomain k (Pi.single (Fin.last (n + 1)) 1) (Pi.single (Fin.last (n + 1)) 1) =
      projectionDomain n (Spec (CommRingCat.of k)) := by
  refine SetLike.coe_injective ?_
  rw [pointProjectionDomain_eq_compl_range (single_last_dotProduct_ne_zero k n),
    projectionDomain_eq_compl_range]
  rfl

/-- **The coordinate case of the general projection.** For `P = (0 : ⋯ : 0 : 1)` and
`H = {x_{n+1} = 0}`, the projection `U_P ⟶ ℙⁿ⁺¹_k` is `projectionFromPoint` followed by the
identification `(x₀ : ⋯ : xₙ) ↦ (x₀ : ⋯ : xₙ : 0)` of `ℙⁿ_k` with `H`. -/
theorem pointProjection_single_last :
    pointProjection k (Pi.single (Fin.last (n + 1)) 1) (Pi.single (Fin.last (n + 1)) 1) =
      (Scheme.isoOfEq _ (pointProjectionDomain_single_last k n)).hom ≫
        projectionFromPoint n _ ≫ hyperplaneInclusion n _ := by
  symm
  rw [← eq_pointProjection_iff]
  set ι' := (Scheme.isoOfEq _ (pointProjectionDomain_single_last k n)).hom
  have hι : ι' ≫ (projectionDomain n (Spec (CommRingCat.of k))).ι =
      (pointProjectionDomain k (Pi.single (Fin.last (n + 1)) 1)
        (Pi.single (Fin.last (n + 1)) 1)).ι := Scheme.isoOfEq_hom_ι _ _
  obtain ⟨hj, ej, hej⟩ := hyperplaneInclusion_spec n (Spec (CommRingCat.of k))
  obtain ⟨hπ, eπ, heπ⟩ := projectionFromPoint_spec n (Spec (CommRingCat.of k))
  obtain ⟨e1, he1⟩ := exists_iso_of_comp (projectionFromPoint n _) _ rfl ej hej
  obtain ⟨e2, he2⟩ := exists_iso_of_comp ι' (projectionFromPoint n _ ≫ hyperplaneInclusion n _)
    rfl (e1 ≪≫ eπ)
    (s := fun i => eπ.hom.app ⊤ (pullbackGlobalSection (projectionFromPoint n _)
      (hyperplaneSections n _ i))) (fun i => by
        simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
        rw [he1])
  obtain ⟨e3, he3⟩ := exists_iso_of_comp_all ι' _ hι (Iso.refl (projectionDomainTwist n _))
  refine ⟨by rw [Category.assoc, Category.assoc, hj, hπ, ← Category.assoc, hι],
    e2 ≪≫ e3.symm, fun i => ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  rw [he2]
  have hee : (Pi.single (Fin.last (n + 1)) (1 : k) : Fin (n + 2) → k) ⬝ᵥ
      Pi.single (Fin.last (n + 1)) 1 = 1 := by simp
  induction i using Fin.lastCases with
  | last =>
    have h0 : projectionVector k (Pi.single (Fin.last (n + 1)) 1)
        (Pi.single (Fin.last (n + 1)) 1) (Fin.last (n + 1)) = 0 := by
      simp [projectionVector, hee]
    simp only [hyperplaneSections, Fin.lastCases_last, pointProjectionSections,
      projectionLinearSections, h0]
    have hl : linearSection k (n + 1) 0 = 0 := by simp [linearSection]
    rw [pullbackGlobalSection_zero, map_zero, pullbackGlobalSection_zero, map_zero, hl,
      pullbackGlobalSection_zero]
  | cast i =>
    have h1 : projectionVector k (Pi.single (Fin.last (n + 1)) 1)
        (Pi.single (Fin.last (n + 1)) 1) i.castSucc = Pi.single i.castSucc 1 := by
      simp [projectionVector, hee]
    simp only [hyperplaneSections, Fin.lastCases_castSucc, heπ, pointProjectionSections,
      projectionLinearSections, h1, linearSection_single]
    have h2 : e3.hom.app ⊤ (pullbackGlobalSection (pointProjectionDomain k
        (Pi.single (Fin.last (n + 1)) 1) (Pi.single (Fin.last (n + 1)) 1)).ι
        (projectiveSpaceCoordinate (n + 1) _ i.castSucc)) =
        pullbackGlobalSection ι' (projectionSections n _ i) := he3 _
    exact iso_inv_app_eq_of_hom_app_eq e3 h2

end CoordinateCase

/-! ### Summary -/

section Summary

open Matrix

variable {k : Type u} [Field k] {n : ℕ}

/-- If `Q` is not a multiple of `P`, then `h(P) Q − h(Q) P ≠ 0`. -/
theorem projection_ne_zero {p h q : Fin (n + 2) → k} (hph : h ⬝ᵥ p ≠ 0)
    (hq : ¬∃ t : k, q = t • p) : (h ⬝ᵥ p) • q - (h ⬝ᵥ q) • p ≠ 0 :=
  fun hz => hq ((projection_eq_zero_iff hph).mp hz)

/-- `h(P) Q − h(Q) P` lies on `H = {h = 0}`. -/
theorem dotProduct_projection (p h q : Fin (n + 2) → k) :
    h ⬝ᵥ ((h ⬝ᵥ p) • q - (h ⬝ᵥ q) • p) = 0 := by
  simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

/-- **Projection from a point is a morphism** (Hartshorne I, Exercise 3.14(a)). Let
`P = (p₀ : ⋯ : p_{n+1})` be a rational point of `ℙⁿ⁺¹_k` and `H = {h = 0}`, `h = ∑ hⱼ xⱼ`, a
hyperplane not containing `P` (`h(P) ≠ 0`), and let `π = pointProjection k p h : U_P ⟶ ℙⁿ⁺¹_k`.
Then:

* `U_P = ℙⁿ⁺¹_k − {P}`;
* `π` is a morphism, namely the unique `k`-morphism defined (Hartshorne II, Theorem 7.1) by the
  sections `h(P) xᵢ − pᵢ h` of `𝒪(1)`;
* `π` maps into `H`: it pulls the equation `h` back to zero, and no point of its image lies
  off `H`;
* on rational points, `π(Q)` is the intersection of the line `PQ` with `H`: for
  `Q = (q₀ : ⋯ : q_{n+1}) ≠ P` (that is, `q` is not a multiple of `p`), `Q` lies in `U_P` and
  `π(Q) = h(P) Q − h(Q) P`, a point of the line `PQ` lying on `H`.

The book works with varieties over an algebraically closed field; here `k` is any field. The
target is `ℙⁿ⁺¹_k`, with image in `H`. -/
theorem pointProjection_isProjection {p h : Fin (n + 2) → k} (hph : h ⬝ᵥ p ≠ 0) :
    (pointProjectionDomain k p h : Set _) =
        (Set.range (projectivePoint k p (ne_zero_of_dotProduct_ne_zero hph)))ᶜ ∧
      (∀ π : (pointProjectionDomain k p h).toScheme ⟶
          projectiveSpaceOverScheme (n + 1) (Spec (CommRingCat.of k)),
        (π ≫ projectiveSpaceOverSchemeProjection (n + 1) _ =
            (pointProjectionDomain k p h).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) _ ∧
          ∃ e : (Scheme.Modules.pullback π).obj (projectiveSpaceTwistingSheaf (n + 1) _ 1) ≅
              pointProjectionTwist k p h,
            ∀ i, e.hom.app ⊤ (pullbackGlobalSection π (projectiveSpaceCoordinate (n + 1) _ i)) =
              pointProjectionSections k p h i) ↔ π = pointProjection k p h) ∧
      pullbackGlobalSection (pointProjection k p h) (linearSection k (n + 1) h) = 0 ∧
      (∀ y, pointProjection k p h y ∉ nonvanishingLocus _ (linearSection k (n + 1) h)) ∧
      ∀ (q : Fin (n + 2) → k) (hq : ¬∃ t : k, q = t • p),
        h ⬝ᵥ ((h ⬝ᵥ p) • q - (h ⬝ᵥ q) • p) = 0 ∧
        ∃ Q : Spec (CommRingCat.of k) ⟶ (pointProjectionDomain k p h).toScheme,
          Q ≫ (pointProjectionDomain k p h).ι =
              projectivePoint k q (ne_zero_of_projection_ne_zero (projection_ne_zero hph hq)) ∧
            Q ≫ pointProjection k p h =
              projectivePoint k ((h ⬝ᵥ p) • q - (h ⬝ᵥ q) • p) (projection_ne_zero hph hq) :=
  ⟨pointProjectionDomain_eq_compl_range hph, eq_pointProjection_iff k p h,
    pullbackGlobalSection_pointProjection_linearSection p h,
    pointProjection_notMem_nonvanishingLocus p h,
    fun q hq => ⟨dotProduct_projection p h q,
      exists_lift_projectivePoint_comp_pointProjection (projection_ne_zero hph hq)⟩⟩

end Summary

section CoordinateSummary

variable (k : Type u) [Field k] (n : ℕ)

/-- **Projection from a point, in coordinates** (Hartshorne I, Exercise 3.14(a), in the coordinates
in which the point `P` is the omitted coordinate point `(0 : ⋯ : 0 : 1)` of `ℙⁿ⁺¹_k` and the
hyperplane `H` is `x_{n+1} = 0`, identified with `ℙⁿ_k` by `(x₀ : ⋯ : xₙ) ↦ (x₀ : ⋯ : xₙ : 0)`).
Let `U ⊆ ℙⁿ⁺¹_k` be the open where one of `x₀, …, xₙ` is nonzero, and `π : U ⟶ ℙⁿ_k`
`projectionFromPoint`. Then:

* `U = ℙⁿ⁺¹_k − {P}`;
* `π` is the morphism defined (Hartshorne II, Theorem 7.1) by the remaining homogeneous
  coordinates `x₀, …, xₙ`: it is the unique `k`-morphism `U ⟶ ℙⁿ_k` pulling `𝒪(1)` back to
  `𝒪(1)|_U` with each `xᵢ` going to `xᵢ|_U`;
* the identification `ℙⁿ_k ⟶ ℙⁿ⁺¹_k`, `(x₀ : ⋯ : xₙ) ↦ (x₀ : ⋯ : xₙ : 0)`, lands in `H`;
* on rational points, `π(Q)` is the intersection of the line `PQ` with `H`: for
  `Q = (a₀ : ⋯ : a_{n+1}) ≠ P`, `Q` lies in `U` and `π(Q)` is the point
  `(a₀ : ⋯ : aₙ : 0) = Q − a_{n+1} P` of `H`;
* `π` followed by `ℙⁿ_k ⟶ H` is the general projection `pointProjection` for this `P` and `H`.

The general point and hyperplane are `pointProjection_isProjection`. -/
theorem projectionFromPoint_isProjection :
    (projectionDomain n (Spec (CommRingCat.of k)) : Set _) =
        (Set.range (coordinatePoint k n))ᶜ ∧
      (∀ π : (projectionDomain n (Spec (CommRingCat.of k))).toScheme ⟶
          projectiveSpaceOverScheme n (Spec (CommRingCat.of k)),
        (π ≫ projectiveSpaceOverSchemeProjection n _ =
            (projectionDomain n _).ι ≫ projectiveSpaceOverSchemeProjection (n + 1) _ ∧
          ∃ e : (Scheme.Modules.pullback π).obj (projectiveSpaceTwistingSheaf n _ 1) ≅
              projectionDomainTwist n _,
            ∀ i, e.hom.app ⊤ (pullbackGlobalSection π (projectiveSpaceCoordinate n _ i)) =
              projectionSections n _ i) ↔ π = projectionFromPoint n _) ∧
      (∀ y, hyperplaneInclusion n (Spec (CommRingCat.of k)) y ∉
        projectiveSpaceChart (n + 1) _ (Fin.last (n + 1))) ∧
      (∀ (a : Fin (n + 2) → k) (ha : (fun i : Fin (n + 1) => a i.castSucc) ≠ 0),
        ∃ Q : Spec (CommRingCat.of k) ⟶ (projectionDomain n (Spec (CommRingCat.of k))).toScheme,
          Q ≫ (projectionDomain n _).ι =
              projectivePoint k a (ne_zero_of_comp_castSucc_ne_zero ha) ∧
            Q ≫ projectionFromPoint n _ ≫ hyperplaneInclusion n _ =
              projectivePoint k (a - a (Fin.last (n + 1)) • Pi.single (Fin.last (n + 1)) 1)
                (sub_smul_single_last_ne_zero ha)) ∧
      ∃ hU : pointProjectionDomain k (Pi.single (Fin.last (n + 1)) 1)
          (Pi.single (Fin.last (n + 1)) 1) = projectionDomain n (Spec (CommRingCat.of k)),
        pointProjection k (Pi.single (Fin.last (n + 1)) 1) (Pi.single (Fin.last (n + 1)) 1) =
          (Scheme.isoOfEq _ hU).hom ≫ projectionFromPoint n _ ≫ hyperplaneInclusion n _ :=
  ⟨projectionDomain_eq_compl_range k n, eq_projectionFromPoint_iff n _,
    hyperplaneInclusion_notMem_projectiveSpaceChart_last n _,
    fun _ ha => exists_lift_projectivePoint_comp_projectionFromPoint_hyperplaneInclusion ha,
    pointProjectionDomain_single_last k n, pointProjection_single_last k n⟩

end CoordinateSummary

end Hartshorne
