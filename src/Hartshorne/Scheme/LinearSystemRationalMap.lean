/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FiniteLinearSystem
import Hartshorne.Scheme.BasePointFree
import Hartshorne.Scheme.BlowupUniversalProperty
import Hartshorne.Scheme.ProjectiveSpaceOverSpec
import Hartshorne.Scheme.ProjectiveSpaceChart
import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# The rational map defined by a linear system, its image and the image dimension

Let `X` be a scheme over a field `k` with structure morphism `q`, `L` an invertible sheaf on `X`
and `s₀, …, sₙ` global sections of `L`. On the complement `X - B` of the base locus the `sᵢ`
generate `L`, and define a morphism `φ : X - B ⟶ ℙⁿ_k` (`Hartshorne.linearSystemMorphism`). This
file packages `φ` as a rational map and records its image.

## Main definitions and results

* `linearSystemPartialMap`, `linearSystemRationalMap`: on an integral `X`, if some `sᵢ` is
  nonzero then `X - B` is a nonempty, hence dense, open set, and `φ` is a rational map
  `X ⇢ ℙⁿ_k`.
* `linearSystemImage`: the closure `\overline{φ(X - B)}` of the image of `φ`, a closed subset of
  `ℙⁿ_k`; `linearSystemImageDim`: its topological Krull dimension.
* `LinearSystem.mem_linearSystemDomain_iff_not_isBasePoint`: for a family spanning a linear
  system `𝔡`, `X - B` is exactly the set of points that are not base points of `𝔡`.
* **Removing a fixed part.** Let `m : L' ⟶ L` be a morphism of invertible sheaves, for instance
  multiplication `𝒪(M) ⟶ 𝒪(M + F)` by a section with divisor of zeros `F`, and let
  `sᵢ = m(s'ᵢ)`. Then `X - B ⊆ X - B'` (`linearSystemDomain_map_le`), the morphism defined by the
  `sᵢ` is the restriction of the morphism defined by the `s'ᵢ`
  (`linearSystemMorphism_map`), the two rational maps are equal
  (`linearSystemRationalMap_map`) and so are the two images (`linearSystemImage_map`).
* `subsingleton_projectiveSpaceOverScheme_zero`: `ℙ⁰_k` has a single point. Hence a single
  nonzero section defines a map whose image has dimension zero
  (`linearSystemImageDim_eq_zero`).

## Proof

For the fixed part, on `X - B` the sections `m(s'ᵢ)` generate `L`, so the restriction of `m`
there is an epimorphism of invertible sheaves, hence an isomorphism (Exercise II.7.1). It
identifies the data `(φ'^* 𝒪(1), φ'^* xᵢ)` of the restricted morphism `φ'` with
`(L, m(s'ᵢ))`, and the uniqueness in Theorem II.7.1 gives the equality of morphisms. The images
agree because `X - B` is dense in `X - B'` and `φ'` is continuous.

`ℙ⁰_k ≅ Proj k[x₀]` is covered by the single chart `D₊(x₀) ≅ Spec k[x₀]_{(x₀)}`, and the
degree-zero localization `k[x₀]_{(x₀)}` is the polynomial ring in no variables, that is `k`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

variable {X : Scheme.{u}} {L L' : X.Modules}

/-! ### Morphisms of modules shrink nonvanishing loci -/

section NonvanishingLocus

/-- A morphism of modules out of an invertible sheaf can only shrink nonvanishing loci: if `t`
vanishes at `x`, so does `m(t)`. -/
theorem nonvanishingLocus_app_subset (hL' : L'.IsInvertible) (m : L' ⟶ L) (t : Γ(L', ⊤)) :
    nonvanishingLocus L (m.app ⊤ t) ⊆ nonvanishingLocus L' t := by
  intro x hx
  by_contra ht
  obtain ⟨U, e, hxU, he⟩ := exists_isTrivializingSection hL' x
  obtain ⟨g, hg⟩ := he.exists_eq_smul t
  have hgx : x ∉ X.basicOpen g := fun h => ht ((he.mem_nonvanishingLocus_iff hg hxU).mpr h)
  apply hx
  have hgerm : L.presheaf.germ ⊤ x trivial (m.app ⊤ t) =
      X.presheaf.germ U x hxU g • L.presheaf.germ U x hxU (m.app U e) := by
    rw [← TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE (le_top : U ≤ ⊤)) x hxU,
      ← hom_app_map, hg, Scheme.Modules.Hom.app_smul]
    exact schemeModules_germ_smul L U x hxU g (m.app U e)
  have hg' : X.presheaf.germ U x hxU g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hgx ((X.mem_basicOpen g x hxU).mpr hu)
  rw [hgerm]
  let := moduleSheafStalkModule L x
  exact Submodule.smul_mem_smul hg' Submodule.mem_top

end NonvanishingLocus

/-! ### Removing a fixed part does not change the morphism -/

section FixedPart

variable {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k)) {n : ℕ}
  (hL : L.IsInvertible)

/-- **The base locus can only grow when a fixed part is added**: for `m : L' ⟶ L`, the
complement of the base locus of the sections `m(s'ᵢ)` lies in that of the `s'ᵢ`. -/
theorem linearSystemDomain_map_le (hL' : L'.IsInvertible) (m : L' ⟶ L) (s' : Fin (n + 1) → Γ(L', ⊤)) :
    linearSystemDomain hL (fun i => m.app ⊤ (s' i)) ≤ linearSystemDomain hL' s' := by
  intro x hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, nonvanishingLocus_app_subset hL' m (s' i) hi⟩

/-- `(g)^* N ≅ (g')^* N` for `g = g'` sends `g^* e` to `g'^* e`. -/
private theorem pullbackCongr_hom_pullbackGlobalSection' {Y Z : Scheme.{u}} {g g' : Y ⟶ Z}
    (h : g = g') {N : Z.Modules} (e : Γ(N, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).hom.app N).app ⊤ (pullbackGlobalSection g e) =
      pullbackGlobalSection g' e := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- A morphism of modules sends the compatible family of restrictions of a global section `t` to
that of its image. -/
private theorem sectionsMap_sectionsOfTop' {Z : Scheme.{u}} {F G : Z.Modules} (g : F ⟶ G)
    (t : Γ(F, ⊤)) :
    SheafOfModules.sectionsMap g (Scheme.Modules.GloballyGenerated.sectionsOfTop F t) =
      Scheme.Modules.GloballyGenerated.sectionsOfTop G (g.app ⊤ t) := by
  ext W
  exact hom_app_map g (le_top : W.unop ≤ ⊤) t

/-- On the complement of the base locus of the sections `m(s'ᵢ)`, the morphism `m : L' ⟶ L` of
invertible sheaves restricts to an isomorphism. -/
theorem isIso_pullback_map_linearSystemDomain (hL' : L'.IsInvertible) (m : L' ⟶ L)
    (s' : Fin (n + 1) → Γ(L', ⊤)) :
    IsIso ((Scheme.Modules.pullback
      (linearSystemDomain hL (fun i => m.app ⊤ (s' i))).ι).map m) := by
  let W := linearSystemDomain hL (fun i => m.app ⊤ (s' i))
  let M : (Scheme.Modules.pullback W.ι).obj L' ⟶ (Scheme.Modules.pullback W.ι).obj L :=
    (Scheme.Modules.pullback W.ι).map m
  have hepi := (isGeneratedBySections_linearSystemSections hL (fun i => m.app ⊤ (s' i))).epi
  let p' : @Quiver.Hom W.toScheme.Modules _ (SheafOfModules.free (ULift.{u} (Fin (n + 1))))
      ((Scheme.Modules.pullback W.ι).obj L') :=
    (SheafOfModules.freeHomEquiv _).symm fun i : ULift.{u} (Fin (n + 1)) =>
      Scheme.Modules.GloballyGenerated.sectionsOfTop _ (pullbackGlobalSection W.ι (s' i.down))
  have hcomp : p' ≫ M = (SheafOfModules.freeHomEquiv _).symm fun i : ULift.{u} (Fin (n + 1)) =>
      Scheme.Modules.GloballyGenerated.sectionsOfTop _
        (linearSystemSections hL (fun i => m.app ⊤ (s' i)) i.down) := by
    refine (SheafOfModules.freeHomEquiv_symm_comp _ _).trans ?_
    congr 1
    funext i
    rw [sectionsMap_sectionsOfTop', pullback_map_pullbackGlobalSection]
  have : Epi (p' ≫ M) := by
    rw [hcomp]
    exact hepi
  have : Epi M := epi_of_epi p' M
  exact isIso_of_epi_of_isInvertible (hL'.pullback _) (hL.pullback _) M

/-- **Removing a fixed part does not change the morphism.** Let `m : L' ⟶ L` be a morphism of
invertible sheaves (for instance multiplication by a section whose divisor of zeros `F` is the
fixed part) and `sᵢ = m(s'ᵢ)`. On the complement of the base locus of the `sᵢ`, the morphism
to `ℙⁿ_k` they define is the restriction of the morphism defined by the `s'ᵢ`. -/
theorem linearSystemMorphism_map (hL' : L'.IsInvertible) (m : L' ⟶ L) (s' : Fin (n + 1) → Γ(L', ⊤)) :
    linearSystemMorphism q hL (fun i => m.app ⊤ (s' i)) =
      X.homOfLE (linearSystemDomain_map_le hL hL' m s') ≫ linearSystemMorphism q hL' s' := by
  let W := linearSystemDomain hL (fun i => m.app ⊤ (s' i))
  let W' := linearSystemDomain hL' s'
  have hle : W ≤ W' := linearSystemDomain_map_le hL hL' m s'
  let j := X.homOfLE hle
  have hj : j ≫ W'.ι = W.ι := X.homOfLE_ι hle
  obtain ⟨hφ', e', he'⟩ := linearSystemMorphism_spec q hL' s'
  obtain ⟨eA, heA⟩ := exists_iso_of_comp j (linearSystemMorphism q hL' s') rfl e' he'
  have := isIso_pullback_map_linearSystemDomain hL hL' m s'
  refine ((existsUnique_linearSystemMorphism q hL (fun i => m.app ⊤ (s' i))).unique
    (linearSystemMorphism_spec q hL _) ⟨?_, ?_⟩)
  · rw [Category.assoc, hφ', ← Category.assoc, hj]
  · refine ⟨eA ≪≫ (Scheme.Modules.pullbackComp j W'.ι).app L' ≪≫
      (Scheme.Modules.pullbackCongr hj).app L' ≪≫
      asIso ((Scheme.Modules.pullback W.ι).map m), fun i => ?_⟩
    simp only [Iso.trans_hom, Iso.app_hom, asIso_hom, Scheme.Modules.Hom.comp_app,
      ConcreteCategory.comp_apply]
    rw [heA, pullbackComp_hom_pullbackGlobalSection, pullbackCongr_hom_pullbackGlobalSection',
      pullback_map_pullbackGlobalSection]

end FixedPart

/-! ### The rational map and its image -/

section RationalMap

variable {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k)) {n : ℕ}
  (hL : L.IsInvertible)

/-- On an integral scheme, the complement of the base locus of a family of sections that are
not all zero is nonempty. -/
theorem linearSystemDomain_nonempty [IsIntegral X] {s : Fin (n + 1) → Γ(L, ⊤)} (hs : s ≠ 0) :
    (linearSystemDomain hL s : Set X).Nonempty := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hs
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  refine hi (eq_zero_of_forall_notMem_nonvanishingLocus hL fun x hx => ?_)
  have hx' : x ∈ (linearSystemDomain hL s : Set X) :=
    TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx⟩
  rw [h] at hx'
  exact hx'

/-- On an integral scheme, the complement of the base locus of a family of sections that are
not all zero is dense. -/
theorem dense_linearSystemDomain [IsIntegral X] {s : Fin (n + 1) → Γ(L, ⊤)} (hs : s ≠ 0) :
    Dense (linearSystemDomain hL s : Set X) :=
  (linearSystemDomain hL s).isOpen.dense (linearSystemDomain_nonempty hL hs)

/-- The morphism `X - B ⟶ ℙⁿ_k` defined by sections `s₀, …, sₙ` of `L`, not all zero, on an
integral scheme, as a partial map: a morphism on a dense open subscheme. -/
def linearSystemPartialMap [IsIntegral X] (s : Fin (n + 1) → Γ(L, ⊤)) (hs : s ≠ 0) :
    X.PartialMap (projectiveSpaceOverScheme n (Spec (CommRingCat.of k))) where
  domain := linearSystemDomain hL s
  dense_domain := dense_linearSystemDomain hL hs
  hom := linearSystemMorphism q hL s

/-- **The rational map `X ⇢ ℙⁿ_k` defined by a linear system** with spanning family
`s₀, …, sₙ` (not all zero) on an integral scheme: the class of the morphism defined by the `sᵢ`
on the complement of the base locus. -/
def linearSystemRationalMap [IsIntegral X] (s : Fin (n + 1) → Γ(L, ⊤)) (hs : s ≠ 0) :
    X ⤏ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)) :=
  (linearSystemPartialMap q hL s hs).toRationalMap

/-- **The image of the map defined by a linear system**: the closure `\overline{φ(X - B)}` in
`ℙⁿ_k` of the image of the morphism `φ` defined by `s₀, …, sₙ` on the complement of the base
locus. -/
def linearSystemImage (s : Fin (n + 1) → Γ(L, ⊤)) :
    Closeds (projectiveSpaceOverScheme n (Spec (CommRingCat.of k))) :=
  ⟨closure (Set.range (linearSystemMorphism q hL s)), isClosed_closure⟩

/-- **The dimension of the image** of the map defined by `s₀, …, sₙ`: the topological Krull
dimension of `\overline{φ(X - B)}`. -/
def linearSystemImageDim (s : Fin (n + 1) → Γ(L, ⊤)) : WithBot ℕ∞ :=
  topologicalKrullDim (linearSystemImage q hL s : Set (projectiveSpaceOverScheme n
    (Spec (CommRingCat.of k))))

/-- **Removing a fixed part does not change the rational map.** For a morphism `m : L' ⟶ L` of
invertible sheaves on an integral scheme and sections `sᵢ = m(s'ᵢ)` not all zero, the rational
maps defined by the `sᵢ` and by the `s'ᵢ` are equal. -/
theorem linearSystemRationalMap_map [IsIntegral X] (hL' : L'.IsInvertible) (m : L' ⟶ L)
    (s' : Fin (n + 1) → Γ(L', ⊤)) (hs : (fun i => m.app ⊤ (s' i)) ≠ 0) (hs' : s' ≠ 0) :
    linearSystemRationalMap q hL (fun i => m.app ⊤ (s' i)) hs =
      linearSystemRationalMap q hL' s' hs' := by
  have hle : linearSystemDomain hL (fun i => m.app ⊤ (s' i)) ≤
      (linearSystemPartialMap q hL' s' hs').domain := linearSystemDomain_map_le hL hL' m s'
  have h : linearSystemPartialMap q hL (fun i => m.app ⊤ (s' i)) hs =
      (linearSystemPartialMap q hL' s' hs').restrict _ (dense_linearSystemDomain hL hs) hle := by
    simp only [linearSystemPartialMap, Scheme.PartialMap.restrict]
    congr 1
    exact linearSystemMorphism_map q hL hL' m s'
  rw [linearSystemRationalMap, linearSystemRationalMap, h,
    Scheme.PartialMap.restrict_toRationalMap]

/-- **Removing a fixed part does not change the image.** For a morphism `m : L' ⟶ L` of
invertible sheaves on an irreducible scheme and sections `sᵢ = m(s'ᵢ)` whose base locus is not
everything, the images of the maps defined by the `sᵢ` and by the `s'ᵢ` have the same
closure. -/
theorem linearSystemImage_map [IrreducibleSpace X] (hL' : L'.IsInvertible) (m : L' ⟶ L)
    (s' : Fin (n + 1) → Γ(L', ⊤))
    (hne : (linearSystemDomain hL (fun i => m.app ⊤ (s' i)) : Set X).Nonempty) :
    linearSystemImage q hL (fun i => m.app ⊤ (s' i)) = linearSystemImage q hL' s' := by
  have hle := linearSystemDomain_map_le hL hL' m s'
  have hφ := linearSystemMorphism_map q hL hL' m s'
  refine Closeds.ext (le_antisymm (closure_mono ?_) ?_)
  · rintro _ ⟨z, rfl⟩
    exact ⟨X.homOfLE hle z, by rw [hφ, Scheme.Hom.comp_apply]⟩
  · refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨z, rfl⟩
    have hdense : Dense ((linearSystemDomain hL' s').ι ⁻¹'
        (linearSystemDomain hL (fun i => m.app ⊤ (s' i)) : Set X)) :=
      ((linearSystemDomain hL _).isOpen.dense hne).preimage
        (linearSystemDomain hL' s').ι.isOpenEmbedding.isOpenMap
    have hsub : (linearSystemDomain hL' s').ι ⁻¹'
        (linearSystemDomain hL (fun i => m.app ⊤ (s' i)) : Set X) ⊆
        Set.range (X.homOfLE hle) := by
      intro w hw
      exact ⟨⟨w.1, hw⟩, Subtype.ext (Scheme.homOfLE_apply hle ⟨w.1, hw⟩)⟩
    have hz : z ∈ closure (Set.range (X.homOfLE hle)) :=
      closure_mono hsub (hdense.closure_eq.symm ▸ Set.mem_univ z)
    refine closure_mono ?_ (image_closure_subset_closure_image
      (linearSystemMorphism q hL' s').continuous ⟨z, hz, rfl⟩)
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, by rw [hφ, Scheme.Hom.comp_apply]⟩

end RationalMap

/-! ### Projective space of dimension zero is a point -/

section ProjectiveSpaceZero

open MvPolynomial in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- **`ℙ⁰_k` has exactly one point** (it is nonempty by the cover by charts): `ℙ⁰_k ≅ Proj k[x₀]`
is covered by the chart `D₊(x₀) ≅ Spec k[x₀]_{(x₀)}`, and `k[x₀]_{(x₀)} ≅ k` is a field. -/
theorem subsingleton_projectiveSpaceOverScheme_zero (k : Type u) [Field k] :
    Subsingleton (projectiveSpaceOverScheme 0 (Spec (CommRingCat.of k))) := by
  let 𝒜 := homogeneousSubmodule (Fin (0 + 1)) k
  have htop : Proj.basicOpen 𝒜 (X 0) = ⊤ := by
    have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    rw [← iSup_proj_basicOpen_X_eq_top (σ := Fin (0 + 1)) k, iSup_unique]
    congr 2
    exact Subsingleton.elim (α := Fin 1) _ _
  let F := Proj.basicOpenIsoSpec 𝒜 (X 0) (X_mem_homogeneousSubmodule_one k 0) Nat.one_pos
  have : IsEmpty {j : Fin (0 + 1) // j ≠ 0} := ⟨fun j => j.2 (Subsingleton.elim (α := Fin 1) _ _)⟩
  have hfield : IsField (HomogeneousLocalization.Away 𝒜 (X 0)) :=
    ((chartAwayEquiv k (0 : Fin (0 + 1))).trans
      (MvPolynomial.isEmptyAlgEquiv k {j : Fin (0 + 1) // j ≠ 0}).toRingEquiv).isField
      (Field.toIsField k)
  have hspec : Subsingleton (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (X 0)))) := by
    let := hfield.toField
    change Subsingleton (PrimeSpectrum (HomogeneousLocalization.Away 𝒜 (X 0)))
    infer_instance
  have hproj : Subsingleton (Proj 𝒜) := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ Proj.basicOpen 𝒜 (X 0) := htop ▸ trivial
    have hb : b ∈ Proj.basicOpen 𝒜 (X 0) := htop ▸ trivial
    have h := F.hom.isOpenEmbedding.injective (hspec.elim (F.hom ⟨a, ha⟩) (F.hom ⟨b, hb⟩))
    exact congrArg Subtype.val h
  exact (projectiveSpaceOverSpecIso k 0 (Equiv.refl _)).inv.isOpenEmbedding.injective.subsingleton

/-- A nonempty space with at most one point has topological Krull dimension zero. -/
theorem topologicalKrullDim_eq_zero_of_subsingleton (T : Type*) [TopologicalSpace T]
    [Subsingleton T] [Nonempty T] : topologicalKrullDim T = 0 := by
  have huniv : IsIrreducible (Set.univ : Set T) := by
    obtain ⟨t⟩ := ‹Nonempty T›
    rw [show (Set.univ : Set T) = {t} from
      Set.eq_singleton_iff_unique_mem.mpr ⟨trivial, fun y _ => Subsingleton.elim y t⟩]
    exact isIrreducible_singleton
  have : Nonempty (IrreducibleCloseds T) := ⟨⟨Set.univ, huniv, isClosed_univ⟩⟩
  have huniv' : ∀ Z : IrreducibleCloseds T, (Z : Set T) = Set.univ := fun Z =>
    Set.eq_univ_of_forall fun y => by
      obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
      exact Subsingleton.elim z y ▸ hz
  have : Subsingleton (IrreducibleCloseds T) :=
    ⟨fun Z Z' => IrreducibleCloseds.ext ((huniv' Z).trans (huniv' Z').symm)⟩
  exact Order.krullDim_eq_zero

variable {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k)) (hL : L.IsInvertible)

/-- **A single nonzero section defines a map with zero-dimensional image.** On an integral
scheme, the image of the map `X - B ⟶ ℙ⁰_k` defined by one nonzero section of `L` has
dimension zero. -/
theorem linearSystemImageDim_eq_zero [IsIntegral X] {s : Fin (0 + 1) → Γ(L, ⊤)} (hs : s ≠ 0) :
    linearSystemImageDim q hL s = 0 := by
  have := subsingleton_projectiveSpaceOverScheme_zero k
  obtain ⟨x, hx⟩ := linearSystemDomain_nonempty hL hs
  have : Nonempty (linearSystemImage q hL s : Set (projectiveSpaceOverScheme 0
      (Spec (CommRingCat.of k)))) :=
    ⟨⟨linearSystemMorphism q hL s ⟨x, hx⟩, subset_closure ⟨⟨x, hx⟩, rfl⟩⟩⟩
  exact topologicalKrullDim_eq_zero_of_subsingleton _

end ProjectiveSpaceZero

/-! ### Linear systems -/

namespace LinearSystem

variable {k : Type u} [Field k] {q : X ⟶ Spec (CommRingCat.of k)} {n : ℕ}

/-- **The domain is the complement of the base points.** For a family `s₀, …, sₙ` spanning a
linear system `𝔡`, a point lies in the complement `X - B` of the base locus of the `sᵢ` exactly
when it is not a base point of `𝔡`. -/
theorem mem_linearSystemDomain_iff_not_isBasePoint (𝔡 : LinearSystem q L)
    (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) (x : X) :
    x ∈ linearSystemDomain 𝔡.isInvertible (fun i => toSection (s i)) ↔ ¬ 𝔡.IsBasePoint x := by
  rw [𝔡.isBasePoint_iff_of_span_eq s hs, linearSystemDomain, TopologicalSpace.Opens.mem_iSup]
  push Not
  rfl

/-- A family spanning a nonzero linear system is not identically zero. -/
theorem toSection_ne_zero_of_span_eq (𝔡 : LinearSystem q L)
    (s : Fin (n + 1) → globalSectionsOverField q L)
    (hs : Submodule.span k (Set.range s) = 𝔡.sections) (h : 𝔡.sections ≠ ⊥) :
    (fun i => toSection (s i)) ≠ 0 := by
  intro h0
  apply h
  rw [← hs, Submodule.span_eq_bot]
  rintro _ ⟨i, rfl⟩
  exact congrFun h0 i

/-- **An empty linear system.** On an integral scheme, a linear system has no divisors exactly
when its subspace of sections is zero. -/
theorem divisors_eq_empty_iff [IsIntegral X] (𝔡 : LinearSystem q L) :
    𝔡.divisors = ∅ ↔ 𝔡.sections = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro s hs
    by_contra hs0
    obtain ⟨D, hD, -⟩ := 𝔡.exists_mem_divisors hs hs0
    rw [h] at hD
    exact hD
  · intro h
    rw [Set.eq_empty_iff_forall_notMem]
    rintro D ⟨s, hs, hs0, -⟩
    rw [h, Submodule.mem_bot] at hs
    exact hs0 hs

/-- A linear system has dimension `-1` exactly when its subspace of sections is zero. -/
theorem dim_eq_neg_one_iff (𝔡 : LinearSystem q L) : 𝔡.dim = -1 ↔ 𝔡.sections = ⊥ := by
  rw [dim, ← Submodule.finrank_eq_zero (R := k)]
  omega

end LinearSystem

end Hartshorne
