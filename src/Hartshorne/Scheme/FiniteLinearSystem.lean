/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectionFromPoint
import Hartshorne.Intersection.SectionZeroScheme
import Hartshorne.Scheme.EffectiveCartierDivisor
import Hartshorne.Scheme.ReesAlgebraBlowup

/-!
# Finite-dimensional linear systems on an arbitrary scheme over a field

The setting of Hartshorne, *Algebraic Geometry*, III, Remark 10.9.2 (p. 275): a
finite-dimensional linear system `V ⊆ Γ(X, L)` of an invertible sheaf `L` on a scheme `X` over a
field `k`, with `X` not assumed projective. `V` is given by a spanning family `s₀, …, sₙ`
(a basis, when `ℙ(V)` is identified with `ℙⁿ_k`): `V = linearSystem q s` is the set of
combinations `∑ aᵢ sᵢ = linearSystemSection q s a`, `a ∈ kⁿ⁺¹`, where `q : X ⟶ Spec k` is the
structure morphism.

## Main definitions and results

* `invertibleZeroIdeal hL s`: the ideal sheaf of the zero scheme `Z(s)` of a section `s` of an
  invertible sheaf (the image of `s^∨ : L^∨ → 𝒪_X`, Appendix A, C6). On an affine open where `L`
  is trivialized by `e` and `s = g e`, it is `(g)` (`invertibleZeroIdeal_ideal_eq_span`); its
  support is the vanishing set of `s` (`mem_support_invertibleZeroIdeal_iff`).
* `invertibleZeroIdeal_pullbackGlobalSection`: `Z(f^* t) = f⁻¹ Z(t)` as closed subschemes, and
  `invertibleZeroIdeal_map_iso`: zero schemes are invariant under isomorphisms of invertible
  sheaves.
* `baseLocusIdeal hL S`, `baseLocus hL S`: the scheme-theoretic base locus `B` of a set `S` of
  sections, the closed subscheme with ideal `∑_{t ∈ S} I_{Z(t)}`; a point lies in it exactly when
  every member of `S` vanishes there (`mem_support_baseLocusIdeal_iff`).
* `linearSystemDomain hL s`: the open `X - B = ⋃ X_{sᵢ}` (`mem_linearSystemDomain_iff`,
  `range_baseLocus_subschemeι`). On it the evaluation map is surjective (`span_germ_linearSystem_eq_top`,
  `isGeneratedBySections_linearSystemSections`).
* `linearSystemMorphism q hL s : X - B ⟶ ℙⁿ_k`: the morphism defined (Hartshorne II,
  Theorem 7.1) by the `sᵢ|_{X - B}` (`existsUnique_linearSystemMorphism`,
  `linearSystemMorphism_spec`).
* `comap_invertibleZeroIdeal_linearSystemSection`: on `X - B`, the zero scheme of `∑ aᵢ sᵢ` is
  the pullback of the hyperplane `∑ aᵢ xᵢ = 0`.
* `isLocallyPrincipalNonZeroDivisor_invertibleZeroIdeal`,
  `exists_isEffective_idealSheafData_eq_invertibleZeroIdeal`: on an integral scheme the zero
  scheme of a nonzero section is an effective Cartier divisor. Nonsingularity is not needed, and
  on an integral scheme a section vanishing identically on a component is zero.

## Proof

Everything is computed on affine opens `U` trivializing `L` by a section `e`: writing `s = g e`,
the image of `s^∨` on `U` is `(g)`, since `L^∨` is trivialized by the dual section `e^∨`. This
identifies the support of `Z(s)` with the vanishing set of `s`, and, together with the formula
`Γ(U', f⁻¹I · 𝒪) = f^♯(Γ(U, I)) · Γ(U', 𝒪)` for the inverse image ideal, gives
`Z(f^* t) = f⁻¹ Z(t)`. The hyperplane clause follows: the isomorphism `φ^* 𝒪(1) ≅ L|_{X - B}` of
Theorem 7.1 carries `φ^*(∑ aᵢ xᵢ)` to `(∑ aᵢ sᵢ)|_{X - B}`. On an integral scheme `Γ(U, 𝒪_X)` is a
domain for nonempty `U`, and `g ≠ 0` because otherwise the open nonvanishing locus of `s` would
miss the nonempty open `U`, hence be empty, forcing `s = 0`.
-/
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

variable {X : Scheme.{u}} {L : X.Modules}

namespace Ringed

variable {T : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}

/-- A local section of the dual evaluates linearly. -/
private theorem dualEval_smul' {A : SheafOfModules.{u} (ringCatSheafOf R)} {U : Opens T}
    (ψ : (moduleSheafDual A).val.presheaf.obj (op U)) (r : R.obj.obj (op U))
    (x : A.val.presheaf.obj (op U)) :
    dualEval ψ (le_refl U) (r • x) = r * dualEval ψ (le_refl U) x :=
  (dualEval ψ (le_refl U)).map_smul r x

/-- The dual of a one-element frame `e` sends `e` to `1`. -/
private theorem dualEval_dualLocalFrame_self {A : SheafOfModules.{u} (ringCatSheafOf R)}
    {U : Opens T} {e : A.val.presheaf.obj (op U)}
    (hA : IsLocalFrame A U (fun _ : ULift.{u} (Fin 1) => e)) :
    dualEval (hA.dualLocalFrame default) (le_refl U) e = 1 := by
  have hE : A.val.presheaf.map (homOfLE (le_refl U)).op e = e := by
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]; rfl
  have := congrFun (hA.localFrameEval_dualLocalFrame (le_refl U) default) default
  rw [localFrameEval_apply, moduleSheafHomEval_restrict, Pi.single_eq_same, hE] at this
  exact this

end Ringed

section ZeroIdeal

variable (hL : L.IsInvertible)

/-- **The ideal of the zero scheme `Z(s)` of a section `s` of an invertible sheaf `L`**: the
image of the dual map `s^∨ : L^∨ ⟶ 𝒪_X` (Hartshorne, Appendix A, C6, for `E = L`). -/
def invertibleZeroIdeal (s : Γ(L, ⊤)) : X.IdealSheafData :=
  sectionZeroIdeal ((Scheme.Modules.isInvertible_iff_ringed L).mp hL).isFiniteLocallyFree s

/-- **Local equation of the zero scheme.** On an affine open `U` on which `e` trivializes `L`,
if `s|_U = g e` then the ideal of `Z(s)` over `U` is `(g)`. -/
theorem invertibleZeroIdeal_ideal_eq_span {U : X.affineOpens} {e : Γ(L, U)}
    (he : IsTrivializingSection L U e) {s : Γ(L, ⊤)} {g : Γ(X, U)}
    (hg : L.presheaf.map (homOfLE le_top).op s = g • e) :
    (invertibleZeroIdeal hL s).ideal U = Ideal.span {g} := by
  have hF := isLocalFrame_of_isTrivializingSection he
  refine le_antisymm ?_ ?_
  · intro t ht
    obtain ⟨ψ, rfl⟩ := (mem_sectionZeroIdeal_iff _ s U t).mp ht
    refine Ideal.mem_span_singleton'.mpr ⟨Ringed.dualEval ψ le_rfl e, ?_⟩
    rw [hg]
    exact (mul_comm _ _).trans (Ringed.dualEval_smul' (R := X.sheaf) ψ g e).symm
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine (mem_sectionZeroIdeal_iff _ s U g).mpr ⟨hF.dualLocalFrame default, ?_⟩
    rw [hg]
    exact (Ringed.dualEval_smul' (R := X.sheaf) _ g e).trans
      ((congrArg (g * ·) (Ringed.dualEval_dualLocalFrame_self (R := X.sheaf) hF)).trans
        (mul_one g))

/-- The underlying set of `Z(s)` is the set of points where `s` vanishes. -/
theorem mem_support_invertibleZeroIdeal_iff (s : Γ(L, ⊤)) (x : X) :
    x ∈ (invertibleZeroIdeal hL s).support ↔ x ∉ nonvanishingLocus L s := by
  obtain ⟨U, e, hxU, hU, he⟩ := exists_isAffineOpen_isTrivializingSection hL x
  obtain ⟨g, hg⟩ := he.exists_eq_smul s
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU,
    invertibleZeroIdeal_ideal_eq_span hL (U := ⟨U, hU⟩) he hg,
    he.mem_nonvanishingLocus_iff hg hxU, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h hx
    exact h g (Ideal.mem_span_singleton_self g) hx
  · intro h f hf hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [X.basicOpen_mul] at hx
    exact h hx.2

end ZeroIdeal

section Functoriality

/-- Transport of a trivializing section along an isomorphism of modules. -/
private theorem isTrivializingSection_map_iso {M N : X.Modules} (α : M ≅ N) {U : X.Opens}
    {e : Γ(M, U)} (he : IsTrivializingSection M U e) :
    IsTrivializingSection N U (α.hom.app U e) := by
  intro V h
  have key : (fun a : Γ(X, V) => a • N.presheaf.map (homOfLE h).op (α.hom.app U e)) =
      (α.hom.app V) ∘ (fun a : Γ(X, V) => a • M.presheaf.map (homOfLE h).op e) := by
    funext a
    simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul, hom_app_map]
  rw [key]
  refine Function.Bijective.comp ?_ (he V h)
  refine Function.bijective_iff_has_inverse.mpr ⟨α.inv.app V, fun m => ?_, fun m => ?_⟩
  · change (α.hom ≫ α.inv).app V m = m
    rw [α.hom_inv_id]; rfl
  · change (α.inv ≫ α.hom).app V m = m
    rw [α.inv_hom_id]; rfl

/-- **The zero scheme is invariant under isomorphisms of invertible sheaves.** -/
theorem invertibleZeroIdeal_map_iso {M N : X.Modules} (hM : M.IsInvertible)
    (hN : N.IsInvertible) (α : M ≅ N) (t : Γ(M, ⊤)) :
    invertibleZeroIdeal hN (α.hom.app ⊤ t) = invertibleZeroIdeal hM t := by
  choose U e hxU hU he using exists_isAffineOpen_isTrivializingSection hM
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun x => ⟨U x, hU x⟩)
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x => ?_
  obtain ⟨g, hg⟩ := (he x).exists_eq_smul t
  have hg' : N.presheaf.map (homOfLE le_top).op (α.hom.app ⊤ t) = g • α.hom.app (U x) (e x) := by
    rw [← hom_app_map, hg, Scheme.Modules.Hom.app_smul]
  rw [invertibleZeroIdeal_ideal_eq_span hM (U := ⟨U x, hU x⟩) (he x) hg,
    invertibleZeroIdeal_ideal_eq_span hN (U := ⟨U x, hU x⟩)
      (isTrivializingSection_map_iso α (he x)) hg']

/-- **The zero scheme of a pulled-back section is the pullback of the zero scheme**:
`Z(f^* t) = f⁻¹ Z(t)` as closed subschemes. -/
theorem invertibleZeroIdeal_pullbackGlobalSection (hL : L.IsInvertible) {X' : Scheme.{u}}
    (f : X' ⟶ X) (t : Γ(L, ⊤)) :
    invertibleZeroIdeal (hL.pullback f) (pullbackGlobalSection f t) =
      (invertibleZeroIdeal hL t).comap f := by
  have hx : ∀ x : X', ∃ (W : X.affineOpens) (e : Γ(L, W)) (U : X'.affineOpens)
      (h : (U : X'.Opens) ≤ f ⁻¹ᵁ W), x ∈ (U : X'.Opens) ∧ IsTrivializingSection L W e := by
    intro x
    obtain ⟨W, e, hxW, hW, he⟩ := exists_isAffineOpen_isTrivializingSection hL (f x)
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X'.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ W from hxW) (f ⁻¹ᵁ W).isOpen
    exact ⟨⟨W, hW⟩, e, ⟨V, hV⟩, hVW, hxV, he⟩
  choose W e U h hxU he using hx
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x => ?_
  obtain ⟨g, hg⟩ := (he x).exists_eq_smul t
  have hpe := ((he x).pullback f).restrict (h x)
  have hg' : ((Scheme.Modules.pullback f).obj L).presheaf.map
      (homOfLE (le_top : (U x : X'.Opens) ≤ ⊤)).op (pullbackGlobalSection f t) =
      f.appLE (W x) (U x) (h x) g • ((Scheme.Modules.pullback f).obj L).presheaf.map
        (homOfLE (h x)).op (pullbackSection f (e x)) := by
    rw [← Scheme.Modules.map_map_homOfLE _ (le_top : f ⁻¹ᵁ (W x : X.Opens) ≤ ⊤) (h x),
      pullbackGlobalSection_restrict, hg, pullbackSection_smul, Scheme.Modules.map_smul]
    rfl
  rw [invertibleZeroIdeal_ideal_eq_span (hL.pullback f) hpe hg',
    show (invertibleZeroIdeal hL t).comap f = inverseImageIdeal f (invertibleZeroIdeal hL t)
      from rfl, inverseImageIdeal_ideal f _ (W x) (U x) (h x),
    invertibleZeroIdeal_ideal_eq_span hL (he x) hg, Ideal.map_span, Set.image_singleton]

end Functoriality

section BaseLocus

variable (hL : L.IsInvertible)

/-- **The scheme-theoretic base locus** of a set `S` of global sections of an invertible sheaf:
the ideal sheaf `∑_{t ∈ S} I_{Z(t)}`, the sum of the ideals of the zero schemes of the members
of `S`. -/
def baseLocusIdeal (S : Set Γ(L, ⊤)) : X.IdealSheafData :=
  ⨆ t ∈ S, invertibleZeroIdeal hL t

/-- The base locus is the closed subscheme cut out by `baseLocusIdeal`. -/
abbrev baseLocus (S : Set Γ(L, ⊤)) : Scheme.{u} := (baseLocusIdeal hL S).subscheme

/-- A point lies in the base locus exactly when every section of `S` vanishes there. -/
theorem mem_support_baseLocusIdeal_iff (S : Set Γ(L, ⊤)) (x : X) :
    x ∈ (baseLocusIdeal hL S).support ↔ ∀ t ∈ S, x ∉ nonvanishingLocus L t := by
  simp_rw [← mem_support_invertibleZeroIdeal_iff hL]
  constructor
  · intro hx t ht
    exact Scheme.IdealSheafData.support_antitone
      (le_iSup₂ (f := fun t (_ : t ∈ S) => invertibleZeroIdeal hL t) t ht) hx
  · intro hx
    let Z : Closeds X := ⨅ t ∈ S, (invertibleZeroIdeal hL t).support
    have hZ : Z ≤ (baseLocusIdeal hL S).support := by
      rw [Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
      refine iSup₂_le fun t ht => ?_
      rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
      exact iInf₂_le t ht
    apply hZ
    show x ∈ (Z : Set X)
    simp only [Z, TopologicalSpace.Closeds.coe_iInf, Set.mem_iInter]
    exact hx

end BaseLocus

section LinearSystem

variable {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k)) {n : ℕ}

/-- The section `∑ aᵢ sᵢ` of `L`, for `a ∈ kⁿ⁺¹`. -/
def linearSystemSection (s : Fin (n + 1) → Γ(L, ⊤)) (a : Fin (n + 1) → k) : Γ(L, ⊤) :=
  ∑ i, kConst q (a i) • s i

/-- The linear system `V = k s₀ + ⋯ + k sₙ ⊆ Γ(X, L)` spanned by `s₀, …, sₙ`. -/
def linearSystem (s : Fin (n + 1) → Γ(L, ⊤)) : Set Γ(L, ⊤) :=
  Set.range (linearSystemSection q s)

/-- `∑ aᵢ sᵢ` for the standard basis vector `a = eᵢ` is `sᵢ`. -/
theorem linearSystemSection_single (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1)) :
    linearSystemSection q s (Pi.single i 1) = s i := by
  rw [linearSystemSection, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, map_one, one_smul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, map_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- Each `sᵢ` lies in the linear system it spans. -/
theorem mem_linearSystem (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1)) :
    s i ∈ linearSystem q s :=
  ⟨Pi.single i 1, linearSystemSection_single q s i⟩

/-- A combination `∑ aᵢ sᵢ` vanishes wherever all the `sᵢ` vanish. -/
theorem nonvanishingLocus_linearSystemSection_subset (s : Fin (n + 1) → Γ(L, ⊤))
    (a : Fin (n + 1) → k) :
    nonvanishingLocus L (linearSystemSection q s a) ⊆ ⋃ i, nonvanishingLocus L (s i) := by
  intro x hx
  by_contra hno
  simp only [Set.mem_iUnion, not_exists] at hno
  apply hx
  rw [linearSystemSection, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_contra h
  exact hno i (nonvanishingLocus_smul_subset L _ _ h)

variable (hL : L.IsInvertible)

/-- The complement `X - B` of the base locus: the union of the nonvanishing loci `X_{sᵢ}`. -/
def linearSystemDomain (s : Fin (n + 1) → Γ(L, ⊤)) : X.Opens :=
  ⨆ i, nonvanishingLocusOpens hL (s i)

/-- **The complement of the base locus.** A point lies in `linearSystemDomain` exactly when it is
not in the base locus of the linear system `V` spanned by the `sᵢ`. -/
theorem mem_linearSystemDomain_iff (s : Fin (n + 1) → Γ(L, ⊤)) (x : X) :
    x ∈ linearSystemDomain hL s ↔ x ∉ (baseLocusIdeal hL (linearSystem q s)).support := by
  rw [mem_support_baseLocusIdeal_iff, linearSystemDomain, TopologicalSpace.Opens.mem_iSup]
  push Not
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨s i, mem_linearSystem q s i, hi⟩
  · rintro ⟨_, ⟨a, rfl⟩, ha⟩
    exact Set.mem_iUnion.mp (nonvanishingLocus_linearSystemSection_subset q s a ha)

/-- The underlying set of the base locus is the complement of `linearSystemDomain`. -/
theorem range_baseLocus_subschemeι (s : Fin (n + 1) → Γ(L, ⊤)) :
    Set.range (baseLocusIdeal hL (linearSystem q s)).subschemeι =
      (linearSystemDomain hL s : Set X)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι]
  ext x
  change x ∈ (baseLocusIdeal hL (linearSystem q s)).support ↔ x ∉ linearSystemDomain hL s
  rw [mem_linearSystemDomain_iff q hL, not_not]

/-- **The evaluation map is surjective off the base locus**: at every point `x` of
`linearSystemDomain`, the germs of `s₀, …, sₙ` generate the stalk `L_x`. -/
theorem span_germ_linearSystem_eq_top (s : Fin (n + 1) → Γ(L, ⊤)) {x : X}
    (hx : x ∈ linearSystemDomain hL s) :
    Submodule.span (X.presheaf.stalk x)
      (Set.range fun i => L.presheaf.germ ⊤ x trivial (s i)) = ⊤ := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have he := isTrivializingSection_nonvanishingLocusOpens hL (s i)
  refine top_unique fun z _ => ?_
  obtain ⟨b, rfl⟩ := he.exists_smul_germ_eq hi z
  rw [TopCat.Presheaf.germ_res_apply]
  exact Submodule.smul_mem _ b (Submodule.subset_span ⟨i, rfl⟩)

/-- `L|_U` on `U = linearSystemDomain`. -/
abbrev linearSystemTwist (s : Fin (n + 1) → Γ(L, ⊤)) :
    (linearSystemDomain hL s).toScheme.Modules :=
  (Scheme.Modules.pullback (linearSystemDomain hL s).ι).obj L

/-- The restrictions `sᵢ|_U`. -/
abbrev linearSystemSections (s : Fin (n + 1) → Γ(L, ⊤)) (i : Fin (n + 1)) :
    Γ(linearSystemTwist hL s, ⊤) :=
  pullbackGlobalSection (linearSystemDomain hL s).ι (s i)

/-- The `sᵢ|_U` generate `L|_U`: the evaluation map `𝒪_Uⁿ⁺¹ → L|_U` is surjective. -/
theorem isGeneratedBySections_linearSystemSections (s : Fin (n + 1) → Γ(L, ⊤)) :
    (linearSystemTwist hL s).IsGeneratedBySections
      (fun i : ULift.{u} (Fin (n + 1)) => linearSystemSections hL s i.down) := by
  refine isGeneratedBySections_of_forall_isTrivializingSection _ fun y => ?_
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp y.2
  refine ⟨⟨i⟩, (linearSystemDomain hL s).ι ⁻¹ᵁ nonvanishingLocusOpens hL (s i), hi, ?_⟩
  rw [pullbackGlobalSection_restrict]
  exact IsTrivializingSection.pullback _ (isTrivializingSection_nonvanishingLocusOpens _ _)

/-- Theorem 7.1(b) for the sections `sᵢ|_U` of `L|_U`. -/
theorem existsUnique_linearSystemMorphism (s : Fin (n + 1) → Γ(L, ⊤)) :
    ∃! φ : (linearSystemDomain hL s).toScheme ⟶
        projectiveSpaceOverScheme n (Spec (CommRingCat.of k)),
      φ ≫ projectiveSpaceOverSchemeProjection n _ = (linearSystemDomain hL s).ι ≫ q ∧
      ∃ e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅
          linearSystemTwist hL s,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) =
          linearSystemSections hL s i :=
  existsUnique_morphism_of_isGeneratedBySections _ (hL.pullback _)
    (linearSystemSections hL s) (isGeneratedBySections_linearSystemSections hL s)

/-- **The morphism `X - B ⟶ ℙⁿ_k` defined by the linear system** with spanning family `s₀, …, sₙ`
(Hartshorne II, Theorem 7.1): the unique `k`-morphism pulling `𝒪(1)` back to `L|_U` with
`xᵢ ↦ sᵢ|_U`. -/
def linearSystemMorphism (s : Fin (n + 1) → Γ(L, ⊤)) :
    (linearSystemDomain hL s).toScheme ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)) :=
  (existsUnique_linearSystemMorphism q hL s).exists.choose

/-- The defining property of `linearSystemMorphism`. -/
theorem linearSystemMorphism_spec (s : Fin (n + 1) → Γ(L, ⊤)) :
    linearSystemMorphism q hL s ≫ projectiveSpaceOverSchemeProjection n _ =
        (linearSystemDomain hL s).ι ≫ q ∧
      ∃ e : (Scheme.Modules.pullback (linearSystemMorphism q hL s)).obj
          (projectiveSpaceTwistingSheaf n _ 1) ≅ linearSystemTwist hL s,
        ∀ i, e.hom.app ⊤ (pullbackGlobalSection (linearSystemMorphism q hL s)
          (projectiveSpaceCoordinate n _ i)) = linearSystemSections hL s i :=
  (existsUnique_linearSystemMorphism q hL s).exists.choose_spec

/-- **The zero scheme of `∑ aᵢ sᵢ` is the pullback of the hyperplane `∑ aᵢ xᵢ = 0`.** On
`U = X - B`, the zero scheme of the section `∑ aᵢ sᵢ` of `L` (restricted to `U`) equals, as a
closed subscheme of `U`, the preimage under `φ : U ⟶ ℙⁿ_k` of the zero scheme of the linear form
`∑ aᵢ xᵢ ∈ Γ(ℙⁿ_k, 𝒪(1))`. -/
theorem comap_invertibleZeroIdeal_linearSystemSection (s : Fin (n + 1) → Γ(L, ⊤))
    (a : Fin (n + 1) → k) :
    (invertibleZeroIdeal hL (linearSystemSection q s a)).comap (linearSystemDomain hL s).ι =
      (invertibleZeroIdeal (isInvertible_projectiveSpaceTwistingSheaf n _ 1)
        (linearSection k n a)).comap (linearSystemMorphism q hL s) := by
  obtain ⟨hφ, e, he⟩ := linearSystemMorphism_spec q hL s
  rw [← invertibleZeroIdeal_pullbackGlobalSection, ← invertibleZeroIdeal_pullbackGlobalSection,
    ← invertibleZeroIdeal_map_iso _ (hL.pullback _) e, iso_app_linearSection hφ e he,
    linearSystemSection, pullbackGlobalSection_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pullbackGlobalSection_smul, appTop_kConst]

end LinearSystem

section Cartier

variable (hL : L.IsInvertible)

/-- **On an integral scheme a nonzero section has an effective Cartier zero scheme**: its zero
ideal is locally generated by a single non-zero-divisor. -/
theorem isLocallyPrincipalNonZeroDivisor_invertibleZeroIdeal [IsIntegral X] {s : Γ(L, ⊤)}
    (hs : s ≠ 0) : (invertibleZeroIdeal hL s).IsLocallyPrincipalNonZeroDivisor := by
  intro x
  obtain ⟨U, e, hxU, hU, he⟩ := exists_isAffineOpen_isTrivializingSection hL x
  obtain ⟨g, hg⟩ := he.exists_eq_smul s
  refine ⟨⟨U, hU⟩, hxU, g, ?_, invertibleZeroIdeal_ideal_eq_span hL (U := ⟨U, hU⟩) he hg⟩
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  apply hs
  refine eq_zero_of_forall_notMem_nonvanishingLocus hL fun y hy => ?_
  have h1 := he.nonvanishingLocus_inter_eq hg
  rw [X.basicOpen_zero] at h1
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (isOpen_nonvanishingLocus hL s) U.isOpen
    ⟨y, hy⟩ ⟨x, hxU⟩
  rw [h1] at hz
  exact hz

/-- **The zero scheme of a nonzero section on an integral scheme is an effective Cartier
divisor.** -/
theorem exists_isEffective_idealSheafData_eq_invertibleZeroIdeal [IsIntegral X] {s : Γ(L, ⊤)}
    (hs : s ≠ 0) :
    ∃ (D : X.CartierDivisor) (hD : D.IsEffective),
      Scheme.CartierDivisor.idealSheafData hD = invertibleZeroIdeal hL s :=
  Scheme.CartierDivisor.exists_idealSheafData_eq
    (isLocallyPrincipalNonZeroDivisor_invertibleZeroIdeal hL hs)

end Cartier

end Hartshorne
