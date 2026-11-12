/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.MorphismFromGeneratedLineBundle
import Hartshorne.Intersection.SectionZeroScheme
import Hartshorne.Scheme.ReesAlgebraBlowup

/-!
# Zero schemes, base loci and the linear system spanned by finitely many sections

Hartshorne, *Algebraic Geometry*, II.7, pp. 157–158: the linear system of an invertible sheaf
`L` on a scheme `X` over a field `k` spanned by finitely many global sections, its base points,
and Lemma 7.8 (off the base points the chosen sections generate `L`). `V` is given by a spanning
family `s₀, …, sₙ`: `V = linearSystem q s` is the set of combinations
`∑ aᵢ sᵢ = linearSystemSection q s a`, `a ∈ kⁿ⁺¹`, where `q : X ⟶ Spec k` is the structure
morphism.

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
  `range_baseLocus_subschemeι`). On it the evaluation map is surjective
  (`span_germ_linearSystem_eq_top`, `isGeneratedBySections_linearSystemSections`).

## Proof

Everything is computed on affine opens `U` trivializing `L` by a section `e`: writing `s = g e`,
the image of `s^∨` on `U` is `(g)`, since `L^∨` is trivialized by the dual section `e^∨`. This
identifies the support of `Z(s)` with the vanishing set of `s`, and, together with the formula
`Γ(U', f⁻¹I · 𝒪) = f^♯(Γ(U, I)) · Γ(U', 𝒪)` for the inverse image ideal, gives
`Z(f^* t) = f⁻¹ Z(t)`.
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

end LinearSystem

end Hartshorne
