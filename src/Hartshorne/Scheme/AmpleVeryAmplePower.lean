/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ProjectiveClosedImmersionChartCriterion
import Hartshorne.Scheme.ProjectionFromPoint
import Hartshorne.Scheme.ClosedImmersionIdealSheaf
import Hartshorne.Scheme.RelativeVeryAmple

/-!
# An ample sheaf has a very ample power

Hartshorne, *Algebraic Geometry*, II, Theorem 7.6, the implication "ample ⇒ some power very
ample" (pp. 154–155).

Let `X` be of finite type over a Noetherian ring `A` and `L` an ample invertible sheaf on `X`.
Then some positive tensor power `L^{⊗ k}` is very ample relative to `Spec A`
(`AlgebraicGeometry.Scheme.Modules.IsAmple.exists_isVeryAmpleRelative_moduleSheafTensorPower`).

The proof follows Hartshorne's.

* `X` is covered by finitely many affine nonvanishing loci `X_{sᵢ}` of global sections `sᵢ` of
  one power `L' = L^{⊗ n}` (`IsAmple.exists_isAffineOpen_nonvanishingLocus_of_finiteType`).
* Each `Bᵢ = Γ(X_{sᵢ}, 𝒪_X)` is a finitely generated `A`-algebra, with generators `b`.
* By Lemma II.5.14(b), for one `m > 0` each `sᵢ^m b` extends to a global section `c_{i b}` of
  `𝒪_X ⊗ L'^{⊗ m} ≅ L^{⊗ nm}` (`exists_forall_sectionPowSMul_extension`).
* The sections `sᵢ^m` and `c_{i b}` (together with one zero section, so that the index set is never
  empty) generate `𝒪_X ⊗ L'^{⊗ m}` (since `X_{sᵢ^m} = X_{sᵢ}` cover `X`), so they define a
  morphism `φ : X ⟶ ℙᴺ_A` with `φ^* 𝒪(1) ≅ 𝒪_X ⊗ L'^{⊗ m}` (Theorem 7.1).
* Over the standard open `D₊(xᵢ)` of the coordinate `sᵢ^m`, the preimage is the affine `X_{sᵢ}`
  and the ring map onto `Bᵢ` is surjective, because it hits `A` and each `b = c_{i b}/sᵢ^m`; so
  `φ` restricted over `D₊(xᵢ)` is a closed immersion (the chart criterion behind
  Proposition 7.2). Hence `φ` is a closed immersion into the open union `U` of these `D₊(xᵢ)`,
  so an immersion.
* `φ` is quasi-compact, so it factors as an open immersion into its scheme-theoretic image
  followed by a closed immersion, the shape of immersion in `Hartshorne.IsVeryAmpleRelative`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace AmpleVeryAmplePower

variable {X : Scheme.{u}}

/-- The structure sheaf as an `𝒪_X`-module. -/
local notation "𝒪ₘ" => structureModuleOf X

/-- The section `1` of `𝒪_X` over `U`. -/
private abbrev oneSec (U : X.Opens) : Γ(structureModuleOf X, U) := structureModuleSection X 1

private theorem sectionPowSMul_smul_right {F L : X.Modules} {m : ℕ} {U : X.Opens}
    (f : Γ(L, U)) (a : Γ(X, U)) (s : Γ(F, U)) :
    sectionPowSMul F L m f (a • s) = a • sectionPowSMul F L m f s := by
  unfold sectionPowSMul
  erw [LinearMap.map_smul₂]
  rfl

private theorem restrict_sectionPowSMul_one {L : X.Modules} {m : ℕ} {U V : X.Opens}
    (h : V ≤ U) (f : Γ(L, U)) :
    (tensorPowerTwist 𝒪ₘ L m).presheaf.map (homOfLE h).op (sectionPowSMul 𝒪ₘ L m f (oneSec U)) =
      sectionPowSMul 𝒪ₘ L m (L.presheaf.map (homOfLE h).op f) (oneSec V) := by
  rw [sectionPowSMul_map]
  congr 1
  exact map_one (X.presheaf.map (homOfLE h).op).hom

/-- If `e` trivializes `L` on `U`, then `1 ⊗ e^{⊗ m}` trivializes `𝒪_X ⊗ L^{⊗ m}` on `U`. -/
private theorem isTrivializingSection_sectionPowSMul_one {L : X.Modules} {U : X.Opens}
    {e : Γ(L, U)} (he : IsTrivializingSection L U e) (m : ℕ) :
    IsTrivializingSection (tensorPowerTwist 𝒪ₘ L m) U (sectionPowSMul 𝒪ₘ L m e (oneSec U)) :=
  (he.moduleSheafTensorPower m).map_iso
    (Ringed.moduleSheafUnitTensor (R := X.sheaf) (moduleSheafTensorPower m L)).symm

/-- For `m > 0`, the nonvanishing locus of `f^m = 1 ⊗ f^{⊗ m}` is that of `f`. -/
private theorem nonvanishingLocus_sectionPowSMul_one {L : X.Modules} (hL : L.IsInvertible)
    {m : ℕ} (hm : 0 < m) (f : Γ(L, ⊤)) :
    nonvanishingLocus (tensorPowerTwist 𝒪ₘ L m) (sectionPowSMul 𝒪ₘ L m f (oneSec ⊤)) =
      nonvanishingLocus L f := by
  ext x
  obtain ⟨U, e, hxU, he⟩ := exists_isTrivializingSection hL x
  obtain ⟨g, hg⟩ := he.exists_eq_smul f
  have hg' : (tensorPowerTwist 𝒪ₘ L m).presheaf.map (homOfLE le_top).op
      (sectionPowSMul 𝒪ₘ L m f (oneSec ⊤)) = g ^ m • sectionPowSMul 𝒪ₘ L m e (oneSec U) := by
    rw [restrict_sectionPowSMul_one, hg, sectionPowSMul_smul, ← sectionPowSMul_smul_right]
  rw [(isTrivializingSection_sectionPowSMul_one he m).mem_nonvanishingLocus_iff hg' hxU,
    he.mem_nonvanishingLocus_iff hg hxU, Scheme.basicOpen_pow _ _ hm]

/-- **One chart of Proposition 7.2.** For the morphism `φ : X ⟶ ℙⁿ_Y` defined by sections `tⱼ`
of `M`, if `X_{t_k}` is affine and `Γ(X_{t_k}, 𝒪_X)` is generated as a ring by the image of
`Γ(Y, 𝒪_Y)` and by functions `b` with `b t_k = t_l` on `X_{t_k}`, then `φ` restricted over the
standard open `D₊(x_k)` is a closed immersion. -/
private theorem isClosedImmersion_morphismRestrict_chart {n : ℕ} {Y : Scheme.{u}} [IsAffine Y]
    {M : X.Modules} (hM : M.IsInvertible) (t : Fin (n + 1) → Γ(M, ⊤)) (p : X ⟶ Y)
    (φ : X ⟶ projectiveSpaceOverScheme n Y)
    (hφ : φ ≫ projectiveSpaceOverSchemeProjection n Y = p)
    (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n Y 1) ≅ M)
    (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n Y i)) = t i)
    (k : Fin (n + 1)) {V : X.Opens} (hV : nonvanishingLocusOpens hM (t k) = V)
    (hVaff : IsAffineOpen V)
    (hgen : ∀ z : Γ(X, V), z ∈ Subring.closure (Set.range (p.appLE ⊤ V le_top) ∪
      {b | ∃ l, b • M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (t k) =
        M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (t l)})) :
    IsClosedImmersion (φ ∣_ projectiveSpaceChart n Y k) := by
  subst hV hφ
  rw [isClosedImmersion_morphismRestrict_iff φ (isAffineOpen_projectiveSpaceChart n Y k)
    (preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hM t φ e he k)]
  refine ⟨hVaff, fun z => ?_⟩
  refine (Subring.closure_le.mpr ?_ : _ ≤ (φ.appLE _ _ _).hom.range) (hgen z)
  rintro b (⟨a, rfl⟩ | ⟨l, hb⟩)
  · refine ⟨(projectiveSpaceOverSchemeProjection n Y).appLE ⊤ (projectiveSpaceChart n Y k) le_top a,
      ?_⟩
    exact ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE φ
      (projectiveSpaceOverSchemeProjection n Y) ⊤ (projectiveSpaceChart n Y k) _ le_top _) a
  · refine ⟨projectiveSpaceChartRatio n Y k l, eq_of_smul_eq hM t k le_rfl ?_⟩
    rw [appLE_projectiveSpaceChartRatio_smul hM t φ e he k l]
    exact hb.symm

/-- A morphism that is a closed immersion over each member of a family of opens whose preimages
cover the source is an immersion: it is a closed immersion into the union of the opens. -/
private theorem isImmersion_of_isClosedImmersion_morphismRestrict {X Y : Scheme.{u}}
    (φ : X ⟶ Y) {ι : Type*} (W : ι → Y.Opens) (hpre : ⨆ i, φ ⁻¹ᵁ W i = ⊤)
    (h : ∀ i, IsClosedImmersion (φ ∣_ W i)) : IsImmersion φ := by
  set U := ⨆ i, W i with hU
  have hcov : ⨆ i, U.ι ⁻¹ᵁ W i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Opens.ι_preimage_self]
  have hcl : IsClosedImmersion (φ ∣_ U) := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hcov]
    intro i
    have hi : U.ι ''ᵁ U.ι ⁻¹ᵁ W i = W i := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (le_iSup W i)
    rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (morphismRestrictRestrict φ U _),
      MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (morphismRestrictEq φ hi)]
    exact h i
  have htop : φ ⁻¹ᵁ U = ⊤ := by rw [hU, Scheme.Hom.preimage_iSup, hpre]
  have : IsImmersion ((φ ⁻¹ᵁ U).ι ≫ φ) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have : IsIso (φ ⁻¹ᵁ U).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
    have hx : x ∈ φ ⁻¹ᵁ U := htop ▸ trivial
    exact ⟨⟨x, hx⟩, rfl⟩
  rw [show φ = inv (φ ⁻¹ᵁ U).ι ≫ (φ ⁻¹ᵁ U).ι ≫ φ by simp]
  infer_instance

end AmpleVeryAmplePower

end Hartshorne

namespace AlgebraicGeometry.Scheme.Modules

open Hartshorne Hartshorne.AmpleVeryAmplePower

variable {X : Scheme.{u}}

/-- **Hartshorne II, Theorem 7.6** (the implication "ample ⇒ some power very ample",
pp. 154–155). Let `X` be of finite type over a Noetherian ring `A` and `L` an ample invertible
sheaf on `X`. Then some positive tensor power `L^{⊗ k}` is very ample relative to `Spec A`. -/
theorem IsAmple.exists_isVeryAmpleRelative_moduleSheafTensorPower {A : CommRingCat.{u}}
    [IsNoetherianRing A] (f : X ⟶ Spec A) (hf : FiniteType f) {L : X.Modules}
    (hL : haveI := finiteType_isNoetherian f hf; L.IsAmple) :
    ∃ k > 0, IsVeryAmpleRelative f (moduleSheafTensorPower k L) := by
  classical
  have hXn := finiteType_isNoetherian f hf
  have : LocallyOfFiniteType f := hf.1
  have := ClosedImmersionIdeal.isQuasicoherent_unit X
  -- Finitely many affine `X_{sᵢ}`, `sᵢ ∈ Γ(X, L^{⊗ n})`, cover `X`.
  obtain ⟨-, n, hn, S, hSaff, hScov⟩ :=
    hL.exists_isAffineOpen_nonvanishingLocus_of_finiteType f hf
  let L' : X.Modules := moduleSheafTensorPower n L
  have hL' : L'.IsInvertible := isInvertible_moduleSheafTensorPower hL.1 n
  let s : Fin S.card → Γ(L', ⊤) := fun i => (S.equivFin.symm i).1
  let V : Fin S.card → X.Opens := fun i => nonvanishingLocusOpens hL' (s i)
  have hVaff : ∀ i, IsAffineOpen (V i) := fun i => hSaff _ (S.equivFin.symm i).2
  have hVcov : ∀ x : X, ∃ i, x ∈ V i := by
    intro x
    obtain ⟨s₀, hs₀, hx⟩ := hScov x
    refine ⟨S.equivFin ⟨s₀, hs₀⟩, ?_⟩
    change x ∈ nonvanishingLocus L' (S.equivFin.symm (S.equivFin ⟨s₀, hs₀⟩)).1
    rw [Equiv.symm_apply_apply]
    exact hx
  have hVsup : ⨆ i, V i = ⊤ :=
    top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.mpr (hVcov x)
  -- Each `Γ(X_{sᵢ}, 𝒪_X)` is a finitely generated `A`-algebra.
  have hft : ∀ i, (f.appLE ⊤ (V i) le_top).hom.FiniteType := fun i =>
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf.1 ⟨⊤, isAffineOpen_top _⟩ ⟨V i, hVaff i⟩
      le_top
  have hgen : ∀ i, ∃ G : Finset Γ(X, V i), ∀ z : Γ(X, V i),
      z ∈ Subring.closure (Set.range (f.appLE ⊤ (V i) le_top) ∪ (G : Set Γ(X, V i))) := by
    intro i
    let := (f.appLE ⊤ (V i) le_top).hom.toAlgebra
    obtain ⟨G, hG⟩ := (hft i).out
    refine ⟨G, fun z => ?_⟩
    have hz : z ∈ (Algebra.adjoin Γ(Spec A, ⊤) (G : Set Γ(X, V i))).toSubring := by
      rw [hG]
      trivial
    rw [Algebra.adjoin_eq_ring_closure] at hz
    exact hz
  choose G hG using hgen
  -- Lemma II.5.14(b): for one `m > 0`, each `sᵢ^m b` extends to a global section.
  have hqc : ∀ i j, IsCompact ((V i ⊓ V j : X.Opens) : Set X) := fun i j =>
    NoetherianSpace.isCompact _
  have hext : ∀ p : Σ i, G i, ∃ N : ℕ, ∀ m ≥ N,
      ∃ u : Γ(tensorPowerTwist (structureModuleOf X) L' m, ⊤),
        (tensorPowerTwist (structureModuleOf X) L' m).presheaf.map
            (homOfLE le_top : V p.1 ⟶ ⊤).op u =
          sectionPowSMul (structureModuleOf X) L' m (L'.presheaf.map (homOfLE le_top).op (s p.1))
            (structureModuleSection X p.2.1) := fun p =>
    exists_forall_sectionPowSMul_extension hL' (s p.1) (structureModuleOf X) V hVsup hVaff
      (fun i => L'.presheaf.map (homOfLE le_top).op (s i))
      (fun i => isTrivializingSection_nonvanishingLocusOpens hL' (s i)) hqc
      (structureModuleSection X p.2.1)
  choose N hN using hext
  let m := Finset.univ.sup N + 1
  have hm : 0 < m := Nat.succ_pos _
  choose u hu using fun p => hN p m ((Finset.le_sup (Finset.mem_univ p)).trans (Nat.le_succ _))
  -- The sheaf `M = 𝒪_X ⊗ L'^{⊗ m} ≅ L^{⊗ nm}`.
  let M : X.Modules := tensorPowerTwist (structureModuleOf X) L' m
  let eM : M ≅ moduleSheafTensorPower (n * m) L :=
    Ringed.moduleSheafUnitTensor (R := X.sheaf) _ ≪≫ Ringed.moduleSheafTensorPowerMulIso L n m
  have hLk : Scheme.Modules.IsInvertible (moduleSheafTensorPower (n * m) L) :=
    isInvertible_moduleSheafTensorPower hL.1 _
  have hM : M.IsInvertible := (isInvertible_iff_ringed _).mpr
    (Ringed.IsInvertible.of_iso ((isInvertible_iff_ringed _).mp hLk) eM.symm)
  -- The sections `sᵢ^m` and `c_{i b}`, plus a zero section so that there is at least one.
  let J := Option (Fin S.card ⊕ Σ i, G i)
  let T : J → Γ(M, ⊤) := fun j => Option.elim j 0
    (Sum.elim (fun i => sectionPowSMul (structureModuleOf X) L' m (s i) (oneSec ⊤)) u)
  let N' := Fintype.card (Fin S.card ⊕ Σ i, G i)
  let ε : J ≃ Fin (N' + 1) := Fintype.equivFinOfCardEq (by simp [J, N'])
  let t : Fin (N' + 1) → Γ(M, ⊤) := fun k => T (ε.symm k)
  have ht : ∀ j, t (ε j) = T j := fun j => by simp [t]
  have hlocus : ∀ i, nonvanishingLocusOpens hM (t (ε (some (Sum.inl i)))) = V i := fun i => by
    ext1
    change nonvanishingLocus M (t _) = nonvanishingLocus L' (s i)
    rw [ht]
    exact nonvanishingLocus_sectionPowSMul_one hL' hm (s i)
  have hres : ∀ i, M.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (t (ε (some (Sum.inl i)))) =
      sectionPowSMul (structureModuleOf X) L' m (L'.presheaf.map (homOfLE le_top).op (s i))
        (oneSec (V i)) := fun i => by
    rw [ht]
    exact restrict_sectionPowSMul_one le_top (s i)
  have htriv : ∀ i, IsTrivializingSection M (V i)
      (M.presheaf.map (homOfLE le_top).op (t (ε (some (Sum.inl i))))) := fun i => by
    rw [hres]
    exact isTrivializingSection_sectionPowSMul_one
      (isTrivializingSection_nonvanishingLocusOpens hL' (s i)) m
  -- Theorem 7.1: the sections define `φ : X ⟶ ℙᴺ_A` with `φ^* 𝒪(1) ≅ M`.
  have hgenM : M.IsGeneratedBySections (fun k : ULift.{u} (Fin (N' + 1)) => t k.down) :=
    isGeneratedBySections_of_forall_isTrivializingSection _ fun x => by
      obtain ⟨i, hi⟩ := hVcov x
      exact ⟨⟨ε (some (Sum.inl i))⟩, V i, hi, htriv i⟩
  obtain ⟨φ, ⟨hφ, e, he⟩, -⟩ := existsUnique_morphism_of_isGeneratedBySections f hM t hgenM
  -- Over `D₊(x)` for the coordinate `sᵢ^m`, `φ` is a closed immersion.
  have hcl : ∀ i, IsClosedImmersion
      (φ ∣_ projectiveSpaceChart N' (Spec A) (ε (some (Sum.inl i)))) := fun i =>
    isClosedImmersion_morphismRestrict_chart hM t f φ hφ e he _ (hlocus i) (hVaff i) fun z => by
      refine Subring.closure_mono (Set.union_subset_union_right _ ?_) (hG i z)
      intro b hb
      refine ⟨ε (some (Sum.inr ⟨i, ⟨b, hb⟩⟩)), ?_⟩
      have h1 := hu ⟨i, ⟨b, hb⟩⟩
      rw [hres i, ht]
      refine Eq.trans ?_ h1.symm
      rw [← sectionPowSMul_smul_right, ← structureModuleSection_eq_smul]
  -- So `φ` is an immersion, and quasi-compact; factor it through its scheme-theoretic image.
  have hpre : ⨆ i, φ ⁻¹ᵁ projectiveSpaceChart N' (Spec A) (ε (some (Sum.inl i))) = ⊤ := by
    simp_rw [preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hM t φ e he, hlocus]
    exact hVsup
  have : IsImmersion φ := isImmersion_of_isClosedImmersion_morphismRestrict φ _ hpre hcl
  refine ⟨n * m, Nat.mul_pos hn hm, hLk, N', φ.image, φ.toImage, φ.imageι, inferInstance,
    inferInstance, by rw [Scheme.Hom.toImage_imageι, hφ], ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackCongr (Scheme.Hom.toImage_imageι φ)).app _ ≪≫ e ≪≫ eM

end AlgebraicGeometry.Scheme.Modules
