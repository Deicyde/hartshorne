/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BlowupIsoOffCenter
import Hartshorne.Scheme.RelativeProjAmpleTwist
import Hartshorne.Scheme.ProjectiveMorphismCalculus
import Hartshorne.Scheme.VeryAmplePowerImpliesAmple

/-!
# Blowing up a variety

Hartshorne, *Algebraic Geometry*, II, Proposition 7.16 (p. 166).

Let `X` be a variety over a field `k` (an integral scheme, separated and of finite type over
`k`) and `I` a nonzero coherent sheaf of ideals on `X`, with blowing-up
`π : X̃ = Proj_X (⨁_d Iᵈ) ⟶ X`. Then `X̃` is again a variety, and `π` is birational, proper and
surjective. If `X` is quasi-projective (resp. projective) over `k`, then `π` is projective and `X̃`
is quasi-projective (resp. projective) over `k`.

## Proof

* `π` is proper (relative `Proj` is proper), so `X̃` is separated and of finite type over `k`.
* Let `Y` be the closed subscheme defined by `I`. Since `I ≠ 0` and `X` is reduced, `X \ Y` is a
  nonempty open subset of `X`, and `π` is an isomorphism over `X \ Y`; so `π` is birational.
* `X̃` is integral. Over an affine open `U ⊆ X`, the piece `π⁻¹(U) = Proj (⨁_d Γ(U, I)ᵈ tᵈ)` is
  the `Proj` of a subring of the polynomial ring `Γ(U, 𝒪_X)[t]` over a domain, hence is integral
  whenever it is nonempty (`irreducibleSpace_proj_of_isDomain`, `isDomain_stalk_proj_of_isDomain`).
  Therefore `X̃` is reduced, and every point of `X̃` lies in an irreducible open meeting
  `π⁻¹(X \ Y) ≅ X \ Y`, which is irreducible; so `π⁻¹(X \ Y)` is dense and `X̃` is irreducible.
* The image of `π` is closed (`π` is proper) and contains the dense open `X \ Y`, so `π` is
  surjective.
* A quasi-projective `X` carries an ample invertible sheaf (the restriction of `𝒪(1)`), so the
  relative `Proj` `π` is projective; composing, `X̃` is quasi-projective (resp. projective).

## Main results

* `Hartshorne.isIntegral_proj_of_isDomain`: `Proj A` is integral for a nonempty `Proj` of a
  graded domain `A`.
* `Hartshorne.Projective.comp_quasiProjective`: a projective morphism followed by a
  quasi-projective one is quasi-projective (when the composite is quasi-compact).
* `Hartshorne.QuasiProjective.exists_isAmple`: a scheme quasi-projective and of finite type over
  a Noetherian ring has an ample invertible sheaf.
* `Hartshorne.QuasicoherentIdealSubsheaf.isIntegral_blowup`: the blowing-up of an integral
  Noetherian scheme along a nonzero coherent ideal is integral.
* `Hartshorne.QuasicoherentIdealSubsheaf.blowup_variety`: **Hartshorne II, Proposition 7.16**.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace Hartshorne

/-! ### `Proj` of a graded domain -/

section ProjDomain

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsDomain A]

/-- For a graded domain `A` with `Proj A` nonempty, `Proj A` is irreducible: the zero ideal is
a relevant homogeneous prime, a generic point specializing to every point. -/
theorem irreducibleSpace_proj_of_isDomain [Nonempty (Proj 𝒜)] : IrreducibleSpace (Proj 𝒜) := by
  obtain ⟨y⟩ := ‹Nonempty (Proj 𝒜)›
  let g : Proj 𝒜 := ⟨⊥, Ideal.isPrime_bot, fun h => y.not_irrelevant_le (h.trans bot_le)⟩
  have hg : IsGenericPoint g Set.univ := isGenericPoint_iff_specializes.mpr fun x =>
    ⟨fun _ => trivial, fun _ => by
      rw [specializes_iff_mem_closure]
      exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 g x).1
        (show g.asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)⟩
  exact (irreducibleSpace_def _).mpr hg.isIrreducible

/-- For a graded domain `A`, the stalks of `Proj A` are domains: they are homogeneous
localizations, subrings of localizations of `A`. -/
theorem isDomain_stalk_proj_of_isDomain (x : Proj 𝒜) :
    IsDomain ((Proj 𝒜).presheaf.stalk x) := by
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have : IsDomain (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    Function.Injective.isDomain
      (algebraMap (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
      (HomogeneousLocalization.val_injective _)
  have : IsDomain
      (CommRingCat.of (HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)) := this
  exact Function.Injective.isDomain (Proj.stalkIso 𝒜 x).hom.hom
    (ConcreteCategory.injective_of_mono_of_preservesPullback (Proj.stalkIso 𝒜 x).hom)

/-- **`Proj` of a graded domain is integral** when it is nonempty. -/
theorem isIntegral_proj_of_isDomain [Nonempty (Proj 𝒜)] : IsIntegral (Proj 𝒜) := by
  have := irreducibleSpace_proj_of_isDomain 𝒜
  have : ∀ x : Proj 𝒜, _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) := fun x =>
    have := isDomain_stalk_proj_of_isDomain 𝒜 x
    inferInstance
  have : IsReduced (Proj 𝒜) := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end ProjDomain

/-! ### Quasi-projective schemes -/

/-- A projective morphism followed by a quasi-projective morphism is quasi-projective, provided
the composite is quasi-compact. If `X ⟶ ℙʳ_Y` is the closed immersion and `Y ⊆ W` the open
immersion into a scheme projective over `Z`, the composite `X ⟶ ℙʳ_Y ⊆ ℙʳ_W` is a quasi-compact
immersion, hence an open immersion into its scheme-theoretic image, a closed subscheme of the
`Z`-projective scheme `ℙʳ_W`. -/
theorem Projective.comp_quasiProjective {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Projective f) (hg : QuasiProjective g) [QuasiCompact (f ≫ g)] :
    QuasiProjective (f ≫ g) := by
  obtain ⟨r, i, hi, rfl⟩ := hf
  obtain ⟨W, j, h, hj, hh, rfl⟩ := hg
  have : IsOpenImmersion (projectiveSpaceOverSchemeMap r j) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (projectiveSpaceOverSchemeMap_isPullback r j).flip hj
  let φ : X ⟶ projectiveSpaceOverScheme r W := i ≫ projectiveSpaceOverSchemeMap r j
  have hproj : Projective (projectiveSpaceOverSchemeProjection r W ≫ h) :=
    Projective.comp (Projective.projection r W) hh
  have : IsProper (projectiveSpaceOverSchemeProjection r W ≫ h) := hproj.isProper
  have hfac : φ ≫ projectiveSpaceOverSchemeProjection r W ≫ h =
      (i ≫ projectiveSpaceOverSchemeProjection r Y) ≫ j ≫ h := by
    simp only [φ, Category.assoc, projectiveSpaceOverSchemeMap_projection_assoc]
  have : QuasiCompact φ := by
    have : QuasiCompact (φ ≫ projectiveSpaceOverSchemeProjection r W ≫ h) := by
      rw [hfac]
      infer_instance
    exact QuasiCompact.of_comp φ (projectiveSpaceOverSchemeProjection r W ≫ h)
  have : IsImmersion φ := inferInstance
  refine QuasiProjective.mk φ.toImage (φ.imageι ≫ projectiveSpaceOverSchemeProjection r W ≫ h)
    (Projective.comp (Projective.of_isClosedImmersion _) hproj) ?_
  rw [← Category.assoc, φ.toImage_imageι, hfac]

/-- A scheme `X` quasi-projective and of finite type over a Noetherian ring `A` has an ample
invertible sheaf: if `X ⊆ Z ⊆ ℙʳ_A` with `X` open in the closed subscheme `Z`, the restriction of
`𝒪(1)` is very ample, hence ample (Hartshorne II, Theorem 7.6). -/
theorem QuasiProjective.exists_isAmple {X : Scheme.{u}} {A : CommRingCat.{u}}
    [IsNoetherianRing A] (p : X ⟶ Spec A) (hp : FiniteType p) (hq : QuasiProjective p) :
    haveI := finiteType_isNoetherian p hp; ∃ L : X.Modules, L.IsAmple := by
  obtain ⟨Z, j, g, hj, ⟨r, c, hc, rfl⟩, hjg⟩ := hq
  let L := (Scheme.Modules.pullback (j ≫ c)).obj (projectiveSpaceTwistingSheaf r (Spec A) 1)
  have hL : L.IsInvertible :=
    Scheme.Modules.IsInvertible.pullback _ (isInvertible_projectiveSpaceTwistingSheaf r _ 1)
  have hV : IsVeryAmpleRelative p L :=
    ⟨hL, r, Z, j, c, hj, hc, by rw [Category.assoc, hjg], ⟨Iso.refl _⟩⟩
  have e : L ≅ moduleSheafTensorPower 1 L :=
    ((Ringed.moduleSheafTensorPowerSuccIso L 0 ≪≫
      Ringed.moduleSheafTensorIsoOfIso (Ringed.moduleSheafTensorPowerZeroIso L) (Iso.refl _) ≪≫
      Ringed.moduleSheafUnitTensor L).symm)
  exact ⟨L, isAmple_of_isVeryAmpleRelative_moduleSheafTensorPower p hp hL one_pos (hV.of_iso e)⟩

/-! ### The affine pieces of relative `Proj` -/

namespace QuasiCoherentGradedAlgebra

variable {X : Scheme.{u}} (S : QuasiCoherentGradedAlgebra X)

/-- A point of `Proj_X S` lying over an affine open `U ⊆ X` comes from the affine piece
`Proj S(U)`. -/
theorem exists_projι_eq_of_mem {x : S.relProj} {U : X.AffineZariskiSite}
    (hx : S.relProjToBase x ∈ U.toOpens) : ∃ y, S.projι U y = x := by
  have hx' : x ∈ (S.relProjToBase ⁻¹ᵁ U.1 : S.relProj.Opens) := hx
  rw [S.relProjToBase_preimage U] at hx'
  exact hx'

/-- Every point of `Proj_X S` comes from the affine piece `Proj S(U)` over some affine
open `U ⊆ X`. -/
theorem exists_projι_eq (x : S.relProj) :
    ∃ (U : X.AffineZariskiSite) (y : Proj (S.grading U)), S.projι U y = x := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (S.relProjToBase x)) isOpen_univ
  exact ⟨⟨V, hV⟩, S.exists_projι_eq_of_mem (U := ⟨V, hV⟩) hxV⟩

end QuasiCoherentGradedAlgebra

/-! ### The blowing-up of an integral scheme -/

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- Over a nonempty affine open `U` of an integral scheme, the ring of sections
`⨁_d Γ(U, I)ᵈ tᵈ ⊆ Γ(U, 𝒪_X)[t]` of the sheaf of Rees algebras is a domain. -/
theorem isDomain_reesAlgebra_obj [IsIntegral X] (U : X.AffineZariskiSite)
    [Nonempty U.toOpens] : IsDomain (I.reesAlgebra.obj.obj (.op U)) :=
  inferInstanceAs (IsDomain (_root_.reesAlgebra (I.ideal U.toOpens)))

/-- If `I` has a nonzero section, then on a reduced scheme the complement `X \ Y` of the closed
subscheme defined by `I` is nonempty. -/
theorem nonempty_centerCompl [IsReduced X] (hI0 : ∃ U : X.Opens, I.ideal U ≠ ⊥) :
    (I.centerCompl : Set X).Nonempty := by
  obtain ⟨U, hU⟩ := hI0
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hne : (X.basicOpen s : Set X).Nonempty := by
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty]
    exact fun h => hs0 ((basicOpen_eq_bot_iff s).mp h)
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (X.basicOpen_le s hx) U.2
  rw [SetLike.mem_coe, mem_centerCompl_iff, Scheme.IdealSheafData.range_subschemeι,
    SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV,
    Scheme.mem_zeroLocus_iff]
  push Not
  have hVU' : V ≤ U := hVU
  refine ⟨X.presheaf.map (homOfLE hVU').op s, ?_, ?_⟩
  · exact ArtinReesKernelSheaf.res_mem I.carrier hVU' hs
  · rw [Scheme.basicOpen_res]
    exact ⟨hxV, hx⟩

variable [IsNoetherian X] (hI : IsCoherent I.toModules)

/-- Every point of the center complement `X \ Y` is the image of a point of the blowing-up. -/
theorem exists_blowupProjection_eq_of_mem_centerCompl {z : X} (hz : z ∈ I.centerCompl) :
    ∃ w, I.blowupProjection hI w = z := by
  have := I.isIso_blowupProjection_restrict_centerCompl hI
  obtain ⟨w, hw⟩ := (I.blowupProjection hI ∣_ I.centerCompl).surjective ⟨z, hz⟩
  exact ⟨w.1, by rw [← morphismRestrict_base_coe, hw]⟩

/-- **The blowing-up of an integral scheme along a nonzero coherent ideal is integral.** Let `X`
be an integral Noetherian scheme and `I` a coherent sheaf of ideals with a nonzero section. Then
the blowing-up `X̃ = Proj_X (⨁_d Iᵈ)` is integral. -/
theorem isIntegral_blowup [IsIntegral X] (hI0 : ∃ U : X.Opens, I.ideal U ≠ ⊥) :
    IsIntegral (I.blowup hI) := by
  let W : (I.blowup hI).Opens := I.blowupProjection hI ⁻¹ᵁ I.centerCompl
  have hC : (I.centerCompl : Set X).Nonempty := I.nonempty_centerCompl hI0
  -- The affine pieces through a point are `Proj` of a domain.
  have hdom : ∀ (U : X.AffineZariskiSite) (_ : Proj (I.reesAlgebra.grading U)),
      IsDomain (I.reesAlgebra.obj.obj (.op U)) := fun U y => by
    have : Nonempty U.toOpens := ⟨I.reesAlgebra.projToOpen U y⟩
    exact I.isDomain_reesAlgebra_obj U
  -- `W = π⁻¹(X \ Y) ≅ X \ Y` is irreducible.
  have hirrC : IsIrreducible (I.centerCompl : Set X) :=
    ⟨hC, (IrreducibleSpace.isIrreducible_univ X).2.open_subset I.centerCompl.2
      (Set.subset_univ _)⟩
  have hirrW : IsIrreducible (W : Set (I.blowup hI)) := by
    have : IrreducibleSpace I.centerCompl.toScheme := Subtype.irreducibleSpace hirrC
    let e := Scheme.homeoOfIso (I.blowupIsoOffCenter hI)
    have h := (IrreducibleSpace.isIrreducible_univ I.centerCompl.toScheme).image
      (W.ι ∘ e.symm) (W.ι.continuous.comp e.symm.continuous).continuousOn
    rwa [Set.image_univ, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ,
      Scheme.Opens.range_ι] at h
  -- `W` is dense.
  have hdense : ∀ x : I.blowup hI, x ∈ closure (W : Set (I.blowup hI)) := by
    intro x
    obtain ⟨U, y, rfl⟩ := I.reesAlgebra.exists_projι_eq x
    have := hdom U y
    have : Nonempty (Proj (I.reesAlgebra.grading U)) := ⟨y⟩
    have := irreducibleSpace_proj_of_isDomain (I.reesAlgebra.grading U)
    obtain ⟨z, hzU, hzC⟩ := nonempty_preirreducible_inter U.toOpens.2 I.centerCompl.2
      ⟨_, (I.reesAlgebra.projToOpen U y).2⟩ hC
    obtain ⟨w, hw⟩ := I.exists_blowupProjection_eq_of_mem_centerCompl hI hzC
    obtain ⟨y', rfl⟩ := I.reesAlgebra.exists_projι_eq_of_mem (x := w) (U := U)
      (show I.blowupProjection hI w ∈ U.toOpens by rw [hw]; exact hzU)
    have hopen : ((I.reesAlgebra.projι U ⁻¹ᵁ W : (Proj (I.reesAlgebra.grading U)).Opens) :
        Set _).Nonempty :=
      ⟨y', show I.blowupProjection hI (I.reesAlgebra.projι U y') ∈ I.centerCompl by
        rw [hw]; exact hzC⟩
    have hy : y ∈ closure
        ((I.reesAlgebra.projι U ⁻¹ᵁ W : (Proj (I.reesAlgebra.grading U)).Opens) : Set _) :=
      ((I.reesAlgebra.projι U ⁻¹ᵁ W).2.dense hopen).closure_eq ▸ Set.mem_univ y
    exact map_mem_closure (I.reesAlgebra.projι U).continuous hy fun a ha => ha
  have hirr : IrreducibleSpace (I.blowup hI) := by
    rw [irreducibleSpace_def]
    have := hirrW.closure
    rwa [show closure (W : Set (I.blowup hI)) = ⊤ from
      Set.eq_univ_of_forall hdense] at this
  have : ∀ x : I.blowup hI, _root_.IsReduced ((I.blowup hI).presheaf.stalk x) := by
    intro x
    obtain ⟨U, y, rfl⟩ := I.reesAlgebra.exists_projι_eq x
    have := hdom U y
    have := isDomain_stalk_proj_of_isDomain (I.reesAlgebra.grading U) y
    have : IsDomain ((I.blowup hI).presheaf.stalk (I.reesAlgebra.projι U y)) :=
      Function.Injective.isDomain ((I.reesAlgebra.projι U).stalkMap y).hom
        (ConcreteCategory.injective_of_mono_of_preservesPullback
          ((I.reesAlgebra.projι U).stalkMap y))
    exact inferInstance
  have : IsReduced (I.blowup hI) := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end QuasicoherentIdealSubsheaf

/-! ### Blowing up a variety -/

namespace QuasicoherentIdealSubsheaf

/-- **Hartshorne II, Proposition 7.16.** Let `X` be a variety over a field `k`: an integral
scheme with a separated morphism `p : X ⟶ Spec k` of finite type. Let `I` be a nonzero coherent
sheaf of ideals on `X` (it has a nonzero section), and `π : X̃ ⟶ X` the blowing-up of `I`. Then:
* `X̃` is a variety over `k`: it is integral, and `π ≫ p` is separated and of finite type;
* `π` is birational: it restricts to an isomorphism over a nonempty open subset of `X` (dense,
  as `X` is irreducible);
* `π` is proper and surjective;
* if `X` is quasi-projective over `k`, then `π` is projective and `X̃` is quasi-projective
  over `k`;
* if `X` is projective over `k`, then `π` is projective and `X̃` is projective over `k`.

The book takes `k` algebraically closed; the statement here holds over any field. `X` is
Noetherian, being of finite type over `k`. -/
theorem blowup_variety {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsIntegral X] [IsSeparated p] (hp : FiniteType p) (I : QuasicoherentIdealSubsheaf X)
    (hI : IsCoherent I.toModules) (hI0 : ∃ U : X.Opens, I.ideal U ≠ ⊥) :
    haveI := finiteType_isNoetherian p hp
    (IsIntegral (I.blowup hI) ∧ IsSeparated (I.blowupProjection hI ≫ p) ∧
        FiniteType (I.blowupProjection hI ≫ p)) ∧
      (∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (I.blowupProjection hI ∣_ U)) ∧
      IsProper (I.blowupProjection hI) ∧ Surjective (I.blowupProjection hI) ∧
      (QuasiProjective p →
        Projective (I.blowupProjection hI) ∧ QuasiProjective (I.blowupProjection hI ≫ p)) ∧
      (Projective p →
        Projective (I.blowupProjection hI) ∧ Projective (I.blowupProjection hI ≫ p)) := by
  have := finiteType_isNoetherian p hp
  have := hp.1
  have := hp.2
  have hπ : IsProper (I.blowupProjection hI) := (I.blowupData hI).isProper_projection
  have hC := I.nonempty_centerCompl hI0
  have hsurj : Surjective (I.blowupProjection hI) := by
    refine ⟨fun z => ?_⟩
    have hsub : (I.centerCompl : Set X) ⊆ Set.range (I.blowupProjection hI) :=
      fun z hz => I.exists_blowupProjection_eq_of_mem_centerCompl hI hz
    have huniv := closure_minimal hsub (I.blowupProjection hI).isClosedMap.isClosed_range
    have hd : Dense (I.centerCompl : Set X) := I.centerCompl.isOpen.dense hC
    rw [hd.closure_eq] at huniv
    exact huniv (Set.mem_univ z)
  have hproj : QuasiProjective p → Projective (I.blowupProjection hI) := fun hq => by
    obtain ⟨L, hL⟩ := QuasiProjective.exists_isAmple p hp hq
    exact ((I.blowupData hI).projective_projection_and_isVeryAmpleRelative_of_isAmple hL).1
  exact ⟨⟨I.isIntegral_blowup hI hI0, inferInstance, ⟨inferInstance, inferInstance⟩⟩,
    ⟨I.centerCompl, hC, I.isIso_blowupProjection_restrict_centerCompl hI⟩, hπ, hsurj,
    fun hq => ⟨hproj hq, (hproj hq).comp_quasiProjective hq⟩,
    fun hq => ⟨hproj (.of_projective hq), (hproj (.of_projective hq)).comp hq⟩⟩

end QuasicoherentIdealSubsheaf

end Hartshorne
