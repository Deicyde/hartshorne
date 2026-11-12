/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.ReesAlgebraBlowup

/-!
# The blowing-up is an isomorphism off its center

Hartshorne, *Algebraic Geometry*, II.7, Proposition 7.13(b), p. 164.

Let `X` be a Noetherian scheme, `I` a coherent sheaf of ideals on `X`, `Y` the closed subscheme
defined by `I`, and `π : X̃ = Proj_X (⨁_d Iᵈ) ⟶ X` the blowing-up. Then `π` induces an isomorphism
`π⁻¹(X \ Y) = X̃ \ π⁻¹(Y) ≅ X \ Y`.

Following the book: on `U = X \ Y` we have `I|_U = 𝒪_U`, so the Rees algebra restricts to
`𝒪_U[T]`, and `Proj 𝒪_U[T] = U`. In the encoding of `Proj_X` by gluing the schemes
`Proj Γ(V, ⨁_d Iᵈ)` over affine opens `V ⊆ X`, this reads: for an affine open `V ⊆ X \ Y` the
ideal `Γ(V, I)` is the unit ideal, so `Γ(V, ⨁_d Iᵈ)` is the polynomial ring `Γ(V, 𝒪_X)[T]`, and
`Proj Γ(V, 𝒪_X)[T] ⟶ Spec Γ(V, 𝒪_X) = V` is an isomorphism; being an isomorphism is local on the
target.

## Main results

* `isIso_toSpecZero_of_forall_mem_eq_mul_pow`: `Proj A ⟶ Spec A₀` is an isomorphism when some
  degree-one non-zero-divisor `t` has every homogeneous element of degree `n` of the form `b tⁿ`
  with `b ∈ A₀` (that is, `A = A₀[t]`).
* `isIso_toSpecZero_reesGrading_of_eq_top`: the local identity `Proj R[T] ≅ Spec R`, for the Rees
  algebra of the unit ideal.
* `QuasicoherentIdealSubsheaf.centerCompl`: the open complement `X \ Y` of the closed subscheme `Y`
  defined by `I`.
* `QuasicoherentIdealSubsheaf.isIso_blowupProjection_restrict_centerCompl`,
  `QuasicoherentIdealSubsheaf.blowupIsoOffCenter`: **Hartshorne II.7.13(b)**, the restriction
  `π⁻¹(X \ Y) ⟶ X \ Y` of the blowing-up is an isomorphism.
-/

noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry HomogeneousLocalization

universe u

namespace Hartshorne

/-! ### `Proj A₀[t] = Spec A₀` -/

section ProjPolynomial

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If `t ∈ A₁` is a non-zero-divisor and every homogeneous element of degree `n` is `b tⁿ` with
`b ∈ A₀` (so `A = A₀[t]` as a graded ring), then the structure map `Proj A ⟶ Spec A₀` is an
isomorphism. -/
theorem isIso_toSpecZero_of_forall_mem_eq_mul_pow {t : A} (ht : t ∈ 𝒜 1)
    (hreg : ∀ a : A, t * a = 0 → a = 0)
    (h : ∀ (n : ℕ), ∀ a ∈ 𝒜 n, ∃ b ∈ 𝒜 0, a = b * t ^ n) :
    IsIso (Proj.toSpecZero 𝒜) := by
  classical
  -- `D₊(t)` is all of `Proj A`, since `t` generates the irrelevant ideal.
  have hirr : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range fun _ : Unit => t) := by
    intro a ha
    have ha' : GradedRing.proj 𝒜 0 a = 0 := ha
    rw [← sub_zero a, ← ha']
    clear ha ha'
    refine DirectSum.Decomposition.inductionOn 𝒜 (motive := fun a =>
      a - GradedRing.proj 𝒜 0 a ∈ Ideal.span (Set.range fun _ : Unit => t)) ?_ ?_ ?_ a
    · simp
    · intro i m
      by_cases hi : i = 0
      · subst hi
        rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same 𝒜 m.2, sub_self]
        exact zero_mem _
      · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 m.2 hi, sub_zero]
        obtain ⟨b, -, hb⟩ := h i m m.2
        rw [hb]
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _
          (Ideal.subset_span (Set.mem_range_self (f := fun _ : Unit => t) ())) i
          (Nat.pos_of_ne_zero hi))
    · intro m m' hm hm'
      rw [map_add, add_sub_add_comm]
      exact add_mem hm hm'
  have htop : Proj.basicOpen 𝒜 t = ⊤ := by
    simpa using Proj.iSup_basicOpen_eq_top 𝒜 _ hirr
  -- Hence the open immersion `Spec A_(t) ⟶ Proj A` onto `D₊(t)` is an isomorphism.
  have hι : IsIso (Proj.awayι 𝒜 t ht one_pos) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
    have hx : x ∈ (Proj.awayι 𝒜 t ht one_pos).opensRange := by
      rw [Proj.opensRange_awayι, htop]
      trivial
    exact hx
  -- And `A₀ → A_(t)` is bijective.
  have hbij : Function.Bijective (fromZeroRingHom 𝒜 (Submonoid.powers t)) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro b hb
      have hb' := congrArg HomogeneousLocalization.val hb
      rw [HomogeneousLocalization.val_zero] at hb'
      change (Localization.mk (b : A) 1 : Localization.Away t) = 0 at hb'
      rw [Localization.mk_one_eq_algebraMap,
        IsLocalization.map_eq_zero_iff (Submonoid.powers t)] at hb'
      obtain ⟨⟨_, k, rfl⟩, hk⟩ := hb'
      apply Subtype.ext
      change (b : A) = 0
      induction k with
      | zero => simpa using hk
      | succ k ih =>
        apply ih
        apply hreg
        simpa [pow_succ', mul_assoc] using hk
    · intro x
      obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht x
      have ha' : a ∈ 𝒜 n := by simpa using ha
      obtain ⟨b, hb, hab⟩ := h n a ha'
      refine ⟨⟨b, hb⟩, ?_⟩
      apply HomogeneousLocalization.val_injective
      rw [Away.val_mk]
      change (Localization.mk b 1 : Localization.Away t) = _
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp [hab, mul_comm]⟩
  have hSpec : IsIso (Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers t)))) := by
    have : IsIso (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers t))) :=
      (ConcreteCategory.isIso_iff_bijective _).2 hbij
    infer_instance
  rw [← Proj.awayι_toSpecZero 𝒜 t ht one_pos] at hSpec
  exact IsIso.of_isIso_comp_left (Proj.awayι 𝒜 t ht one_pos) (Proj.toSpecZero 𝒜)

end ProjPolynomial

section Rees

variable {R : Type u} [CommRing R]

/-- **The local identity `Proj R[T] ≅ Spec R`.** For the unit ideal `I = R`, the Rees algebra
`⨁_d Iᵈ Tᵈ` is the polynomial ring `R[T]`, and the structure map `Proj R[T] ⟶ Spec R` is an
isomorphism. -/
theorem isIso_toSpecZero_reesGrading_of_eq_top {I : Ideal R} (hI : I = ⊤) :
    IsIso (Proj.toSpecZero (reesGrading I)) := by
  subst hI
  have hX : (X : R[X]) ∈ reesAlgebra (⊤ : Ideal R) :=
    (mem_reesAlgebra_iff _ _).2 fun i => by simp [Ideal.top_pow]
  refine isIso_toSpecZero_of_forall_mem_eq_mul_pow (reesGrading (⊤ : Ideal R))
    (t := ⟨X, hX⟩) ?_ ?_ ?_
  · rw [mem_reesGrading_iff]
    simpa using monomial_one_one_eq_X.symm
  · intro a ha
    apply Subtype.ext
    exact monic_X.mul_right_eq_zero_iff.1 (congrArg Subtype.val ha)
  · intro n a ha
    refine ⟨_, algebraMap_mem_reesGrading_zero _ ((a : R[X]).coeff n), ?_⟩
    apply Subtype.ext
    rw [mem_reesGrading_iff] at ha
    rw [Subalgebra.coe_mul, coe_algebraMap_reesAlgebra, SubmonoidClass.coe_pow,
      C_mul_X_pow_eq_monomial]
    exact ha

end Rees

/-! ### The blowing-up off its center -/

/-- If `π : X ⟶ Y` restricts to an isomorphism over each member of a family of opens of `Y`
contained in `U` and covering `U`, then it restricts to an isomorphism over `U`. -/
theorem isIso_morphismRestrict_of_forall_exists {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (H : ∀ x ∈ U, ∃ V : Y.Opens, V ≤ U ∧ x ∈ V ∧ IsIso (f ∣_ V)) : IsIso (f ∣_ U) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme) fun x => ?_
  obtain ⟨V, hVU, hxV, hV⟩ := H x.1 x.2
  refine ⟨U.ι ⁻¹ᵁ V, hxV, ?_⟩
  have hV' : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).2 ?_
  rw [hV']
  exact hV

namespace QuasicoherentIdealSubsheaf

variable {X : Scheme.{u}} (I : QuasicoherentIdealSubsheaf X)

/-- The open complement `X \ Y` of the closed subscheme `Y` defined by `I` (the complement of the
image of the closed immersion `Y ⟶ X` whose kernel is `I`). -/
def centerCompl : X.Opens :=
  ⟨(Set.range (quasicoherentIdealSubsheafEquiv I).subschemeι)ᶜ, by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact (Scheme.IdealSheafData.support _).isClosed.isOpen_compl⟩

theorem mem_centerCompl_iff (x : X) :
    x ∈ I.centerCompl ↔ x ∉ Set.range (quasicoherentIdealSubsheafEquiv I).subschemeι :=
  Iff.rfl

/-- `I|_{X \ Y} = 𝒪_{X \ Y}`: on every affine open `V ⊆ X \ Y`, `Γ(V, I)` is the unit ideal. -/
theorem ideal_eq_top_of_le_centerCompl {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ I.centerCompl) :
    I.ideal V = ⊤ := by
  set J := quasicoherentIdealSubsheafEquiv I
  change J.ideal ⟨V, hV⟩ = ⊤
  rw [← Ideal.span_eq (J.ideal ⟨V, hV⟩), ← hV.self_le_iSup_basicOpen_iff]
  intro x hx
  have hxs : x ∉ J.support := by
    have := hVU hx
    rw [mem_centerCompl_iff, Scheme.IdealSheafData.range_subschemeι] at this
    exact this
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hx,
    Scheme.mem_zeroLocus_iff] at hxs
  push Not at hxs
  obtain ⟨f, hf, hxf⟩ := hxs
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hxf⟩

variable [IsNoetherian X] (hI : IsCoherent I.toModules)

/-- Over an affine open `V ⊆ X \ Y`, the blowing-up restricts to an isomorphism: there
`Γ(V, ⨁_d Iᵈ) = Γ(V, 𝒪_X)[T]` and `Proj Γ(V, 𝒪_X)[T] = V`. -/
theorem isIso_blowupProjection_restrict_of_isAffineOpen {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ I.centerCompl) : IsIso (I.blowupProjection hI ∣_ V) := by
  let V' : X.AffineZariskiSite := ⟨V, hV⟩
  let S := I.reesAlgebra
  have hrees : IsIso (Proj.toSpecZero (S.grading V')) :=
    isIso_toSpecZero_reesGrading_of_eq_top (I.ideal_eq_top_of_le_centerCompl hV hVU)
  have hzero : IsIso (S.toZero V') :=
    (ConcreteCategory.isIso_iff_bijective _).2 ((I.blowupData hI).degreeZero V')
  have hproj : IsIso (S.projToOpen V') := by
    change IsIso ((S.projToSpec ≫ (Scheme.AffineZariskiSite.restrictIsoSpec X).inv).app V')
    rw [NatTrans.comp_app]
    have : IsIso (S.projToSpec.app V') := by
      change IsIso (Proj.toSpecZero (S.grading V') ≫ Spec.map (S.toZero V'))
      infer_instance
    infer_instance
  rw [← I.blowupRestrictIso_hom_projToOpen hI V']
  exact IsIso.comp_isIso' (Iso.isIso_hom ((I.blowupData hI).restrictIso V')) hproj

/-- **Hartshorne II.7.13(b).** Let `X` be a Noetherian scheme, `I` a coherent sheaf of ideals and
`Y` the closed subscheme defined by `I`. Then the blowing-up `π : X̃ ⟶ X` restricts to an
isomorphism `π⁻¹(X \ Y) ⟶ X \ Y`. -/
theorem isIso_blowupProjection_restrict_centerCompl :
    IsIso (I.blowupProjection hI ∣_ I.centerCompl) := by
  refine isIso_morphismRestrict_of_forall_exists _ _ fun x hx => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx I.centerCompl.2
  exact ⟨V, hVU, hxV, I.isIso_blowupProjection_restrict_of_isAffineOpen hI hV hVU⟩

/-- `π⁻¹(X \ Y)` is the complement `X̃ \ π⁻¹(Y)` of the preimage of `Y`. -/
theorem coe_blowupProjection_preimage_centerCompl :
    ((I.blowupProjection hI ⁻¹ᵁ I.centerCompl : (I.blowup hI).Opens) : Set (I.blowup hI)) =
      (I.blowupProjection hI ⁻¹' Set.range (quasicoherentIdealSubsheafEquiv I).subschemeι)ᶜ :=
  rfl

/-- **Hartshorne II.7.13(b).** The blowing-up `π : X̃ ⟶ X` induces an isomorphism
`X̃ \ π⁻¹(Y) = π⁻¹(X \ Y) ≅ X \ Y`; its underlying morphism is the restriction of `π`
(`blowupIsoOffCenter_hom`). -/
def blowupIsoOffCenter :
    (I.blowupProjection hI ⁻¹ᵁ I.centerCompl).toScheme ≅ I.centerCompl.toScheme :=
  haveI := I.isIso_blowupProjection_restrict_centerCompl hI
  asIso (I.blowupProjection hI ∣_ I.centerCompl)

@[simp]
theorem blowupIsoOffCenter_hom :
    (I.blowupIsoOffCenter hI).hom = I.blowupProjection hI ∣_ I.centerCompl :=
  rfl

end QuasicoherentIdealSubsheaf

end Hartshorne
