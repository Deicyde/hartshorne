/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.AdjunctionEffectiveCartierDivisor
import Hartshorne.Scheme.Differentials.CanonicalSheafProjectiveSpace
import Hartshorne.Scheme.Differentials.PlurigenusBirational
import Hartshorne.Scheme.InvertibleSectionDivisor
import Hartshorne.Scheme.CartierLinearEquivalenceSheaf
import Hartshorne.Scheme.ProjTwistPullback

/-!
# The canonical sheaf of a smooth hypersurface

Hartshorne, *Algebraic Geometry*, II.8, Example 8.20.3 (pp. 183–184): if `Y` is a nonsingular
hypersurface of degree `d` in `X = ℙⁿ_k`, then `ω_Y ≅ 𝒪_Y(d - n - 1)`; for `d ≥ n + 1`, `Y` has
nonzero canonical sections and is not rational.

A hypersurface of degree `d` is the divisor of zeros `D = (s)₀` of a nonzero global section `s` of
`𝒪_X(d)` (`Hartshorne.SmoothHypersurface.hypersurface`, with closed immersion
`Hartshorne.SmoothHypersurface.hypersurfaceι`); "nonsingular" means irreducible and regular, as in
the formalization of adjunction. `𝒪_Y(m)` is the pullback `i^* 𝒪_X(m)`.

## Main results

* `Hartshorne.SmoothHypersurface.canonicalSheaf_smoothHypersurface`: `ω_Y ≅ 𝒪_Y(d - n - 1)`. The
  isomorphism is `Hartshorne.SmoothHypersurface.canonicalSheafIsoPullbackTwist`, the composite of
  adjunction `ω_Y ≅ i^*(ω_X ⊗ 𝒪_X(D))` (Proposition 8.20) with `ω_X ≅ 𝒪_X(-n-1)`
  (Example 8.20.1) and `𝒪_X(D) ≅ 𝒪_X(d)`
  (`Hartshorne.SmoothHypersurface.nonempty_sheaf_iso_of_isDivisorOfZeros`).
* `Hartshorne.SmoothHypersurface.nontrivial_globalSections_canonicalSheaf`: for `d ≥ n + 1`,
  `Γ(Y, ω_Y) ≠ 0`, as `𝒪_Y(m)`, `m ≥ 0`, has the nonzero section `ℓ^m` for a linear form `ℓ` not
  vanishing at some point of `Y`
  (`Hartshorne.SmoothHypersurface.exists_pullback_projTwistingSheaf_globalSection_ne_zero`).
  Hence `p_g(Y) > 0` once `Γ(Y, ω_Y)` is known to be finite-dimensional
  (`Hartshorne.SmoothHypersurface.geometricGenus_pos`).
* `Hartshorne.SmoothHypersurface.not_rational`: for `n ≥ 2` and `d ≥ n + 1`, `Y` is not birational
  to any `ℙᵐ_k`: for `m ≥ 1`, `Γ(ℙᵐ_k, ω) = 0` and the dimension of the space of canonical
  sections is a birational invariant (Theorem 8.19); for `m = 0`, `Y` would be a point, whose image
  is a closed point of `ℙⁿ_k`, of codimension `n ≠ 1`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne.SmoothHypersurface

open Ringed AlgebraicGeometry.Scheme.CartierDivisor EulerSequence

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ}

local notation3 "𝒜" => grading k n

/-- `ℙⁿ_k` is proper over `k`. -/
instance toBase_isProper : IsProper (toBase k n) := by
  have := projectiveSpaceOverSchemeProjection_isProper n (Spec (.of k))
  rw [show toBase k n = (projectiveSpaceOverSpecIso k n (Equiv.refl _)).hom ≫
      projectiveSpaceOverSchemeProjection n (Spec (.of k)) from
    (projToProjectiveSpaceOverSpec_projection k n (Equiv.refl _)).symm]
  infer_instance

/-- `ℙⁿ_k` is of finite type over `k`. -/
theorem toBase_finiteType : FiniteType (toBase k n) :=
  ⟨inferInstance, inferInstance⟩

section Iso

variable [IsAlgClosed k]

/-- **Hartshorne II, Example 8.20.3**, the isomorphism, for an effective Cartier divisor `D` on
`X = ℙⁿ_k` whose associated closed subscheme `i : Y ⟶ X` is nonsingular, given identifications
`ω_X ≅ 𝒪_X(-n-1)` and `𝒪_X(D) ≅ 𝒪_X(d)`: adjunction gives
`ω_Y ≅ i^*(ω_X ⊗ 𝒪_X(D)) ≅ i^*(𝒪_X(-n-1) ⊗ 𝒪_X(d)) ≅ i^* 𝒪_X(d - n - 1) = 𝒪_Y(d - n - 1)`. -/
noncomputable def canonicalSheafIsoPullbackTwist {D : (Proj 𝒜).CartierDivisor} (hD : D.IsEffective)
    [IrreducibleSpace (idealSheafData hD).subscheme]
    (hY : (idealSheafData hD).subscheme.IsRegular) {d : ℤ}
    (eω : canonicalSheaf (toBase k n) ≅ projTwistingSheaf 𝒜 (-((n : ℤ) + 1)))
    (eL : D.sheaf ≅ projTwistingSheaf 𝒜 d) :
    canonicalSheaf (subschemeι hD ≫ toBase k n) ≅
      (Scheme.Modules.pullback (subschemeι hD)).obj (projTwistingSheaf 𝒜 (d - n - 1)) :=
  adjunctionEffectiveCartierDivisorIso (toBase k n) hD toBase_finiteType
      projectiveSpace_isRegular hY ≪≫
    (Scheme.Modules.pullback (subschemeι hD)).mapIso
      (modulesIsoOfRinged (Ringed.moduleSheafTensorIsoOfIso eω eL) ≪≫
        modulesIsoOfRinged (Ringed.moduleSheafTensorIsoTensor _ _) ≪≫
        twistMulIso 𝒜 (ProjectiveSpacePicard.adjoin_one_eq_top k n) _ _ ≪≫
        eqToIso (congrArg (projTwistingSheaf 𝒜) (by ring)))

end Iso

section DivisorOfZeros

variable {d : ℕ}

/-- The divisor of zeros of a global section of `𝒪(d)` on `ℙⁿ_k` is effective. -/
theorem isEffective_of_isDivisorOfZeros {s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤)}
    {D : (Proj 𝒜).CartierDivisor} (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D) :
    D.IsEffective :=
  hD.isEffective
    (ProjectiveSpacePicard.projTwistingSheafIsoImageDivisorSheaf (k := k) (n := n) _)

/-- **The divisor sheaf of a degree-`d` hypersurface is `𝒪(d)`.** If `D` is the divisor of zeros
of a nonzero global section `s` of `𝒪(d)` on `ℙⁿ_k`, then `𝒪_X(D) ≅ 𝒪(d)`: `D` is linearly
equivalent to the divisor `D_d` with `𝒪(d) ≅ 𝒪_X(D_d)` (Proposition 7.7(a)), so
`𝒪_X(D) ≅ 𝒪_X(D_d) ≅ 𝒪(d)` (Proposition 6.13(c)). -/
theorem nonempty_sheaf_iso_of_isDivisorOfZeros {s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤)}
    {D : (Proj 𝒜).CartierDivisor} (hs : s ≠ 0)
    (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D) :
    Nonempty (D.sheaf ≅ projTwistingSheaf 𝒜 (d : ℤ)) := by
  let φ := ProjectiveSpacePicard.projTwistingSheafIsoImageDivisorSheaf (k := k) (n := n) (d : ℤ)
  obtain ⟨D', hD', -, hlin⟩ := exists_isDivisorOfZeros φ hs
  rw [hD.unique φ hD']
  obtain ⟨e⟩ := (linearEquivalent_iff_nonempty_iso _ _).1 hlin
  exact ⟨e ≪≫ φ.symm⟩

/-- The hypersurface `Y = (s)₀ ⊆ ℙⁿ_k`: the closed subscheme of the divisor of zeros `D` of a
global section `s` of `𝒪(d)`. -/
noncomputable abbrev hypersurface (s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤))
    {D : (Proj 𝒜).CartierDivisor} (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D) :
    Scheme.{u} :=
  (idealSheafData (isEffective_of_isDivisorOfZeros hD)).subscheme

/-- The closed immersion `i : Y ⟶ ℙⁿ_k` of the hypersurface `Y = (s)₀`. -/
noncomputable abbrev hypersurfaceι (s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤))
    {D : (Proj 𝒜).CartierDivisor} (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D) :
    hypersurface s hD ⟶ Proj 𝒜 :=
  subschemeι (isEffective_of_isDivisorOfZeros hD)

/-- **Hartshorne II, Example 8.20.3: the canonical sheaf of a nonsingular hypersurface.** Let `k`
be algebraically closed and `Y ⊆ X = ℙⁿ_k` a nonsingular (irreducible and regular) hypersurface
of degree `d`, i.e. the divisor of zeros `D` of a nonzero global section `s` of `𝒪(d)`, with
closed immersion `i : Y ⟶ X`. Then `ω_Y ≅ 𝒪_Y(d - n - 1) = i^* 𝒪_X(d - n - 1)`.

Following the book, adjunction (Proposition 8.20) gives `ω_Y ≅ i^*(ω_X ⊗ 𝒪_X(D))`, and
`ω_X ≅ 𝒪_X(-n-1)` (Example 8.20.1), `𝒪_X(D) ≅ 𝒪_X(d)`. Hartshorne assumes `n ≥ 2`, which is not
used. -/
theorem canonicalSheaf_smoothHypersurface [IsAlgClosed k]
    {s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤)} {D : (Proj 𝒜).CartierDivisor} (hs : s ≠ 0)
    (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D)
    [IrreducibleSpace (hypersurface s hD)] (hY : (hypersurface s hD).IsRegular) :
    Nonempty (canonicalSheaf (hypersurfaceι s hD ≫ toBase k n) ≅
      (Scheme.Modules.pullback (hypersurfaceι s hD)).obj
        (projTwistingSheaf 𝒜 ((d : ℤ) - n - 1))) := by
  obtain ⟨eω⟩ := canonicalSheaf_projectiveSpace (k := k) (n := n)
  obtain ⟨eL⟩ := nonempty_sheaf_iso_of_isDivisorOfZeros hs hD
  exact ⟨canonicalSheafIsoPullbackTwist _ hY eω eL⟩

end DivisorOfZeros

section Sections

open ProjGradedModuleSheaf

variable {ℓ : MvPolynomial (Fin (n + 1)) k}

/-- `1` lies in no homogeneous prime of `Proj`. -/
theorem one_notMem (x : ProjectiveSpectrum 𝒜) :
    (1 : MvPolynomial (Fin (n + 1)) k) ∉ x.asHomogeneousIdeal :=
  fun h => x.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

/-- The global section `ℓ^m` of `𝒪(m)`, `m ≥ 0`, for a linear form `ℓ`. -/
noncomputable def linearPowGlobalSection (hℓ : ℓ ∈ 𝒜 1) (m : ℕ) :
    (projTwistingSheaf 𝒜 (m : ℤ)).val.obj (op ⊤) :=
  have hm : ℓ ^ m ∈ gradedTwist 𝒜 (m : ℤ) ((0 : ℕ) : ℤ) :=
    (mem_gradedTwist_of_eq (k := m) (by omega)).2 (pow_mem_graded_one _ hℓ m)
  (⟨fun x => HomogeneousLocalizedModule.mk 0 (ℓ ^ m) hm 1 SetLike.GradedOne.one_mem
      (one_notMem x.1),
    fun _ => ⟨⊤, trivial, 𝟙 _, 0, ℓ ^ m, hm, 1, SetLike.GradedOne.one_mem,
      fun z => one_notMem z.1, fun _ => rfl⟩⟩ :
    (sheafInType 𝒜 (gradedTwist 𝒜 (m : ℤ))).1.obj (op ⊤))

/-- On `D₊(ℓ)`, the global section `ℓ^m` restricts to the local generator `ℓ^m` of `𝒪(m)`. -/
theorem linearPowGlobalSection_restrict (hℓ : ℓ ∈ 𝒜 1) (m : ℕ) :
    (projTwistingSheaf 𝒜 (m : ℤ)).val.presheaf.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 ℓ ≤ ⊤)).op
        (linearPowGlobalSection hℓ m) = twistGenSection hℓ (m : ℤ) := by
  refine section_ext (ℳ := gradedTwist 𝒜 (m : ℤ)) fun x => HomogeneousLocalizedModule.ext ?_
  exact LocalizedModule.mk_eq.2 ⟨1, by simp [Submonoid.smul_def]⟩

/-- **Nonnegative twists restricted to a nonempty scheme have a nonzero global section.** For a
morphism `i : Y ⟶ ℙⁿ_k` from a nonempty scheme and `m ≥ 0`, the pullback `i^* 𝒪(m)` has a nonzero
global section: the pullback of `ℓ^m` for a linear form `ℓ` not vanishing at the image of a point
of `Y`, which generates `i^* 𝒪(m)` near that point. -/
theorem exists_pullback_projTwistingSheaf_globalSection_ne_zero {Y : Scheme.{u}} [Nonempty Y]
    (i : Y ⟶ Proj 𝒜) {l : ℤ} (hl : 0 ≤ l) :
    ∃ t : Γ((Scheme.Modules.pullback i).obj (projTwistingSheaf 𝒜 l), ⊤), t ≠ 0 := by
  classical
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hl
  obtain ⟨y⟩ := ‹Nonempty Y›
  obtain ⟨ℓ, hℓ1, -, hy⟩ := ProjectiveSpacePicard.exists_linear_notMem (i.base y)
  have hℓ : ℓ ∈ 𝒜 1 := (MvPolynomial.mem_homogeneousSubmodule 1 ℓ).mpr hℓ1
  have hF := Ringed.IsLocalFrame.pullback (φ := i.toRingCatSheafHom)
    (ProjTwistPullback.isLocalFrame_twistGenSection hℓ (m : ℤ))
  refine ⟨etaSec (φ := i.toRingCatSheafHom) (E := projTwistingSheaf 𝒜 (m : ℤ)) (W := ⊤)
    (linearPowGlobalSection hℓ m), fun h0 => ?_⟩
  have h1 : etaSec (φ := i.toRingCatSheafHom) (E := projTwistingSheaf 𝒜 (m : ℤ))
      (W := ProjectiveSpectrum.basicOpen 𝒜 ℓ) (twistGenSection hℓ (m : ℤ)) = 0 := by
    have h := etaSec_restrict (φ := i.toRingCatSheafHom) (E := projTwistingSheaf 𝒜 (m : ℤ))
      (le_top : ProjectiveSpectrum.basicOpen 𝒜 ℓ ≤ ⊤) (linearPowGlobalSection hℓ m)
    erw [linearPowGlobalSection_restrict hℓ m] at h
    rw [h]
    erw [h0, map_zero]
  have hV : Nonempty ((Opens.map i.base).obj (ProjectiveSpectrum.basicOpen 𝒜 ℓ)) := ⟨⟨y, hy⟩⟩
  have hsz : ∀ (M : PresheafOfModules.{u} (ringCatSheafOf Y.sheaf).obj) (W : Y.Opensᵒᵖ)
      (a : (ringCatSheafOf Y.sheaf).obj.obj W), a • (0 : M.presheaf.obj W) = 0 :=
    fun _ _ a => smul_zero a
  have h2 := (hF _ le_rfl).1 (a₁ := fun _ => 1) (a₂ := 0) (by
    erw [localFrameMap_apply, localFrameMap_apply, Fintype.sum_unique, Fintype.sum_unique, h1]
    rw [map_zero]
    exact (hsz _ _ _).trans (hsz _ _ _).symm)
  have : Nontrivial Γ(Y, (Opens.map i.base).obj (ProjectiveSpectrum.basicOpen 𝒜 ℓ)) :=
    inferInstance
  exact one_ne_zero (α := Γ(Y, (Opens.map i.base).obj (ProjectiveSpectrum.basicOpen 𝒜 ℓ)))
    (congrFun h2 PUnit.unit)

end Sections

section Genus

variable {d : ℕ}

/-- **Hartshorne II, Example 8.20.3: canonical sections of a hypersurface of large degree.** If
`Y ⊆ ℙⁿ_k` is a nonsingular hypersurface of degree `d ≥ n + 1`, then `Γ(Y, ω_Y) ≠ 0`: by
`ω_Y ≅ 𝒪_Y(d - n - 1)` with `d - n - 1 ≥ 0`, and `𝒪_Y(d - n - 1)` has a nonzero global section. -/
theorem nontrivial_globalSections_canonicalSheaf [IsAlgClosed k]
    {s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤)}
    {D : (Proj 𝒜).CartierDivisor} (hs : s ≠ 0)
    (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D)
    [IrreducibleSpace (hypersurface s hD)] (hY : (hypersurface s hD).IsRegular)
    (hdn : n + 1 ≤ d) :
    Nontrivial (GlobalSectionsOver (hypersurfaceι s hD ≫ toBase k n)
      (canonicalSheaf (hypersurfaceι s hD ≫ toBase k n))) := by
  obtain ⟨e⟩ := canonicalSheaf_smoothHypersurface hs hD hY
  obtain ⟨t, ht⟩ := exists_pullback_projTwistingSheaf_globalSection_ne_zero (hypersurfaceι s hD)
    (l := (d : ℤ) - n - 1) (by omega)
  have key : e.inv.app ⊤ t ≠ 0 := fun h => ht (by
    have h2 : e.hom.app ⊤ (e.inv.app ⊤ t) = t := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
      rfl
    rw [← h2, h, map_zero])
  exact ⟨⟨e.inv.app ⊤ t, 0, key⟩⟩

/-- **Hartshorne II, Example 8.20.3: positive geometric genus**, granted finite-dimensionality of
`Γ(Y, ω_Y)` (Hartshorne II.5.19). If `Y ⊆ ℙⁿ_k` is a nonsingular hypersurface of degree
`d ≥ n + 1`, then `p_g(Y) > 0`. -/
theorem geometricGenus_pos [IsAlgClosed k] {s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤)}
    {D : (Proj 𝒜).CartierDivisor} (hs : s ≠ 0)
    (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D)
    [IrreducibleSpace (hypersurface s hD)] (hY : (hypersurface s hD).IsRegular)
    (hdn : n + 1 ≤ d) [Module.Finite k (GlobalSectionsOver (hypersurfaceι s hD ≫ toBase k n)
      (canonicalSheaf (hypersurfaceι s hD ≫ toBase k n)))] :
    0 < geometricGenus (hypersurfaceι s hD ≫ toBase k n) := by
  have := nontrivial_globalSections_canonicalSheaf hs hD hY hdn
  exact Module.finrank_pos

/-- `Γ(ℙᵐ_k, ω) = 0` for `m ≥ 1`. -/
theorem subsingleton_globalSections_canonicalSheaf_projectiveSpace {m : ℕ} (hm : 0 < m) :
    Subsingleton (GlobalSectionsOver (toBase k m) (canonicalSheaf (toBase k m))) := by
  obtain ⟨e⟩ := canonicalSheaf_projectiveSpace (k := k) (n := m)
  have key : ∀ a : Γ(canonicalSheaf (toBase k m), ⊤), a = 0 := fun a => by
    have h1 : e.hom.app ⊤ a = 0 :=
      ProjectiveSpacePicard.projTwistingSheaf_globalSections_eq_zero hm (by omega) _
    have h2 : e.inv.app ⊤ (e.hom.app ⊤ a) = a := by
      rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
      rfl
    rw [← h2, h1, map_zero]
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- **Hartshorne II, Example 8.20.3: a hypersurface of large degree is not rational.** If
`Y ⊆ ℙⁿ_k` is a nonsingular hypersurface of degree `d ≥ n + 1`, then `Y` is not birational over
`k` to any projective space `ℙᵐ_k` with `m ≥ 1` (in particular not to `ℙⁿ⁻¹_k`). As in the book,
`Γ(Y, ω_Y) ≠ 0` while `Γ(ℙᵐ_k, ω) = 0`, and the dimension of the space of canonical sections is
a birational invariant (Theorem 8.19). -/
theorem not_birational_projectiveSpace [IsAlgClosed k]
    {s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤)}
    {D : (Proj 𝒜).CartierDivisor} (hs : s ≠ 0)
    (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D)
    [IrreducibleSpace (hypersurface s hD)] (hY : (hypersurface s hD).IsRegular)
    (hdn : n + 1 ≤ d) {m : ℕ} (hm : 0 < m) :
    ¬ ∃ e : (hypersurface s hD).PartialIso (Proj (grading k m)),
      e.IsOver (hypersurfaceι s hD ≫ toBase k n) (toBase k m) := by
  rintro ⟨e, he⟩
  have : IsIntegral (hypersurface s hD) := isIntegral_of_isRegular hY
  have hp : FiniteType (hypersurfaceι s hD ≫ toBase k n) := ⟨inferInstance, inferInstance⟩
  obtain ⟨N, hN⟩ := exists_topologicalKrullDim_eq_nat _ hp
  have hN' := topologicalKrullDim_eq_of_partialIso _ (toBase k m) hp toBase_finiteType e hN
  have hle := rank_globalSections_exteriorPower_le_of_partialIso (toBase k m) _
    projectiveSpace_isRegular hY e.symm he.symm hN' hN N
  rw [← canonicalSheaf_eq _ hN, ← canonicalSheaf_eq _ hN'] at hle
  have := subsingleton_globalSections_canonicalSheaf_projectiveSpace (k := k) hm
  have := nontrivial_globalSections_canonicalSheaf hs hD hY hdn
  have h0 : Module.rank k (GlobalSectionsOver (toBase k m) (canonicalSheaf (toBase k m))) = 0 :=
    rank_subsingleton' _ _
  rw [h0] at hle
  exact (rank_pos (R := k)).ne' (le_antisymm hle zero_le)

/-- **A nonsingular hypersurface in `ℙⁿ_k`, `n ≥ 2`, is not birational to `ℙ⁰_k`.** Otherwise `Y`
has dimension `0`, so it is a single point, whose image in `ℙⁿ_k` is a closed point of codimension
one; but a closed point of `ℙⁿ_k` has codimension `n`. -/
theorem not_birational_projectiveSpace_zero (hn : 2 ≤ n)
    {s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤)} {D : (Proj 𝒜).CartierDivisor}
    (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D)
    [IrreducibleSpace (hypersurface s hD)] (hY : (hypersurface s hD).IsRegular) :
    ¬ ∃ e : (hypersurface s hD).PartialIso (Proj (grading k 0)),
      e.IsOver (hypersurfaceι s hD ≫ toBase k n) (toBase k 0) := by
  rintro ⟨e, -⟩
  have : IsIntegral (hypersurface s hD) := isIntegral_of_isRegular hY
  have hp : FiniteType (hypersurfaceι s hD ≫ toBase k n) := ⟨inferInstance, inferInstance⟩
  have hY0 : topologicalKrullDim (hypersurface s hD) = ((0 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_partialIso (toBase k 0) _ toBase_finiteType hp e.symm
      topologicalKrullDim_projectiveSpace
  -- every point of `Y` is its generic point
  have hpt : ∀ y : hypersurface s hD, y = genericPoint (hypersurface s hD) := fun y => by
    have h := NonsingularConormal.height_add_coheight_point _ hp y
    rw [hY0] at h
    have h' : Order.height y + Order.coheight y = 0 := by exact_mod_cast h
    have hmax := Order.coheight_eq_zero.1 (add_eq_zero.1 h').2
    have h1 : genericPoint (hypersurface s hD) ⤳ y :=
      (genericPoint_spec (hypersurface s hD)).specializes (Set.mem_univ y)
    exact (Specializes.antisymm
      (show y ⤳ genericPoint (hypersurface s hD) from hmax (show y ≤ _ from h1)) h1).eq
  set x := (hypersurfaceι s hD).base (genericPoint (hypersurface s hD))
  have hrange : Set.range (hypersurfaceι s hD).base = closure {x} := by
    have h : Set.range (hypersurfaceι s hD).base = {x} := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        rw [hpt y]
        rfl
      · rintro rfl
        exact ⟨_, rfl⟩
    rw [← h]
    exact ((hypersurfaceι s hD).isClosedEmbedding.isClosed_range.closure_eq).symm
  have hcodim : Order.coheight x = 1 := by
    rw [← codim_closure_singleton_eq_coheight, ← hrange]
    exact codim_range_subschemeι _
  have hheight : Order.height x = 0 := by
    refine Order.height_eq_zero.2 fun z hz => ?_
    have hz' : z ∈ closure {x} := specializes_iff_mem_closure.mp hz
    rw [← hrange] at hz'
    obtain ⟨y, rfl⟩ := hz'
    rw [hpt y]
  have h := NonsingularConormal.height_add_coheight_point (toBase k n) toBase_finiteType x
  rw [hheight, hcodim, topologicalKrullDim_projectiveSpace] at h
  have h1 : ((1 : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by simpa using h
  have h2 : (1 : ℕ) = n := by exact_mod_cast h1
  omega

/-- **Hartshorne II, Example 8.20.3: a nonsingular hypersurface of degree `d ≥ n + 1` in `ℙⁿ_k`,
`n ≥ 2`, is not rational**: it is not birational over `k` to any projective space `ℙᵐ_k`. For
`m ≥ 1` this is `not_birational_projectiveSpace` (canonical sections); for `m = 0` it is
`not_birational_projectiveSpace_zero` (dimension). -/
theorem not_rational [IsAlgClosed k] (hn : 2 ≤ n)
    {s : (projTwistingSheaf 𝒜 (d : ℤ)).val.obj (op ⊤)} {D : (Proj 𝒜).CartierDivisor} (hs : s ≠ 0)
    (hD : IsDivisorOfZeros (projTwistingSheaf 𝒜 (d : ℤ)) s D)
    [IrreducibleSpace (hypersurface s hD)] (hY : (hypersurface s hD).IsRegular)
    (hdn : n + 1 ≤ d) (m : ℕ) :
    ¬ ∃ e : (hypersurface s hD).PartialIso (Proj (grading k m)),
      e.IsOver (hypersurfaceι s hD ≫ toBase k n) (toBase k m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact not_birational_projectiveSpace_zero hn hD hY
  · exact not_birational_projectiveSpace hs hD hY hdn hm

end Genus

end Hartshorne.SmoothHypersurface
