/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BirationalBlowupRees
import Hartshorne.Scheme.BlowupVariety

/-!
# A birational projective morphism is a blowup

Hartshorne, *Algebraic Geometry*, II, Theorem 7.17 (pp. 166–168).
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne.BirationalBlowup

open SectionAlgebraModel Scheme QuasiCoherentGradedAlgebra

/-! ### Gluing the local identifications -/

namespace Setup

variable {r : ℕ} {X Z : Scheme.{u}} {i : Z ⟶ projectiveSpaceOverScheme r X} [IsIntegral X]
  [IsIntegral Z] [IsNoetherian X] {d : ℕ} (P : Setup i d)

omit [AlgebraicGeometry.IsNoetherian X] in
theorem isEmpty_proj (A : QuasiCoherentGradedAlgebra X) (U : X.AffineZariskiSite)
    (hU : genericPoint X ∉ U.1) : IsEmpty (Proj (A.grading U)) := by
  have h := opens_eq_bot_of_genericPoint_notMem hU
  refine ⟨fun x => ?_⟩
  obtain ⟨z, hz⟩ := (A.projToOpen U).base x
  have hz' : z ∈ U.1 := hz
  rw [h] at hz'
  exact hz'

open Classical in
/-- The local isomorphism `Proj (⊕_m I(U)ᵐ) ≅ Proj (S · D)(U)` over an affine open `U` on which `D`
has a frame: the identification `S(U) ≅ ⊕_m I(U)ᵐ` followed by the inverse of the local
isomorphism of Lemma 7.9 (both schemes are empty when `U` is). -/
def localIso (U : (framedAffines P.D).FullSubcategory) :
    Proj (P.I.reesAlgebra.grading U.obj) ≅ Proj ((P.S.lineBundleTwist P.D P.hD).grading U.obj) :=
  if hU : genericPoint X ∈ U.obj.1 then
    projIsoOfBijective (P.ρ U.obj hU U.property.choose_spec)
        (P.ρ_bijective U.obj hU U.property.choose_spec) ≪≫
      (P.S.framedIso (hL := P.hD) U).symm
  else
    have := isEmpty_proj P.I.reesAlgebra U.obj hU
    have := isEmpty_proj (P.S.lineBundleTwist P.D P.hD) U.obj hU
    isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty

theorem localIso_hom_of_mem (U : (framedAffines P.D).FullSubcategory)
    (hU : genericPoint X ∈ U.obj.1) :
    (P.localIso U).hom = (projIsoOfBijective (P.ρ U.obj hU U.property.choose_spec)
        (P.ρ_bijective U.obj hU U.property.choose_spec)).hom ≫
      (P.S.framedIso (hL := P.hD) U).inv := by
  rw [localIso, dif_pos hU]
  rfl

private theorem projMap_congr' {A B : Type u} [CommRing A] [CommRing B] {𝒜 : ℕ → AddSubgroup A}
    {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ] {φ ψ : 𝒜 →+*ᵍ ℬ} (e : φ = ψ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ) :
    Proj.map φ hφ = Proj.map ψ hψ := by
  subst e
  rfl

theorem localIso_naturality {U V : (framedAffines P.D).FullSubcategory} (f : U ⟶ V) :
    Proj.map (P.I.reesAlgebra.restrict f.hom) (P.I.reesAlgebra.irrelevant_le f.hom) ≫
        (P.localIso V).hom =
      (P.localIso U).hom ≫ Proj.map ((P.S.lineBundleTwist P.D P.hD).restrict f.hom)
        ((P.S.lineBundleTwist P.D P.hD).irrelevant_le f.hom) := by
  by_cases hU : genericPoint X ∈ U.obj.1
  swap
  · have := isEmpty_proj P.I.reesAlgebra U.obj hU
    exact isInitialOfIsEmpty.hom_ext _ _
  have hV : genericPoint X ∈ V.obj.1 := AffineZariskiSite.toOpens_mono f.hom.le hU
  have hpU := U.property.choose_spec
  have hpV := V.property.choose_spec
  have hpVU := isLocalFrame_restrictFrame f.hom hpV
  rw [localIso_hom_of_mem P U hU, localIso_hom_of_mem P V hV,
    P.projIso_ρ_eq U.obj hU hpVU hpU]
  have key : Proj.map (P.I.reesAlgebra.restrict f.hom) (P.I.reesAlgebra.irrelevant_le f.hom) ≫
      (projIsoOfBijective (P.ρ V.obj hV hpV) (P.ρ_bijective V.obj hV hpV)).hom =
      (projIsoOfBijective (P.ρ U.obj hU hpVU) (P.ρ_bijective U.obj hU hpVU)).hom ≫
        Proj.map (P.S.restrict f.hom) (P.S.irrelevant_le f.hom) := by
    rw [projIsoOfBijective_hom, projIsoOfBijective_hom, ← Proj.map_comp, ← Proj.map_comp]
    exact projMap_congr' (P.ρ_restrict f.hom hU hpV) _ _
  have key2 : (P.S.framedIso (hL := P.hD) U).inv ≫
      Proj.map ((P.S.lineBundleTwist P.D P.hD).restrict f.hom)
        ((P.S.lineBundleTwist P.D P.hD).irrelevant_le f.hom) =
      Proj.map (P.S.restrict f.hom) (P.S.irrelevant_le f.hom) ≫
        (P.S.framedIso (hL := P.hD) V).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← framedIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, key, Category.assoc, Category.assoc, key2]

theorem localIso_hom_toSpec (U : (framedAffines P.D).FullSubcategory) :
    (P.localIso U).hom ≫ Proj.toSpecZero ((P.S.lineBundleTwist P.D P.hD).grading U.obj) ≫
        Spec.map ((P.S.lineBundleTwist P.D P.hD).toZero U.obj) =
      Proj.toSpecZero (P.I.reesAlgebra.grading U.obj) ≫ Spec.map (P.I.reesAlgebra.toZero U.obj) := by
  by_cases hU : genericPoint X ∈ U.obj.1
  swap
  · have := isEmpty_proj P.I.reesAlgebra U.obj hU
    exact isInitialOfIsEmpty.hom_ext _ _
  rw [localIso_hom_of_mem P U hU, Category.assoc, ← P.S.framedIso_hom_toSpec (hL := P.hD) U,
    Iso.inv_hom_id_assoc, projIsoOfBijective_hom, ← Category.assoc, projMap_toSpecZero,
    Category.assoc, ← Spec.map_comp]
  congr 2
  ext a : 2
  exact Subtype.ext (P.ρ_structureMap U.obj hU U.property.choose_spec a)

/-- **`Bl_I X ≅ Proj_X S` over `X`** (Hartshorne II, proof of Theorem 7.17, Step 5): the local
identifications `S(U) ≅ ⊕_m I(U)ᵐ` glue, through Lemma 7.9 for `S · D`, to an isomorphism
`Proj_X (⊕_m Iᵐ) ≅ Proj_X (S · D) ≅ Proj_X S`. -/
def blowupIso : P.I.reesAlgebra.relProj ≅ P.S.relProj :=
  framedGlueIso P.hD P.localIso P.localIso_naturality ≪≫ P.S.lineBundleTwistIso P.hD

theorem blowupIso_hom_relProjToBase :
    P.blowupIso.hom ≫ P.S.relProjToBase = P.I.reesAlgebra.relProjToBase := by
  rw [blowupIso, Iso.trans_hom, Category.assoc, lineBundleTwistIso_hom_relProjToBase,
    framedGlueIso_hom_relProjToBase _ _ _ P.localIso_hom_toSpec]

end Setup

/-! ### Existence of the data -/

section Existence

variable {r : ℕ} {X Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOverScheme r X) [IsClosedImmersion i]
  [IsIntegral X] [IsIntegral Z] [IsNoetherian X]

/-- **The data of Theorem 7.17, Steps 4–5, exist**: for `X` of finite type over a field with an
ample invertible sheaf `A`, and `f = π ∘ i` birational, there are a degree `d`, a section-algebra
model `S` of `f` in degree `d`, and for `D = A^{-n}` (`n > 0`) a nonzero morphism `t : D ⟶ 𝒪_X`
with values in the denominator ideal of `f_* L^{d} ⊆ K_X`. -/
theorem nonempty_setup (k : Type u) [Field k] (pX : X ⟶ Spec (.of k)) [LocallyOfFiniteType pX]
    (hf : (proj i).base (genericPoint Z) = genericPoint X)
    (hbij : Function.Bijective ((proj i).genericFunctionFieldMap hf)) {A : X.Modules}
    (hA : A.IsAmple) : ∃ d : ℕ, Nonempty (Setup i d) := by
  obtain ⟨d₀, hd₀⟩ := exists_sectionAlgebraModel_multiplicative i k pX hf
  obtain ⟨Dt, E, h₁, h₂, h₃, e, he⟩ := hd₀ (d₀ + 1) (Nat.le_succ d₀)
  let M : SectionModel i (d₀ + 1) := ⟨Dt, E, h₁, h₂, h₃, e, he⟩
  let θ := (RingEquiv.ofBijective ((proj i).genericFunctionFieldMap hf).hom hbij).symm.toRingHom
  have hθ : ∀ g, θ ((proj i).genericFunctionFieldMap hf g) = g := fun g =>
    (RingEquiv.ofBijective ((proj i).genericFunctionFieldMap hf).hom hbij).symm_apply_apply g
  have hL : ((Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf r X 1)).IsInvertible :=
    Scheme.Modules.IsInvertible.pullback _ (isInvertible_projectiveSpaceTwistingSheaf r _ 1)
  obtain ⟨W, e, hW, he⟩ := exists_isTrivializingSection hL (genericPoint Z)
  have hfp : Hartshorne.Projective (proj i) := Projective.mk r i rfl
  have hF := isCoherent_pushforward_of_isInvertible (proj i) k pX hfp
    (isInvertible_moduleSheafTensorPower hL (1 * (d₀ + 1)))
  obtain ⟨n, -, hG⟩ := exists_isGloballyGenerated_denominatorIdealSheaf_tensor hF
    (fracHom hf θ hθ he hW (1 * (d₀ + 1))) hA
  have hA' : Ringed.IsInvertible (R := X.sheaf) A := (Modules.isInvertible_iff_ringed A).mp hA.1
  have hP := Ringed.isInvertible_moduleSheafTensorPower hA' n
  obtain ⟨t, ht0, ht⟩ := exists_dual_hom_denominator hF (fracHom hf θ hθ he hW (1 * (d₀ + 1))) hP hG
  exact ⟨d₀ + 1, ⟨⟨hf, θ, hθ, W, e, he, hW, M, hF, _,
    (Modules.isInvertible_iff_ringed _).mpr (Ringed.isInvertible_moduleSheafDual hP), t, ht, ht0⟩⟩⟩

end Existence

/-! ### The theorem -/

namespace Setup

variable {r : ℕ} {X Z : Scheme.{u}} {i : Z ⟶ projectiveSpaceOverScheme r X} [IsIntegral X]
  [IsIntegral Z] [IsNoetherian X] {d : ℕ} (P : Setup i d)

/-- The ideal of the blowup is nonzero: otherwise `Proj_X (⊕_m Iᵐ)` would be empty, while it is
isomorphic to the nonempty scheme `Z`. -/
theorem exists_ideal_ne_bot : ∃ U : X.Opens, P.I.ideal U ≠ ⊥ := by
  by_contra h
  push Not at h
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X)) isOpen_univ
  let U : X.AffineZariskiSite := ⟨V, hV⟩
  let x := (P.M.iso.inv ≫ P.blowupIso.inv).base (genericPoint Z)
  have hx : P.I.reesAlgebra.relProjToBase x ∈ U.1 := by
    have hb : (P.M.iso.inv ≫ P.blowupIso.inv) ≫ P.I.reesAlgebra.relProjToBase = proj i := by
      rw [Category.assoc, ← P.blowupIso_hom_relProjToBase, Iso.inv_hom_id_assoc, Iso.inv_comp_eq,
        P.M.iso_hom]
      rfl
    change ((P.M.iso.inv ≫ P.blowupIso.inv) ≫ P.I.reesAlgebra.relProjToBase).base
      (genericPoint Z) ∈ V
    rw [hb, P.hf]
    exact hηV
  have hx' : x ∈ (P.I.reesAlgebra.relProjToBase ⁻¹ᵁ U.1 : _) := hx
  rw [P.I.reesAlgebra.relProjToBase_preimage U] at hx'
  obtain ⟨y, -⟩ := hx'
  apply (show ProjectiveSpectrum (P.I.reesAlgebra.grading U) from y).not_irrelevant_le
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro m hm a ha
  obtain ⟨b, hb, hab⟩ := (P.I.mem_reesAlgebra_grading_iff U m a).1 ha
  rw [h U.1, Ideal.bot_pow (Nat.pos_iff_ne_zero.1 hm), Ideal.mem_bot] at hb
  have ha0 : a = 0 := Subtype.ext (by
    change ReesAlgebraSheaf.toPolynomial _ a = 0
    rw [hab, hb, map_zero])
  rw [ha0]
  exact zero_mem _

end Setup

end Hartshorne.BirationalBlowup

namespace Hartshorne

open BirationalBlowup

/-- **Hartshorne II, Theorem 7.17.** Let `X` be a quasi-projective variety over a field `k`: an
integral scheme with `p : X ⟶ Spec k` of finite type and quasi-projective. Let `Z` be a variety
(only its integrality is used) and `f : Z ⟶ X` a birational projective morphism: `f` maps the
generic point of `Z` to that of `X` and induces an isomorphism `K(X) ≅ K(Z)` of function fields.
Then there is a nonzero coherent sheaf of ideals `I` on `X` such that `Z` is isomorphic over `X` to
the blowing-up `Bl_I X = Proj_X (⊕_m Iᵐ)`.

The book takes `k` algebraically closed and `Z` a variety; the proof here works over any field
and uses only that `Z` is integral. -/
theorem exists_iso_blowup_of_birational_projective {k : Type u} [Field k] {X Z : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] (hp : FiniteType p) (hq : QuasiProjective p)
    [IsIntegral Z] (f : Z ⟶ X) (hfp : Projective f)
    (hf : f.base (genericPoint Z) = genericPoint X)
    (hbij : Function.Bijective (f.genericFunctionFieldMap hf)) :
    haveI := finiteType_isNoetherian p hp
    ∃ (I : QuasicoherentIdealSubsheaf X) (hI : IsCoherent I.toModules),
      (∃ U : X.Opens, I.ideal U ≠ ⊥) ∧
        ∃ e : Z ≅ I.blowup hI, e.hom ≫ I.blowupProjection hI = f := by
  have := finiteType_isNoetherian p hp
  have : LocallyOfFiniteType p := hp.1
  obtain ⟨A, hA⟩ := QuasiProjective.exists_isAmple p hp hq
  obtain ⟨r, i, hi, rfl⟩ := hfp
  obtain ⟨d, ⟨P⟩⟩ := nonempty_setup i k p hf hbij hA
  refine ⟨P.I, isCoherent_blowupIdeal _ _ _ _ _ _ _, P.exists_ideal_ne_bot,
    (P.blowupIso ≪≫ P.M.iso).symm, ?_⟩
  change P.M.iso.inv ≫ P.blowupIso.inv ≫ P.I.reesAlgebra.relProjToBase = _
  rw [← P.blowupIso_hom_relProjToBase, Iso.inv_hom_id_assoc, Iso.inv_comp_eq, P.M.iso_hom]
  rfl

end Hartshorne
