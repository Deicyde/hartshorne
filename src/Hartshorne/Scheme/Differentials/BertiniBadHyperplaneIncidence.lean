/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SeparatesPointsTangentVectors
import Hartshorne.Scheme.Differentials.RegularHypersurfaceCriterion
import Hartshorne.Scheme.DimensionAtClosedPoint

/-!
# Bad hyperplanes at a point

Hartshorne, *Algebraic Geometry*, II.8, proof of Theorem 8.18 (pp. 179–180).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  IsLocalRing

namespace Hartshorne

universe u

namespace BertiniIncidence

/-! ### Linear algebra of `R / 𝔪²` -/

section Algebra

variable {k R : Type*} [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]

/-- If `k → R/𝔪` is bijective, then `dim_k R/𝔪² = dim_k 𝔪/𝔪² + 1`. -/
theorem finrank_quotient_maximalIdeal_sq
    (hk : Function.Bijective (algebraMap k (ResidueField R))) :
    Module.finrank k (R ⧸ maximalIdeal R ^ 2) =
      Module.finrank (ResidueField R) (CotangentSpace R) + 1 := by
  set 𝔪 := maximalIdeal R
  have : IsScalarTower k (ResidueField R) (CotangentSpace R) :=
    IsScalarTower.of_algebraMap_smul fun c m => by
      rw [IsScalarTower.algebraMap_apply k R (ResidueField R), algebraMap_smul, algebraMap_smul]
  have hk1 : Module.finrank k (ResidueField R) = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap k (ResidueField R)) hk).finrank_eq,
      Module.finrank_self]
  have hcot : Module.finrank k (CotangentSpace R) =
      Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [← Module.finrank_mul_finrank k (ResidueField R) (CotangentSpace R), hk1, one_mul]
  -- the ideal `𝔪/𝔪²` of `R/𝔪²` as a `k`-subspace
  let N : Submodule k (R ⧸ 𝔪 ^ 2) := 𝔪.cotangentIdeal.restrictScalars k
  have hN : Module.finrank k N = Module.finrank k (CotangentSpace R) :=
    ((𝔪.cotangentEquivIdeal).restrictScalars k).finrank_eq.symm
  have hQ : Module.finrank k ((R ⧸ 𝔪 ^ 2) ⧸ N) = 1 := by
    let e : ((R ⧸ 𝔪 ^ 2) ⧸ N) ≃ₗ[k] ResidueField R :=
      { toFun := fun y => 𝔪.quotCotangent y
        invFun := fun y => 𝔪.quotCotangent.symm y
        map_add' := map_add _
        map_smul' := fun c y => by
          induction y using Submodule.Quotient.induction_on with | _ y => ?_
          induction y using Submodule.Quotient.induction_on with | _ y => ?_
          rfl
        left_inv := 𝔪.quotCotangent.left_inv
        right_inv := 𝔪.quotCotangent.right_inv }
    rw [e.finrank_eq, hk1]
  have : Module.Finite k (ResidueField R) := Module.finite_of_finrank_eq_succ hk1
  have : FiniteDimensional k (CotangentSpace R) :=
    Module.Finite.trans (ResidueField R) (CotangentSpace R)
  have : FiniteDimensional k N :=
    LinearEquiv.finiteDimensional ((𝔪.cotangentEquivIdeal).restrictScalars k)
  have : FiniteDimensional k ((R ⧸ 𝔪 ^ 2) ⧸ N) :=
    Module.finite_of_finrank_eq_succ hQ
  have h := Submodule.rank_quotient_add_rank N
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, hQ, hN, hcot] at h
  refine Module.finrank_eq_of_rank_eq ?_
  rw [← h]
  push_cast
  ring

end Algebra

/-! ### Stalks of an invertible sheaf -/

section Stalks

variable {X : Scheme.{u}}

/-- Germs of module sections are compatible with the action of functions. -/
theorem germ_smul_module (F : X.Modules) {U : X.Opens} (x : X) (hx : x ∈ U) (r : Γ(X, U))
    (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  PresheafOfModules.germ_smul M x U hx r m

/-- A trivializing section generates the stalk freely: `b ε_x ∈ I L_x` iff `b ∈ I`. -/
theorem smul_germ_mem_smul_top_iff {L : X.Modules} {U : X.Opens}
    {ε : Γ(L, U)} (hε : IsTrivializingSection L U ε) {x : X} (hx : x ∈ U)
    (I : Ideal (X.presheaf.stalk x)) (b : X.presheaf.stalk x) :
    b • L.presheaf.germ U x hx ε ∈
        I • (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) ↔ b ∈ I := by
  have htop : (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) =
      Submodule.span (X.presheaf.stalk x) {L.presheaf.germ U x hx ε} := by
    refine (Submodule.eq_top_iff'.mpr fun z => ?_).symm
    obtain ⟨c, rfl⟩ := hε.exists_smul_germ_eq hx z
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  rw [htop, Submodule.mem_smul_span_singleton]
  constructor
  · rintro ⟨c, hc, hce⟩
    have hsub : (c - b) • L.presheaf.germ U x hx ε = 0 := by rw [sub_smul, hce, sub_self]
    rwa [sub_eq_zero.mp (hε.eq_zero_of_smul_germ_eq_zero hx _ hsub)] at hc
  · intro hb
    exact ⟨b, hb, rfl⟩

end Stalks

/-! ### The subspace of hyperplanes that are bad at a point -/

section BadSubspace

variable {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
  {L : X.Modules} {n : ℕ} (s : Fin (n + 1) → Γ(L, ⊤))

theorem linearSystemSection_add (a b : Fin (n + 1) → k) :
    linearSystemSection q s (a + b) = linearSystemSection q s a + linearSystemSection q s b := by
  simp only [linearSystemSection, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem linearSystemSection_smul (c : k) (a : Fin (n + 1) → k) :
    linearSystemSection q s (c • a) = kConst q c • linearSystemSection q s a := by
  simp only [linearSystemSection, Pi.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, mul_smul]

theorem linearSystemSection_zero : linearSystemSection q s 0 = 0 := by
  simp only [linearSystemSection, Pi.zero_apply, map_zero, zero_smul, Finset.sum_const_zero]

/-- The coefficient vectors `a` for which the section `∑ aᵢ sᵢ` lies in `𝔪_x² L_x` at `x`. -/
def badSubspace (x : X) : Submodule k (Fin (n + 1) → k) where
  carrier := {a | L.presheaf.germ ⊤ x trivial (linearSystemSection q s a) ∈
    maximalIdeal (X.presheaf.stalk x) ^ 2 •
      (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x))}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, linearSystemSection_add, map_add] at ha hb ⊢
    exact add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, linearSystemSection_zero, map_zero]
    exact zero_mem _
  smul_mem' c a ha := by
    simp only [Set.mem_ofPred_eq, linearSystemSection_smul] at ha ⊢
    have h := germ_smul_module L x (show x ∈ (⊤ : X.Opens) from trivial) (kConst q c)
      (linearSystemSection q s a)
    erw [h]
    exact Submodule.smul_mem _ _ ha

theorem mem_badSubspace_iff (x : X) (a : Fin (n + 1) → k) :
    a ∈ badSubspace q s x ↔ L.presheaf.germ ⊤ x trivial (linearSystemSection q s a) ∈
      maximalIdeal (X.presheaf.stalk x) ^ 2 •
        (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) := Iff.rfl

end BadSubspace

/-! ### Dimension of the bad subspace -/

section Dimension

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q]

/-- The identification `κ(P) ≅ k` at a closed point is evaluation of constants. -/
theorem residueFieldIsoBase_inv_eq' (P : X) (hP : IsClosed {P}) :
    (residueFieldIsoBase q P hP).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop ≫ X.Γevaluation P := by
  have h := congrArg (fun g => g.appTop ≫ (Scheme.ΓSpecIso (X.residueField P)).hom)
    (SpecMap_residueFieldIsoBase_inv q P hP)
  simp only [Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, Scheme.fromSpecResidueField,
    Category.assoc, Scheme.fromSpecStalk_appTop] at h
  rw [← Iso.eq_inv_comp] at h
  rw [h]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_assoc]
  rfl

/-- At a closed point, the constants `k → κ(P)` are bijective. -/
theorem bijective_residue_kConstStalk (P : X) (hP : IsClosed {P}) :
    Function.Bijective ((residue (X.presheaf.stalk P)).comp (kConstStalk q P)) := by
  have h : (residue (X.presheaf.stalk P)).comp (kConstStalk q P) =
      (residueFieldIsoBase q P hP).inv.hom := by
    rw [residueFieldIsoBase_inv_eq']
    rfl
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso (residueFieldIsoBase q P hP).inv)

variable {n : ℕ} {L : X.Modules} (hL : L.IsInvertible) (s : Fin (n + 1) → Γ(L, ⊤))
  (φ : X ⟶ projectiveSpaceOverScheme n (Spec (CommRingCat.of k)))
  (hφ : φ ≫ projectiveSpaceOverSchemeProjection n _ = q)
  (e : (Scheme.Modules.pullback φ).obj (projectiveSpaceTwistingSheaf n _ 1) ≅ L)
  (he : ∀ i, e.hom.app ⊤ (pullbackGlobalSection φ (projectiveSpaceCoordinate n _ i)) = s i)

include hL hφ he in
/-- **The bad hyperplanes at a closed point form a subspace of codimension `r + 1`.** Let
`φ : X ⟶ ℙⁿ_k` be a closed immersion defined by sections `sᵢ` of `L`, and let `x` be a closed
point at which `𝒪_{X,x}` is regular of dimension `r`. The coefficient vectors `a` for which
`∑ aᵢ sᵢ` lies in `𝔪_x² L_x` form a subspace of `kⁿ⁺¹` of dimension `n - r`: the map
`kⁿ⁺¹ → L_x / 𝔪_x² L_x ≅ 𝒪_{X,x}/𝔪_x²` is surjective since `V` separates tangent vectors
(Proposition II.7.3) and `sᵢ` is a unit near `x`, and its target has dimension `r + 1`. -/
theorem finrank_badSubspace [IsClosedImmersion φ] (x : X) (hx : IsClosed {x})
    [IsRegularLocalRing (X.presheaf.stalk x)] {r : ℕ}
    (hr : ringKrullDim (X.presheaf.stalk x) = r) :
    Module.finrank k (badSubspace q s x) = n - r := by
  let : Algebra k (X.presheaf.stalk x) := (kConstStalk q x).toAlgebra
  obtain ⟨i, hi⟩ := exists_mem_chartPreimage φ x
  have hW : φ x ∈ projectiveSpaceChart n (Spec (CommRingCat.of k)) i := hi
  have hxU : x ∈ nonvanishingLocusOpens hL (s i) := by
    rw [← preimage_projectiveSpaceChart_eq_nonvanishingLocusOpens hL s φ e he i]
    exact hW
  have hε := isTrivializingSection_nonvanishingLocusOpens hL (s i)
  obtain ⟨g, hg_def⟩ : ∃ g, L.presheaf.germ _ x hxU
      (L.presheaf.map (homOfLE le_top).op (s i)) = g := ⟨_, rfl⟩
  have hg : g = L.presheaf.germ ⊤ x trivial (s i) := by
    rw [← hg_def]; exact TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hfree : ∀ (I : Ideal (X.presheaf.stalk x)) (b : X.presheaf.stalk x),
      b • g ∈ I • (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) ↔ b ∈ I := by
    rw [← hg_def]; exact smul_germ_mem_smul_top_iff hε hxU
  have huniq : ∀ b b' : X.presheaf.stalk x, b • g = b' • g → b = b' := by
    intro b b' h
    have hsub : (b - b') • g = 0 := by rw [sub_smul, h, sub_self]
    rw [← hg_def] at hsub
    exact sub_eq_zero.mp (hε.eq_zero_of_smul_germ_eq_zero hxU _ hsub)
  have hex : ∀ z : L.presheaf.stalk x, ∃ b : X.presheaf.stalk x, b • g = z := by
    rw [← hg_def]; exact hε.exists_smul_germ_eq hxU
  choose β hβ using fun a : Fin (n + 1) → k =>
    hex (L.presheaf.germ ⊤ x trivial (linearSystemSection q s a))
  have hconst : ∀ c : k, algebraMap k (X.presheaf.stalk x) c =
      X.presheaf.germ ⊤ x trivial (kConst q c) := fun _ => rfl
  let βl : (Fin (n + 1) → k) →ₗ[k] X.presheaf.stalk x :=
    { toFun := β
      map_add' := fun a b => huniq _ _ (by
        rw [add_smul, hβ, hβ, hβ, linearSystemSection_add, map_add])
      map_smul' := fun c a => huniq _ _ (by
        change β (c • a) • g = (algebraMap k _ c * β a) • g
        rw [mul_smul, hβ, hβ, linearSystemSection_smul, hconst]
        exact germ_smul_module L x (show x ∈ (⊤ : X.Opens) from trivial) _ _) }
  have hmem : ∀ a, a ∈ badSubspace q s x ↔ β a ∈ maximalIdeal (X.presheaf.stalk x) ^ 2 := by
    intro a
    rw [mem_badSubspace_iff, ← hβ, hfree]
  let f := (Ideal.Quotient.mkₐ k (maximalIdeal (X.presheaf.stalk x) ^ 2)).toLinearMap ∘ₗ βl
  have hker : LinearMap.ker f = badSubspace q s x := by
    ext a
    rw [hmem]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hβi : β (Pi.single i 1) = 1 := huniq _ _ (by
    rw [hβ, linearSystemSection_single, one_smul, hg])
  have hk : Function.Bijective (algebraMap k (ResidueField (X.presheaf.stalk x))) :=
    bijective_residue_kConstStalk q x hx
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := hk.2 (residue _ y)
    set m := y - algebraMap k (X.presheaf.stalk x) c with hm_def
    have hm : m ∈ maximalIdeal (X.presheaf.stalk x) := by
      rw [← residue_eq_zero_iff, hm_def, map_sub, sub_eq_zero]
      exact hc.symm
    have hz : m • g ∈ maximalIdeal (X.presheaf.stalk x) •
        (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) :=
      Submodule.smul_mem_smul hm Submodule.mem_top
    obtain ⟨M, d, t, ht, hrest⟩ :=
      sectionsSeparateTangentVectors_of_isClosedImmersion q hL s φ hφ e he x hx (m • g) hz
    choose a ha using fun j => (ht j).1
    refine ⟨c • Pi.single i 1 + ∑ j, d j • a j, ?_⟩
    change Ideal.Quotient.mk _ (βl _) = Ideal.Quotient.mk _ y
    rw [Ideal.Quotient.eq]
    have hA : βl (c • Pi.single i 1 + ∑ j, d j • a j) =
        algebraMap k _ c + ∑ j, algebraMap k _ (d j) * β (a j) := by
      rw [map_add, map_smul, map_sum]
      simp only [map_smul]
      change c • β (Pi.single i 1) + ∑ j, d j • β (a j) = _
      rw [hβi]
      simp only [Algebra.smul_def, mul_one]
    rw [hA, ← hfree, ← neg_mem_iff, ← neg_smul, neg_sub]
    have hy : y - (algebraMap k _ c + ∑ j, algebraMap k _ (d j) * β (a j)) =
        m - ∑ j, algebraMap k _ (d j) * β (a j) := by
      rw [hm_def]; ring
    rw [hy, sub_smul, Finset.sum_smul]
    convert hrest using 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, hβ, ha]
    rfl
  have hcot : Module.finrank (ResidueField (X.presheaf.stalk x))
      (CotangentSpace (X.presheaf.stalk x)) = r := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.presheaf.stalk x)).mp
      inferInstance
    rw [hr] at h
    exact_mod_cast h
  have hdim : Module.finrank k (X.presheaf.stalk x ⧸ maximalIdeal (X.presheaf.stalk x) ^ 2) =
      r + 1 := by
    rw [finrank_quotient_maximalIdeal_sq hk, hcot]
  have := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hdim, hker, Module.finrank_fin_fun] at this
  omega

end Dimension

/-! ### Stalks of closed subschemes -/

section ClosedImmersionStalk

variable {X Y : Scheme.{u}}

/-- For a closed immersion `ι : Y ⟶ X` and an affine open `U ∋ ι(z)`, the kernel of
`𝒪_{X,ι(z)} → 𝒪_{Y,z}` is generated by the germs of the kernel of `Γ(X, U) → Γ(Y, ι⁻¹ U)`. -/
theorem ker_stalkMap_eq_map_ker_app (ι : Y ⟶ X) [IsClosedImmersion ι] (z : Y) {U : X.Opens}
    (hU : IsAffineOpen U) (hz : ι z ∈ U) :
    RingHom.ker (ι.stalkMap z).hom =
      (RingHom.ker (ι.app U).hom).map (X.presheaf.germ U (ι z) hz).hom := by
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_)
  swap
  · rw [Ideal.mem_comap, RingHom.mem_ker, Scheme.Hom.germ_stalkMap_apply, RingHom.mem_ker.mp ha,
      map_zero]
  -- germs of sections over `U` killed by the stalk map
  have key : ∀ a : Γ(X, U), ι.stalkMap z (X.presheaf.germ U (ι z) hz a) = 0 →
      X.presheaf.germ U (ι z) hz a ∈
        (RingHom.ker (ι.app U).hom).map (X.presheaf.germ U (ι z) hz).hom := by
    intro a ha
    rw [Scheme.Hom.germ_stalkMap_apply] at ha
    obtain ⟨W, hzW, iW, iV, hW⟩ := TopCat.Presheaf.germ_eq Y.presheaf z hz (show z ∈ (⊤ : Y.Opens)
      from trivial) (ι.app U a) 0 (by rw [ha, map_zero])
    have hV : IsAffineOpen (ι ⁻¹ᵁ U) := hU.preimage ι
    obtain ⟨v, hvW, hzv⟩ := hV.exists_basicOpen_le ⟨z, hzW⟩ hz
    have hres : (ι.app U a) |_ (Y.basicOpen v) = 0 := by
      have : Y.basicOpen v ≤ W := hvW
      rw [map_zero] at hW
      change Y.presheaf.map (homOfLE _).op _ = 0
      rw [show (homOfLE (Y.basicOpen_le v)) = homOfLE this ≫ iW from rfl, op_comp,
        Functor.map_comp, CommRingCat.comp_apply, hW, map_zero]
    obtain ⟨N, hN⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen Y hV _ _ hres
    have hN' : v ^ (N + 1) * ι.app U a = 0 := by rw [pow_succ', mul_assoc, hN, mul_zero]
    obtain ⟨w, hw⟩ := ι.app_surjective U hU (v ^ (N + 1))
    have hzw : ι z ∈ X.basicOpen w := by
      change z ∈ ι ⁻¹ᵁ X.basicOpen w
      rw [Scheme.preimage_basicOpen, hw, Scheme.basicOpen_pow _ _ N.succ_pos]
      exact hzv
    have hwa : w * a ∈ RingHom.ker (ι.app U).hom := by
      rw [RingHom.mem_ker, map_mul, hw, hN']
    obtain ⟨c, hc⟩ := ((X.mem_basicOpen w (ι z) hz).mp hzw).exists_left_inv
    have hca : X.presheaf.germ U (ι z) hz a = c * X.presheaf.germ U (ι z) hz (w * a) := by
      rw [map_mul, ← mul_assoc, hc, one_mul]
    rw [hca]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hwa)
  intro α hα
  rw [RingHom.mem_ker] at hα
  let := X.presheaf.algebra_section_stalk ⟨ι z, hz⟩
  have hloc := hU.isLocalization_stalk ⟨ι z, hz⟩
  obtain ⟨⟨a, u⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (hU.primeIdealOf ⟨ι z, hz⟩).asIdeal.primeCompl α
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (ι z)) a u
  have hu := IsLocalization.map_units (X.presheaf.stalk (ι z)) u
  change _ * X.presheaf.germ U (ι z) hz u = X.presheaf.germ U (ι z) hz a at hspec
  change IsUnit (X.presheaf.germ U (ι z) hz u) at hu
  have hga : ι.stalkMap z (X.presheaf.germ U (ι z) hz a) = 0 := by
    rw [← hspec, map_mul, hα, zero_mul]
  obtain ⟨c, hc⟩ := hu.exists_right_inv
  have hα' : IsLocalization.mk' (X.presheaf.stalk (ι z)) a u =
      X.presheaf.germ U (ι z) hz a * c := by
    rw [← hspec, mul_assoc, hc, mul_one]
  change IsLocalization.mk' (X.presheaf.stalk (ι z)) a u ∈ _
  rw [hα']
  exact Ideal.mul_mem_right _ _ (key a hga)

end ClosedImmersionStalk

end BertiniIncidence

end Hartshorne
