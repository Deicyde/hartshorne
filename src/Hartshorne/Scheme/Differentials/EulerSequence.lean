/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.EulerSequenceChainRule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# The Euler sequence on projective space

Hartshorne, *Algebraic Geometry*, II.8, Theorem 8.13 (pp. 176–177): for `X = ℙⁿ_A` over
`Y = Spec A` the sequence `0 → Ω_{X/Y} → 𝒪_X(-1)^{n+1} → 𝒪_X → 0` is exact.

The maps `α`, `β` and `α ≫ β = 0` are in `EulerSequenceMaps`, and the chain rule on a standard
chart is in `EulerSequenceChainRule`. Here, on an open `W ⊆ D₊(x_i)`, the map
`ψ(s) = ∑_l (x_i s_l) d(x_l / x_i)` satisfies `α ∘ ψ = id` on the kernel of `β` and `ψ ∘ α = id`.
So `α` is injective and its image is the kernel of `β` locally. Gluing over the charts shows that
`α` is a kernel of `β`, and `β` is an epimorphism. The main result is `eulerSequence`.
-/

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry HomogeneousLocalization TopologicalSpace Opposite
  Hartshorne.ProjGradedModuleSheaf

noncomputable section

namespace Hartshorne.EulerSequence

variable {A : Type u} [CommRing A] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

local notation3 "𝒜" => grading A n
local notation3 "S" => MvPolynomial (Fin (n + 1)) A

/-! ### The inverse of `α` on a chart -/

/-- On an open `W ⊆ D₊(x_i)`, the map `𝒪(-1)^{n+1} → Ω`, `s ↦ ∑_l (x_i s_l) d(x_l / x_i)`,
inverse to `α` on the kernel of `β`. -/
def psi (i : Fin (n + 1)) (W : (Proj 𝒜).Opens) (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i))
    (s : (E A n).val.obj (op W)) : (Ω A n).val.obj (op W) :=
  ∑ l, secMul i (op W) (comp l s) • dd (yS i l W hW)

omit [CommRing A] in
theorem sum_smul_add' {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Fintype ι]
    (a b c : ι → R) (y : ι → M) (h : ∀ l, a l = b l + c l) :
    ∑ l, a l • y l = ∑ l, b l • y l + ∑ l, c l • y l := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by rw [h, add_smul]

omit [CommRing A] in
theorem sum_smul_mul' {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Fintype ι]
    (r : R) (a b : ι → R) (y : ι → M) (h : ∀ l, a l = r * b l) :
    ∑ l, a l • y l = r • ∑ l, b l • y l := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [h, mul_smul]

theorem comp_add (l : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ} (s t : (E A n).val.obj U) :
    comp l (s + t) = comp l s + comp l t :=
  map_add _ s t

theorem comp_smul (l : Fin (n + 1)) {U : (Proj 𝒜).Opensᵒᵖ}
    (r : (Proj 𝒜).ringCatSheaf.obj.obj U) (s : (E A n).val.obj U) :
    comp l (r • s) = r • comp l s :=
  map_smul _ r s

theorem psi_add (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (s t : (E A n).val.obj (op W)) :
    psi i W hW (s + t) = psi i W hW s + psi i W hW t :=
  sum_smul_add' (R := (Proj 𝒜).ringCatSheaf.obj.obj (op W)) _ _ _ _ fun l =>
    (congrArg (secMul i (op W)) (comp_add l s t)).trans (map_add _ _ _)

theorem psi_smul (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (r : (Proj 𝒜).ringCatSheaf.obj.obj (op W))
    (s : (E A n).val.obj (op W)) : psi i W hW (r • s) = r • psi i W hW s :=
  sum_smul_mul' (R := (Proj 𝒜).ringCatSheaf.obj.obj (op W)) r _ _ _ fun l =>
    (congrArg (secMul i (op W)) (comp_smul l r s)).trans ((secMul i (op W)).map_smul r _)

theorem psi_alpha_dd (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (f : (Proj 𝒜).presheaf.obj (op W)) :
    psi i W hW ((alpha A n).val.app (op W) (dd f)) = dd f := by
  refine Eq.trans ?_ (chain_rule i W hW f).symm
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [comp_alpha, alphaj_d]

/-! ### Injectivity of `α` -/

variable (A n) in
/-- The Kähler presheaf whose sheafification is `Ω`. -/
abbrev Pk : (Proj 𝒜).PresheafOfModules := Scheme.relativeDifferentialsPresheaf (toBase A n)

variable (A n) in
/-- The sheafification unit `Pk ⟶ Ω`. -/
abbrev eta := (PresheafOfModules.sheafificationAdjunction (𝟙 (Proj 𝒜).ringCatSheaf.obj)).unit.app
  (Pk A n)

/-- Every section of `Ω` is locally the image of a section of the Kähler presheaf. -/
theorem local_gen {U : (Proj 𝒜).Opensᵒᵖ} (ω : (Ω A n).val.obj U) {p : Proj 𝒜}
    (hp : p ∈ U.unop) :
    ∃ (V : (Proj 𝒜).Opens) (hV : V ≤ U.unop), p ∈ V ∧
      ∃ κ : (Pk A n).obj (op V), (Ω A n).val.map (homOfLE hV).op ω = (eta A n).app (op V) κ := by
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology (Proj 𝒜))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (Proj 𝒜)) (Pk A n).presheaf) ω
  obtain ⟨V, f, ⟨κ, hκ⟩, hpV⟩ := hmem p hp
  exact ⟨V, f.le, hpV, κ, hκ.symm⟩

theorem eta_d {U : (Proj 𝒜).Opensᵒᵖ} (b : (Proj 𝒜).presheaf.obj U) :
    (eta A n).app U (CommRingCat.KaehlerDifferential.d
      (f := (Scheme.inverseImageStructureSheafMap (toBase A n)).hom.app U) b) = dd b := rfl

theorem psi_zero (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) : psi i W hW 0 = 0 := by
  simp only [psi, map_zero, zero_smul, Finset.sum_const_zero]

theorem psi_alpha_eta (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (κ : (Pk A n).obj (op W)) :
    psi i W hW ((alpha A n).val.app (op W) ((eta A n).app (op W) κ)) = (eta A n).app (op W) κ := by
  let _ := ((Scheme.inverseImageStructureSheafMap (toBase A n)).hom.app (op W)).hom.toAlgebra
  have hκ : (κ : _root_.KaehlerDifferential
        ((Scheme.inverseImageStructureSheaf (toBase A n)).obj.obj (op W))
        ((Proj 𝒜).sheaf.obj.obj (op W))) ∈
      Submodule.span ((Proj 𝒜).sheaf.obj.obj (op W))
        (Set.range (_root_.KaehlerDifferential.D
          ((Scheme.inverseImageStructureSheaf (toBase A n)).obj.obj (op W))
          ((Proj 𝒜).sheaf.obj.obj (op W)))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hκ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact psi_alpha_dd i W hW b
  | zero =>
    rw [map_zero, map_zero, psi_zero]
  | add x y _ _ hx hy =>
    have e1 : (eta A n).app (op W) (x + y) =
        (eta A n).app (op W) x + (eta A n).app (op W) y := map_add _ x y
    have e2 : (alpha A n).val.app (op W) ((eta A n).app (op W) x + (eta A n).app (op W) y) =
        (alpha A n).val.app (op W) ((eta A n).app (op W) x) +
          (alpha A n).val.app (op W) ((eta A n).app (op W) y) := map_add _ _ _
    exact (congrArg (fun z => psi i W hW ((alpha A n).val.app (op W) z)) e1).trans
      ((congrArg (psi i W hW) e2).trans ((psi_add i W hW _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans e1.symm)))
  | smul r x _ hx =>
    have e1 : (eta A n).app (op W) (r • x) =
        (show (Proj 𝒜).ringCatSheaf.obj.obj (op W) from r) • (eta A n).app (op W) x :=
      ((eta A n).app (op W)).hom.map_smul _ _
    have e2 : (alpha A n).val.app (op W)
        ((show (Proj 𝒜).ringCatSheaf.obj.obj (op W) from r) • (eta A n).app (op W) x) =
        (show (Proj 𝒜).ringCatSheaf.obj.obj (op W) from r) •
          (alpha A n).val.app (op W) ((eta A n).app (op W) x) := map_smul _ _ _
    exact (congrArg (fun z => psi i W hW ((alpha A n).val.app (op W) z)) e1).trans
      ((congrArg (psi i W hW) e2).trans ((psi_smul i W hW _ _).trans
        ((congrArg _ hx).trans e1.symm)))

set_option maxHeartbeats 1600000 in
omit [CommRing A] in
theorem map_map_apply' {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens} (h₁ : V ≤ U)
    (h₂ : W ≤ V) (m : M.val.obj (op U)) :
    M.val.map (homOfLE h₂).op (M.val.map (homOfLE h₁).op m) =
      M.val.map (homOfLE (h₂.trans h₁)).op m :=
  (PresheafOfModules.map_comp_apply M.val _ _ m).symm

set_option maxHeartbeats 1600000 in
/-- **`α` is injective on sections.** -/
theorem alpha_app_eq_zero {U : (Proj 𝒜).Opensᵒᵖ} (ω : (Ω A n).val.obj U)
    (h : (alpha A n).val.app U ω = 0) : ω = 0 := by
  refine modules_ext (Ω A n) fun p hp => ?_
  obtain ⟨i, hi⟩ := exists_X_notMem (p : ProjectiveSpectrum 𝒜)
  obtain ⟨V, hVU, hpV, κ, hκ⟩ := local_gen ω hp
  have hV'V : V ⊓ Proj.basicOpen 𝒜 (MvPolynomial.X i) ≤ V := inf_le_left
  refine ⟨_, hV'V.trans hVU, ⟨hpV, hi⟩, ?_⟩
  have e1 : (Ω A n).val.map (homOfLE (hV'V.trans hVU)).op ω =
      (eta A n).app _ ((Pk A n).map (homOfLE hV'V).op κ) := by
    rw [← map_map_apply' (Ω A n) hVU hV'V, hκ]
    exact (PresheafOfModules.naturality_apply (eta A n) (homOfLE hV'V).op κ).symm
  have e2 : (alpha A n).val.app _ ((Ω A n).val.map (homOfLE (hV'V.trans hVU)).op ω) = 0 := by
    rw [PresheafOfModules.naturality_apply, h, map_zero]
  have e3 := psi_alpha_eta i _ inf_le_right ((Pk A n).map (homOfLE hV'V).op κ)
  rw [← e1, e2, psi_zero] at e3
  rw [map_zero]
  exact e3.symm

/-! ### `α ∘ ψ` is the identity on the kernel of `β` -/

local notation3 "at " p =>
  HomogeneousLocalization.AtPrime (grading A n)
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p))

local notation3 "Mt " p =>
  HomogeneousLocalizedModule (grading A n) (gradedTwist (grading A n) (-1))
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal p)).primeCompl

theorem toLoc_pD_frac (p : ProjectiveSpectrum 𝒜) (i k l : Fin (n + 1))
    (hp : MvPolynomial.X i ∉ p.asHomogeneousIdeal) :
    toLoc _ (pD A k (pt p) (Localization.mk (MvPolynomial.X l)
        (⟨MvPolynomial.X i, hp⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl))) =
      Localization.mk (MvPolynomial.X i * Pi.single (M := fun _ => S) k 1 l -
        MvPolynomial.X l * Pi.single (M := fun _ => S) k 1 i)
        (⟨MvPolynomial.X i, hp⟩ * ⟨MvPolynomial.X i, hp⟩ :
          p.asHomogeneousIdeal.toIdeal.primeCompl) := by
  rw [pD_mk, toLoc_mk, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]

/-- The pointwise identity behind `α ∘ ψ = id` on the kernel of `β`:
`∑_l (x_i σ_l) ∂(x_l/x_i)/∂x_k = σ_k` whenever `∑_l x_l σ_l = 0`. -/
theorem pt_alpha_psi (p : ProjectiveSpectrum 𝒜) (i : Fin (n + 1))
    (hp : MvPolynomial.X i ∉ p.asHomogeneousIdeal) (σ : Fin (n + 1) → Mt p)
    (hσ : ∑ l, ptMul l p (σ l) = 0) (y : Fin (n + 1) → at p)
    (hy : ∀ l, (y l).val = Localization.mk (MvPolynomial.X l)
      (⟨MvPolynomial.X i, hp⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl)) (k : Fin (n + 1)) :
    ∑ l, ptMul i p (σ l) • ptD k p (y l) = σ k := by
  obtain ⟨xi, hxi⟩ : ∃ xi : p.asHomogeneousIdeal.toIdeal.primeCompl,
      (xi : S) = MvPolynomial.X i := ⟨⟨_, hp⟩, rfl⟩
  have hu : algebraMap S (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)
      (MvPolynomial.X i) * Localization.mk 1 xi = 1 := by
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_mul, mul_one, ← hxi]
    exact Localization.mk_self xi
  have hmk : ∀ a : S, Localization.mk a (xi * xi) =
      algebraMap S _ a * Localization.mk 1 xi * Localization.mk 1 xi := by
    intro a
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, Localization.mk_mul, mul_one,
      mul_one, one_mul]
  have hσ' : ∑ l, algebraMap S (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)
      (MvPolynomial.X l) * toLoc _ (σ l).val = 0 := by
    have := congrArg HomogeneousLocalization.val hσ
    rw [← HomogeneousLocalization.algebraMap_apply, map_sum] at this
    simpa only [HomogeneousLocalization.algebraMap_apply, ptMul_val,
      HomogeneousLocalization.val_zero] using this
  apply HomogeneousLocalizedModule.ext
  apply toLoc_injective
  have hval : ∀ (f : Fin (n + 1) → Mt p),
      toLoc _ (∑ l, f l : Mt p).val = ∑ l, toLoc _ (f l).val := by
    intro f
    rw [← map_sum]
    congr 1
    exact Submodule.coe_sum _ _ _
  rw [hval]
  have hxi' : (⟨MvPolynomial.X i, hp⟩ : p.asHomogeneousIdeal.toIdeal.primeCompl) = xi :=
    Subtype.ext hxi.symm
  have hterm : ∀ l, toLoc _ (ptMul i p (σ l) • ptD k p (y l)).val =
      algebraMap S _ (MvPolynomial.X i) * toLoc _ (σ l).val *
        (algebraMap S _ (MvPolynomial.X i * Pi.single (M := fun _ => S) k 1 l -
          MvPolynomial.X l * Pi.single (M := fun _ => S) k 1 i) *
            Localization.mk 1 xi * Localization.mk 1 xi) := by
    intro l
    rw [HomogeneousLocalizedModule.val_smul, toLoc_smul, ptMul_val, ptD_val, hy]
    erw [toLoc_pD_frac p i k l hp]
    rw [hxi', hmk]
  rw [Finset.sum_congr rfl fun l _ => hterm l]
  simp only [map_sub, map_mul, Pi.single_apply, apply_ite (algebraMap S _), map_one, map_zero]
  have e : ∀ l, algebraMap S (Localization p.asHomogeneousIdeal.toIdeal.primeCompl)
      (MvPolynomial.X i) * toLoc _ (σ l).val *
      ((algebraMap S _ (MvPolynomial.X i) * (if l = k then 1 else 0) -
        algebraMap S _ (MvPolynomial.X l) * (if i = k then 1 else 0)) *
          Localization.mk 1 xi * Localization.mk 1 xi) =
      (algebraMap S _ (MvPolynomial.X i) * Localization.mk 1 xi) ^ 2 *
          (if l = k then toLoc _ (σ l).val else 0) -
        (if i = k then 1 else 0) * (algebraMap S _ (MvPolynomial.X i) * Localization.mk 1 xi) *
          Localization.mk 1 xi * (algebraMap S _ (MvPolynomial.X l) * toLoc _ (σ l).val) := by
    intro l
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hσ', Finset.sum_ite_eq', if_pos (Finset.mem_univ k), hu]
  ring

theorem O1_sum_apply {ι : Type*} (s : Finset ι) {U : (Proj 𝒜).Opensᵒᵖ}
    (f : ι → (O1 A n).val.obj U) (x : U.unop) :
    ((∑ i ∈ s, f i : (O1 A n).val.obj U) : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj U).1 x =
      ∑ i ∈ s, ((f i : (O1 A n).val.obj U) : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj U).1 x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

theorem alphaj_psi (i k : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (s : (E A n).val.obj (op W)) :
    (alphaj k).val.app (op W) (psi i W hW s) =
      ∑ l, secMul i (op W) (comp l s) • secD k (op W) (yS i l W hW) := by
  rw [psi, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, alphaj_d]

/-- **`α ∘ ψ = id` on the kernel of `β`**, on an open subset of `D₊(x_i)`. -/
theorem alpha_psi (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (s : (E A n).val.obj (op W))
    (hs : (beta A n).val.app (op W) s = 0) : (alpha A n).val.app (op W) (psi i W hW s) = s := by
  refine E_ext fun k => ?_
  rw [comp_alpha, alphaj_psi]
  refine section_ext (U := op W) fun x => ?_
  rw [O1_sum_apply]
  have hσ : ∑ l, ptMul l x.1 (((comp l s : (O1 A n).val.obj (op W)) :
      (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj (op W)).1 x) = 0 := by
    have := congrArg (fun t : (O0 A n).val.obj (op W) =>
      ((t : (Proj 𝒜).presheaf.obj (op W)).1 x)) ((beta_app s).symm.trans hs)
    simp only at this
    rw [O0_sum_apply] at this
    exact this
  exact pt_alpha_psi x.1 i (hW x.2) _ hσ _ (fun l => by
    erw [fracSec_val]
    congr 1
    exact Subtype.ext (pow_one _)) k

/-! ### Exactness -/

/-- `α` is injective on sections. -/
theorem alpha_injective (U : (Proj 𝒜).Opensᵒᵖ) : Function.Injective ((alpha A n).val.app U) := by
  intro ω ω' h
  rw [← sub_eq_zero]
  refine alpha_app_eq_zero _ ?_
  rw [map_sub, h, sub_self]

/-- `α` is a monomorphism. -/
instance mono_alpha : Mono (alpha A n) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective fun U => alpha_injective U

theorem map_beta_eq_zero {U V : (Proj 𝒜).Opensᵒᵖ} (f : U ⟶ V) {s : (E A n).val.obj U}
    (hs : (beta A n).val.app U s = 0) : (beta A n).val.app V ((E A n).val.map f s) = 0 := by
  rw [PresheafOfModules.naturality_apply, hs, map_zero]

set_option maxHeartbeats 1600000 in
/-- **Exactness in the middle**: every section of `𝒪(-1)^{n+1}` killed by `β` comes from `Ω`. -/
theorem exists_alpha_eq (U : (Proj 𝒜).Opensᵒᵖ) (s : (E A n).val.obj U)
    (hs : (beta A n).val.app U s = 0) : ∃ ω, (alpha A n).val.app U ω = s := by
  let V : Fin (n + 1) → (Proj 𝒜).Opens := fun i => U.unop ⊓ Proj.basicOpen 𝒜 (MvPolynomial.X i)
  let F : TopCat.Sheaf AddCommGrpCat.{u} (Proj 𝒜) := ⟨(Ω A n).presheaf, (Ω A n).isSheaf⟩
  let ω : ∀ i, (Ω A n).val.obj (op (V i)) := fun i =>
    psi i (V i) inf_le_right ((E A n).val.map (homOfLE inf_le_left).op s)
  have hω : ∀ i, (alpha A n).val.app _ (ω i) = (E A n).val.map (homOfLE inf_le_left).op s :=
    fun i => alpha_psi i (V i) inf_le_right _ (map_beta_eq_zero _ hs)
  have hcompat : TopCat.Presheaf.IsCompatible F.1 V ω := by
    intro i j
    apply alpha_injective
    change (alpha A n).val.app (op (V i ⊓ V j)) ((Ω A n).val.map (homOfLE inf_le_left).op (ω i)) =
      (alpha A n).val.app (op (V i ⊓ V j)) ((Ω A n).val.map (homOfLE inf_le_right).op (ω j))
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hω, hω,
      ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    rfl
  have hcover : U.unop ≤ iSup V := by
    intro p hp
    obtain ⟨i, hi⟩ := exists_X_notMem (p : ProjectiveSpectrum 𝒜)
    exact Opens.mem_iSup.2 ⟨i, hp, hi⟩
  obtain ⟨g, hg, -⟩ := F.existsUnique_gluing' V U.unop (fun i => homOfLE inf_le_left) hcover ω
    hcompat
  refine ⟨g, modules_ext (E A n) fun p hp => ?_⟩
  obtain ⟨i, hi⟩ := exists_X_notMem (p : ProjectiveSpectrum 𝒜)
  refine ⟨V i, inf_le_left, ⟨hp, hi⟩, ?_⟩
  rw [← PresheafOfModules.naturality_apply]
  have := hg i
  change (Ω A n).val.map (homOfLE inf_le_left).op g = ω i at this
  rw [this, hω]

/-- The lift through `α` of a map into the kernel of `β`, defined sectionwise. -/
def liftFun {Z : (Proj 𝒜).Modules} (k : Z ⟶ E A n) (hk : k ≫ beta A n = 0)
    (U : (Proj 𝒜).Opensᵒᵖ) (t : Z.val.obj U) : (Ω A n).val.obj U :=
  (exists_alpha_eq U (k.val.app U t) (app_eq_zero_of_eq_zero hk U t)).choose

theorem alpha_liftFun {Z : (Proj 𝒜).Modules} (k : Z ⟶ E A n) (hk : k ≫ beta A n = 0)
    (U : (Proj 𝒜).Opensᵒᵖ) (t : Z.val.obj U) :
    (alpha A n).val.app U (liftFun k hk U t) = k.val.app U t :=
  (exists_alpha_eq U (k.val.app U t) (app_eq_zero_of_eq_zero hk U t)).choose_spec

theorem liftFun_map {Z : (Proj 𝒜).Modules} (k : Z ⟶ E A n) (hk : k ≫ beta A n = 0)
    {U V : (Proj 𝒜).Opensᵒᵖ} (f : U ⟶ V) (t : Z.val.obj U) :
    liftFun k hk V (Z.val.map f t) = (Ω A n).val.map f (liftFun k hk U t) :=
  alpha_injective V (by
    rw [alpha_liftFun, PresheafOfModules.naturality_apply k.val,
      PresheafOfModules.naturality_apply (alpha A n).val, alpha_liftFun])

theorem liftFun_add {Z : (Proj 𝒜).Modules} (k : Z ⟶ E A n) (hk : k ≫ beta A n = 0)
    (U : (Proj 𝒜).Opensᵒᵖ) (t t' : Z.val.obj U) :
    liftFun k hk U (t + t') = liftFun k hk U t + liftFun k hk U t' :=
  alpha_injective U (by rw [alpha_liftFun, map_add, map_add, alpha_liftFun, alpha_liftFun])

theorem liftFun_zero {Z : (Proj 𝒜).Modules} (k : Z ⟶ E A n) (hk : k ≫ beta A n = 0)
    (U : (Proj 𝒜).Opensᵒᵖ) : liftFun k hk U 0 = 0 :=
  alpha_injective U (by rw [alpha_liftFun, map_zero, map_zero])

theorem liftFun_smul {Z : (Proj 𝒜).Modules} (k : Z ⟶ E A n) (hk : k ≫ beta A n = 0)
    (U : (Proj 𝒜).Opensᵒᵖ) (r : (Proj 𝒜).ringCatSheaf.obj.obj U) (t : Z.val.obj U) :
    liftFun k hk U (r • t) = r • liftFun k hk U t :=
  alpha_injective U (by rw [alpha_liftFun, map_smul, map_smul, alpha_liftFun])

/-- The lift through `α` of a map into the kernel of `β`. -/
def lift {Z : (Proj 𝒜).Modules} (k : Z ⟶ E A n) (hk : k ≫ beta A n = 0) : Z ⟶ Ω A n where
  val := PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := liftFun k hk U
          map_zero' := liftFun_zero k hk U
          map_add' := liftFun_add k hk U }
      naturality := fun _ _ f => by
        ext t
        exact liftFun_map k hk f t }
    (fun U r t => liftFun_smul k hk U r t)

theorem lift_alpha {Z : (Proj 𝒜).Modules} (k : Z ⟶ E A n) (hk : k ≫ beta A n = 0) :
    lift k hk ≫ alpha A n = k := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro t
  exact alpha_liftFun k hk U t

/-- `α` is a kernel of `β`. -/
def isLimitAlpha : Limits.IsLimit (Limits.KernelFork.ofι (alpha A n) alpha_beta) :=
  Limits.KernelFork.IsLimit.ofι' _ _ fun k hk => ⟨lift k hk, lift_alpha k hk⟩

/-- **The Euler sequence is short exact.** -/
theorem shortExact : (ShortComplex.mk (alpha A n) (beta A n) alpha_beta).ShortExact :=
  haveI := epi_beta (A := A) (n := n)
  { exact := ShortComplex.exact_of_f_is_kernel _ isLimitAlpha }

/-! ### The chart description -/

/-- `ψ ∘ α = id` on an open subset of `D₊(x_i)`. -/
theorem psi_alpha (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (ω : (Ω A n).val.obj (op W)) :
    psi i W hW ((alpha A n).val.app (op W) ω) = ω :=
  alpha_injective _ (alpha_psi i W hW _ (app_eq_zero_of_eq_zero alpha_beta _ ω))

/-- The coefficient of `d(x_l / x_i)` is recovered from `α` as `x_i α_l`. -/
theorem secMul_comp_alpha_sum (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i))
    (c : {l // l ≠ i} → (Proj 𝒜).ringCatSheaf.obj.obj (op W)) (l : {l // l ≠ i}) :
    secMul i (op W) (comp l.1 ((alpha A n).val.app (op W)
      (∑ m, c m • dd (yS i m.1 W hW)))) = c l := by
  rw [comp_alpha, map_sum, map_sum]
  refine (Finset.sum_eq_single l (fun m _ hm => ?_)
    (fun h => absurd (Finset.mem_univ l) h)).trans ?_
  · rw [map_smul, alphaj_d, map_smul]
    change c m * cD i l.1 (yS i m.1 W hW) = 0
    rw [cD_yS i l.1 m.1 l.2, if_neg (fun h => hm (Subtype.ext h).symm), mul_zero]
  · rw [map_smul, alphaj_d, map_smul]
    change c l * cD i l.1 (yS i l.1 W hW) = c l
    rw [cD_yS i l.1 l.1 l.2, if_pos rfl, mul_one]

omit [CommRing A] in
theorem sum_smul_subtype_ne {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] [Fintype ι]
    [DecidableEq ι] (a : ι → R) (y : ι → M) (i : ι) (hi : y i = 0) :
    ∑ l, a l • y l = ∑ l : {l // l ≠ i}, a l.1 • y l.1 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi, smul_zero, zero_add]

/-- **The chart description**: on an open subset `W` of the standard chart `D₊(x_i)`, the
sections of `Ω` form the free module on the differentials `d(x_l / x_i)`, `l ≠ i`. -/
theorem existsUnique_coeffs (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (ω : (Ω A n).val.obj (op W)) :
    ∃! c : {l // l ≠ i} → (Proj 𝒜).ringCatSheaf.obj.obj (op W),
      ω = ∑ l, c l • dd (yS i l.1 W hW) := by
  refine ⟨fun l => secMul i (op W) (comp l.1 ((alpha A n).val.app (op W) ω)), ?_, ?_⟩
  · have hi : dd (yS i i W hW) = 0 := by rw [yS_self]; exact dd_one
    exact (psi_alpha i W hW ω).symm.trans
      (sum_smul_subtype_ne (R := (Proj 𝒜).ringCatSheaf.obj.obj (op W)) _ _ i hi)
  · intro c hc
    funext l
    rw [hc, secMul_comp_alpha_sum]

/-- The value of `α(d(x_j / x_i))` on the chart `D₊(x_i)`: its `k`-th component is
`(x_i δ_{kj} - x_j δ_{ki}) / x_i²`. -/
theorem alpha_dd_yS (i j k : Fin (n + 1)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (p : ProjectiveSpectrum 𝒜) (hp : p ∈ W) :
    toLoc _ ((((comp k ((alpha A n).val.app (op W) (dd (yS i j W hW))) :
        (O1 A n).val.obj (op W)) : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj (op W)).1
          ⟨p, hp⟩).val) =
      Localization.mk (MvPolynomial.X i * Pi.single (M := fun _ => S) k 1 j -
        MvPolynomial.X j * Pi.single (M := fun _ => S) k 1 i)
        (⟨MvPolynomial.X i, hW hp⟩ * ⟨MvPolynomial.X i, hW hp⟩ :
          p.asHomogeneousIdeal.toIdeal.primeCompl) := by
  rw [comp_alpha, alphaj_d]
  erw [secD_apply, ptD_val, fracSec_val]
  rw [← toLoc_pD_frac p i k j (hW hp)]
  congr 3
  exact Subtype.ext (pow_one _)

variable (A n) in
/-- `ℙⁿ_A` is, by definition, the scheme `Proj A[x₀, …, xₙ]` used throughout this file. -/
theorem projectiveSpaceScheme_eq : projectiveSpaceScheme A n = Proj 𝒜 := rfl

variable (A n) in
/-- **The Euler sequence** on `X = ℙⁿ_A = Proj A[x₀, …, xₙ]` over `Y = Spec A`:
`0 → Ω_{X/Y} → 𝒪_X(-1)^{n+1} → 𝒪_X → 0` is short exact, where `β` sends `(s_j)` to
`∑ x_j s_j` and `α` is induced by the derivations `f ↦ ∂f/∂x_j`. On an open subset `W` of a
standard chart `D₊(x_i)`, `α` sends `d(x_j / x_i)` to the section with components
`(x_i δ_{kj} - x_j δ_{ki}) / x_i²`, and the sections of `Ω_{X/Y}` over `W` form the free module
on the `d(x_l / x_i)`, `l ≠ i`. -/
theorem eulerSequence :
    (ShortComplex.mk (alpha A n) (beta A n) alpha_beta).ShortExact ∧
    (∀ (i j k : Fin (n + 1)) (W : (Proj 𝒜).Opens)
      (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (p : ProjectiveSpectrum 𝒜) (hp : p ∈ W),
      toLoc _ ((((comp k ((alpha A n).val.app (op W) (dd (yS i j W hW))) :
        (O1 A n).val.obj (op W)) : (sheafInType 𝒜 (gradedTwist 𝒜 (-1))).1.obj (op W)).1
          ⟨p, hp⟩).val) =
        Localization.mk (MvPolynomial.X i * Pi.single (M := fun _ => S) k 1 j -
          MvPolynomial.X j * Pi.single (M := fun _ => S) k 1 i)
          (⟨MvPolynomial.X i, hW hp⟩ * ⟨MvPolynomial.X i, hW hp⟩ :
            p.asHomogeneousIdeal.toIdeal.primeCompl)) ∧
    (∀ (i : Fin (n + 1)) (W : (Proj 𝒜).Opens)
      (hW : W ≤ Proj.basicOpen 𝒜 (MvPolynomial.X i)) (ω : (Ω A n).val.obj (op W)),
      ∃! c : {l // l ≠ i} → (Proj 𝒜).ringCatSheaf.obj.obj (op W),
        ω = ∑ l, c l • dd (yS i l.1 W hW)) :=
  ⟨shortExact, alpha_dd_yS, existsUnique_coeffs⟩

end Hartshorne.EulerSequence
