/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Hartshorne.Scheme.SheafTensorAlgebras
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality

/-!
# The perfect exterior-power pairing

Hartshorne, *Algebraic Geometry*, II, Exercise 5.16(b) (printed p. 127).

Let `(X, 𝒪_X)` be a ringed space (a topological space `X` with a sheaf `R` of commutative rings;
`𝒪_X`-modules are `SheafOfModules (ringCatSheafOf R)`), and let `F` be an `𝒪_X`-module which is
locally free of rank `n` (`Hartshorne.Ringed.IsLocallyFreeOfRank F n`). For `r + s = n`,
multiplication in the exterior algebra gives a pairing
`exteriorPowerPairing F r s : ⋀^r F ⊗ ⋀^s F ⟶ ⋀^{r+s} F`, and we prove that it is perfect:

* `exteriorPowerPairingCurry_isIso`: the induced morphism
  `exteriorPowerPairingCurry F r s : ⋀^r F ⟶ ℋom(⋀^s F, ⋀^{r+s} F)`, `a ↦ (b ↦ a ∧ b)`
  (`exteriorPowerPairingCurry_eval`), is an isomorphism;
* `exteriorPowerPerfectPairingIso`: hence `⋀^r F ≅ ℋom(⋀^s F, ⋀^n F)`;
* `exteriorPowerDualTensorIso`: equivalently `⋀^r F ≅ (⋀^s F)^∨ ⊗ ⋀^n F`.

The proof is local. If `(e_i)_{i ∈ I}` is a frame of `F` over `U` (`Hartshorne.Ringed.IsLocalFrame`),
then for every open `V ⊆ U` the module `F(V)` is free with basis `e_i|_V` (`frameBasis`), so the
presheaf `V ↦ ⋀^k F(V)` has the exterior products `e_K`, `K ⊆ I` of size `k`, as a presheaf frame
over `U` (`isPresheafFrame_exteriorPower`, using Mathlib's `Module.Basis.exteriorPower`). A presheaf
frame survives sheafification: on opens inside `U` the unit of sheafification is bijective and the
images of the frame form a frame of the sheafification (`IsPresheafFrame.sheafifyUnit_bijective`,
`IsPresheafFrame.isLocalFrame`); in particular the `e_K` form a frame of `⋀^k F`
(`isLocalFrame_exteriorPowerFrame`). On sections over `V ⊆ U` the pairing is then the pairing of
exterior powers of the free module `F(V)`, which is perfect because `e_K ∧ e_J` is `±e_I` if `K` is
the complement of `J` and `0` otherwise (`bijective_μ_basis`).
-/

universe u

open CategoryTheory TopologicalSpace Opposite
open scoped TensorProduct

namespace Hartshorne

namespace ExteriorPerfectPairing

section Algebra

open Module Set Set.powersetCard exteriorPower

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
  {I : Type*} [LinearOrder I] [Fintype I] {r s : ℕ}

omit [LinearOrder I] in
lemma powersetCard_subsingleton (hrs : r + s = Fintype.card I) :
    Subsingleton (powersetCard I (r + s)) := by
  classical
  refine ⟨fun t t' => (eq_iff_subset).2 ?_⟩
  have : (t' : Finset I) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [card_eq t', hrs])
  rw [this]
  exact Finset.subset_univ _

omit [LinearOrder I] in
lemma disjoint_iff_eq_compl [DecidableEq I] (hrs : r + s = Fintype.card I)
    (K : powersetCard I r) (J : powersetCard I s) :
    Disjoint K.val J.val ↔ K = compl hrs J := by
  constructor
  · intro h
    refine (eq_iff_subset).2 fun i hi => ?_
    rw [coe_compl, Finset.mem_compl]
    exact Finset.disjoint_left.1 h hi
  · rintro rfl
    exact disjoint_compl_left (a := (J : Finset I))

/-- The sign `±1` relating `e_{Jᶜ} ∧ e_J` to the top exterior product. -/
noncomputable def complSign [DecidableEq I] (hrs : r + s = Fintype.card I)
    (J : powersetCard I s) : A :=
  (((permOfDisjoint ((disjoint_iff_eq_compl hrs (compl hrs J) J).2 rfl)).sign : ℤ) : A)

lemma complSign_mul_self [DecidableEq I] (hrs : r + s = Fintype.card I) (J : powersetCard I s) :
    complSign (A := A) hrs J * complSign hrs J = 1 := by
  rw [complSign, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

variable (μ : ⋀[A]^r M →ₗ[A] ⋀[A]^s M →ₗ[A] ⋀[A]^(r + s) M)
  (hμ : ∀ x y, (μ x y : ExteriorAlgebra A M) = (x : ExteriorAlgebra A M) * y)
include hμ

/-- The products of the basis vectors of `⋀^r M` and `⋀^s M` attached to a basis of `M`. -/
lemma μ_basis [DecidableEq I] (b : Module.Basis I A M) (hrs : r + s = Fintype.card I)
    (t : powersetCard I (r + s)) (K : powersetCard I r) (J : powersetCard I s) :
    μ (ιMulti_family A r b K) (ιMulti_family A s b J) =
      if K = compl hrs J then complSign (A := A) hrs J • ιMulti_family A (r + s) b t else 0 := by
  have := powersetCard_subsingleton hrs
  apply Subtype.val_injective
  rw [hμ]
  split_ifs with hK
  · subst hK
    have hd := (disjoint_iff_eq_compl hrs (compl hrs J) J).2 rfl
    rw [ιMulti_family_apply_coe, ιMulti_family_apply_coe,
      ExteriorAlgebra.ιMulti_family_mul_of_disjoint A b _ _ hd, Subsingleton.elim (disjUnion hd) t,
      Submodule.coe_smul, complSign, Int.cast_smul_eq_zsmul, ← Units.smul_def]
    rfl
  · rw [ιMulti_family_apply_coe, ιMulti_family_apply_coe,
      ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint A b _ _
        (fun hd => hK ((disjoint_iff_eq_compl hrs K J).1 hd))]
    rfl

lemma μ_basis_right [DecidableEq I] (b : Module.Basis I A M) (hrs : r + s = Fintype.card I)
    (t : powersetCard I (r + s)) (x : ⋀[A]^r M) (J : powersetCard I s) :
    μ x (ιMulti_family A s b J) =
      ((b.exteriorPower r).repr x (compl hrs J) * complSign (A := A) hrs J) •
        ιMulti_family A (r + s) b t := by
  conv_lhs => rw [← (b.exteriorPower r).sum_repr x]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single (compl hrs J)]
  · rw [map_smul, LinearMap.smul_apply, basis_apply, μ_basis μ hμ b hrs t, if_pos rfl, smul_smul]
  · intro K _ hK
    rw [map_smul, LinearMap.smul_apply, basis_apply, μ_basis μ hμ b hrs t, if_neg hK, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The perfect pairing for a finite free module.** For a module `M` with a basis indexed by a
finite linearly ordered set `I` with `r + s = |I|`, the map
`⋀^r M → (⋀^{r+s} M)^{(subsets of I of size s)}`, `x ↦ (x ∧ e_J)_J`, is bijective. -/
theorem bijective_μ_basis (b : Module.Basis I A M) (hrs : r + s = Fintype.card I) :
    Function.Bijective (fun x : ⋀[A]^r M => fun J : powersetCard I s =>
      μ x (ιMulti_family A s b J)) := by
  classical
  have := powersetCard_subsingleton hrs
  obtain ⟨t⟩ : Nonempty (powersetCard I (r + s)) := by
    obtain ⟨J⟩ : Nonempty (powersetCard I s) := by
      obtain ⟨J, -, hJ⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset I)) (n := s)
        (by rw [Finset.card_univ]; omega)
      exact ⟨⟨J, mem_iff.2 hJ⟩⟩
    exact ⟨disjUnion ((disjoint_iff_eq_compl hrs (compl hrs J) J).2 rfl)⟩
  let B := b.exteriorPower (r + s)
  have hB : ∀ c : A, B.repr (c • ιMulti_family A (r + s) b t) t = c := fun c => by
    rw [← basis_apply, map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_eq_same]
  have hBt : ∀ d : ⋀[A]^(r + s) M, B.repr d t • ιMulti_family A (r + s) b t = d := fun d => by
    conv_rhs => rw [← B.sum_repr d]
    rw [Fintype.sum_subsingleton _ t, basis_apply]
  refine ⟨fun x y hxy => ?_, fun g => ?_⟩
  · apply (b.exteriorPower r).repr.injective
    ext K
    have h := congrFun hxy ((compl hrs).symm K)
    simp only at h
    rw [μ_basis_right μ hμ b hrs t, μ_basis_right μ hμ b hrs t, Equiv.apply_symm_apply] at h
    have h' := congrArg (fun d => B.repr d t) h
    simp only [hB] at h'
    have := congrArg (· * complSign (A := A) hrs ((compl hrs).symm K)) h'
    simpa only [mul_assoc, complSign_mul_self, mul_one] using this
  · refine ⟨(b.exteriorPower r).equivFun.symm
      (fun K => B.repr (g ((compl hrs).symm K)) t * complSign hrs ((compl hrs).symm K)), ?_⟩
    funext J
    simp only
    rw [μ_basis_right μ hμ b hrs t, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
      Equiv.symm_apply_apply, mul_assoc, complSign_mul_self, mul_one, hBt]

end Algebra

section Frames

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

open SheafAlgebraOperations ModuleSheafTensor Ringed

set_option hygiene false in
/-- Sections of the structure sheaf, as the rings over which presheaves of modules take values. -/
local notation3 "𝒪ᵣ(" V ")" => (R.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)

variable (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) {κ : Type*} [Fintype κ]

/-- For sections `f_k` of a presheaf of modules over `U` and an open `V ⊆ U`, the map
`(a_k) ↦ ∑ a_k f_k|_V`. -/
noncomputable def presheafFrameMap {U : Opens X} (f : κ → P.obj (op U)) {V : Opens X}
    (h : V ≤ U) : (κ → 𝒪ᵣ(V)) →ₗ[𝒪ᵣ(V)] P.obj (op V) :=
  Fintype.linearCombination 𝒪ᵣ(V) (fun k => P.restrictₛₗ (homOfLE h).op (f k))

lemma presheafFrameMap_apply {U : Opens X} (f : κ → P.obj (op U)) {V : Opens X} (h : V ≤ U)
    (a : κ → 𝒪ᵣ(V)) :
    presheafFrameMap P f h a = ∑ k, a k • P.restrictₛₗ (homOfLE h).op (f k) :=
  Fintype.linearCombination_apply _ _ _

/-- A finite family of sections of a presheaf of modules over `U` is a *presheaf frame* if on
every open `V ⊆ U` every section is uniquely a linear combination of the restricted family. -/
def IsPresheafFrame {U : Opens X} (f : κ → P.obj (op U)) : Prop :=
  ∀ (V : Opens X) (h : V ≤ U), Function.Bijective (presheafFrameMap P f h)

variable {P}

lemma presheafFrameMap_restrict {U : Opens X} (f : κ → P.obj (op U)) {V W : Opens X}
    (h : V ≤ U) (i : W ⟶ V) (a : κ → 𝒪ᵣ(V)) :
    P.restrictₛₗ i.op (presheafFrameMap P f h a) =
      presheafFrameMap P f ((leOfHom i).trans h)
        (fun k => ((R.obj ⋙ forget₂ CommRingCat RingCat).map i.op).hom (a k)) := by
  rw [presheafFrameMap_apply, presheafFrameMap_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, ← SheafTensorOperations.restrictₛₗ_comp]
  rfl

namespace IsPresheafFrame

variable {U : Opens X} {f : κ → P.obj (op U)} (hf : IsPresheafFrame P f)
include hf

/-- On opens inside `U`, the unit of sheafification is injective. -/
lemma sheafifyUnit_injective {V : Opens X} (hV : V ≤ U) :
    Function.Injective ((sheafifyUnit P).app (op V)) := by
  intro p q hpq
  obtain ⟨a, rfl⟩ := (hf V hV).2 p
  obtain ⟨b, rfl⟩ := (hf V hV).2 q
  have hloc : ∀ x : V, ∃ (W : Opens X) (_ : x.1 ∈ W) (i : W ⟶ V),
      P.restrictₛₗ i.op (presheafFrameMap P f hV a) =
        P.restrictₛₗ i.op (presheafFrameMap P f hV b) := by
    intro x
    have h1 : sectionGerm P x.1 V x.2 (presheafFrameMap P f hV a) =
        sectionGerm P x.1 V x.2 (presheafFrameMap P f hV b) := by
      apply (stalkMap_sheafifyUnit_bijective P x.1).1
      rw [Ringed.stalkAddMap_germ, Ringed.stalkAddMap_germ, hpq]
    obtain ⟨W, hxW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq P.presheaf x.1 x.2 x.2 _ _ h1
    obtain rfl : iV = iU := Subsingleton.elim _ _
    exact ⟨W, hxW, iV, e⟩
  choose W hxW iW hW using hloc
  have hab : a = b := by
    funext k
    refine TopCat.Sheaf.eq_of_locally_eq' (F := R) W V iW
      (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxW _⟩) _ _ fun x => ?_
    have h2 := hW x
    rw [presheafFrameMap_restrict, presheafFrameMap_restrict] at h2
    exact congrFun ((hf (W x) _).1 h2) k
  rw [hab]

/-- On opens inside `U`, the unit of sheafification is surjective. -/
lemma sheafifyUnit_surjective {V : Opens X} (hV : V ≤ U) :
    Function.Surjective ((sheafifyUnit P).app (op V)) := by
  intro s
  have hloc := fun x : V => exists_unit_eq_map P s x.2
  choose W hxW iW p hp using hloc
  have hWU : ∀ x, W x ≤ U := fun x => (leOfHom (iW x)).trans hV
  let c : ∀ x : V, κ → 𝒪ᵣ(W x) := fun x =>
    (LinearEquiv.ofBijective _ (hf (W x) (hWU x))).symm (p x)
  have hc : ∀ x, presheafFrameMap P f (hWU x) (c x) = p x := fun x =>
    LinearEquiv.apply_ofBijective_symm_apply _ (p x)
  have hcompat : ∀ k, TopCat.Presheaf.IsCompatible R.obj W (fun x => c x k) := by
    intro k x y
    have hle : W x ⊓ W y ≤ U := inf_le_left.trans (hWU x)
    have hp' : P.restrictₛₗ (Opens.infLELeft (W x) (W y)).op (p x) =
        P.restrictₛₗ (Opens.infLERight (W x) (W y)).op (p y) := by
      apply hf.sheafifyUnit_injective hle
      rw [PresheafOfModules.restrictₛₗ_apply, PresheafOfModules.restrictₛₗ_apply,
        PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, hp, hp,
        ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
      rfl
    rw [← hc x, ← hc y, presheafFrameMap_restrict, presheafFrameMap_restrict] at hp'
    exact congrFun ((hf _ _).1 hp') k
  choose b hb using fun k => (TopCat.Sheaf.existsUnique_gluing' (F := R) W V iW
    (fun y hy => Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxW _⟩) (fun x => c x k) (hcompat k)).exists
  refine ⟨presheafFrameMap P f hV b, ?_⟩
  refine sheaf_section_ext _ _ _ fun x hx => ⟨W ⟨x, hx⟩, hxW _, iW _, ?_⟩
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.restrictₛₗ_apply,
    presheafFrameMap_restrict, ← hp, ← hc]
  congr 2
  funext k
  exact hb k ⟨x, hx⟩

lemma sheafifyUnit_bijective {V : Opens X} (hV : V ≤ U) :
    Function.Bijective ((sheafifyUnit P).app (op V)) :=
  ⟨hf.sheafifyUnit_injective hV, hf.sheafifyUnit_surjective hV⟩

/-- **A presheaf frame becomes a frame of the sheafification.** -/
theorem isLocalFrame :
    IsLocalFrame (sheafify P) U (fun k => (sheafifyUnit P).app (op U) (f k)) := by
  intro V h
  have e : ∀ a, localFrameMap (sheafify P) (fun k => (sheafifyUnit P).app (op U) (f k)) h a =
      (sheafifyUnit P).app (op V) (presheafFrameMap P f h a) := by
    intro a
    refine (localFrameMap_apply _ _ h a).trans ?_
    rw [presheafFrameMap_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    exact congrArg (fun y => a k • y)
      (PresheafOfModules.naturality_apply (sheafifyUnit P) (homOfLE h).op (f k)).symm
  obtain ⟨hi, hs⟩ := (hf.sheafifyUnit_bijective h).comp (hf V h)
  refine ⟨fun a b hab => hi ((e a).symm.trans (hab.trans (e b))), fun y => ?_⟩
  obtain ⟨a, ha⟩ := hs y
  exact ⟨a, (e a).trans ha⟩

end IsPresheafFrame

end Frames


section ExteriorFrames

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

open SheafAlgebraOperations Ringed SheafTensorOperations

set_option hygiene false in
/-- Sections of the structure sheaf, as the rings over which presheaves of modules take values. -/
local notation3 "𝒪ᵣ(" V ")" => (R.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

variable (F : SheafOfModules.{u} (ringCatSheafOf R)) {ι : Type*} [Fintype ι] {U : Opens X}
  {e : ι → F.val.obj (op U)}

/-- The basis of `F(V)`, `V ⊆ U`, given by a frame of `F` over `U`. -/
noncomputable def frameBasis (hF : IsLocalFrame F U e) {V : Opens X}
    (h : V ≤ U) : Module.Basis ι 𝒪ᵣ(V) (F.val.obj (op V)) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective
    (Fintype.linearCombination 𝒪ᵣ(V) (fun i => F.val.restrictₛₗ (homOfLE h).op (e i)))
    (hF V h)).symm

lemma frameBasis_apply [DecidableEq ι] (hF : IsLocalFrame F U e) {V : Opens X} (h : V ≤ U)
    (i : ι) : frameBasis F hF h i = F.val.restrictₛₗ (homOfLE h).op (e i) := by
  rw [frameBasis, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
  exact (Fintype.linearCombination_apply_single _ _ _ _).trans (one_smul _ _)

omit [Fintype ι] in
lemma exteriorPowerPresheaf_restrictₛₗ_ιMulti_family [LinearOrder ι] (k : ℕ) {U V : Opens X}
    (i : op U ⟶ op V) (v : ι → F.val.obj (op U)) (K : Set.powersetCard ι k) :
    (moduleSheafExteriorPowerPresheaf k F).restrictₛₗ i (exteriorPower.ιMulti_family 𝒪ᵣ(U) k v K) =
      exteriorPower.ιMulti_family 𝒪ᵣ(V) k (fun j => F.val.restrictₛₗ i (v j)) K :=
  exteriorPowerMap_ιMulti k _ (F.val.restrictₛₗ i) _

/-- **The exterior products of a frame form a presheaf frame of the exterior power presheaf.** -/
theorem isPresheafFrame_exteriorPower [LinearOrder ι] [DecidableEq ι] (hF : IsLocalFrame F U e)
    (k : ℕ) :
    IsPresheafFrame (moduleSheafExteriorPowerPresheaf k F)
      (exteriorPower.ιMulti_family 𝒪ᵣ(U) k (M := F.val.obj (op U)) e) := by
  intro V h
  let B := (frameBasis F hF h).exteriorPower k
  have hb : (fun j => F.val.restrictₛₗ (homOfLE h).op (e j)) = ⇑(frameBasis F hF h) :=
    funext fun j => (frameBasis_apply F hF h j).symm
  have key : ∀ a, presheafFrameMap (moduleSheafExteriorPowerPresheaf k F)
      (exteriorPower.ιMulti_family 𝒪ᵣ(U) k (M := F.val.obj (op U)) e) h a = B.equivFun.symm a := by
    intro a
    refine (presheafFrameMap_apply _ _ h a).trans ?_
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun K _ => congrArg (a K • ·) ?_
    refine (exteriorPowerPresheaf_restrictₛₗ_ιMulti_family F k _ e K).trans ?_
    rw [exteriorPower.basis_apply, hb]
  exact ⟨fun a b hab => B.equivFun.symm.injective ((key a).symm.trans (hab.trans (key b))),
    fun y => ⟨B.equivFun y, (key _).trans (B.equivFun.symm_apply_apply y)⟩⟩

/-- The exterior products `e_K = e_{k₁} ∧ ⋯ ∧ e_{k_k}` of a family of sections, `K` running over the
subsets of size `k`, as sections of `⋀^k F`. -/
noncomputable def exteriorPowerFrame [LinearOrder ι] (k : ℕ) (e : ι → F.val.obj (op U)) :
    Set.powersetCard ι k → Γ(moduleSheafExteriorPower k F, U) := fun K =>
  (moduleSheafExteriorPowerUnit k F).app (op U)
    (exteriorPower.ιMulti_family 𝒪ᵣ(U) k (M := F.val.obj (op U)) e K)

/-- **Frames of exterior powers.** If `(e_i)` is a frame of `F` over `U`, the exterior products
`e_K` form a frame of `⋀^k F` over `U`. -/
theorem isLocalFrame_exteriorPowerFrame [LinearOrder ι] [DecidableEq ι] (hF : IsLocalFrame F U e)
    (k : ℕ) : IsLocalFrame (moduleSheafExteriorPower k F) U (exteriorPowerFrame F k e) :=
  (isPresheafFrame_exteriorPower F hF k).isLocalFrame

/-- The exterior powers of a locally free module of finite rank admit frames locally. -/
theorem exists_isLocalFrame_exteriorPower (hF : IsFiniteLocallyFree F) (k : ℕ) (x : X) :
    ∃ (U : Opens X) (ι : Type u) (_ : Fintype ι) (e : ι → Γ(moduleSheafExteriorPower k F, U)),
      x ∈ U ∧ IsLocalFrame (moduleSheafExteriorPower k F) U e := by
  classical
  obtain ⟨U, hxU, n, ⟨α⟩⟩ := hF x
  exact ⟨U, Set.powersetCard (ULift.{u} (Fin n)) k, inferInstance, _, hxU,
    isLocalFrame_exteriorPowerFrame F (isLocalFrame_of_over_iso α) k⟩

end ExteriorFrames

section Pairing

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

open SheafAlgebraOperations Ringed SheafTensorOperations

set_option hygiene false in
/-- Sections of the structure sheaf, as the rings over which presheaves of modules take values. -/
local notation3 "𝒪ᵣ(" V ")" => (R.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op V)

/-- Sections of a module sheaf over an open, as an abelian group. -/
local notation3 "Γ(" M ", " U ")" => (PresheafOfModules.presheaf (SheafOfModules.val M)).obj
  (Opposite.op U)

variable (F : SheafOfModules.{u} (ringCatSheafOf R)) (r s : ℕ)

/-- The multiplication `⋀^r F × ⋀^s F → ⋀^{r+s} F` of the exterior algebra of `F`, as a bilinear
morphism. -/
noncomputable def exteriorPowerPairingBilinear :
    ModuleSheafBilinear (moduleSheafExteriorPower r F) (moduleSheafExteriorPower s F)
      (moduleSheafExteriorPower (r + s) F) where
  app := (moduleSheafExteriorPowerMul r F s).app
  naturality := (moduleSheafExteriorPowerMul r F s).naturality

/-- **The exterior-power pairing** `⋀^r F ⊗ ⋀^s F ⟶ ⋀^{r+s} F` induced by multiplication in the
exterior algebra `⋀(F)`: `a ⊗ b ↦ a ∧ b`. -/
noncomputable def exteriorPowerPairing :
    moduleSheafTensor (moduleSheafExteriorPower r F) (moduleSheafExteriorPower s F) ⟶
      moduleSheafExteriorPower (r + s) F :=
  (moduleSheafTensorHomEquiv _ _ _).symm (exteriorPowerPairingBilinear F r s)

theorem exteriorPowerPairing_tmul (U : (Opens X)ᵒᵖ) (a : (moduleSheafExteriorPower r F).val.obj U)
    (b : (moduleSheafExteriorPower s F).val.obj U) :
    (exteriorPowerPairing F r s).val.app U ((moduleSheafTensorBilinear _ _).app U a b) =
      (moduleSheafExteriorPowerMul r F s).app U a b :=
  congrArg (fun β : ModuleSheafBilinear _ _ _ => β.app U a b)
    ((moduleSheafTensorHomEquiv_apply (exteriorPowerPairing F r s)).symm.trans
      (Equiv.apply_symm_apply (moduleSheafTensorHomEquiv _ _ _) _))

/-- The bilinear morphism `(b, a) ↦ a ∧ b`, `b ∈ ⋀^s F`, `a ∈ ⋀^r F`. -/
noncomputable def exteriorPowerPairingFlip :
    ModuleSheafBilinear (moduleSheafExteriorPower s F) (moduleSheafExteriorPower r F)
      (moduleSheafExteriorPower (r + s) F) where
  app U := ((moduleSheafExteriorPowerMul r F s).app U).flip
  naturality i b a := (moduleSheafExteriorPowerMul r F s).naturality i a b

/-- The morphism `⋀^r F ⟶ ℋom(⋀^s F, ⋀^{r+s} F)`, `a ↦ (b ↦ a ∧ b)`, induced by the
exterior-power pairing (`exteriorPowerPairingCurry_eval`). -/
noncomputable def exteriorPowerPairingCurry :
    moduleSheafExteriorPower r F ⟶
      moduleSheafHom (moduleSheafExteriorPower s F) (moduleSheafExteriorPower (r + s) F) :=
  bilinearCurry (exteriorPowerPairingFlip F r s)

/-- The morphism `exteriorPowerPairingCurry` sends a section `a` of `⋀^r F` over `U` to the local
morphism `b ↦ a|_V ∧ b` given by the exterior-power pairing. -/
theorem exteriorPowerPairingCurry_eval {U : Opens X} (a : Γ(moduleSheafExteriorPower r F, U))
    {V : Opens X} (h : V ≤ U) (b : Γ(moduleSheafExteriorPower s F, V)) :
    moduleSheafHomEval (sectionsMap (exteriorPowerPairingCurry F r s) U a) h b =
      (exteriorPowerPairing F r s).val.app (op V) ((moduleSheafTensorBilinear _ _).app (op V)
        ((moduleSheafExteriorPower r F).val.presheaf.map (homOfLE h).op a) b) :=
  (exteriorPowerPairing_tmul F r s (op V) _ b).symm

variable {F r s}

/-- Over an open `V` inside an open `U` carrying a frame of `F` of size `r + s`, the morphism
`⋀^r F ⟶ ℋom(⋀^s F, ⋀^{r+s} F)` is bijective on sections. -/
theorem exteriorPowerPairingCurry_bijective {ι : Type*} [Fintype ι] [LinearOrder ι]
    [DecidableEq ι] {U : Opens X} {e : ι → F.val.obj (op U)} (hF : IsLocalFrame F U e)
    (hrs : r + s = Fintype.card ι) {V : Opens X} (h : V ≤ U) :
    Function.Bijective (sectionsMap (exteriorPowerPairingCurry F r s) V) := by
  have hr := (isPresheafFrame_exteriorPower F hF r).sheafifyUnit_bijective h
  have hn := (isPresheafFrame_exteriorPower F hF (r + s)).sheafifyUnit_bijective h
  have hL := (isLocalFrame_exteriorPowerFrame F hF s).localFrameEval_bijective
    (G := moduleSheafExteriorPower (r + s) F) h
  have hT := bijective_μ_basis
    ((moduleSheafExteriorAlgebraPresheaf_isGraded F).presheafMulApp r s (op V))
    (fun x y => (moduleSheafExteriorAlgebraPresheaf_isGraded F).ι_presheafMulApp r s (op V) x y)
    (frameBasis F hF h) hrs
  have key : ∀ x, localFrameEval (exteriorPowerFrame F s e) h
      (sectionsMap (exteriorPowerPairingCurry F r s) V
        ((sheafifyUnit (moduleSheafExteriorPowerPresheaf r F)).app (op V) x)) =
      fun J => (sheafifyUnit (moduleSheafExteriorPowerPresheaf (r + s) F)).app (op V)
        ((moduleSheafExteriorAlgebraPresheaf_isGraded F).presheafMulApp r s (op V) x
          (exteriorPower.ιMulti_family 𝒪ᵣ(V) s (frameBasis F hF h) J)) := by
    intro x
    funext J
    have h1 : (moduleSheafExteriorPower s F).val.map (homOfLE h).op (exteriorPowerFrame F s e J) =
        (sheafifyUnit (moduleSheafExteriorPowerPresheaf s F)).app (op V)
          (exteriorPower.ιMulti_family 𝒪ᵣ(V) s (frameBasis F hF h) J) := by
      refine (PresheafOfModules.naturality_apply
        (sheafifyUnit (moduleSheafExteriorPowerPresheaf s F)) (homOfLE h).op _).symm.trans ?_
      congr 1
      refine (exteriorPowerPresheaf_restrictₛₗ_ιMulti_family F s _ e J).trans ?_
      rw [show (fun j => F.val.restrictₛₗ (homOfLE h).op (e j)) = ⇑(frameBasis F hF h) from
        funext fun j => (frameBasis_apply F hF h j).symm]
    have h2 : (moduleSheafExteriorPower r F).val.map (homOfLE (le_refl V)).op
        ((sheafifyUnit (moduleSheafExteriorPowerPresheaf r F)).app (op V) x) =
        (sheafifyUnit (moduleSheafExteriorPowerPresheaf r F)).app (op V) x :=
      restrictₛₗ_id (moduleSheafExteriorPower r F).val (op V) _
    change (moduleSheafExteriorPowerMul r F s).app (op V)
        ((moduleSheafExteriorPower r F).val.map (homOfLE (le_refl V)).op
          ((sheafifyUnit (moduleSheafExteriorPowerPresheaf r F)).app (op V) x))
        ((moduleSheafExteriorPower s F).val.map (homOfLE h).op (exteriorPowerFrame F s e J)) = _
    rw [h1, h2]
    exact (moduleSheafExteriorAlgebraPresheaf_isGraded F).sheafMul_unit r s (op V) x _
  have hcomp : Function.Bijective (fun x => localFrameEval (exteriorPowerFrame F s e) h
      (sectionsMap (exteriorPowerPairingCurry F r s) V
        ((sheafifyUnit (moduleSheafExteriorPowerPresheaf r F)).app (op V) x))) := by
    rw [funext key]
    exact hn.comp_left.comp hT
  have h1 : Function.Bijective (fun x => sectionsMap (exteriorPowerPairingCurry F r s) V
      ((sheafifyUnit (moduleSheafExteriorPowerPresheaf r F)).app (op V) x)) :=
    (Function.Bijective.of_comp_iff' hL _).1 hcomp
  exact (Function.Bijective.of_comp_iff _ hr).1 h1

variable (F r s)

/-- **Hartshorne II, Exercise 5.16(b): the perfect exterior-power pairing.** Let `F` be a locally
free `𝒪_X`-module of rank `n` and `r + s = n`. Then the pairing `⋀^r F ⊗ ⋀^s F ⟶ ⋀^n F` induced by
multiplication is perfect: the induced morphism `⋀^r F ⟶ ℋom(⋀^s F, ⋀^n F)`, `a ↦ (b ↦ a ∧ b)`, is
an isomorphism. -/
theorem exteriorPowerPairingCurry_isIso {n : ℕ} (hrs : r + s = n)
    (hF : IsLocallyFreeOfRank F n) : IsIso (exteriorPowerPairingCurry F r s) :=
  modules_isIso_of_locally_bijective _ fun x => by
    classical
    obtain ⟨U, hxU, ⟨α⟩⟩ := hF x
    exact ⟨U, hxU, fun V h => exteriorPowerPairingCurry_bijective (isLocalFrame_of_over_iso α)
      (by rw [Fintype.card_ulift, Fintype.card_fin, hrs]) h⟩

/-- **The perfect pairing as an isomorphism** `⋀^r F ≅ ℋom(⋀^s F, ⋀^n F)` for `F` locally free of
rank `n` and `r + s = n`; it is `exteriorPowerPairingCurry`, followed by the identification
`⋀^{r+s} F = ⋀^n F`. -/
noncomputable def exteriorPowerPerfectPairingIso {n : ℕ} (hrs : r + s = n)
    (hF : IsLocallyFreeOfRank F n) :
    moduleSheafExteriorPower r F ≅
      moduleSheafHom (moduleSheafExteriorPower s F) (moduleSheafExteriorPower n F) :=
  haveI := exteriorPowerPairingCurry_isIso F r s hrs hF
  asIso (exteriorPowerPairingCurry F r s) ≪≫ eqToIso (by rw [hrs])

/-- **Hartshorne II, Exercise 5.16(b), dual form.** For `F` locally free of rank `n` and
`r + s = n`, `⋀^r F ≅ (⋀^s F)^∨ ⊗ ⋀^n F`: the perfect pairing followed by the inverse of the
canonical isomorphism `(⋀^s F)^∨ ⊗ ⋀^n F ≅ ℋom(⋀^s F, ⋀^n F)` (`⋀^s F` is locally free of finite
rank). -/
noncomputable def exteriorPowerDualTensorIso {n : ℕ} (hrs : r + s = n)
    (hF : IsLocallyFreeOfRank F n) :
    moduleSheafExteriorPower r F ≅
      moduleSheafTensor (moduleSheafDual (moduleSheafExteriorPower s F))
        (moduleSheafExteriorPower n F) :=
  haveI := isIso_moduleSheafDualTensorMap_of_localFrames (E := moduleSheafExteriorPower s F)
    (F := moduleSheafExteriorPower n F)
    (exists_isLocalFrame_exteriorPower F hF.isFiniteLocallyFree s)
  exteriorPowerPerfectPairingIso F r s hrs hF ≪≫ (asIso (moduleSheafDualTensorMap _ _)).symm

end Pairing

end ExteriorPerfectPairing

end Hartshorne
