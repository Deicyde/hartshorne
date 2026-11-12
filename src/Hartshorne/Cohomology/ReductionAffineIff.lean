/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.SerreAffinenessCriterion
import Hartshorne.Scheme.IdealPowerProduct
import Hartshorne.Scheme.ReducedInducedSubscheme

/-!
# Affineness is invariant under reduction

Hartshorne, *Algebraic Geometry*, III, Exercise 3.1 (p. 216).

For a Noetherian scheme `X`, `X` is affine if and only if `X_red` is affine
(`Hartshorne.ReductionAffine.isAffine_iff_isAffine_reduced`). Here `X_red` is the closed
subscheme cut out by the nilradical (`X.nilradical.subscheme`), which is reduced
(`Hartshorne.ReductionAffine.isReduced_reduced`).

## Proof

A closed subscheme of an affine scheme is affine, which gives one direction
(`Hartshorne.ReductionAffine.isAffine_reduced_of_isAffine`).

For the converse we use Serre's criterion (Hartshorne III.3.7,
`Hartshorne.isAffine_tfae_sheafCohomology`): it suffices that `H^1(X, J) = 0` for every coherent
ideal sheaf `J`. The nilradical `𝒩` is nilpotent on a Noetherian scheme
(`exists_nilradical_pow_eq_bot`), so `J ⊇ 𝒩 J ⊇ 𝒩^2 J ⊇ ⋯ ⊇ 𝒩^m J = 0`. Each quotient
`𝒩^k J / 𝒩^{k+1} J` is a quasi-coherent `𝒪_X`-module killed by the nilpotent sections of `𝒪_X`
(`smul_eq_zero_cokernel`). The long exact sequence of cohomology and descending induction on `k`
reduce the vanishing of `H^1(X, J)` to that of `H^1` of these quotients
(`isAffine_of_forall_isZero_H1`).

A quasi-coherent `𝒪_X`-module `Q` killed by the nilpotent sections is a quasi-coherent
`𝒪_{X_red}`-module on the same underlying space (`redModules`): the map `X_red ⟶ X` is a
homeomorphism (`redHomeo`), and a section `a` of `𝒪_{X_red}` acts on a section `s` of `Q` by
gluing `b • s` over the affine opens `W`, where `b ∈ Γ(W, 𝒪_X)` lifts `a` (on affine opens
`Γ(W, 𝒪_X) ⟶ Γ(W ∩ X_red, 𝒪_{X_red})` is surjective with kernel the nilradical, which kills `Q`).
On `W ∩ X_red` this module is the tilde of `Γ(W, Q)`, because `Q` is quasi-coherent on `W`
(`isQuasicoherent_redModules`). If `X_red` is affine, Theorem III.3.5 gives
`H^1(X_red, Q) = 0`, and the cohomology of the same abelian sheaf on `X` is the same, since the
two spaces are homeomorphic (`isZero_H1_of_isAffine_red`).
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

namespace ReductionAffine

open SerreAffineness ArtinReesKernelSheaf

variable {X : Scheme.{u}}

/-- A section of an `𝒪_X`-module which vanishes near every point is zero. -/
theorem eq_zero_of_locally (F : X.Modules) {U : X.Opens} (s : Γ(F, U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧ res F hVU s = 0) : s = 0 := by
  choose V hVU hxV hV using h
  let ι := {x : X // x ∈ U}
  let W : ι → X.Opens := fun x => V x.1 x.2
  let M' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨F.val.presheaf, F.isSheaf⟩
  have hcover : U ≤ iSup W := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩
  apply M'.eq_of_locally_eq' W U (fun i => CategoryTheory.homOfLE (hVU _ _)) hcover
  intro i
  refine (hV i.1 i.2).trans ?_
  exact (map_zero (res F (hVU i.1 i.2))).symm

/-- On a Noetherian scheme the nilradical is nilpotent: `𝒩 ^ m = 0` for some `m`. -/
theorem exists_nilradical_pow_eq_bot [IsNoetherian X] : ∃ m : ℕ, X.nilradical ^ m = ⊥ := by
  have hcover : (Set.univ : Set X) ⊆ ⋃ U : X.affineOpens, ((U : X.Opens) : Set X) := by
    intro x _
    obtain ⟨U, -, hxU⟩ := exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
    exact Set.mem_iUnion.mpr ⟨U, hxU⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _
    (fun U : X.affineOpens => (U : X.Opens).isOpen) hcover
  have hnil : ∀ U : X.affineOpens, ∃ n : ℕ, nilradical Γ(X, (U : X.Opens)) ^ n = ⊥ := fun U => by
    have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical Γ(X, (U : X.Opens))
    exact ⟨n, hn⟩
  choose n hn using hnil
  refine ⟨t.sup n, ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : t => U.1) ?_ fun U => ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  · simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
      Pi.bot_apply, Scheme.nilradical, Scheme.IdealSheafData.radical_ideal]
    refine le_bot_iff.mp ((Ideal.pow_le_pow_right (Finset.le_sup U.2)).trans ?_)
    exact (hn U.1).le

/-- The nilradical kills the sections of `𝒩^m J` for `𝒩^m = 0`. -/
theorem powSmul_eq_bot_of_pow_eq_bot {E : X.Modules} {m : ℕ} (hm : X.nilradical ^ m = ⊥)
    (N : E.val.Submodule) : powSmul X.nilradical m N = ⊥ := by
  refine le_antisymm (fun U s hs => ?_) bot_le
  change s ∈ (⊥ : Submodule _ _)
  rw [Submodule.mem_bot]
  apply eq_zero_of_locally E s
  intro x hx
  obtain ⟨V, hVU, hxV, hV⟩ := hs x hx
  refine ⟨V, hVU, hxV, ?_⟩
  change _ ∈ X.nilradical.ideal V ^ m • sub N V at hV
  have h0 : X.nilradical.ideal V ^ m = ⊥ := by
    have := congrArg (fun I : X.IdealSheafData => I.ideal V) hm
    simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
      Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using this
  rw [h0, Submodule.bot_smul, Submodule.mem_bot] at hV
  exact hV

/-- A nilpotent section multiplies `𝒩^k N` into `𝒩^{k+1} N`. -/
theorem smul_mem_powSmul_succ {E : X.Modules} (N : E.val.Submodule) {k : ℕ} {V : X.Opens}
    (a : Γ(X, V)) (ha : IsNilpotent a) {s : Γ(E, V)}
    (hs : s ∈ sub (powSmul X.nilradical k N) V) :
    a • s ∈ sub (powSmul X.nilradical (k + 1) N) V := by
  intro y hy
  obtain ⟨W, hWV, hyW, hW⟩ := hs y hy
  refine ⟨W, hWV, hyW, ?_⟩
  change res E hWV (a • s) ∈ X.nilradical.ideal W ^ (k + 1) • sub N W
  change res E hWV s ∈ X.nilradical.ideal W ^ k • sub N W at hW
  rw [LinearMap.map_smulₛₗ, pow_succ', Submodule.mul_smul]
  refine Submodule.smul_mem_smul ?_ hW
  have hnil : IsNilpotent ((X.presheaf.map (homOfLE hWV).op).hom a) := ha.map _
  simp only [Scheme.nilradical, Scheme.IdealSheafData.radical_ideal,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  exact mem_nilradical.mpr hnil

section Filtration

variable (J : QuasicoherentIdealSubsheaf X)

/-- The ideal sheaf `𝒩^k J`, as an `𝒪_X`-module. -/
abbrev filt (k : ℕ) : X.Modules :=
  toModules (powSmul X.nilradical k J.carrier) (isLocal_powSmul _ _ _)

/-- The inclusion `𝒩^{k+1} J ⟶ 𝒩^k J`. -/
abbrev filtι (k : ℕ) : filt J (k + 1) ⟶ filt J k :=
  inclusion _ _ (powSmul_antitone _ _ (Nat.le_succ k))

instance (k : ℕ) : Mono (filtι J k) := by
  have : Mono ((SheafOfModules.forget X.ringCatSheaf).map (filtι J k)) :=
    inferInstanceAs (Mono (PresheafOfModules.Submodule.homOfLE _))
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map this

/-- The short exact sequence `0 ⟶ 𝒩^{k+1} J ⟶ 𝒩^k J ⟶ 𝒩^k J / 𝒩^{k+1} J ⟶ 0`. -/
abbrev filtSC (k : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (filtι J k) (cokernel.π (filtι J k)) (cokernel.condition _)

theorem filtSC_shortExact (k : ℕ) : (filtSC J k).ShortExact :=
  ShortComplex.ShortExact.mk' ((filtSC J k).exact_of_g_is_cokernel (cokernelIsCokernel _))
    inferInstance inferInstance

instance isQuasicoherent_filt (k : ℕ) : (filt J k).IsQuasicoherent := by
  have := J.isQuasicoherent
  exact isQuasicoherent_powSmul X.nilradical k J.isLocal

instance isQuasicoherent_cokernel_filtι (k : ℕ) : (cokernel (filtι J k)).IsQuasicoherent :=
  isQuasicoherent_cokernel _

/-- The quotient `𝒩^k J / 𝒩^{k+1} J` is killed by the nilpotent sections of `𝒪_X`. -/
theorem smul_eq_zero_cokernel (k : ℕ) {U : X.Opens} (a : Γ(X, U)) (ha : IsNilpotent a)
    (s : Γ(cokernel (filtι J k), U)) : a • s = 0 := by
  apply eq_zero_of_locally _ (a • s)
  intro x hx
  obtain ⟨V, hVU, hxV, t, ht⟩ := modules_exists_local_lift (cokernel.π (filtι J k)) s hx
  refine ⟨V, hVU, hxV, ?_⟩
  set a' := (X.presheaf.map (homOfLE hVU).op).hom a
  have hmem := smul_mem_powSmul_succ J.carrier a' (ha.map _)
    (t : sub (powSmul X.nilradical k J.carrier) V).2
  let t' : Γ(filt J (k + 1), V) := ⟨_, hmem⟩
  have ht' : (filtι J k).app V t' = a' • t := Subtype.ext rfl
  have h0 : (cokernel.π (filtι J k)).app V ((filtι J k).app V t') = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition]
    rfl
  rw [res_apply, Scheme.Modules.map_smul, ← ht, ← Scheme.Modules.Hom.app_smul, ← ht', h0]

/-- `𝒩^0 J = J`. -/
def filtZeroIso : filt J 0 ≅ J.toModules where
  hom := inclusion _ _ (powSmul_le J.isLocal)
  inv := inclusion _ _ (powSmul_zero _ J.isLocal).ge
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem isZero_filt {m : ℕ} (hm : X.nilradical ^ m = ⊥) : IsZero (filt J m) := by
  rw [IsZero.iff_id_eq_zero]
  ext U s : 3
  have hs := PresheafOfModules.Submodule.le_iff.1
    (powSmul_eq_bot_of_pow_eq_bot hm J.carrier).le _
    (s : sub (powSmul X.nilradical m J.carrier) U).2
  change s = 0
  exact Subtype.ext ((Submodule.mem_bot _).mp hs)

end Filtration

/-- **Reduction to modules killed by the nilradical** (the filtration step of Hartshorne III,
Exercise 3.1). On a Noetherian scheme `X`, if `H^1(X, Q) = 0` for every quasi-coherent
`𝒪_X`-module `Q` killed by the nilpotent sections of `𝒪_X`, then `X` is affine. -/
theorem isAffine_of_forall_isZero_H1 [IsNoetherian X]
    (h : ∀ (Q : X.Modules) [Q.IsQuasicoherent],
      (∀ (U : X.Opens) (a : Γ(X, U)), IsNilpotent a → ∀ s : Γ(Q, U), a • s = 0) →
        IsZero (H 1 Q)) :
    IsAffine X := by
  refine ((isAffine_tfae_sheafCohomology X).out 2 0).mp fun J _ => ?_
  obtain ⟨m, hm⟩ := exists_nilradical_pow_eq_bot (X := X)
  have key : ∀ j, j ≤ m → IsZero (H 1 (filt J (m - j))) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact isZero_H_of_isZero (by simpa using isZero_filt J hm) 1
    | succ j ih =>
      intro hj
      obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
      have hk' : m - (j + 1) = k := by omega
      rw [hk']
      have h₁ : IsZero (H 1 (filt J (k + 1))) := by
        rw [← hk]
        exact ih (by omega)
      have h₃ : IsZero (H 1 (cokernel (filtι J k))) :=
        h (cokernel (filtι J k)) fun U a ha s => smul_eq_zero_cokernel J k a ha s
      exact isZero_H1_of_shortExact (S := filtSC J k) (filtSC_shortExact J k) h₁ h₃
  have h0 := key m le_rfl
  rw [Nat.sub_self] at h0
  exact h0.of_iso ((sheafCohomology X.toTopCat 1).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso (filtZeroIso J).symm))

/-! ### Modules killed by the nilradical as modules on `X_red` -/

section Descent

variable (X) in
/-- The reduction `X_red`: the closed subscheme cut out by the nilradical. -/
abbrev red : Scheme.{u} := X.nilradical.subscheme

variable (X) in
/-- The closed immersion `X_red ⟶ X`. -/
abbrev redι : red X ⟶ X := X.nilradical.subschemeι

/-- Two sections of an `𝒪_X`-module agreeing on every affine open inside are equal. -/
theorem ext_of_affine (F : X.Modules) {U : X.Opens} {s t : Γ(F, U)}
    (h : ∀ (W : X.affineOpens) (hW : (W : X.Opens) ≤ U), res F hW s = res F hW t) : s = t := by
  rw [← sub_eq_zero]
  apply eq_zero_of_locally
  intro x hx
  obtain ⟨W, hWU, hxW⟩ := exists_affine_le hx
  exact ⟨W, hWU, hxW, by rw [map_sub, h W hWU, sub_self]⟩

theorem mem_support_nilradical (x : X) : x ∈ X.nilradical.support := by
  rw [Scheme.support_nilradical]
  trivial

variable (X) in
/-- The inverse of the homeomorphism `X_red ⟶ X`. -/
def redInv : X.toTopCat ⟶ (red X).toTopCat :=
  TopCat.ofHom ⟨fun x => ⟨x, mem_support_nilradical x⟩,
    continuous_id.subtype_mk mem_support_nilradical⟩

variable (X) in
/-- The closed immersion `X_red ⟶ X` is a homeomorphism. -/
def redHomeo : (red X).toTopCat ≅ X.toTopCat where
  hom := (redι X).base
  inv := redInv X
  hom_inv_id := by ext z; rfl
  inv_hom_id := by ext x; rfl

/-- The open of `X` corresponding to an open of `X_red`. -/
abbrev redOpen (V : (red X).Opens) : X.Opens := (Opens.map (redInv X)).obj V

theorem preimage_redOpen (V : (red X).Opens) : (redι X) ⁻¹ᵁ redOpen V = V := rfl

theorem redOpen_preimage (U : X.Opens) : redOpen ((redι X) ⁻¹ᵁ U) = U := rfl

/-- Restriction of sections of `𝒪_X` is compatible with `X_red ⟶ X`. -/
theorem app_res {U W : X.Opens} (h : W ≤ U) (c : Γ(X, U)) :
    (redι X).app W (X.presheaf.map (homOfLE h).op c) =
      (red X).presheaf.map (homOfLE (fun _ hz => h hz : (redι X) ⁻¹ᵁ W ≤ (redι X) ⁻¹ᵁ U)).op
        ((redι X).app U c) := by
  exact congrArg (fun φ => φ.hom c) ((redι X).naturality (homOfLE h).op)

variable {Q : X.Modules}
  (hQ : ∀ (U : X.Opens) (a : Γ(X, U)), IsNilpotent a → ∀ s : Γ(Q, U), a • s = 0)

include hQ in
/-- Sections of `𝒪_X` vanishing on `X_red` kill `Q`. -/
theorem smul_eq_zero_of_app_eq_zero {U : X.Opens} (c : Γ(X, U)) (hc : (redι X).app U c = 0)
    (s : Γ(Q, U)) : c • s = 0 := by
  apply eq_zero_of_locally _ (c • s)
  intro x hx
  obtain ⟨W, hWU, hxW⟩ := exists_affine_le hx
  refine ⟨W, hWU, hxW, ?_⟩
  rw [LinearMap.map_smulₛₗ]
  apply hQ
  have h1 : (redι X).app W (X.presheaf.map (homOfLE hWU).op c) = 0 := by
    rw [app_res, hc, map_zero]
  have h2 : X.presheaf.map (homOfLE hWU).op c ∈ RingHom.ker ((redι X).app W).hom := h1
  rw [Scheme.IdealSheafData.ker_subschemeι_app] at h2
  simp only [Scheme.nilradical, Scheme.IdealSheafData.radical_ideal,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at h2
  exact mem_nilradical.mp h2

/-- `b` lifts `a` over `W`. -/
def IsLift {V : (red X).Opens} (a : Γ(red X, V)) {W : X.Opens} (hW : W ≤ redOpen V)
    (b : Γ(X, W)) : Prop :=
  (redι X).app W b = (red X).presheaf.map (homOfLE (fun _ hz => hW hz : (redι X) ⁻¹ᵁ W ≤ V)).op a

theorem exists_isLift {V : (red X).Opens} (a : Γ(red X, V)) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ redOpen V) : ∃ b : Γ(X, W), IsLift a hW b :=
  X.nilradical.subschemeι_app_surjective W _

theorem IsLift.res {V : (red X).Opens} {a : Γ(red X, V)} {W : X.Opens} {hW : W ≤ redOpen V}
    {b : Γ(X, W)} (hb : IsLift a hW b) {W' : X.Opens} (h : W' ≤ W) :
    IsLift a (h.trans hW) (X.presheaf.map (homOfLE h).op b) := by
  unfold IsLift at hb ⊢
  rw [app_res, hb, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

include hQ in
theorem IsLift.smul_eq {V : (red X).Opens} {a : Γ(red X, V)} {W : X.Opens} {hW : W ≤ redOpen V}
    {b b' : Γ(X, W)} (hb : IsLift a hW b) (hb' : IsLift a hW b') (s : Γ(Q, W)) :
    b • s = b' • s := by
  rw [← sub_eq_zero, ← sub_smul]
  refine smul_eq_zero_of_app_eq_zero hQ _ ?_ s
  rw [map_sub]
  exact sub_eq_zero.mpr (hb.trans hb'.symm)

include hQ in
theorem exists_glue (V : (red X).Opens) (a : Γ(red X, V)) (s : Γ(Q, redOpen V)) :
    ∃ t : Γ(Q, redOpen V), ∀ (W : X.Opens) (hW : W ≤ redOpen V) (b : Γ(X, W)),
      IsLift a hW b → res Q hW t = b • res Q hW s := by
  let ι := {W : X.affineOpens // (W : X.Opens) ≤ redOpen V}
  let Wf : ι → X.Opens := fun W => W.1
  choose b hb using fun W : ι => exists_isLift a W.1 W.2
  let M' : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨Q.val.presheaf, Q.isSheaf⟩
  have hcover : redOpen V ≤ iSup Wf := fun x hx => by
    obtain ⟨W, hWU, hxW⟩ := exists_affine_le hx
    exact Opens.mem_iSup.mpr ⟨⟨W, hWU⟩, hxW⟩
  let sf : ∀ W : ι, ToType (M'.1.obj (op (Wf W))) := fun W => b W • res Q W.2 s
  have hsf : TopCat.Presheaf.IsCompatible M'.1 Wf sf := by
    intro W₁ W₂
    have h₁ := (hb W₁).res (inf_le_left : (W₁.1 : X.Opens) ⊓ W₂.1 ≤ W₁.1)
    have h₂ := (hb W₂).res (inf_le_right : (W₁.1 : X.Opens) ⊓ W₂.1 ≤ W₂.1)
    change res Q inf_le_left (b W₁ • res Q W₁.2 s) = res Q inf_le_right (b W₂ • res Q W₂.2 s)
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, res_res, res_res]
    exact h₁.smul_eq hQ h₂ _
  obtain ⟨t₀, ht, -⟩ := M'.existsUnique_gluing' Wf (redOpen V)
    (fun W => CategoryTheory.homOfLE W.2) hcover sf hsf
  let t : Γ(Q, redOpen V) := t₀
  refine ⟨t, fun W hW c hc => ?_⟩
  refine ext_of_affine Q fun W' hW' => ?_
  rw [res_res, LinearMap.map_smulₛₗ, res_res]
  have e1 : res Q (hW'.trans hW) t = b ⟨W', hW'.trans hW⟩ • res Q (hW'.trans hW) s :=
    ht ⟨W', hW'.trans hW⟩
  rw [e1]
  exact (hb ⟨W', hW'.trans hW⟩).smul_eq hQ (hc.res hW') _

/-- The action of `Γ(X_red, V)` on `Γ(Q, V)`. -/
def redSMul (V : (red X).Opens) (a : Γ(red X, V)) (s : Γ(Q, redOpen V)) : Γ(Q, redOpen V) :=
  (exists_glue hQ V a s).choose

theorem redSMul_spec (V : (red X).Opens) (a : Γ(red X, V)) (s : Γ(Q, redOpen V)) {W : X.Opens}
    (hW : W ≤ redOpen V) {b : Γ(X, W)} (hb : IsLift a hW b) :
    res Q hW (redSMul hQ V a s) = b • res Q hW s :=
  (exists_glue hQ V a s).choose_spec W hW b hb

theorem isLift_one (V : (red X).Opens) {W : X.Opens} (hW : W ≤ redOpen V) :
    IsLift (1 : Γ(red X, V)) hW 1 := by
  unfold IsLift
  rw [map_one, map_one]

theorem IsLift.mul {V : (red X).Opens} {a a' : Γ(red X, V)} {W : X.Opens} {hW : W ≤ redOpen V}
    {b b' : Γ(X, W)} (hb : IsLift a hW b) (hb' : IsLift a' hW b') :
    IsLift (a * a') hW (b * b') := by
  unfold IsLift at *
  rw [map_mul, map_mul, hb, hb']

theorem IsLift.add {V : (red X).Opens} {a a' : Γ(red X, V)} {W : X.Opens} {hW : W ≤ redOpen V}
    {b b' : Γ(X, W)} (hb : IsLift a hW b) (hb' : IsLift a' hW b') :
    IsLift (a + a') hW (b + b') := by
  unfold IsLift at *
  rw [map_add, map_add, hb, hb']

theorem isLift_zero (V : (red X).Opens) {W : X.Opens} (hW : W ≤ redOpen V) :
    IsLift (0 : Γ(red X, V)) hW 0 := by
  unfold IsLift
  rw [map_zero, map_zero]

/-- `Γ(Q, V)` as a `Γ(X_red, V)`-module. -/
@[instance_reducible]
def redModule (V : (red X).Opens) : Module Γ(red X, V) Γ(Q, redOpen V) where
  smul := redSMul hQ V
  one_smul s := ext_of_affine Q fun W hW =>
    (redSMul_spec hQ V 1 s hW (isLift_one V hW)).trans (one_smul _ _)
  mul_smul a a' s := ext_of_affine Q fun W hW => by
    obtain ⟨b, hb⟩ := exists_isLift a W hW
    obtain ⟨b', hb'⟩ := exists_isLift a' W hW
    change res Q hW (redSMul hQ V (a * a') s) = res Q hW (redSMul hQ V a (redSMul hQ V a' s))
    rw [redSMul_spec hQ V _ s hW (hb.mul hb'), redSMul_spec hQ V a _ hW hb,
      redSMul_spec hQ V a' s hW hb', mul_smul]
  smul_zero a := ext_of_affine Q fun W hW => by
    obtain ⟨b, hb⟩ := exists_isLift a W hW
    change res Q hW (redSMul hQ V a 0) = res Q hW 0
    rw [redSMul_spec hQ V a 0 hW hb, map_zero, smul_zero]
  smul_add a s s' := ext_of_affine Q fun W hW => by
    obtain ⟨b, hb⟩ := exists_isLift a W hW
    change res Q hW (redSMul hQ V a (s + s')) =
      res Q hW (redSMul hQ V a s + redSMul hQ V a s')
    rw [redSMul_spec hQ V a _ hW hb, map_add, map_add, smul_add, redSMul_spec hQ V a s hW hb,
      redSMul_spec hQ V a s' hW hb]
  add_smul a a' s := ext_of_affine Q fun W hW => by
    obtain ⟨b, hb⟩ := exists_isLift a W hW
    obtain ⟨b', hb'⟩ := exists_isLift a' W hW
    change res Q hW (redSMul hQ V (a + a') s) =
      res Q hW (redSMul hQ V a s + redSMul hQ V a' s)
    rw [redSMul_spec hQ V _ s hW (hb.add hb'), map_add, add_smul, redSMul_spec hQ V a s hW hb,
      redSMul_spec hQ V a' s hW hb']
  zero_smul s := ext_of_affine Q fun W hW => by
    change res Q hW (redSMul hQ V 0 s) = res Q hW 0
    rw [redSMul_spec hQ V 0 s hW (isLift_zero V hW), zero_smul, map_zero]

theorem redOpen_mono {V V' : (red X).Opens} (h : V' ≤ V) : redOpen V' ≤ redOpen V :=
  fun _ hx => h hx

/-- The action of `Γ(X_red, -)` is compatible with restriction. -/
theorem redSMul_res {V V' : (red X).Opens} (h : V' ≤ V) (a : Γ(red X, V))
    (s : Γ(Q, redOpen V)) :
    res Q (redOpen_mono h) (redSMul hQ V a s) =
      redSMul hQ V' ((red X).presheaf.map (homOfLE h).op a) (res Q (redOpen_mono h) s) := by
  refine ext_of_affine Q fun W hW => ?_
  obtain ⟨b, hb⟩ := exists_isLift a W (hW.trans (redOpen_mono h))
  have hb' : IsLift ((red X).presheaf.map (homOfLE h).op a) hW b := by
    unfold IsLift at hb ⊢
    rw [hb, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [res_res, redSMul_spec hQ V a s _ hb, redSMul_spec hQ V' _ _ hW hb', res_res]

/-- The underlying presheaf of abelian groups of `Q`, on `X_red`. -/
abbrev redPresheaf (Q : X.Modules) : (Opens (red X).toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (Opens.map (redInv X)).op ⋙ Q.presheaf

/-- An `𝒪_X`-module killed by the nilpotent sections of `𝒪_X`, viewed as an
`𝒪_{X_red}`-module. -/
def redModules : (red X).Modules where
  val :=
    letI : ∀ V : (Opens (red X).toTopCat)ᵒᵖ,
        Module ((red X).ringCatSheaf.obj.obj V) ((redPresheaf Q).obj V) :=
      fun V => redModule hQ V.unop
    PresheafOfModules.ofPresheaf (redPresheaf Q)
      (fun _ _ f a s => redSMul_res hQ (leOfHom f.unop) a s)
  isSheaf := ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (redInv X)).obj
    ⟨Q.val.presheaf, Q.isSheaf⟩).property

theorem redSMul_eq_of (V : (red X).Opens) (a : Γ(red X, V)) (s : Γ(Q, redOpen V))
    (b : Γ(X, redOpen V)) (hb : (redι X).app (redOpen V) b = a) : redSMul hQ V a s = b • s := by
  have hb' : IsLift a le_rfl b := by
    unfold IsLift
    rw [hb]
    change a = (red X).presheaf.map (𝟙 (op V)) a
    rw [CategoryTheory.Functor.map_id]
    rfl
  have := redSMul_spec hQ V a s le_rfl hb'
  rwa [res_refl, res_refl] at this

theorem exists_pow_smul_eq_zero_aux [Q.IsQuasicoherent] (U : X.affineOpens) (g : Γ(X, U))
    {W : X.Opens}
    (hW : W = X.basicOpen g) (hWU : W ≤ U) (s : Γ(Q, U)) (hs : res Q hWU s = 0) :
    ∃ n : ℕ, g ^ n • s = 0 := by
  subst hW
  exact exists_pow_smul_eq_zero_of_isAffineOpen Q U.2 g s hs

theorem exists_pow_smul_extension_aux [Q.IsQuasicoherent] (U : X.affineOpens) (g : Γ(X, U))
    {W : X.Opens} (hW : W = X.basicOpen g) (hWU : W ≤ U) (t : Γ(Q, W)) :
    ∃ (n : ℕ) (s : Γ(Q, U)), res Q hWU s = (X.presheaf.map (homOfLE hWU).op g) ^ n • t := by
  subst hW
  exact exists_pow_smul_extension_of_isAffineOpen Q U.2 g t

/-- The affine open `U ∩ X_red` of `X_red`. -/
def redAffine (U : X.affineOpens) : (red X).affineOpens :=
  ⟨(redι X) ⁻¹ᵁ (U : X.Opens), U.2.preimage _⟩

theorem iSup_redAffine : (⨆ U : X.affineOpens, ((redAffine U : (red X).affineOpens) :
    (red X).Opens)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨U, -, hU⟩ := exists_affine_le (show (redι X) z ∈ (⊤ : X.Opens) from trivial)
  exact Opens.mem_iSup.mpr ⟨U, hU⟩

theorem isIso_fromTildeΓ_redModules [Q.IsQuasicoherent] (U : X.affineOpens) :
    IsIso (specRestriction (redModules hQ) (redAffine U)).fromTildeΓ := by
  refine isIso_fromTildeΓ_of_pow_smul _ _ (fun g s hs => ?_) (fun g t => ?_)
  · obtain ⟨g', rfl⟩ := X.nilradical.subschemeι_app_surjective U g
    have hD : redOpen ((red X).basicOpen ((redι X).app U g')) = X.basicOpen g' :=
      (congrArg redOpen (Scheme.preimage_basicOpen (redι X) g')).symm
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_aux U g' hD
      (redOpen_mono ((red X).basicOpen_le _)) (show Γ(Q, (U : X.Opens)) from s) hs
    refine ⟨n, ?_⟩
    change redSMul hQ _ (((redι X).app U g') ^ n) s = 0
    exact (redSMul_eq_of hQ _ _ s (g' ^ n) (map_pow _ g' n)).trans hn
  · obtain ⟨g', rfl⟩ := X.nilradical.subschemeι_app_surjective U g
    have hD : redOpen ((red X).basicOpen ((redι X).app U g')) = X.basicOpen g' :=
      (congrArg redOpen (Scheme.preimage_basicOpen (redι X) g')).symm
    have hWU := redOpen_mono ((red X).basicOpen_le ((redι X).app U g'))
    obtain ⟨n, s, hs⟩ := exists_pow_smul_extension_aux U g' hD hWU t
    refine ⟨n, s, ?_⟩
    change res Q hWU s = redSMul hQ _ _ t
    rw [redSMul_eq_of hQ _ _ t ((X.presheaf.map (homOfLE hWU).op g') ^ n)]
    · exact hs
    · exact (map_pow _ _ n).trans (congrArg (· ^ n) (app_res hWU g'))

theorem isQuasicoherent_redModules [Q.IsQuasicoherent] : (redModules hQ).IsQuasicoherent := by
  have h : HasAffineTildeCover (redModules hQ) :=
    ⟨X.affineOpens, redAffine, iSup_redAffine, fun U =>
      ⟨_, ⟨@asIso _ _ _ _ (specRestriction (redModules hQ) (redAffine U)).fromTildeΓ
        (isIso_fromTildeΓ_redModules hQ U)⟩⟩⟩
  exact ((quasicoherent_affine_local_tfae _).out 1 0).mp h

theorem isLocallyNoetherian_red [IsLocallyNoetherian X] : IsLocallyNoetherian (red X) := by
  refine isLocallyNoetherian_of_affine_cover iSup_redAffine fun U => ?_
  have : IsNoetherianRing Γ(X, (U : X.Opens)) := IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_surjective _ _ _ (X.nilradical.subschemeι_app_surjective U)

include hQ in
/-- **`H^1` of a module killed by the nilradical** (the step of Hartshorne III, Exercise 3.1 on
the quotients of the filtration). If `X_red` is affine and Noetherian and `Q` is a quasi-coherent
`𝒪_X`-module killed by the nilpotent sections of `𝒪_X`, then `H^1(X, Q) = 0`: `Q` is a
quasi-coherent `𝒪_{X_red}`-module (`redModules`) on the same underlying space, so its
cohomology vanishes by Theorem III.3.5. -/
theorem isZero_H1_of_isAffine_red [IsLocallyNoetherian (red X)] [IsAffine (red X)]
    [Q.IsQuasicoherent] : IsZero (H 1 Q) := by
  have := isQuasicoherent_redModules hQ
  have h := sheafCohomology_isZero_of_isQuasicoherent_of_isAffine (redModules hQ) 1 one_pos
  exact h.of_iso (sheafCohomologyPushforwardIsoOfIso (redHomeo X).symm
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj Q) 1).symm

end Descent

/-- A closed subscheme of an affine scheme is affine; in particular `X_red` is affine when `X`
is. -/
theorem isAffine_reduced_of_isAffine [IsAffine X] : IsAffine X.nilradical.subscheme :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine X.nilradical.subschemeι).1

/-- `X_red` is reduced: it is the reduced induced closed subscheme on all of `X`. -/
instance isReduced_reduced (X : Scheme.{u}) : IsReduced X.nilradical.subscheme := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_top]
  exact isReduced_reducedInducedSubscheme ⊤

/-- **Affineness is invariant under reduction** (Hartshorne III, Exercise 3.1). A Noetherian
scheme `X` is affine if and only if its reduction `X_red` (the closed subscheme cut out by the
nilradical) is affine. -/
theorem isAffine_iff_isAffine_reduced (X : Scheme.{u}) [IsNoetherian X] :
    IsAffine X ↔ IsAffine X.nilradical.subscheme := by
  refine ⟨fun _ => isAffine_reduced_of_isAffine, fun _ => ?_⟩
  have : IsLocallyNoetherian (red X) := isLocallyNoetherian_red
  exact isAffine_of_forall_isZero_H1 fun Q _ hQ => isZero_H1_of_isAffine_red hQ

end ReductionAffine

end Hartshorne
