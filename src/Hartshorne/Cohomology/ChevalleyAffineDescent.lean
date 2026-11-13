/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.ChevalleyGenericApproximation
import Hartshorne.Cohomology.AffineMorphismCohomologyPushforward
import Hartshorne.Cohomology.ReducedComponentsAffine
import Hartshorne.Scheme.ModuleSheafSupport

/-!
# Chevalley's affine descent theorem
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

namespace ChevalleyDescent

open SerreAffineness ArtinReesKernelSheaf

variable {Y : Scheme.{u}}

/-- A quasi-coherent module without nonzero sections over the members of an affine open cover
has no nonzero sections at all. -/
theorem eq_zero_of_affineCover (N : Y.Modules) [N.IsQuasicoherent] {ι : Type*}
    (U : ι → Y.affineOpens) (hU : ∀ x : Y, ∃ i, x ∈ (U i : Y.Opens))
    (h : ∀ i (s : Γ(N, U i)), s = 0) {V : Y.Opens} (s : Γ(N, V)) : s = 0 := by
  apply ReductionAffine.eq_zero_of_locally N s
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  obtain ⟨g, hgV, hxg⟩ := (U i).2.exists_basicOpen_le ⟨x, hx⟩ hi
  refine ⟨Y.basicOpen g, hgV, hxg, ?_⟩
  obtain ⟨n, t', ht'⟩ := exists_pow_smul_extension_of_isAffineOpen N (U i).2 g (res N hgV s)
  rw [h i t', map_zero] at ht'
  have hunit : IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op g) ^ n) :=
    (isUnit_res_of_le_basicOpen g (Y.basicOpen_le g) le_rfl).pow n
  exact hunit.smul_eq_zero.1 ht'.symm

/-- Sections of an `𝒪_Y`-module over an open set disjoint from its support vanish. -/
theorem eq_zero_of_disjoint_support (K : Y.Modules) {V : Y.Opens}
    (hV : ∀ x ∈ V, x ∉ moduleSheafSupport K) (s : Γ(K, V)) : s = 0 := by
  apply ReductionAffine.eq_zero_of_locally K s
  intro x hx
  have : Subsingleton (K.presheaf.stalk x) := not_nontrivial_iff_subsingleton.1 (hV x hx)
  have h0 : K.presheaf.germ V x hx s = K.presheaf.germ V x hx 0 := Subsingleton.elim _ _
  obtain ⟨W, hxW, i, i', hW⟩ := TopCat.Presheaf.germ_eq K.presheaf x hx hx s 0 h0
  refine ⟨W, leOfHom i, hxW, ?_⟩
  rw [res_apply]
  simp only [map_zero] at hW
  convert hW
  exact Subsingleton.elim _ _

/-- On an affine open `U` of a locally Noetherian scheme, a power of the ideal of a closed set
`W` containing the support of a coherent module `K` kills `Γ(U, K)`. -/
theorem exists_pow_le_annihilator [IsLocallyNoetherian Y] (K : Y.Modules) (hK : IsCoherent K)
    (W : Closeds Y) (hW : moduleSheafSupport K ⊆ W) (U : Y.affineOpens) :
    ∃ n, (Scheme.IdealSheafData.vanishingIdeal W).ideal U ^ n ≤
      (⊤ : Submodule Γ(Y, U) Γ(K, U)).annihilator := by
  have : K.IsQuasicoherent := hK.isQuasicoherent
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian U
  have hfin : Module.Finite Γ(Y, U) Γ(K, U) := (forall_affine_finite_of_isCoherent K hK U).1
  refine Ideal.exists_pow_le_of_le_radical_of_fg (fun a ha => ?_) (IsNoetherian.noetherian _)
  have hzero : ∀ s : Γ(K, U), ∃ n : ℕ, a ^ n • s = 0 := fun s =>
    exists_pow_smul_eq_zero_of_isAffineOpen K U.2 a s
      (eq_zero_of_disjoint_support K (fun x hx hxK =>
        not_mem_basicOpen_of_mem_vanishingIdeal ha (Y.basicOpen_le a hx) (hW hxK) hx) _)
  obtain ⟨S, hS⟩ := hfin.fg_top
  choose n hn using hzero
  refine ⟨∑ x ∈ S, n x, ?_⟩
  rw [← hS, Submodule.mem_annihilator_span]
  intro x
  have hle : n x ≤ ∑ y ∈ S, n y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) x.2
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hn, smul_zero]

/-- On a Noetherian scheme, if the support of a coherent module `K` lies in a closed set `W`,
then `I_W ^ m K = 0` for some `m`, where `I_W` is the ideal sheaf of `W`. -/
theorem exists_isZero_powSmul [IsNoetherian Y] (K : Y.Modules) (hK : IsCoherent K)
    (W : Closeds Y) (hW : moduleSheafSupport K ⊆ W) :
    ∃ m, IsZero (toModules (powSmul (Scheme.IdealSheafData.vanishingIdeal W) m
      (⊤ : K.val.Submodule)) (isLocal_powSmul _ _ _)) := by
  have : K.IsQuasicoherent := hK.isQuasicoherent
  have := isQuasicoherent_top (E := K)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : Y.affineOpens => (U : Set Y))
    (fun U => U.1.2) (fun x _ => by
      obtain ⟨U, -, hx⟩ := exists_affine_le (show x ∈ (⊤ : Y.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨U, hx⟩)
  choose n hn using exists_pow_le_annihilator K hK W hW
  have := isQuasicoherent_powSmul (Scheme.IdealSheafData.vanishingIdeal W) (t.sup n)
    (isLocal_top (E := K))
  refine ⟨t.sup n, ?_⟩
  rw [IsZero.iff_id_eq_zero]
  ext V s : 3
  change s = 0
  refine eq_zero_of_affineCover _ (fun U : t => U.1) (fun x => ?_) (fun U s => ?_) s
  · obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨⟨U, hU⟩, hx⟩
  · apply Subtype.ext
    obtain ⟨v, hv⟩ := s
    change (v : Γ(K, (U.1 : Y.Opens))) = 0
    have hs : (v : Γ(K, (U.1 : Y.Opens))) ∈ sub (powSmul (Scheme.IdealSheafData.vanishingIdeal W) (t.sup n)
        (⊤ : K.val.Submodule)) U.1 := hv
    rw [sub_powSmul_eq _ _ isLocal_top U.1] at hs
    refine Submodule.smul_induction_on (p := fun x : Γ(K, (U.1 : Y.Opens)) => x = 0) hs
      (fun c hc y _ => ?_) (fun _ _ h₁ h₂ => ?_)
    · have hc' := hn U.1 (Ideal.pow_le_pow_right (Finset.le_sup U.2) hc)
      exact (Submodule.mem_annihilator.1 hc') y trivial
    · rw [h₁, h₂, add_zero]

section Filtration

variable (I : Y.IdealSheafData) (K : Y.Modules)

/-- The `𝒪_Y`-module `I ^ k K`. -/
abbrev filt (k : ℕ) : Y.Modules :=
  toModules (powSmul I k (⊤ : K.val.Submodule)) (isLocal_powSmul _ _ _)

/-- The inclusion `I ^ (k + 1) K ⟶ I ^ k K`. -/
abbrev filtι (k : ℕ) : filt I K (k + 1) ⟶ filt I K k :=
  inclusion _ _ (powSmul_antitone _ _ (Nat.le_succ k))

instance (k : ℕ) : Mono (filtι I K k) := by
  have : Mono ((SheafOfModules.forget Y.ringCatSheaf).map (filtι I K k)) :=
    inferInstanceAs (Mono (PresheafOfModules.Submodule.homOfLE _))
  exact (SheafOfModules.forget Y.ringCatSheaf).mono_of_mono_map this

/-- The short exact sequence `0 ⟶ I ^ (k + 1) K ⟶ I ^ k K ⟶ I ^ k K / I ^ (k + 1) K ⟶ 0`. -/
abbrev filtSC (k : ℕ) : ShortComplex Y.Modules :=
  ShortComplex.mk (filtι I K k) (cokernel.π (filtι I K k)) (cokernel.condition _)

theorem filtSC_shortExact (k : ℕ) : (filtSC I K k).ShortExact :=
  ShortComplex.ShortExact.mk' ((filtSC I K k).exact_of_g_is_cokernel (cokernelIsCokernel _))
    inferInstance inferInstance

/-- A section of `I` over an affine open multiplies `I ^ k N` into `I ^ (k + 1) N`. -/
theorem smul_mem_powSmul_succ {E : Y.Modules} (N : E.val.Submodule) {k : ℕ}
    {U : Y.affineOpens} {V : Y.Opens} (hVU : V ≤ U) (c : Γ(Y, U)) (hc : c ∈ I.ideal U)
    {s : Γ(E, V)} (hs : s ∈ sub (powSmul I k N) V) :
    (Y.presheaf.map (homOfLE hVU).op).hom c • s ∈ sub (powSmul I (k + 1) N) V := by
  intro y hy
  obtain ⟨W, hWV, hyW, hW⟩ := hs y hy
  refine ⟨W, hWV, hyW, ?_⟩
  change res E hWV (_ • s) ∈ I.ideal W ^ (k + 1) • sub N W
  change res E hWV s ∈ I.ideal W ^ k • sub N W at hW
  rw [LinearMap.map_smulₛₗ, pow_succ', Submodule.mul_smul]
  refine Submodule.smul_mem_smul ?_ hW
  have h := I.ideal_le_comap_ideal (U := W) (V := U) (hWV.trans hVU) hc
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact h

/-- `I` kills `I ^ k K / I ^ (k + 1) K`. -/
theorem smul_eq_zero_cokernel (k : ℕ) {U : Y.affineOpens} (c : Γ(Y, U)) (hc : c ∈ I.ideal U)
    (s : Γ(cokernel (filtι I K k), U)) : c • s = 0 := by
  apply ReductionAffine.eq_zero_of_locally _ (c • s)
  intro x hx
  obtain ⟨V, hVU, hxV, t, ht⟩ := modules_exists_local_lift (cokernel.π (filtι I K k)) s hx
  refine ⟨V, hVU, hxV, ?_⟩
  set a' := (Y.presheaf.map (homOfLE hVU).op).hom c
  have hmem := smul_mem_powSmul_succ I ⊤ hVU c hc (t : sub (powSmul I k ⊤) V).2
  let t' : Γ(filt I K (k + 1), V) := ⟨_, hmem⟩
  have ht' : (filtι I K k).app V t' = a' • t := Subtype.ext rfl
  have h0 : (cokernel.π (filtι I K k)).app V ((filtι I K k).app V t') = 0 := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, cokernel.condition]
    rfl
  rw [res_apply, Scheme.Modules.map_smul, ← ht, ← Scheme.Modules.Hom.app_smul, ← ht', h0]

/-- The top submodule sheaf of `K` is `K`. -/
def topIso : toModules (⊤ : K.val.Submodule) isLocal_top ≅ K :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => (LinearEquiv.ofTop _ rfl).toModuleIso))

/-- `I ^ 0 K = K`. -/
def filtZeroIso : filt I K 0 ≅ K :=
  { hom := inclusion _ _ (powSmul_le isLocal_top)
    inv := inclusion _ _ (powSmul_zero I isLocal_top).ge
    hom_inv_id := rfl
    inv_hom_id := rfl } ≪≫ topIso K

end Filtration

set_option hygiene false in
local notation "Γ₀" => sheafSectionsOver (X := Y.toTopCat) ⊤

/-- `H^i` vanishes on the middle term of a short exact sequence whose outer terms have vanishing
`H^i`. -/
theorem isZero_H_of_shortExact {S : ShortComplex Y.Modules} (hS : S.ShortExact) (i : ℕ)
    (h₁ : IsZero (H i S.X₁)) (h₃ : IsZero (H i S.X₃)) : IsZero (H i S.X₂) :=
  (rightDerived_exact₂ Γ₀ (sab_shortExact hS) i).isZero_of_both_zeros (h₁.eq_of_src _ _)
    (h₃.eq_of_tgt _ _)

/-- `H^i` vanishes on the last term of a short exact sequence if `H^i` of the middle term and
`H^(i + 1)` of the first term vanish. -/
theorem isZero_H_of_shortExact₃ {S : ShortComplex Y.Modules} (hS : S.ShortExact) (i : ℕ)
    (h₂ : IsZero (H i S.X₂)) (h₁ : IsZero (H (i + 1) S.X₁)) : IsZero (H i S.X₃) :=
  (rightDerived_exact₃ Γ₀ (sab_shortExact hS) i).isZero_of_both_zeros (h₂.eq_of_src _ _)
    (h₁.eq_of_tgt _ _)

/-- **Vanishing for modules supported on a closed set with affine reduced structure.** On a
Noetherian scheme `Y`, let `K` be a coherent module whose support lies in a closed set `W` such
that the reduced induced subscheme on `W` is affine. Then `H^i(Y, K) = 0` for `i > 0`. -/
theorem isZero_H_of_support_le [IsNoetherian Y] (K : Y.Modules) (hK : IsCoherent K)
    (W : Closeds Y) (hW : moduleSheafSupport K ⊆ W) [IsAffine (reducedInducedSubscheme W)]
    (i : ℕ) (hi : 0 < i) : IsZero (H i K) := by
  set I := Scheme.IdealSheafData.vanishingIdeal W
  have : K.IsQuasicoherent := hK.isQuasicoherent
  have := isQuasicoherent_top (E := K)
  have : IsAffine I.subscheme := ‹IsAffine (reducedInducedSubscheme W)›
  have : IsLocallyNoetherian I.subscheme :=
    (inferInstance : IsNoetherian (reducedInducedSubscheme W)).toIsLocallyNoetherian
  obtain ⟨m, hm⟩ := exists_isZero_powSmul K hK W hW
  have hquot : ∀ k, IsZero (H i (cokernel (filtι I K k))) := by
    intro k
    have := isQuasicoherent_powSmul I k (isLocal_top (E := K))
    have := isQuasicoherent_powSmul I (k + 1) (isLocal_top (E := K))
    have : (cokernel (filtι I K k)).IsQuasicoherent := isQuasicoherent_cokernel _
    obtain ⟨G, hG, ⟨e⟩⟩ :=
      ReducedComponentsAffine.ClosedDescent.exists_isQuasicoherent_iso_pushforward (I := I)
        (Q := cokernel (filtι I K k)) (fun U c hc s => smul_eq_zero_cokernel I K k c hc s)
    exact (ReducedComponentsAffine.isZero_H_pushforward I.subschemeι G i hi).of_iso
      ((sheafCohomology Y.toTopCat i).mapIso ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e))
  have key : ∀ j, j ≤ m → IsZero (H i (filt I K (m - j))) := by
    intro j
    induction j with
    | zero =>
      intro _
      simpa using isZero_H_of_isZero hm i
    | succ j ih =>
      intro hj
      obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
      have hk' : m - (j + 1) = k := by omega
      rw [hk']
      have h₁ : IsZero (H i (filt I K (k + 1))) := by
        rw [← hk]
        exact ih (by omega)
      exact isZero_H_of_shortExact (filtSC_shortExact I K k) i h₁ (hquot k)
  have h0 := key m le_rfl
  rw [Nat.sub_self] at h0
  exact h0.of_iso ((sheafCohomology Y.toTopCat i).mapIso
    ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso (filtZeroIso I K).symm))

/-- If `ι` is the first map of a short exact sequence of `𝒪_Y`-modules and `ι ≫ φ = 0` for a
morphism `φ` which is an isomorphism on stalks at `x`, then `x` is not in the support of the
source of `ι`. -/
theorem not_mem_support_of_shortExact {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    {C : Y.Modules} (φ : S.X₂ ⟶ C) (h : S.f ≫ φ = 0) (x : Y)
    (hφ : IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ)) :
    x ∉ moduleSheafSupport S.X₁ := by
  set Φ := Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have h0 : Φ.map S.f = 0 := by
    rw [← cancel_mono (Φ.map φ), ← Φ.map_comp, h, Φ.map_zero, zero_comp]
  have hmono : Mono (Φ.map S.f) :=
    (TopCat.Presheaf.mono_iff_stalk_mono _).1 (sab_shortExact hS).mono_f x
  rw [h0] at hmono
  have hz : IsZero (Φ.obj S.X₁) := IsZero.of_mono_zero _ (Φ.obj S.X₂)
  rw [mem_moduleSheafSupport_iff, not_nontrivial_iff_subsingleton]
  exact AddCommGrpCat.subsingleton_of_isZero hz

/-- If `π` is an epimorphism of `𝒪_Y`-modules and `φ ≫ π = 0` for a morphism `φ` which is an
isomorphism on stalks at `x`, then `x` is not in the support of the target of `π`. -/
theorem not_mem_support_of_epi {A B C : Y.Modules} (φ : A ⟶ B) (π : B ⟶ C) [Epi π]
    (h : φ ≫ π = 0) (x : Y)
    (hφ : IsIso ((Scheme.Modules.toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ)) :
    x ∉ moduleSheafSupport C := by
  set Φ := Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have h0 : Φ.map π = 0 := by
    rw [← cancel_epi (Φ.map φ), ← Φ.map_comp, h, Φ.map_zero, comp_zero]
  have hsurj : Function.Surjective (Φ.map π) := by
    refine (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).1 ?_ x
    refine (TopCat.Presheaf.isLocallySurjective_iff _).2 fun U t y hy => ?_
    obtain ⟨V, hVU, hyV, s, hs⟩ := Hartshorne.modules_exists_local_lift π t hy
    exact ⟨V, hVU, ⟨s, hs⟩, hyV⟩
  rw [mem_moduleSheafSupport_iff, not_nontrivial_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  rw [h0]
  rfl

/-- **The integral case of Chevalley's theorem.** Let `f : X ⟶ Y` be a finite surjective
morphism from an affine Noetherian scheme to an integral Noetherian separated scheme. If the
reduced induced subscheme on every proper closed subset of `Y` is affine, then `Y` is affine. -/
theorem isAffine_of_isIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Surjective f]
    [IsIntegral Y] [IsNoetherian Y] [Y.IsSeparated] [IsNoetherian X] [IsAffine X]
    (hW : ∀ W : Closeds Y, W ≠ ⊤ → IsAffine (reducedInducedSubscheme W)) : IsAffine Y := by
  refine ((isAffine_tfae_sheafCohomology Y).out 2 0).mp fun J hJ => ?_
  obtain ⟨M, hM, r, hr, α, hα⟩ := exists_genericFiniteModuleFrame f
  obtain ⟨G, hG, β, hβ⟩ := exists_genericCoherentApproximation f M hM r α hα J.toModules hJ
  have : G.IsQuasicoherent := hG.isQuasicoherent
  have hE : IsCoherent (⨁ fun _ : Fin r => J.toModules) :=
    (coherentModules Y).prop_of_isLimit_fan (biproduct.isLimit _) fun _ => hJ
  have hfG : IsCoherent ((Scheme.Modules.pushforward f).obj G) :=
    isCoherent_pushforward_of_isFinite f hG
  let S₁ := ShortComplex.mk (kernel.ι (Abelian.factorThruImage β)) (Abelian.factorThruImage β)
    (kernel.condition _)
  have hS₁ : S₁.ShortExact := ShortComplex.ShortExact.mk'
    (S₁.exact_of_f_is_kernel (kernelIsKernel _)) inferInstance inferInstance
  let S₂ := ShortComplex.mk (kernel.ι (cokernel.π β)) (cokernel.π β) (kernel.condition _)
  have hS₂ : S₂.ShortExact := ShortComplex.ShortExact.mk'
    (S₂.exact_of_f_is_kernel (kernelIsKernel _)) inferInstance inferInstance
  have hC : IsCoherent (cokernel β) := isCoherent_cokernel β hfG hE
  have hK : IsCoherent (kernel (Abelian.factorThruImage β)) :=
    isCoherent_kernel _ hfG (isCoherent_kernel _ hE hC)
  have hηK : genericPoint Y ∉ moduleSheafSupport S₁.X₁ := by
    refine not_mem_support_of_shortExact hS₁ β ?_ _ hβ
    change kernel.ι _ ≫ β = 0
    calc kernel.ι (Abelian.factorThruImage β) ≫ β =
        kernel.ι (Abelian.factorThruImage β) ≫ (Abelian.factorThruImage β ≫
          Abelian.image.ι β) := by rw [Abelian.image.fac]
      _ = 0 := by rw [← Category.assoc, kernel.condition, zero_comp]
  have hηC : genericPoint Y ∉ moduleSheafSupport (cokernel β) :=
    not_mem_support_of_epi β (cokernel.π β) (cokernel.condition β) _ hβ
  let W₁ : Closeds Y := ⟨_, isClosed_moduleSheafSupport_of_isCoherent _ hK⟩
  let W₂ : Closeds Y := ⟨_, isClosed_moduleSheafSupport_of_isCoherent _ hC⟩
  have := hW W₁ fun h => hηK (show genericPoint Y ∈ (W₁ : Set Y) by rw [h]; trivial)
  have := hW W₂ fun h => hηC (show genericPoint Y ∈ (W₂ : Set Y) by rw [h]; trivial)
  have hH₁ : IsZero (H 1 ((Scheme.Modules.pushforward f).obj G)) :=
    (sheafCohomology_isZero_of_isQuasicoherent_of_isAffine G 1 one_pos).of_iso
      (sheafCohomologyIsoPushforwardOfIsAffineHom f G 1).symm
  have hIm : IsZero (H 1 S₁.X₃) :=
    isZero_H_of_shortExact₃ hS₁ 1 hH₁ (isZero_H_of_support_le _ hK W₁ subset_rfl 2 two_pos)
  have hsum : IsZero (H 1 S₂.X₂) :=
    isZero_H_of_shortExact hS₂ 1 hIm (isZero_H_of_support_le _ hC W₂ subset_rfl 1 one_pos)
  let Fc : Y.Modules ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf Y.ringCatSheaf ⋙ sheafCohomology Y.toTopCat 1
  have hcomp : Fc.map (biproduct.ι (fun _ : Fin r => J.toModules) ⟨0, hr⟩) ≫
      Fc.map (biproduct.π (fun _ : Fin r => J.toModules) ⟨0, hr⟩) = 𝟙 _ := by
    rw [← Fc.map_comp, biproduct.ι_π_self, Fc.map_id]
  change IsZero (Fc.obj J.toModules)
  rw [IsZero.iff_id_eq_zero, ← hcomp, hsum.eq_of_tgt (Fc.map (biproduct.ι _ _)) 0, zero_comp]

end ChevalleyDescent

end Hartshorne
