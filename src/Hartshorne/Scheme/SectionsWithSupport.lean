/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.IdealPowerProduct
import Hartshorne.Scheme.CoherentFreeLocus
import Hartshorne.Scheme.ModuleSheafSupport
import Hartshorne.Cohomology.LocalCohomologyDerivedTorsion

/-!
# Sections with support in a closed subset

Hartshorne, *Algebraic Geometry*, II, Exercise 5.6(d) (p. 124).

For an `𝒪_X`-module `E` and a subset `Z ⊆ X`, the sections of `E` over `U` supported in `Z` are
those whose germs vanish at every point of `U \ Z` (`supportSubmodule`). They form a submodule
sheaf `Γ_Z(E)` of `E` (`sectionsWithSupport`).

* `exists_pow_smul_eq_zero_iff`: over a Noetherian ring `R`, an element `s` of a module is killed
  by a power of an ideal `a` exactly when `s` vanishes in the localization at every prime not
  containing `a`.

For a Noetherian ring `R`, an ideal `a` and an `R`-module `M`, let
`Γ_a(M) = {m | aⁿ m = 0 for some n}` (`Ideal.primaryComponent M a`). Then:

* `sectionsWithSupportIso`: `Γ_{V(a)}(M̃) ≅ Γ_a(M)~`;
* `isLocalizedModule_sectionsWithSupport_basicOpen`: the sections of `Γ_{V(a)}(M̃)` over `D(f)`
  are `Γ_a(M)_f`;
* `isLocalizedModule_sectionsWithSupport_stalk`: the stalk of `Γ_{V(a)}(M̃)` at `p` is
  `Γ_a(M)_p`.

The proof shows that the supported sections over `D(f)` are the localization of the supported
global sections (`isLocalizedModule_supportRestrict`), so `Γ_{V(a)}(M̃)` is quasi-coherent, and
identifies the supported global sections with `Γ_a(M)` (`isSupportedIn_toOpen_top_iff`).
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

/-! ### Torsion and support over a Noetherian ring -/

/-- Over a Noetherian ring, `aⁿ s = 0` for some `n` if and only if, for every prime `p` not
containing `a`, some `c ∉ p` kills `s`. -/
theorem exists_pow_smul_eq_zero_iff {R N : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup N] [Module R N] (a : Ideal R) (s : N) :
    (∃ n : ℕ, ∀ r ∈ a ^ n, r • s = 0) ↔
      ∀ p : Ideal R, p.IsPrime → ¬ a ≤ p → ∃ c ∉ p, c • s = 0 := by
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R N s)
  have hI : ∀ r, r ∈ I ↔ r • s = 0 := fun r => Iff.rfl
  constructor
  · rintro ⟨n, hn⟩ p hp hap
    obtain ⟨r, hra, hrp⟩ := Set.not_subset.mp hap
    exact ⟨r ^ n, fun h => hrp (hp.mem_of_pow_mem n h), hn _ (Ideal.pow_mem_pow hra n)⟩
  · intro h
    have hrad : a ≤ I.radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf fun p ⟨hIp, hp⟩ => ?_
      by_contra hap
      obtain ⟨c, hcp, hc⟩ := h p hp hap
      exact hcp (hIp ((hI c).2 hc))
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian a)
    exact ⟨n, fun r hr => (hI r).1 (hn hr)⟩

/-! ### The submodule sheaf of sections with support -/

variable {X : Scheme.{u}}

open ArtinReesKernelSheaf

/-- A section of `E` over `U` is supported in `Z` if its support (the points of `U` where its
germ is nonzero) lies in `Z`. -/
def IsSupportedIn (E : X.Modules) (Z : Set X) {U : X.Opens} (s : Γ(E, U)) : Prop :=
  Subtype.val '' sectionSupport ⟨E.presheaf, E.isSheaf⟩ U s ⊆ Z

variable {E : X.Modules} {Z : Set X}

/-- A section is supported in `Z` exactly when its germs vanish at every point of `U \ Z`. -/
lemma isSupportedIn_iff {U : X.Opens} (s : Γ(E, U)) :
    IsSupportedIn E Z s ↔ ∀ (x : X) (hx : x ∈ U), x ∉ Z → E.presheaf.germ U x hx s = 0 := by
  constructor
  · intro h x hx hZ
    by_contra hne
    exact hZ (h ⟨⟨x, hx⟩, hne, rfl⟩)
  · rintro h _ ⟨⟨x, hx⟩, hne, rfl⟩
    by_contra hZ
    exact hne (h x hx hZ)

lemma isSupportedIn_zero (U : X.Opens) : IsSupportedIn E Z (0 : Γ(E, U)) :=
  (isSupportedIn_iff _).2 fun _ _ _ => map_zero _

lemma IsSupportedIn.add {U : X.Opens} {s t : Γ(E, U)} (hs : IsSupportedIn E Z s)
    (ht : IsSupportedIn E Z t) : IsSupportedIn E Z (s + t) := (isSupportedIn_iff _).2
  fun x hx hZ => by
    rw [map_add, (isSupportedIn_iff s).1 hs x hx hZ, (isSupportedIn_iff t).1 ht x hx hZ, add_zero]

lemma IsSupportedIn.smul {U : X.Opens} (r : Γ(X, U)) {s : Γ(E, U)} (hs : IsSupportedIn E Z s) :
    IsSupportedIn E Z (r • s) := (isSupportedIn_iff _).2 fun x hx hZ => by
  rw [schemeModules_germ_smul, (isSupportedIn_iff s).1 hs x hx hZ]
  exact smul_zero _

lemma IsSupportedIn.res {U V : X.Opens} (h : V ≤ U) {s : Γ(E, U)} (hs : IsSupportedIn E Z s) :
    IsSupportedIn E Z (res E h s) := (isSupportedIn_iff _).2 fun x hx hZ => by
  rw [res_apply, TopCat.Presheaf.germ_res_apply]
  exact (isSupportedIn_iff s).1 hs x _ hZ

variable (E Z) in
/-- The sections of `E` over `U` supported in `Z`: their germs vanish at every point of
`U \ Z`. -/
def supportSubmodule : E.val.Submodule where
  obj U :=
    { carrier := {s | IsSupportedIn E Z (U := U.unop) s}
      zero_mem' := isSupportedIn_zero U.unop
      add_mem' := fun hs ht => IsSupportedIn.add hs ht
      smul_mem' := fun r _ hs => IsSupportedIn.smul (U := U.unop) r hs }
  map f _ hs := IsSupportedIn.res (leOfHom f.unop) hs

variable (E Z)

theorem mem_supportSubmodule_iff {U : X.Opens} (s : Γ(E, U)) :
    s ∈ sub (supportSubmodule E Z) U ↔ IsSupportedIn E Z s :=
  Iff.rfl

/-- Support in `Z` is a local condition. -/
theorem isLocal_supportSubmodule : IsLocal (supportSubmodule E Z) := by
  intro U s hs
  refine (isSupportedIn_iff s).2 fun x hx hZ => ?_
  obtain ⟨V, hVU, hxV, hV⟩ := hs x hx
  have := (isSupportedIn_iff _).1 hV x hxV hZ
  rwa [res_apply, TopCat.Presheaf.germ_res_apply] at this

/-- **The sheaf `Γ_Z(E)` of sections of `E` with support in `Z`**, a submodule sheaf of `E`. -/
def sectionsWithSupport : X.Modules :=
  toModules (supportSubmodule E Z) (isLocal_supportSubmodule E Z)

end Hartshorne

namespace Hartshorne

open ArtinReesKernelSheaf

universe v

section Affine

variable {R : CommRingCat.{v}} (M : ModuleCat.{v} R)

theorem tilde_germ_toOpen_top (x : PrimeSpectrum.Top R) (m : M) :
    (tilde M).presheaf.germ ⊤ x trivial ((tilde.toOpen M ⊤).hom m) = (tilde.toStalk M x).hom m := by
  rfl

theorem tilde_germ_res_toOpen_top (U : (Spec R).Opens) (x : PrimeSpectrum.Top R) (hx : x ∈ U)
    (m : M) :
    (tilde M).presheaf.germ U x hx
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.map U.leTop.op ((tilde.toOpen M ⊤).hom m)) =
      (tilde.toStalk M x).hom m := by
  rw [← tilde_germ_toOpen_top]
  exact TopCat.Presheaf.germ_res_apply (tilde M).presheaf (homOfLE le_top) x hx _

theorem tilde_toStalk_eq_zero_iff (x : PrimeSpectrum.Top R) (m : M) :
    (tilde.toStalk M x).hom m = 0 ↔ ∃ c ∉ x.asIdeal, c • m = 0 := by
  have := x.isPrime
  rw [IsLocalizedModule.eq_zero_iff x.asIdeal.primeCompl]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, c.2, hc⟩, fun ⟨c, hc, h⟩ => ⟨⟨c, hc⟩, h⟩⟩

variable [IsNoetherianRing R] (a : Ideal R)

/-- A global section `m` of `M̃` is supported in `V(a)` exactly when `m ∈ Γ_a(M)`. -/
theorem isSupportedIn_toOpen_top_iff (m : M) :
    IsSupportedIn (tilde M) (PrimeSpectrum.zeroLocus (a : Set R)) ((tilde.toOpen M ⊤).hom m) ↔
      m ∈ Ideal.primaryComponent M a := by
  change Subtype.val '' sectionSupport ⟨(tilde M).presheaf, (tilde M).isSheaf⟩ ⊤
    ((tilde.toOpen M ⊤).hom m) ⊆ _ ↔ _
  rw [sectionSupport_tilde_toOpen_top]
  refine (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).trans ?_
  rw [Ideal.primaryComponent_mem]
  simp only [Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h (IsNoetherian.noetherian a)
    exact ⟨n, fun r hr => (Submodule.mem_annihilator_span_singleton m r).1 (hn hr)⟩
  · rintro ⟨n, hn⟩ r hr
    exact ⟨n, (Submodule.mem_annihilator_span_singleton m _).2 (hn _ (Ideal.pow_mem_pow hr n))⟩

/-- On a basic open `D(f)`, if `s • t` is the restriction of the global section `m` for some
power `s` of `f`, and `t` is supported in `V(a)`, then some `fⁿ m` lies in `Γ_a(M)`. -/
theorem exists_pow_smul_mem_primaryComponent (f : R)
    (t : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (PrimeSpectrum.basicOpen f)))
    (ht : IsSupportedIn (tilde M) (PrimeSpectrum.zeroLocus (a : Set R)) t) (k : ℕ) (m : M)
    (hm : f ^ k • t =
      (modulesSpecToSheaf.obj (tilde M)).presheaf.map (PrimeSpectrum.basicOpen f).leTop.op
        ((tilde.toOpen M ⊤).hom m)) :
    ∃ n : ℕ, f ^ n • m ∈ Ideal.primaryComponent M a := by
  have hloc : ∀ p : Ideal R, p.IsPrime → ¬ a * Ideal.span {f} ≤ p → ∃ c ∉ p, c • m = 0 := by
    intro p hp hp'
    have haf : ¬ a ≤ p := fun h => hp' (Ideal.mul_le_left.trans h)
    have hfp : f ∉ p := fun h => hp' (Ideal.mul_le_right.trans ((Ideal.span_singleton_le_iff_mem
      _).2 h))
    let x : PrimeSpectrum.Top R := ⟨p, hp⟩
    have hx : x ∈ PrimeSpectrum.basicOpen f := hfp
    have h0 := (isSupportedIn_iff _).1 (ht.smul (((Spec R).presheaf.map
      (PrimeSpectrum.basicOpen f).leTop.op) ((Scheme.ΓSpecIso R).inv (f ^ k)))) x hx
      (fun hxZ => haf ((PrimeSpectrum.mem_zeroLocus _ _).1 hxZ))
    change (tilde M).presheaf.germ _ x hx (f ^ k • t) = 0 at h0
    rw [hm] at h0
    exact (tilde_toStalk_eq_zero_iff M x m).1
      ((tilde_germ_res_toOpen_top M _ x hx m).symm.trans h0)
  obtain ⟨n, hn⟩ := (exists_pow_smul_eq_zero_iff (a * Ideal.span {f}) m).2 hloc
  refine ⟨n, (Ideal.primaryComponent_mem _ _ _).2 ⟨n, ?_⟩⟩
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨r, hr⟩
  rw [smul_smul]
  refine hn _ ?_
  rw [mul_pow, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_mul hr (Ideal.mem_span_singleton_self _)

variable {M} in
/-- The `R`-submodule of sections of `M̃` over `U` supported in `V(a)`. -/
def supportRSubmodule (U : (Spec R).Opens) :
    Submodule R ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op U)) where
  carrier := {t | IsSupportedIn (tilde M) (PrimeSpectrum.zeroLocus (a : Set R)) (U := U) t}
  zero_mem' := isSupportedIn_zero U
  add_mem' := fun hs ht => IsSupportedIn.add hs ht
  smul_mem' := fun r _ ht =>
    IsSupportedIn.smul (U := U) (((Spec R).presheaf.map U.leTop.op) ((Scheme.ΓSpecIso R).inv r)) ht

/-- The sections of `Γ_{V(a)}(M̃)` over `U`, as `R`-modules, are the supported sections of
`M̃`. -/
def sectionsWithSupportEquiv (U : (Spec R).Opens) :
    (modulesSpecToSheaf.obj (sectionsWithSupport (tilde M)
      (PrimeSpectrum.zeroLocus (a : Set R)))).presheaf.obj (op U) ≃ₗ[R]
      supportRSubmodule (M := M) a U :=
  LinearEquiv.refl R _

omit [IsNoetherianRing R] in
/-- Restriction from `⊤` to `U` preserves sections supported in `V(a)`. -/
theorem isSupportedIn_map_leTop (U : (Spec R).Opens)
    (t : (modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op ⊤))
    (ht : t ∈ supportRSubmodule (M := M) a ⊤) :
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map U.leTop.op).hom t ∈
      supportRSubmodule (M := M) a U :=
  IsSupportedIn.res (E := tilde M) (le_top : U ≤ ⊤) ht

/-- Restriction from `⊤` to `U` on supported sections of `M̃`. -/
def supportRestrict (U : (Spec R).Opens) : supportRSubmodule (M := M) a ⊤ →ₗ[R]
    supportRSubmodule (M := M) a U :=
  LinearMap.restrict ((modulesSpecToSheaf.obj (tilde M)).presheaf.map U.leTop.op).hom
    (isSupportedIn_map_leTop M a U)

set_option backward.isDefEq.respectTransparency.types false in
/-- Supported sections of `M̃` over `D(f)` are the localization at `f` of supported global
sections. -/
theorem isLocalizedModule_supportRestrict (f : R) :
    IsLocalizedModule (Submonoid.powers f) (supportRestrict M a (PrimeSpectrum.basicOpen f)) := by
  have hloc : IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.map (PrimeSpectrum.basicOpen f).leTop.op).hom :=
    isLocalizing_tilde M f
  refine ⟨fun c => ?_, fun y => ?_, fun {y₁ y₂} h => ?_⟩
  · obtain ⟨_, n, rfl⟩ := c
    rw [Module.End.isUnit_iff]
    have hreg : IsSMulRegular ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj
        (op (PrimeSpectrum.basicOpen f))) (f ^ n) :=
      (Scheme.Modules.isSMulRegular_of_le_basicOpen (M := tilde M) le_rfl).pow n
    let c' : Γ(Spec R, PrimeSpectrum.basicOpen f) :=
      (Spec R).presheaf.map (PrimeSpectrum.basicOpen f).leTop.op ((Scheme.ΓSpecIso R).inv (f ^ n))
    have hu : IsUnit c' := ArtinReesKernelSheaf.isUnit_res_of_le_basicOpen
      ((Scheme.ΓSpecIso R).inv (f ^ n)) le_top (by
        rw [basicOpen_eq_of_affine]
        intro x hx h
        exact hx (x.isPrime.mem_of_pow_mem n h))
    refine ⟨fun y₁ y₂ h => Subtype.ext (hreg (congrArg Subtype.val h)), fun y => ?_⟩
    let s : Γ(tilde M, PrimeSpectrum.basicOpen f) := y.1
    have hs : IsSupportedIn (tilde M) (PrimeSpectrum.zeroLocus (a : Set R)) s := y.2
    refine ⟨⟨(hu.unit⁻¹ : (Γ(Spec R, PrimeSpectrum.basicOpen f))ˣ).1 • s,
      IsSupportedIn.smul (X := Spec R) _ hs⟩, Subtype.ext ?_⟩
    change c' • ((hu.unit⁻¹ : (Γ(Spec R, PrimeSpectrum.basicOpen f))ˣ).1 • s) = s
    rw [smul_smul, hu.mul_val_inv, one_smul]
  · obtain ⟨⟨m₀, ⟨_, k, rfl⟩⟩, h⟩ := hloc.surj y.1
    obtain ⟨m, rfl⟩ : ∃ m, (tilde.toOpen M ⊤).hom m = m₀ :=
      ⟨(tilde.isoTop M).inv m₀, (tilde.isoTop M).inv_hom_id_apply m₀⟩
    obtain ⟨n, hn⟩ := exists_pow_smul_mem_primaryComponent M a f y.1 y.2 k m h
    refine ⟨⟨⟨(tilde.toOpen M ⊤).hom (f ^ n • m), (isSupportedIn_toOpen_top_iff M a _).2 hn⟩,
      ⟨f ^ n * f ^ k, n + k, pow_add f n k⟩⟩, Subtype.ext ?_⟩
    change (f ^ n * f ^ k) • y.1 = ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
      (PrimeSpectrum.basicOpen f).leTop.op).hom ((tilde.toOpen M ⊤).hom (f ^ n • m))
    rw [map_smul, map_smul, mul_smul]
    exact congrArg (f ^ n • ·) h
  · obtain ⟨c, hc⟩ := hloc.exists_of_eq (congrArg Subtype.val h)
    exact ⟨c, Subtype.ext hc⟩

/-- **`Γ_{V(a)}(M̃)` is quasi-coherent**: its restriction to each `D(f)` is the localization of
its global sections. -/
theorem isLocalizing_sectionsWithSupport :
    IsLocalizing (modulesSpecToSheaf.obj
      (sectionsWithSupport (tilde M) (PrimeSpectrum.zeroLocus (a : Set R)))) :=
  fun f => isLocalizedModule_supportRestrict M a f

instance isIso_fromTildeΓ_sectionsWithSupport :
    IsIso (sectionsWithSupport (tilde M) (PrimeSpectrum.zeroLocus (a : Set R))).fromTildeΓ :=
  (isIso_fromTildeΓ_iff_isLocalizing _).2 (isLocalizing_sectionsWithSupport M a)

/-- The supported global sections of `M̃` are `Γ_a(M)`. -/
def primaryComponentEquivSupport :
    Ideal.primaryComponent M a ≃ₗ[R] supportRSubmodule (M := M) a ⊤ :=
  (tilde.isoTop M).toLinearEquiv.ofSubmodules _ _ (by
    ext t
    obtain ⟨m, rfl⟩ : ∃ m, (tilde.toOpen M ⊤).hom m = t :=
      ⟨(tilde.isoTop M).inv t, (tilde.isoTop M).inv_hom_id_apply t⟩
    change _ ↔ IsSupportedIn _ _ _
    rw [isSupportedIn_toOpen_top_iff, Submodule.mem_map]
    constructor
    · rintro ⟨m', hm', he⟩
      have : m' = m := (tilde.isoTop M).toLinearEquiv.injective he
      exact this ▸ hm'
    · exact fun hm => ⟨m, hm, rfl⟩)

/-- **Affine sections with support** (Hartshorne II, Exercise 5.6(d)). For a Noetherian ring
`R`, an ideal `a` and an `R`-module `M`, the sheaf `Γ_{V(a)}(M̃)` of sections of `M̃` supported
in `V(a)` is canonically isomorphic to `Γ_a(M)~`, where
`Γ_a(M) = {m | aⁿ m = 0 for some n}`. -/
def sectionsWithSupportIso :
    sectionsWithSupport (tilde M) (PrimeSpectrum.zeroLocus (a : Set R)) ≅
      tilde ((idealPowerTorsionFunctor R a).obj M) :=
  (asIso (sectionsWithSupport (tilde M) (PrimeSpectrum.zeroLocus (a : Set R))).fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso
      ((sectionsWithSupportEquiv M a ⊤).trans (primaryComponentEquivSupport M a).symm).toModuleIso

/-- **Sections over a basic open.** The sections of `Γ_{V(a)}(M̃)` over `D(f)` are `Γ_a(M)_f`:
the map `Γ_a(M) → Γ(D(f), Γ_{V(a)}(M̃))`, `m ↦ m|_{D(f)}`, is a localization at `f`. -/
theorem isLocalizedModule_sectionsWithSupport_basicOpen (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      (supportRestrict M a (PrimeSpectrum.basicOpen f) ∘ₗ
        (primaryComponentEquivSupport M a).toLinearMap) := by
  have := isLocalizedModule_supportRestrict M a f
  exact IsLocalizedModule.of_linearEquiv_right _ _ _

attribute [local instance] FreeLocusAux.freeLocusStalkAlgebra FreeLocusAux.freeLocus_asIdeal_isPrime
  FreeLocusAux.freeLocusStalkModule

/-- **Stalks.** The stalk of `Γ_{V(a)}(M̃)` at a point `y` of `Spec R` is `Γ_a(M)_y`: the map
`Γ_a(M) → Γ_{V(a)}(M̃)_y`, `m ↦ germ of m`, is a localization at the prime `y`. -/
theorem isLocalizedModule_sectionsWithSupport_stalk (y : Spec R) :
    IsLocalizedModule y.asIdeal.primeCompl
      (FreeLocusAux.germTopLinear
          (sectionsWithSupport (tilde M) (PrimeSpectrum.zeroLocus (a : Set R))) y ∘ₗ
        ((primaryComponentEquivSupport M a).trans
          (sectionsWithSupportEquiv M a ⊤).symm).toLinearMap) := by
  have := FreeLocusAux.isLocalizedModule_germTopLinear _ (isLocalizing_sectionsWithSupport M a) y
  exact IsLocalizedModule.of_linearEquiv_right _ _ _

end Affine

end Hartshorne
