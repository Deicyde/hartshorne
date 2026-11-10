/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SheafTensorOperations
import Hartshorne.RingedSpace.FiniteLocallyFreeDuality
import Hartshorne.Scheme.LocallyFreeRinged

/-!
# Clearing denominators with a section of an invertible sheaf

Hartshorne, *Algebraic Geometry*, II, Lemma 5.14 (pp. 118–119).

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `f ∈ Γ(X, L)`. The *nonvanishing
locus* `X_f` of `f` is the set of points `x` with `f_x ∉ 𝔪_x L_x` (`nonvanishingLocus`); it is
open (`isOpen_nonvanishingLocus`, `nonvanishingLocusOpens`). For an `𝒪_X`-module `F`, a section
`s ∈ Γ(U, F)` and `n ≥ 0`, the section `f^n s ∈ Γ(U, F ⊗ L^{⊗ n})` is `s ⊗ (f|_U)^{⊗ n}`
(`sectionPowSMul`), where `L^{⊗ n}` is the `n`-th tensor power `moduleSheafTensorPower n L`.
For quasi-coherent `F` we prove:

* (a) if `X` is quasi-compact and `s ∈ Γ(X, F)` restricts to zero on `X_f`, then `f^n s = 0`
  for some `n > 0` (`exists_sectionPowSMul_eq_zero`);
* (b) if `X` has a finite cover by open affines `Uᵢ` with `L|_{Uᵢ}` free and every `Uᵢ ∩ Uⱼ`
  quasi-compact, then for every `t ∈ Γ(X_f, F)` there are `n > 0` and a global section of
  `F ⊗ L^{⊗ n}` restricting to `f^n t` on `X_f` (`exists_sectionPowSMul_extension`).

The proof is local. On an open `U` where `L` is trivialized by a section `e` (every section of
`L` over an open `V ⊆ U` is uniquely `a • e|_V`, `IsTrivializingSection`), write `f|_U = g • e`;
then `X_f ∩ U` is the basic open `D(g)` (`nonvanishingLocus_inter_eq`), and
`f^n s|_U = s|_U ⊗ (g e)^{⊗ n} = (g^n s|_U) ⊗ e^{⊗ n}` (`sectionPowSMul_smul`). On an affine `U`,
the restriction `Γ(U, F) → Γ(D(g), F)` of a quasi-coherent `F` is the localization away from `g`
(transported from Mathlib's `isIso_fromTildeΓ_iff_isLocalizing` on `Spec Γ(X, U)`), which gives
the two clauses on one affine (`exists_pow_smul_eq_zero_of_isAffineOpen`,
`exists_pow_smul_extension_of_isAffineOpen`; the extension needs `F` quasi-coherent only on `U`,
`exists_pow_smul_extension_of_isLocalizing`), and then on a quasi-compact open
(`exists_pow_smul_eq_zero_of_isCompact`). A finite cover gives a common exponent, and the local
extensions are glued after a further power of `f`, using (a) on the overlaps.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

variable {X : Scheme.{u}}

/-! ### Sections `f^n s` -/

section SectionPow

variable (F L : X.Modules) (n : ℕ)

/-- The `𝒪_X`-module `F ⊗ L^{⊗ n}`. -/
noncomputable abbrev tensorPowerTwist : X.Modules :=
  moduleSheafTensor F (moduleSheafTensorPower n L)

/-- For a section `f` of `L` and a section `s` of `F` over `U`, the section
`f^n s = s ⊗ f^{⊗ n}` of `F ⊗ L^{⊗ n}` over `U`. -/
noncomputable def sectionPowSMul {U : X.Opens} (f : Γ(L, U)) (s : Γ(F, U)) :
    Γ(tensorPowerTwist F L n, U) :=
  (moduleSheafTensorBilinear F (moduleSheafTensorPower n L)).app (op U) s
    ((moduleSheafTensorPowerMultilinear n L).app (op U) (fun _ => f))

variable {F L n}

theorem sectionPowSMul_smul {U : X.Opens} (f : Γ(L, U)) (s : Γ(F, U)) (a : Γ(X, U)) :
    sectionPowSMul F L n (a • f) s = sectionPowSMul F L n f (a ^ n • s) := by
  unfold sectionPowSMul
  have h1 := ((moduleSheafTensorPowerMultilinear n L).app (op U)).map_smul_univ
    (fun _ => a) (fun _ => f)
  erw [h1, LinearMap.map_smul, LinearMap.map_smul₂]
  congr 1
  exact Fin.prod_const n a

theorem sectionPowSMul_zero {U : X.Opens} (f : Γ(L, U)) :
    sectionPowSMul F L n f 0 = 0 := by
  unfold sectionPowSMul
  erw [LinearMap.map_zero₂]
  rfl

theorem sectionPowSMul_sub {U : X.Opens} (f : Γ(L, U)) (s s' : Γ(F, U)) :
    sectionPowSMul F L n f (s - s') = sectionPowSMul F L n f s - sectionPowSMul F L n f s' := by
  unfold sectionPowSMul
  erw [LinearMap.map_sub₂]
  rfl

theorem sectionPowSMul_map {U V : X.Opens} (i : U ⟶ V) (f : Γ(L, V)) (s : Γ(F, V)) :
    (tensorPowerTwist F L n).presheaf.map i.op
        (sectionPowSMul F L n f s) =
      sectionPowSMul F L n (L.presheaf.map i.op f) (F.presheaf.map i.op s) := by
  unfold sectionPowSMul
  refine ((moduleSheafTensorBilinear F (moduleSheafTensorPower n L)).naturality i.op _ _).trans ?_
  exact congrArg _ ((moduleSheafTensorPowerMultilinear n L).naturality i.op _)

end SectionPow

/-! ### Trivializing sections of an invertible sheaf -/

/-- A section `e` of `L` over `U` *trivializes* `L` on `U` if on every open `V ⊆ U` each
section of `L` is uniquely of the form `a • e|_V` with `a ∈ Γ(V, 𝒪_X)`. -/
def IsTrivializingSection (L : X.Modules) (U : X.Opens) (e : Γ(L, U)) : Prop :=
  ∀ (V : X.Opens) (h : V ≤ U),
    Function.Bijective (fun a : Γ(X, V) => a • L.presheaf.map (homOfLE h).op e)

namespace IsTrivializingSection

variable {L : X.Modules} {U : X.Opens} {e : Γ(L, U)}

theorem restrict (he : IsTrivializingSection L U e) {V : X.Opens} (hVU : V ≤ U) :
    IsTrivializingSection L V (L.presheaf.map (homOfLE hVU).op e) := by
  intro W hW
  have key : (fun a : Γ(X, W) => a • L.presheaf.map (homOfLE hW).op
      (L.presheaf.map (homOfLE hVU).op e)) =
      (fun a : Γ(X, W) => a • L.presheaf.map (homOfLE (hW.trans hVU)).op e) := by
    funext a
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [key]
  exact he W _

/-- A one-element local frame is a trivializing section. -/
theorem of_isLocalFrame {ι : Type u} [Fintype ι] [Unique ι] {e' : ι → Γ(L, U)}
    (he : Ringed.IsLocalFrame (R := X.sheaf) L U e') :
    IsTrivializingSection L U (e' default) := by
  intro V h
  have key : (fun a : Γ(X, V) => a • L.presheaf.map (homOfLE h).op (e' default)) =
      ⇑(Ringed.localFrameMap (R := X.sheaf) L e' h) ∘ ⇑(Equiv.funUnique ι Γ(X, V)).symm := by
    funext a
    change _ = Ringed.localFrameMap (R := X.sheaf) L e' h ((Equiv.funUnique ι Γ(X, V)).symm a)
    refine Eq.trans ?_ (Ringed.localFrameMap_apply (R := X.sheaf) L e' h _).symm
    erw [Fintype.sum_unique]
    rfl
  rw [key]
  exact (he V h).comp (Equiv.funUnique ι Γ(X, V)).symm.bijective

end IsTrivializingSection

/-- An invertible sheaf is trivialized by a section near every point. -/
theorem exists_isTrivializingSection {L : X.Modules} (hL : L.IsInvertible) (x : X) :
    ∃ (U : X.Opens) (e : Γ(L, U)), x ∈ U ∧ IsTrivializingSection L U e := by
  obtain ⟨U, hx, ⟨α⟩⟩ := hL x
  obtain ⟨γ⟩ := (Scheme.Modules.nonempty_restrict_iso_free_iff L U _).mp ⟨α⟩
  exact ⟨U, _, hx, IsTrivializingSection.of_isLocalFrame (Ringed.isLocalFrame_of_over_iso γ)⟩

/-- An invertible sheaf is trivialized by a section on an affine open neighbourhood of every
point. -/
theorem exists_isAffineOpen_isTrivializingSection {L : X.Modules} (hL : L.IsInvertible)
    (x : X) : ∃ (U : X.Opens) (e : Γ(L, U)), x ∈ U ∧ IsAffineOpen U ∧
      IsTrivializingSection L U e := by
  obtain ⟨U, e, hx, he⟩ := exists_isTrivializingSection hL x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  exact ⟨V, _, hxV, hV, he.restrict hVU⟩

/-- If the invertible sheaf `L` is free on `U`, then it is trivialized by a section over `U`. -/
theorem exists_isTrivializingSection_of_isFree {L : X.Modules} (hL : L.IsInvertible)
    {U : X.Opens} (hU : (L.restrict U.ι).IsFree) :
    ∃ e : Γ(L, U), IsTrivializingSection L U e := by
  by_cases hne : ∃ x, x ∈ U
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨I, ⟨α⟩⟩ := hU
    obtain ⟨U', hx', ⟨β⟩⟩ := hL x
    have hcard : Cardinal.mk I = Cardinal.mk (ULift.{u} (Fin 1)) :=
      (L.rankAt_eq α hx).symm.trans (L.rankAt_eq β hx')
    obtain ⟨σ⟩ := Cardinal.eq.mp hcard
    have α' : L.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin 1)) :=
      α ≪≫ SheafOfModules.freeFunctor.mapIso σ.toIso
    obtain ⟨γ⟩ := (Scheme.Modules.nonempty_restrict_iso_free_iff L U _).mp ⟨α'⟩
    exact ⟨_, IsTrivializingSection.of_isLocalFrame (Ringed.isLocalFrame_of_over_iso γ)⟩
  · push Not at hne
    refine ⟨0, fun V hV => ⟨fun a b _ => ?_, fun y => ⟨0, ?_⟩⟩⟩
    · exact TopCat.Presheaf.IsSheaf.section_ext X.sheaf.2
        (fun x hx => absurd (hV hx) (hne x))
    · exact TopCat.Presheaf.IsSheaf.section_ext L.isSheaf
        (fun x hx => absurd (hV hx) (hne x))

/-! ### The nonvanishing locus -/

/-- The stalk `F_x` of an `𝒪_X`-module is a module over the local ring `𝒪_{X,x}`. -/
noncomputable instance moduleSheafStalkModule (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  inferInstanceAs (Module (X.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.presheaf x))

private theorem moduleSheaf_germ_smul (F : X.Modules) {U : X.Opens} (x : X) (hx : x ∈ U)
    (r : Γ(X, U)) (m : Γ(F, U)) :
    F.presheaf.germ U x hx (r • m) = X.presheaf.germ U x hx r • F.presheaf.germ U x hx m :=
  let M : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := F.val
  PresheafOfModules.germ_smul M x U hx r m

/-- **The nonvanishing locus** `X_f` of a global section `f` of an `𝒪_X`-module `L`: the points
`x` at which the germ `f_x` does not lie in `𝔪_x L_x`. -/
def nonvanishingLocus (L : X.Modules) (f : Γ(L, ⊤)) : Set X :=
  {x | L.presheaf.germ ⊤ x trivial f ∉
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x))}

namespace IsTrivializingSection

variable {L : X.Modules} {U : X.Opens} {e : Γ(L, U)}

/-- The germ of a trivializing section generates the stalk. -/
theorem exists_smul_germ_eq (he : IsTrivializingSection L U e) {x : X} (hx : x ∈ U)
    (z : L.presheaf.stalk x) : ∃ b : X.presheaf.stalk x, b • L.presheaf.germ U x hx e = z := by
  obtain ⟨W, hW, hxW, s, rfl⟩ := L.presheaf.exists_le_germ_eq z hx
  obtain ⟨a, ha⟩ := (he W hW).2 s
  refine ⟨X.presheaf.germ W x hxW a, ?_⟩
  rw [← ha, moduleSheaf_germ_smul, TopCat.Presheaf.germ_res_apply]

/-- The germ of a trivializing section is torsion free. -/
theorem eq_zero_of_smul_germ_eq_zero (he : IsTrivializingSection L U e) {x : X} (hx : x ∈ U)
    (b : X.presheaf.stalk x) (hb : b • L.presheaf.germ U x hx e = 0) : b = 0 := by
  obtain ⟨W, hW, hxW, a, rfl⟩ := X.presheaf.exists_le_germ_eq b hx
  rw [← TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE hW) x hxW e,
    ← moduleSheaf_germ_smul] at hb
  obtain ⟨W', hxW', i, j, hi⟩ := L.presheaf.germ_eq x hxW hxW _ 0 (hb.trans (map_zero _).symm)
  have hW' : W' ≤ U := i.le.trans hW
  have h1 : (fun a : Γ(X, W') => a • L.presheaf.map (homOfLE hW').op e)
      (X.presheaf.map i.op a) = (fun a : Γ(X, W') => a • L.presheaf.map (homOfLE hW').op e) 0 := by
    simp only [zero_smul]
    rw [map_zero] at hi
    rw [← hi, Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have h2 := (he W' hW').1 h1
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf i x hxW', h2, map_zero]

/-- On an open trivialized by `e`, with `f|_U = g • e`, a point of `U` lies in the nonvanishing
locus of `f` exactly when it lies in the basic open `D(g)`. -/
theorem mem_nonvanishingLocus_iff (he : IsTrivializingSection L U e) {f : Γ(L, ⊤)}
    {g : Γ(X, U)} (hfg : L.presheaf.map (homOfLE le_top).op f = g • e) {x : X} (hx : x ∈ U) :
    x ∈ nonvanishingLocus L f ↔ x ∈ X.basicOpen g := by
  have hgerm : L.presheaf.germ ⊤ x trivial f =
      X.presheaf.germ U x hx g • L.presheaf.germ U x hx e := by
    rw [← moduleSheaf_germ_smul, ← hfg, TopCat.Presheaf.germ_res_apply]
  rw [Scheme.mem_basicOpen X g x hx]
  simp only [nonvanishingLocus, Set.mem_ofPred_eq, hgerm]
  constructor
  · intro h
    by_contra hg
    exact h (Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hg)
      Submodule.mem_top)
  · intro hg hmem
    have htop : (⊤ : Submodule (X.presheaf.stalk x) (L.presheaf.stalk x)) =
        Submodule.span (X.presheaf.stalk x) {L.presheaf.germ U x hx e} := by
      refine (Submodule.eq_top_iff'.mpr fun z => ?_).symm
      obtain ⟨b, rfl⟩ := he.exists_smul_germ_eq hx z
      exact Submodule.smul_mem _ b (Submodule.mem_span_singleton_self _)
    rw [htop, Submodule.mem_smul_span_singleton] at hmem
    obtain ⟨c, hc, hce⟩ := hmem
    have hsub : (c - X.presheaf.germ U x hx g) • L.presheaf.germ U x hx e = 0 := by
      rw [sub_smul, hce, sub_self]
    have hcg := sub_eq_zero.mp (he.eq_zero_of_smul_germ_eq_zero hx _ hsub)
    exact (IsLocalRing.mem_maximalIdeal _).mp (hcg ▸ hc) hg

theorem nonvanishingLocus_inter_eq (he : IsTrivializingSection L U e) {f : Γ(L, ⊤)}
    {g : Γ(X, U)} (hfg : L.presheaf.map (homOfLE le_top).op f = g • e) :
    nonvanishingLocus L f ∩ (U : Set X) = (X.basicOpen g : Set X) := by
  ext x
  constructor
  · rintro ⟨h, hx⟩
    exact (he.mem_nonvanishingLocus_iff hfg hx).mp h
  · intro h
    have hx : x ∈ U := X.basicOpen_le g h
    exact ⟨(he.mem_nonvanishingLocus_iff hfg hx).mpr h, hx⟩

theorem basicOpen_le_nonvanishingLocus (he : IsTrivializingSection L U e) {f : Γ(L, ⊤)}
    {g : Γ(X, U)} (hfg : L.presheaf.map (homOfLE le_top).op f = g • e) :
    (X.basicOpen g : Set X) ⊆ nonvanishingLocus L f := by
  rw [← he.nonvanishingLocus_inter_eq hfg]
  exact Set.inter_subset_left

end IsTrivializingSection

/-- The nonvanishing locus of a section of an invertible sheaf is open. -/
theorem isOpen_nonvanishingLocus {L : X.Modules} (hL : L.IsInvertible) (f : Γ(L, ⊤)) :
    IsOpen (nonvanishingLocus L f) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, e, hxU, he⟩ := exists_isTrivializingSection hL x
  obtain ⟨g, hg⟩ := (he U le_rfl).2 (L.presheaf.map (homOfLE le_top).op f)
  have hfg : L.presheaf.map (homOfLE le_top).op f = g • e := by
    rw [← hg]
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨X.basicOpen g, he.basicOpen_le_nonvanishingLocus hfg, (X.basicOpen g).isOpen,
    (he.mem_nonvanishingLocus_iff hfg hxU).mp hx⟩

/-- The nonvanishing locus `X_f` of a section of an invertible sheaf, as an open subset. -/
def nonvanishingLocusOpens {L : X.Modules} (hL : L.IsInvertible) (f : Γ(L, ⊤)) : X.Opens :=
  ⟨nonvanishingLocus L f, isOpen_nonvanishingLocus hL f⟩

/-! ### Quasi-coherent sections on affine opens and quasi-compact opens -/

/-- Restricting along `Spec Γ(X, U) ⟶ X` and back is restriction of sections. -/
private theorem affineFromSpec_ring_compat {U : X.Opens} (hU : IsAffineOpen U)
    (V : (Spec Γ(X, U)).Opens) (h : hU.fromSpec ''ᵁ V ≤ U) :
    (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec Γ(X, U)).presheaf.map V.leTop.op ≫
        (hU.fromSpec.appIso V).inv = X.presheaf.map (homOfLE h).op := by
  rw [← Category.assoc, Iso.comp_inv_eq, Scheme.Hom.appIso_hom, ← Category.assoc,
    Scheme.Hom.naturality, hU.fromSpec_app_self]
  simp only [Category.assoc, ← Functor.map_comp]
  rfl

/-- The `Γ(X, U)`-module structure on the sections of `F|_U` on `Spec Γ(X, U)`. -/
private theorem affineFromSpec_smul {U : X.Opens} (hU : IsAffineOpen U) (F : X.Modules)
    (V : (Spec Γ(X, U)).Opens) (h : hU.fromSpec ''ᵁ V ≤ U) (a : Γ(X, U))
    (x : Γ(F.restrict hU.fromSpec, V)) :
    a • x = (show Γ(F.restrict hU.fromSpec, V) from
      X.presheaf.map (homOfLE h).op a • (show Γ(F, hU.fromSpec ''ᵁ V) from x)) := by
  rw [Scheme.Modules.smul_Spec_def]
  rw [← affineFromSpec_ring_compat hU V h]
  rfl

/-- On an affine open `U`, a section of a quasi-coherent sheaf vanishing on `D(g)` is killed by a
power of `g` (Hartshorne II.5.3(a), transported from `Spec Γ(X, U)`). -/
theorem exists_pow_smul_eq_zero_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (g : Γ(X, U)) (s : Γ(F, U))
    (hs : F.presheaf.map (homOfLE (X.basicOpen_le g)).op s = 0) :
    ∃ n : ℕ, g ^ n • s = 0 := by
  have h1 : hU.fromSpec ''ᵁ ⊤ = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have h2 : hU.fromSpec ''ᵁ (PrimeSpectrum.basicOpen g) = X.basicOpen g :=
    hU.fromSpec_image_basicOpen g
  have hloc : IsLocalizing (modulesSpecToSheaf.obj (F.restrict hU.fromSpec)) := by
    rw [← isIso_fromTildeΓ_iff_isLocalizing]
    infer_instance
  let x : Γ(F.restrict hU.fromSpec, ⊤) := F.presheaf.map (eqToHom h1).op s
  have key : F.presheaf.map (eqToHom h1).op ≫ F.presheaf.map
      (homOfLE (Scheme.Hom.image_mono _ (le_top : PrimeSpectrum.basicOpen g ≤ ⊤))).op =
      F.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫ F.presheaf.map (eqToHom h2).op := by
    simp only [← Functor.map_comp]
    rfl
  have hx : ((modulesSpecToSheaf.obj (F.restrict hU.fromSpec)).obj.map
      (PrimeSpectrum.basicOpen g).leTop.op).hom x = 0 := by
    change (F.presheaf.map (eqToHom h1).op ≫ F.presheaf.map
      (homOfLE (Scheme.Hom.image_mono _ (le_top : PrimeSpectrum.basicOpen g ≤ ⊤))).op) s = 0
    rw [key, ConcreteCategory.comp_apply, hs, map_zero]
  have hl := hloc g
  obtain ⟨⟨c, n, rfl⟩, hc⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) _).mp hx
  refine ⟨n, ?_⟩
  have hc' : (g ^ n) • x = 0 := hc
  rw [affineFromSpec_smul hU F ⊤ h1.le] at hc'
  have hc'' : F.presheaf.map (eqToHom h1).op (g ^ n • s) = 0 := by
    rw [Scheme.Modules.map_smul]
    exact hc'
  have := congrArg (F.presheaf.map (eqToHom h1.symm).op) hc''
  rwa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans,
    eqToHom_refl, op_id, CategoryTheory.Functor.map_id, map_zero] at this

/-- Restriction along an equality of opens is injective. -/
private theorem map_eqToHom_injective (F : X.Modules) {V W : X.Opens} (h : V = W) :
    Function.Injective (F.presheaf.map (eqToHom h).op) := by
  subst h
  intro a b hab
  simpa using hab

/-- On an affine open `U` on which `F` is localizing (that is, `F|_U` is quasi-coherent), after
multiplication by a power of `g`, a section of `F` over `D(g)` extends to `U` (Hartshorne
II.5.3(b), transported from `Spec Γ(X, U)`). -/
theorem exists_pow_smul_extension_of_isLocalizing (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (hloc : IsLocalizing (modulesSpecToSheaf.obj (F.restrict hU.fromSpec)))
    (g : Γ(X, U)) (t : Γ(F, X.basicOpen g)) :
    ∃ (n : ℕ) (t' : Γ(F, U)), F.presheaf.map (homOfLE (X.basicOpen_le g)).op t' =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) ^ n • t := by
  have h1 : hU.fromSpec ''ᵁ ⊤ = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let D : (Spec Γ(X, U)).Opens := PrimeSpectrum.basicOpen g
  have h2 : hU.fromSpec ''ᵁ D = X.basicOpen g := hU.fromSpec_image_basicOpen g
  have hl := hloc g
  let y : Γ(F.restrict hU.fromSpec, D) := F.presheaf.map (eqToHom h2).op t
  obtain ⟨⟨m, ⟨c, n, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    ((modulesSpecToSheaf.obj (F.restrict hU.fromSpec)).obj.map D.leTop.op).hom
    (show (modulesSpecToSheaf.obj (F.restrict hU.fromSpec)).obj.obj (op D) from y)
  refine ⟨n, F.presheaf.map (eqToHom h1.symm).op m, ?_⟩
  have hm' : (g ^ n) • y = F.presheaf.map
      (homOfLE (Scheme.Hom.image_mono _ (le_top : D ≤ ⊤))).op m := hm
  rw [affineFromSpec_smul hU F _ (h2.le.trans (X.basicOpen_le g))] at hm'
  apply map_eqToHom_injective F h2
  have hcomp : F.presheaf.map (eqToHom h1.symm).op ≫
      F.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫ F.presheaf.map (eqToHom h2).op =
      F.presheaf.map (homOfLE (Scheme.Hom.image_mono _ (le_top : D ≤ ⊤))).op := by
    simp only [← Functor.map_comp]
    rfl
  have hL := ConcreteCategory.congr_hom hcomp m
  refine Eq.trans hL ?_
  have hr : X.presheaf.map (eqToHom h2).op
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g ^ n) =
      X.presheaf.map (homOfLE (h2.le.trans (X.basicOpen_le g))).op (g ^ n) := by
    rw [map_pow, map_pow, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [← hm', Scheme.Modules.map_smul, hr]

/-- On an affine open `U`, after multiplication by a power of `g`, a section of a quasi-coherent
sheaf over `D(g)` extends to `U` (Hartshorne II.5.3(b), transported from `Spec Γ(X, U)`). -/
theorem exists_pow_smul_extension_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) (g : Γ(X, U)) (t : Γ(F, X.basicOpen g)) :
    ∃ (n : ℕ) (t' : Γ(F, U)), F.presheaf.map (homOfLE (X.basicOpen_le g)).op t' =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) ^ n • t :=
  exists_pow_smul_extension_of_isLocalizing F hU
    ((isIso_fromTildeΓ_iff_isLocalizing _).mp inferInstance) g t


/-- On a quasi-compact open `W`, a section of a quasi-coherent sheaf vanishing on `D(g)` is
killed by a power of `g`. -/
theorem exists_pow_smul_eq_zero_of_isCompact (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens}
    (hW : IsCompact (W : Set X)) (g : Γ(X, W)) (s : Γ(F, W))
    (hs : F.presheaf.map (homOfLE (X.basicOpen_le g)).op s = 0) :
    ∃ n : ℕ, g ^ n • s = 0 := by
  classical
  have hcov : ∀ x : W, ∃ V : X.Opens, (x : X) ∈ V ∧ IsAffineOpen V ∧ V ≤ W := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.isOpen
    exact ⟨V, hxV, hV, hVW⟩
  choose V hxV hV hVW using hcov
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun x : W => (V x : Set X))
    (fun x => (V x).isOpen) (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV _⟩)
  have hloc : ∀ k : W, ∃ n : ℕ, (X.presheaf.map (homOfLE (hVW k)).op g) ^ n •
      F.presheaf.map (homOfLE (hVW k)).op s = 0 := by
    intro k
    refine exists_pow_smul_eq_zero_of_isAffineOpen F (hV k) _ _ ?_
    have hle : X.basicOpen (X.presheaf.map (homOfLE (hVW k)).op g) ≤ X.basicOpen g := by
      rw [Scheme.basicOpen_res]
      exact inf_le_right
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : (homOfLE (hVW k)).op ≫ (homOfLE (X.basicOpen_le _)).op =
        (homOfLE (X.basicOpen_le g)).op ≫ (homOfLE hle).op := rfl
    rw [this, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]
  choose n hn using hloc
  refine ⟨t.sup n, TopCat.Presheaf.IsSheaf.section_ext F.isSheaf (fun x hx => ?_)⟩
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (ht hx)
  refine ⟨V k, hVW k, hxk, ?_⟩
  rw [map_zero, Scheme.Modules.map_smul, map_pow]
  rw [← Nat.sub_add_cancel (Finset.le_sup hk : n k ≤ t.sup n), pow_add, mul_smul, hn k,
    smul_zero]

/-- A trivializing section expresses the restriction of a global section `f`. -/
theorem IsTrivializingSection.exists_eq_smul {L : X.Modules} {U : X.Opens} {e : Γ(L, U)}
    (he : IsTrivializingSection L U e) (f : Γ(L, ⊤)) :
    ∃ g : Γ(X, U), L.presheaf.map (homOfLE le_top).op f = g • e := by
  obtain ⟨g, hg⟩ := (he U le_rfl).2 (L.presheaf.map (homOfLE le_top).op f)
  refine ⟨g, ?_⟩
  rw [← hg]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restricting a section of an `𝒪_X`-module twice is restricting it once. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.map_map_homOfLE (F : X.Modules) {U V W : X.Opens}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op s) =
      F.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting a section of `𝒪_X` twice is restricting it once. -/
theorem _root_.AlgebraicGeometry.Scheme.presheaf_map_map_homOfLE {U V W : X.Opens} (h₁ : V ≤ U)
    (h₂ : W ≤ V) (a : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op a) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-! ### Lemma 5.14 -/

/-- **Hartshorne II, Lemma 5.14(a).** Let `L` be an invertible sheaf on a quasi-compact scheme
`X`, `f ∈ Γ(X, L)`, and `F` a quasi-coherent sheaf. If `s ∈ Γ(X, F)` restricts to zero on the
nonvanishing locus `X_f`, then `f^n s = 0` in `Γ(X, F ⊗ L^{⊗ n})` for some `n > 0`. -/
theorem exists_sectionPowSMul_eq_zero [CompactSpace X] {L : X.Modules} (hL : L.IsInvertible)
    (f : Γ(L, ⊤)) (F : X.Modules) [F.IsQuasicoherent] (s : Γ(F, ⊤))
    (hs : F.presheaf.map (homOfLE le_top : nonvanishingLocusOpens hL f ⟶ ⊤).op s = 0) :
    ∃ n > 0, sectionPowSMul F L n f s = 0 := by
  classical
  choose V e hxV hV he using exists_isAffineOpen_isTrivializingSection hL
  choose g hfg using fun x => (he x).exists_eq_smul f
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  have hloc : ∀ x, ∃ n : ℕ, g x ^ n • F.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op s = 0 := by
    intro x
    refine exists_pow_smul_eq_zero_of_isAffineOpen F (hV x) _ _ ?_
    have hle : X.basicOpen (g x) ≤ nonvanishingLocusOpens hL f :=
      (he x).basicOpen_le_nonvanishingLocus (hfg x)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have : (homOfLE le_top).op ≫ (homOfLE (X.basicOpen_le (g x))).op =
        (homOfLE le_top : nonvanishingLocusOpens hL f ⟶ ⊤).op ≫ (homOfLE hle).op := rfl
    rw [this, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero]
  choose n hn using hloc
  refine ⟨t.sup n + 1, Nat.succ_pos _, ?_⟩
  refine TopCat.Presheaf.IsSheaf.section_ext (tensorPowerTwist F L _).isSheaf (fun x _ => ?_)
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  refine ⟨V y, le_top, hxy, ?_⟩
  rw [map_zero, sectionPowSMul_map, hfg y, sectionPowSMul_smul]
  have hle : n y ≤ t.sup n + 1 := (Finset.le_sup hy).trans (Nat.le_succ _)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hn y, smul_zero, sectionPowSMul_zero]

/-- **Extension in every large degree** (supplements Hartshorne II, Lemma 5.14(b), which gives
one `n`). Under the hypotheses of `exists_sectionPowSMul_extension`, with the cover given by
trivializing sections, there is `N` such that for every `n ≥ N` some global section of
`F ⊗ L^{⊗ n}` restricts to `f^n t` on `X_f`. -/
theorem exists_forall_sectionPowSMul_extension {L : X.Modules} (hL : L.IsInvertible)
    (f : Γ(L, ⊤)) (F : X.Modules) [F.IsQuasicoherent] {ι : Type*} [Finite ι] (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hUaff : ∀ i, IsAffineOpen (U i)) (e : ∀ i, Γ(L, U i))
    (he : ∀ i, IsTrivializingSection L (U i) (e i))
    (hUqc : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (t : Γ(F, nonvanishingLocusOpens hL f)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ u : Γ(tensorPowerTwist F L n, ⊤),
      (tensorPowerTwist F L n).presheaf.map
          (homOfLE le_top : nonvanishingLocusOpens hL f ⟶ ⊤).op u =
        sectionPowSMul F L n (L.presheaf.map (homOfLE le_top).op f) t := by
  classical
  have := Fintype.ofFinite ι
  choose g hfg using fun i => (he i).exists_eq_smul f
  have hD : ∀ i, X.basicOpen (g i) ≤ nonvanishingLocusOpens hL f :=
    fun i => (he i).basicOpen_le_nonvanishingLocus (hfg i)
  choose n₀ t₀ ht₀ using fun i =>
    exists_pow_smul_extension_of_isAffineOpen F (hUaff i) (g i)
      (F.presheaf.map (homOfLE (hD i)).op t)
  set nb := Finset.univ.sup n₀ with hnb
  have hn₀ : ∀ i, n₀ i ≤ nb := fun i => Finset.le_sup (Finset.mem_univ i)
  let t₁ : ℕ → ∀ i, Γ(F, U i) := fun n i => g i ^ (n - n₀ i) • t₀ i
  have ht₁ : ∀ n, nb ≤ n → ∀ i, F.presheaf.map (homOfLE (X.basicOpen_le (g i))).op (t₁ n i) =
      (X.presheaf.map (homOfLE (X.basicOpen_le (g i))).op (g i)) ^ n •
        F.presheaf.map (homOfLE (hD i)).op t := by
    intro n hn i
    simp only [t₁]
    rw [Scheme.Modules.map_smul, ht₀, map_pow, ← mul_smul, ← pow_add,
      Nat.sub_add_cancel ((hn₀ i).trans hn)]
  -- transition functions on the overlaps
  choose h hh using fun i j => (he i (U i ⊓ U j) inf_le_left).2
    (L.presheaf.map (homOfLE inf_le_right).op (e j))
  simp only at hh
  have hgij : ∀ i j, X.presheaf.map (homOfLE inf_le_left).op (g i) =
      h i j * X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (g j) := by
    intro i j
    apply (he i (U i ⊓ U j) inf_le_left).1
    simp only
    rw [mul_comm, mul_smul, hh i j, ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul,
      ← hfg i, ← hfg j, Scheme.Modules.map_map_homOfLE, Scheme.Modules.map_map_homOfLE]
  -- the discrepancy in degree `n` is `g^(n - nb)` times the discrepancy in degree `nb`
  have hdn : ∀ n, nb ≤ n → ∀ i j,
      F.presheaf.map (homOfLE inf_le_left).op (t₁ n i) -
          h i j ^ n • F.presheaf.map (homOfLE inf_le_right).op (t₁ n j) =
        (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (g i)) ^ (n - nb) •
          (F.presheaf.map (homOfLE inf_le_left).op (t₁ nb i) -
            h i j ^ nb • F.presheaf.map (homOfLE inf_le_right).op (t₁ nb j)) := by
    intro n hn i j
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have ei : nb + k - n₀ i = k + (nb - n₀ i) := by have := hn₀ i; omega
    have ej : nb + k - n₀ j = k + (nb - n₀ j) := by have := hn₀ j; omega
    simp only [t₁, ei, ej, Nat.add_sub_cancel_left, Scheme.Modules.map_smul, map_pow, smul_sub,
      smul_smul, pow_add, map_mul]
    rw [hgij i j]
    congr 1
    congr 1
    ring
  -- the discrepancies in degree `nb` are killed by a further power
  have hdisc : ∀ p : ι × ι, ∃ m : ℕ,
      (X.presheaf.map (homOfLE (inf_le_left : U p.1 ⊓ U p.2 ≤ U p.1)).op (g p.1)) ^ m •
        (F.presheaf.map (homOfLE inf_le_left).op (t₁ nb p.1) -
          h p.1 p.2 ^ nb • F.presheaf.map (homOfLE inf_le_right).op (t₁ nb p.2)) = 0 := by
    rintro ⟨i, j⟩
    refine exists_pow_smul_eq_zero_of_isCompact F (hUqc i j) _ _ ?_
    set D := X.basicOpen (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (g i))
    have hDi : D ≤ X.basicOpen (g i) := by
      simp only [D, Scheme.basicOpen_res]
      exact inf_le_right
    have hDj : D ≤ X.basicOpen (g j) := by
      intro x hx
      have hxij : x ∈ U i ⊓ U j := X.basicOpen_le _ hx
      exact ((he j).mem_nonvanishingLocus_iff (hfg j) hxij.2).mp (hD i (hDi hx))
    have hgD : X.presheaf.map (homOfLE (hDi.trans (X.basicOpen_le (g i)))).op (g i) =
        X.presheaf.map (homOfLE (X.basicOpen_le _)).op (h i j) *
          X.presheaf.map (homOfLE (hDj.trans (X.basicOpen_le (g j)))).op (g j) := by
      have := congrArg (X.presheaf.map (homOfLE (X.basicOpen_le
        (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (g i)))).op) (hgij i j)
      rwa [map_mul, Scheme.presheaf_map_map_homOfLE, Scheme.presheaf_map_map_homOfLE] at this
    have e₁ := congrArg (F.presheaf.map (homOfLE hDi).op) (ht₁ nb le_rfl i)
    have e₂ := congrArg (F.presheaf.map (homOfLE hDj).op) (ht₁ nb le_rfl j)
    simp only [Scheme.Modules.map_smul, map_pow, Scheme.Modules.map_map_homOfLE, Scheme.presheaf_map_map_homOfLE] at e₁ e₂
    simp only [map_sub, Scheme.Modules.map_smul, map_pow, Scheme.Modules.map_map_homOfLE]
    rw [e₁, e₂, smul_smul, ← mul_pow, ← hgD, sub_self]
  choose m hm using hdisc
  obtain ⟨M, hmM'⟩ : ∃ M, ∀ p, m p ≤ M :=
    ⟨Finset.univ.sup m, fun p => Finset.le_sup (Finset.mem_univ p)⟩
  refine ⟨nb + M, fun n' hn' => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, n' = n + M := ⟨n' - M, by omega⟩
  have hnb : nb ≤ n := by omega
  have hmM : ∀ i j, (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (g i)) ^ M •
        (F.presheaf.map (homOfLE inf_le_left).op (t₁ n i) -
          h i j ^ n • F.presheaf.map (homOfLE inf_le_right).op (t₁ n j)) = 0 := by
    intro i j
    rw [hdn n hnb i j, smul_smul, ← pow_add, add_comm, pow_add, mul_smul,
      ← Nat.sub_add_cancel (hmM' (i, j)), pow_add, mul_smul, hm (i, j), smul_zero, smul_zero]
  -- the local sections of `F ⊗ L^{⊗ n'}` and their gluing
  let t₂ : ∀ i, Γ(F, U i) := fun i => g i ^ M • t₁ n i
  let u : ∀ i, Γ(tensorPowerTwist F L (n + M), U i) :=
    fun i => sectionPowSMul F L (n + M) (e i) (t₂ i)
  have hcompat : TopCat.Presheaf.IsCompatible (tensorPowerTwist F L (n + M)).presheaf U u := by
    intro i j
    change (tensorPowerTwist F L (n + M)).presheaf.map (homOfLE inf_le_left).op (u i) =
      (tensorPowerTwist F L (n + M)).presheaf.map (homOfLE inf_le_right).op (u j)
    simp only [u, sectionPowSMul_map]
    rw [← hh i j, sectionPowSMul_smul]
    congr 1
    simp only [t₂, Scheme.Modules.map_smul, map_pow]
    have := hmM i j
    rw [smul_sub, sub_eq_zero] at this
    rw [this, hgij i j, smul_smul, smul_smul]
    congr 1
    ring
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨(tensorPowerTwist F L (n + M)).presheaf, (tensorPowerTwist F L (n + M)).isSheaf⟩ U ⊤
    (fun i => homOfLE le_top) hU.ge u hcompat
  refine ⟨s, ?_⟩
  refine TopCat.Presheaf.IsSheaf.section_ext (tensorPowerTwist F L (n + M)).isSheaf
    (fun x hx => ?_)
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
  have hxD : x ∈ X.basicOpen (g i) := ((he i).mem_nonvanishingLocus_iff (hfg i) hxi).mp hx
  refine ⟨X.basicOpen (g i), hD i, hxD, ?_⟩
  have hsi : (tensorPowerTwist F L (n + M)).presheaf.map (homOfLE le_top : U i ⟶ ⊤).op s =
      sectionPowSMul F L (n + M) (e i) (t₂ i) := hs i
  have hL1 : (tensorPowerTwist F L (n + M)).presheaf.map (homOfLE (hD i)).op
      ((tensorPowerTwist F L (n + M)).presheaf.map
        (homOfLE le_top : nonvanishingLocusOpens hL f ⟶ ⊤).op s) =
      (tensorPowerTwist F L (n + M)).presheaf.map (homOfLE (X.basicOpen_le (g i))).op
        (sectionPowSMul F L (n + M) (e i) (t₂ i)) := by
    rw [← hsi, Scheme.Modules.map_map_homOfLE, Scheme.Modules.map_map_homOfLE]
  rw [hL1, sectionPowSMul_map, sectionPowSMul_map]
  have hf : L.presheaf.map (homOfLE (hD i)).op (L.presheaf.map (homOfLE le_top).op f) =
      X.presheaf.map (homOfLE (X.basicOpen_le (g i))).op (g i) •
        L.presheaf.map (homOfLE (X.basicOpen_le (g i))).op (e i) := by
    rw [← Scheme.Modules.map_smul, ← hfg i, Scheme.Modules.map_map_homOfLE, Scheme.Modules.map_map_homOfLE]
  rw [hf, sectionPowSMul_smul]
  congr 1
  simp only [t₂, Scheme.Modules.map_smul, map_pow]
  rw [ht₁ n hnb i, smul_smul, ← pow_add, add_comm]

/-- **Hartshorne II, Lemma 5.14(b).** Let `L` be an invertible sheaf on `X`, `f ∈ Γ(X, L)`, and
`F` a quasi-coherent sheaf. Suppose `X` has a finite cover by open affines `Uᵢ` such that each
`L|_{Uᵢ}` is free and each `Uᵢ ∩ Uⱼ` is quasi-compact. Then for every section `t` of `F` over
the nonvanishing locus `X_f` there is `n > 0` such that `f^n t ∈ Γ(X_f, F ⊗ L^{⊗ n})` extends to a
global section of `F ⊗ L^{⊗ n}`. -/
theorem exists_sectionPowSMul_extension {L : X.Modules} (hL : L.IsInvertible) (f : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] {ι : Type*} [Finite ι] (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (hUaff : ∀ i, IsAffineOpen (U i))
    (hUfree : ∀ i, (L.restrict (U i).ι).IsFree)
    (hUqc : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (t : Γ(F, nonvanishingLocusOpens hL f)) :
    ∃ n > 0, ∃ u : Γ(tensorPowerTwist F L n, ⊤),
      (tensorPowerTwist F L n).presheaf.map
          (homOfLE le_top : nonvanishingLocusOpens hL f ⟶ ⊤).op u =
        sectionPowSMul F L n (L.presheaf.map (homOfLE le_top).op f) t := by
  choose e he using fun i => exists_isTrivializingSection_of_isFree hL (hUfree i)
  obtain ⟨N, hN⟩ := exists_forall_sectionPowSMul_extension hL f F U hU hUaff e he hUqc t
  exact ⟨N + 1, N.succ_pos, hN (N + 1) N.le_succ⟩

end Hartshorne
