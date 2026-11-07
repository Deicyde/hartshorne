/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Projective.HomogeneousLocalizedModule
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The sheaf of a graded module on Proj

Hartshorne, *Algebraic Geometry*, II.5, the definition of `M~` on `Proj S` before
Proposition 5.11 (p. 116).

Let `S` be an `ℕ`-graded ring and `M` a `ℤ`-graded `S`-module. For an open `U ⊆ Proj S`,
the sections of `M~` over `U` are the dependent functions `s` sending `𝔭 ∈ U` to an element
of the degree-zero localization `M_(𝔭)` which are locally fractions: every point of `U` has a
neighbourhood `V` and homogeneous `m ∈ M_n`, `f ∈ S_n` with `f ∉ 𝔮` and `s(𝔮) = m / f` for
all `𝔮 ∈ V`. This mirrors Mathlib's construction of the structure sheaf of `Proj S`, and the
sections form a module over the sections of the structure sheaf pointwise.

## Main definitions

* `Hartshorne.ProjGradedModuleSheaf.isLocallyFraction`: the local predicate.
* `Hartshorne.ProjGradedModuleSheaf.sectionsSubmodule`: locally fractional sections form a
  module over the sections of the structure sheaf.
* `Hartshorne.projGradedModuleSheaf`: `M~` as an `𝒪_{Proj S}`-module.
* `Hartshorne.ProjGradedModuleSheaf.stalkLinearEquiv`: the stalk of `M~` at `x` is `M_(x)`,
  semilinearly over Mathlib's identification of the stalk of `𝒪_{Proj S}` with `S_(x)`;
  the germ of a section goes to its value at `x`.

The chart isomorphism `M~|_{D₊(f)} ≅ (M_(f))~` is in `Hartshorne.Scheme.ProjGradedModuleSheafChart`
and the quasi-coherence and coherence consequences are in
`Hartshorne.Scheme.ProjGradedModuleSheafCoherent`.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

open AlgebraicGeometry TopCat TopologicalSpace CategoryTheory Opposite
  ProjectiveSpectrum.StructureSheaf

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {M σM : Type u} [AddCommGroup M] [Module A M] [SetLike σM M] [AddSubgroupClass σM M]
  (ℳ : ℤ → σM) [SetLike.GradedSMul 𝒜 ℳ]

local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

local notation3 "Mat " x =>
  HomogeneousLocalizedModule 𝒜 ℳ
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x)).primeCompl

namespace ProjGradedModuleSheaf

variable {𝒜 ℳ} in
/-- A dependent function on `U` is a fraction if it is the constant fraction `m / f` of
homogeneous elements of the same degree, with `f` outside every point of `U`. -/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (s : ∀ x : U, Mat x.1) : Prop :=
  ∃ (n : ℕ) (m : M) (hm : m ∈ ℳ n) (f : A) (hf : f ∈ 𝒜 n)
    (f_nin : ∀ x : U, f ∉ x.1.asHomogeneousIdeal),
    ∀ x : U, s x = HomogeneousLocalizedModule.mk n m hm f hf (f_nin x)

/-- Being a fraction is preserved under restriction to a smaller open. -/
def isFractionPrelocal : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => Mat x where
  pred s := IsFraction s
  res := by
    rintro V U i s ⟨n, m, hm, f, hf, h, w⟩
    exact ⟨n, m, hm, f, hf, (h <| i ·), (w <| i ·)⟩

/-- The sections of `M~`: dependent functions which are locally fractions. -/
def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => Mat x :=
  (isFractionPrelocal 𝒜 ℳ).sheafify

variable {𝒜 ℳ}

open HomogeneousLocalizedModule in
theorem zero_mem' (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    (isLocallyFraction 𝒜 ℳ).pred (0 : ∀ x : U, Mat x.1) := fun x =>
  ⟨U, x.2, 𝟙 U, 0, 0, zero_mem _, 1, SetLike.GradedOne.one_mem,
    fun y => y.1.isPrime.ne_top' ∘ (Ideal.eq_top_iff_one _).2, fun y => by
      ext
      exact (LocalizedModule.zero_mk _).symm⟩

theorem add_mem' (U : Opens (ProjectiveSpectrum.top 𝒜)) (a b : ∀ x : U, Mat x.1)
    (ha : (isLocallyFraction 𝒜 ℳ).pred a) (hb : (isLocallyFraction 𝒜 ℳ).pred b) :
    (isLocallyFraction 𝒜 ℳ).pred (a + b) := fun x => by
  obtain ⟨Va, ma, ia, na, ra, hra, sa, hsa, hwa, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, nb, rb, hrb, sb, hsb, hwb, wb⟩ := hb x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, na + nb, sb • ra + sa • rb,
    add_mem ?_ ?_, sa * sb, SetLike.GradedMul.mul_mem hsa hsb, fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩),
    fun y => ?_⟩
  · have := smul_mem_graded_nat 𝒜 ℳ hsb hra
    rwa [show ((nb : ℕ) : ℤ) + na = ((na + nb : ℕ) : ℤ) by push_cast; ring] at this
  · have := smul_mem_graded_nat 𝒜 ℳ hsa hrb
    rwa [show ((na : ℕ) : ℤ) + nb = ((na + nb : ℕ) : ℤ) by push_cast; ring] at this
  · ext
    have ea := congrArg HomogeneousLocalizedModule.val (wa ⟨y.1, y.2.1⟩)
    have eb := congrArg HomogeneousLocalizedModule.val (wb ⟨y.1, y.2.2⟩)
    refine (congrArg₂ (· + ·) ea eb).trans ?_
    simp only [HomogeneousLocalizedModule.val_mk, LocalizedModule.mk_add_mk]
    rfl

theorem neg_mem' (U : Opens (ProjectiveSpectrum.top 𝒜)) (a : ∀ x : U, Mat x.1)
    (ha : (isLocallyFraction 𝒜 ℳ).pred a) : (isLocallyFraction 𝒜 ℳ).pred (-a) := fun x => by
  obtain ⟨V, m, i, n, r, hr, s, hs, nin, w⟩ := ha x
  refine ⟨V, m, i, n, -r, neg_mem hr, s, hs, nin, fun y => ?_⟩
  ext
  have e := congrArg HomogeneousLocalizedModule.val (w y)
  refine (congrArg Neg.neg e).trans ?_
  simp only [HomogeneousLocalizedModule.val_mk, LocalizedModule.mk_neg]

theorem smul_mem' (U : Opens (ProjectiveSpectrum.top 𝒜)) (c : ∀ x : U, at x.1)
    (hc : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred c) (a : ∀ x : U, Mat x.1)
    (ha : (isLocallyFraction 𝒜 ℳ).pred a) :
    (isLocallyFraction 𝒜 ℳ).pred (fun x => c x • a x) := fun x => by
  obtain ⟨Vc, mc, ic, nc, ⟨rc, hrc⟩, ⟨sc, hsc⟩, hwc, wc⟩ := hc x
  obtain ⟨Va, ma, ia, na, ra, hra, sa, hsa, hwa, wa⟩ := ha x
  refine ⟨Vc ⊓ Va, ⟨mc, ma⟩, Opens.infLELeft _ _ ≫ ic, nc + na, rc • ra,
    ?_, sc * sa, SetLike.GradedMul.mul_mem hsc hsa, fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwc ⟨y.1, y.2.1⟩) (hwa ⟨y.1, y.2.2⟩),
    fun y => ?_⟩
  · have := smul_mem_graded_nat 𝒜 ℳ hrc hra
    rwa [show ((nc : ℕ) : ℤ) + na = ((nc + na : ℕ) : ℤ) by push_cast; ring] at this
  · ext
    have ec := congrArg HomogeneousLocalization.val (wc ⟨y.1, y.2.1⟩)
    have ea := congrArg HomogeneousLocalizedModule.val (wa ⟨y.1, y.2.2⟩)
    refine (congrArg₂ (· • ·) ec ea).trans ?_
    simp only [HomogeneousLocalizedModule.val_mk, HomogeneousLocalization.val_mk]
    exact LocalizedModule.mk_smul_mk _ _ _ _

variable (𝒜 ℳ) in
/-- The locally fractional sections over `U` form an additive subgroup of all dependent
functions. -/
def sectionsAddSubgroup (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    AddSubgroup (∀ x : U, Mat x.1) where
  carrier := {s | (isLocallyFraction 𝒜 ℳ).pred s}
  zero_mem' := zero_mem' U
  add_mem' := add_mem' U _ _
  neg_mem' := neg_mem' U _

variable (𝒜 ℳ) in
/-- The sheaf of sets underlying `M~`: locally fractional dependent functions. -/
def sheafInType : Sheaf (Type u) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 ℳ)

instance (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((sheafInType 𝒜 ℳ).1.obj U) :=
  (sectionsAddSubgroup 𝒜 ℳ U.unop).toAddCommGroup

instance (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    SMul ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U) ((sheafInType 𝒜 ℳ).1.obj U) where
  smul r s := ⟨fun x => r.1 x • s.1 x, smul_mem' U.unop r.1 r.2 s.1 s.2⟩

@[simp]
theorem sheafInType_smul_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U) (s : (sheafInType 𝒜 ℳ).1.obj U)
    (x : U.unop) : (r • s).1 x = r.1 x • s.1 x := rfl

@[simp]
theorem sheafInType_add_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s t : (sheafInType 𝒜 ℳ).1.obj U) (x : U.unop) : (s + t).1 x = s.1 x + t.1 x := rfl

@[simp]
theorem sheafInType_zero_apply {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (x : U.unop) :
    (0 : (sheafInType 𝒜 ℳ).1.obj U).1 x = 0 := rfl

instance (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
      ((sheafInType 𝒜 ℳ).1.obj U) where
  one_smul s := Subtype.ext <| funext fun x => one_smul (at x.1) (s.1 x)
  mul_smul r r' s := Subtype.ext <| funext fun x => mul_smul (r.1 x) (r'.1 x) (s.1 x)
  smul_zero r := Subtype.ext <| funext fun x => smul_zero (r.1 x)
  smul_add r s t := Subtype.ext <| funext fun x => smul_add (r.1 x) (s.1 x) (t.1 x)
  add_smul r r' s := Subtype.ext <| funext fun x => add_smul (r.1 x) (r'.1 x) (s.1 x)
  zero_smul s := Subtype.ext <| funext fun x => zero_smul (at x.1) (s.1 x)

variable (𝒜 ℳ) in
/-- The presheaf of abelian groups underlying `M~`. -/
def presheafInAb : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ ⥤ Ab.{u} where
  obj U := AddCommGrpCat.of ((sheafInType 𝒜 ℳ).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sheafInType 𝒜 ℳ).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

end ProjGradedModuleSheaf

open ProjGradedModuleSheaf in
set_option backward.isDefEq.respectTransparency false in
/-- Hartshorne's `M~` on `Proj S` for a `ℤ`-graded `S`-module `M`, as an
`𝒪_{Proj S}`-module: sections are the locally fractional dependent functions into the
degree-zero localizations `M_(𝔭)`. -/
def projGradedModuleSheaf : (Proj 𝒜).Modules where
  val :=
    letI (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
        Module ((Proj 𝒜).ringCatSheaf.1.obj U) ((presheafInAb 𝒜 ℳ).obj U) :=
      inferInstanceAs (Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
        ((sheafInType 𝒜 ℳ).1.obj U))
    .ofPresheaf (presheafInAb 𝒜 ℳ) fun _ _ _ _ _ => rfl
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (sheafInType 𝒜 ℳ).2

namespace ProjGradedModuleSheaf

variable {𝒜 ℳ}

/-- Sections of `M~` are determined by their values at the points of their domain. -/
@[ext]
theorem section_ext {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    {s t : (projGradedModuleSheaf 𝒜 ℳ).val.obj U}
    (h : ∀ x, (s : (sheafInType 𝒜 ℳ).1.obj U).1 x = (t : (sheafInType 𝒜 ℳ).1.obj U).1 x) :
    s = t :=
  Subtype.ext (funext h)

variable (𝒜 ℳ)

/-- `M~` as a presheaf of modules over the `CommRingCat`-valued structure presheaf, the form in
which Mathlib puts a module structure on its stalks. -/
abbrev presheafOfModules :
    PresheafOfModules.{u} ((Proj 𝒜).presheaf ⋙ forget₂ CommRingCat RingCat) :=
  (projGradedModuleSheaf 𝒜 ℳ).val

/-- The presheaf of abelian groups underlying `M~`, viewed on the space `Proj S`. -/
abbrev presheafAb : TopCat.Presheaf Ab.{u} (Proj 𝒜) :=
  (presheafOfModules 𝒜 ℳ).presheaf

/-- Evaluation of a section of `M~` at a point of its domain. -/
def evalAt (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) :
    (presheafAb 𝒜 ℳ).obj (op U) ⟶ AddCommGrpCat.of (Mat x) :=
  AddCommGrpCat.ofHom
    { toFun s := (s : (sheafInType 𝒜 ℳ).1.obj (op U)).1 ⟨x, hx⟩
      map_zero' := rfl
      map_add' _ _ := rfl }

/-- The map from the stalk of `M~` at `x` to `M_(x)`, gluing the evaluation maps. -/
def stalkToFiber (x : ProjectiveSpectrum.top 𝒜) :
    (presheafAb 𝒜 ℳ).stalk x ⟶ AddCommGrpCat.of (Mat x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ presheafAb 𝒜 ℳ)
    { pt := _
      ι := { app := fun U => evalAt 𝒜 ℳ ((OpenNhds.inclusion _).obj U.unop) x U.unop.2 } }

theorem germ_comp_stalkToFiber (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) :
    (presheafAb 𝒜 ℳ).germ U x hx ≫ stalkToFiber 𝒜 ℳ x =
      evalAt 𝒜 ℳ U x hx :=
  Limits.colimit.ι_desc _ _

@[simp]
theorem stalkToFiber_germ (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U)
    (s : (presheafAb 𝒜 ℳ).obj (op U)) :
    stalkToFiber 𝒜 ℳ x ((presheafAb 𝒜 ℳ).germ U x hx s) =
      (s : (sheafInType 𝒜 ℳ).1.obj (op U)).1 ⟨x, hx⟩ :=
  ConcreteCategory.congr_hom (germ_comp_stalkToFiber 𝒜 ℳ U x hx) s

/-- The section `m / f` of `M~` over the basic open `D₊(f)`. -/
def sectionInBasicOpen (n : ℕ) (m : M) (hm : m ∈ ℳ n) (f : A) (hf : f ∈ 𝒜 n) :
    (presheafAb 𝒜 ℳ).obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  (⟨fun y => HomogeneousLocalizedModule.mk n m hm f hf y.2, fun y =>
    ⟨ProjectiveSpectrum.basicOpen 𝒜 f, y.2, 𝟙 _, n, m, hm, f, hf, fun z => z.2,
      fun _ => rfl⟩⟩ : (sheafInType 𝒜 ℳ).1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))

theorem stalkToFiber_surjective (x : ProjectiveSpectrum.top 𝒜) :
    Function.Surjective (stalkToFiber 𝒜 ℳ x) := by
  intro y
  obtain ⟨n, m, hm, f, hf, hfx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
  exact ⟨_, stalkToFiber_germ 𝒜 ℳ (ProjectiveSpectrum.basicOpen 𝒜 f) x hfx
    (sectionInBasicOpen 𝒜 ℳ n m hm f hf)⟩

theorem stalkToFiber_injective (x : ProjectiveSpectrum.top 𝒜) :
    Function.Injective (stalkToFiber 𝒜 ℳ x) := by
  refine (injective_iff_map_eq_zero (stalkToFiber 𝒜 ℳ x).hom).2 fun z hz => ?_
  obtain ⟨U, hxU, s, rfl⟩ := (presheafAb 𝒜 ℳ).exists_germ_eq z
  rw [stalkToFiber_germ] at hz
  obtain ⟨V, hxV, i, n, m, hm, f, hf, nin, w⟩ :=
    (s : (sheafInType 𝒜 ℳ).1.obj (op U)).2 ⟨x, hxU⟩
  have h0 := congrArg HomogeneousLocalizedModule.val ((w ⟨x, hxV⟩).symm.trans hz)
  obtain ⟨⟨u, hu⟩, hum⟩ := LocalizedModule.mk_eq.1
    (h0.trans (LocalizedModule.zero_mk (1 : (x.asHomogeneousIdeal.toIdeal.primeCompl))).symm)
  simp only [one_smul, smul_zero, Submonoid.mk_smul] at hum
  let W := V ⊓ ProjectiveSpectrum.basicOpen 𝒜 u
  have hxW : x ∈ W := ⟨hxV, hu⟩
  have hWU : W ≤ U := inf_le_left.trans i.le
  rw [← (presheafAb 𝒜 ℳ).germ_res_apply (homOfLE hWU) x hxW s]
  convert map_zero ((presheafAb 𝒜 ℳ).germ W x hxW).hom
  refine Subtype.ext (funext fun y => HomogeneousLocalizedModule.ext ?_)
  have ey := congrArg HomogeneousLocalizedModule.val (w ⟨y.1, y.2.1⟩)
  refine ey.trans ?_
  simp only [HomogeneousLocalizedModule.val_mk]
  refine (LocalizedModule.mk_eq.2 ⟨⟨u, y.2.2⟩, ?_⟩).trans (LocalizedModule.zero_mk 1)
  simp only [one_smul, smul_zero]
  exact hum

/-- The stalk of `𝒪_{Proj S}` at `x` is `S_(x)` (Mathlib's `Proj.stalkIso'`). -/
abbrev stalkRingEquiv (x : Proj 𝒜) : (Proj 𝒜).presheaf.stalk x ≃+* at x :=
  Proj.stalkIso' 𝒜 x

/-- The ring isomorphism `𝒪_{Proj S, x} ≅ S_(x)` as a ring homomorphism. -/
abbrev stalkRingHom (x : Proj 𝒜) : (Proj 𝒜).presheaf.stalk x →+* at x :=
  stalkRingEquiv 𝒜 x

/-- The inverse ring homomorphism `S_(x) → 𝒪_{Proj S, x}`. -/
abbrev stalkRingHomInv (x : Proj 𝒜) : (at x) →+* (Proj 𝒜).presheaf.stalk x :=
  (stalkRingEquiv 𝒜 x).symm

instance (x : Proj 𝒜) : RingHomInvPair (stalkRingHom 𝒜 x) (stalkRingHomInv 𝒜 x) :=
  .of_ringEquiv (stalkRingEquiv 𝒜 x)

instance (x : Proj 𝒜) : RingHomInvPair (stalkRingHomInv 𝒜 x) (stalkRingHom 𝒜 x) :=
  .of_ringEquiv_symm (stalkRingEquiv 𝒜 x)

set_option backward.isDefEq.respectTransparency false in
theorem stalkToFiber_smul (x : Proj 𝒜) (r : (Proj 𝒜).presheaf.stalk x)
    (z : (presheafAb 𝒜 ℳ).stalk x) :
    stalkToFiber 𝒜 ℳ x (r • z) = stalkRingEquiv 𝒜 x r • stalkToFiber 𝒜 ℳ x z := by
  obtain ⟨U, hxU, t, rfl⟩ := (Proj 𝒜).presheaf.exists_germ_eq r
  obtain ⟨V, hxV, s, rfl⟩ := (presheafAb 𝒜 ℳ).exists_germ_eq z
  have hxW : x ∈ U ⊓ V := ⟨hxU, hxV⟩
  rw [← (Proj 𝒜).presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hxW t,
    ← (presheafAb 𝒜 ℳ).germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hxW s,
    ← PresheafOfModules.germ_smul, stalkToFiber_germ, stalkToFiber_germ]
  exact congrArg (· • _) (Proj.stalkIso'_germ 𝒜 _ x hxW _).symm

/-- **The stalk formula.** The stalk of `M~` at a point `x` of `Proj S` is `M_(x)`, compatibly
with the identification of the stalk of `𝒪_{Proj S}` at `x` with `S_(x)`: the germ of a section
`s` goes to its value `s(x)`. -/
def stalkLinearEquiv (x : Proj 𝒜) :
    (presheafAb 𝒜 ℳ).stalk x ≃ₛₗ[stalkRingHom 𝒜 x] Mat x :=
  { AddEquiv.ofBijective (stalkToFiber 𝒜 ℳ x).hom
      ⟨stalkToFiber_injective 𝒜 ℳ x, stalkToFiber_surjective 𝒜 ℳ x⟩ with
    map_smul' := stalkToFiber_smul 𝒜 ℳ x }

@[simp]
theorem stalkLinearEquiv_germ (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x ∈ U) (s : (presheafAb 𝒜 ℳ).obj (op U)) :
    stalkLinearEquiv 𝒜 ℳ x ((presheafAb 𝒜 ℳ).germ U x hx s) =
      (s : (sheafInType 𝒜 ℳ).1.obj (op U)).1 ⟨x, hx⟩ :=
  stalkToFiber_germ 𝒜 ℳ U x hx s

end ProjGradedModuleSheaf

end Hartshorne
