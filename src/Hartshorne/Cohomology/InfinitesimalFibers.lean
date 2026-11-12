/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.BaseExtension
import Hartshorne.Scheme.PullbackQuasicoherent
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Infinitesimal fibres

Hartshorne, *Algebraic Geometry*, III.11 (pp. 276–277), the setting of the theorem on formal
functions.

Let `f : X ⟶ Y` be a morphism of schemes, `y : Y`, and let `A = 𝒪_{Y,y}` with maximal ideal
`m`. For `n : ℕ` put

`X_n = X ×_Y Spec (A ⧸ m ^ n)`,

the base extension of `f` along `Spec (A ⧸ m ^ n) ⟶ Spec A ⟶ Y`, and for an `𝒪_X`-module `F`
let `F_n` be the pullback of `F` along the projection `X_n ⟶ X`.

The index is Hartshorne's: stage `n` is cut out by `m ^ n`, so `X_1` is the fibre. The
construction makes sense for every `n : ℕ` (stage `0` is empty, as `A ⧸ m ^ 0 = 0`); the results
that need `n ≥ 1` carry that hypothesis.

## Main definitions and results

* `Hartshorne.infinitesimalFiber f y n`: the scheme `X_n`.
* `Hartshorne.infinitesimalFiberι f y n : X_n ⟶ X`: the natural morphism to `X`.
* `Hartshorne.infinitesimalFiberTransition f y h : X_k ⟶ X_n` for `k ≤ n`, a closed immersion
  (`Hartshorne.isClosedImmersion_infinitesimalFiberTransition`); `X_n ⟶ X_{n+1}` is the case
  `h : n ≤ n + 1`.
* `Hartshorne.infinitesimalFiberModule f y F n`: the module `F_n`, coherent when `F` is
  (`Hartshorne.isCoherent_infinitesimalFiberModule`).
* `Hartshorne.infinitesimalFiberModulePullbackIso`: the pullback of `F_n` along `X_k ⟶ X_n` is
  `F_k`; its adjoint `Hartshorne.infinitesimalFiberModuleMap : F_n ⟶ (X_k ⟶ X_n)_* F_k` is the
  module map along the closed immersion.
* `Hartshorne.infinitesimalFiberOneIso f y : X_1 ≅ X_y`, compatible with the maps to `X`
  (`Hartshorne.infinitesimalFiberOneIso_hom_fiberι`).
* `Hartshorne.isHomeomorph_infinitesimalFiberTransition`: for `1 ≤ k ≤ n` the closed immersion
  `X_k ⟶ X_n` is a homeomorphism; `Hartshorne.infinitesimalFiberHomeomorph` gives
  `X_y ≃ₜ X_n` for `n ≥ 1`, and `Hartshorne.range_infinitesimalFiberι` shows `X_n ⟶ X` has
  image `f ⁻¹ {y}`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Hartshorne

open AlgebraicGeometry

universe u

namespace InfinitesimalFiber

variable {Y : Scheme.{u}} (y : Y)

/-- The quotient `𝒪_{Y,y} ⧸ m_y ^ n` of the local ring at `y`. -/
abbrev thickeningRing (n : ℕ) : CommRingCat.{u} :=
  CommRingCat.of (Y.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n)

/-- The quotient map `𝒪_{Y,y} ⟶ 𝒪_{Y,y} ⧸ m_y ^ n`. -/
def toThickeningRing (n : ℕ) : Y.presheaf.stalk y ⟶ thickeningRing y n :=
  CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n))

/-- The reduction `𝒪_{Y,y} ⧸ m_y ^ n ⟶ 𝒪_{Y,y} ⧸ m_y ^ k` for `k ≤ n`. -/
def thickeningRingMap {k n : ℕ} (h : k ≤ n) : thickeningRing y n ⟶ thickeningRing y k :=
  CommRingCat.ofHom (Ideal.Quotient.factor (S := IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n)
    (T := IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ k) (Ideal.pow_le_pow_right h))

@[reassoc (attr := simp)]
lemma toThickeningRing_thickeningRingMap {k n : ℕ} (h : k ≤ n) :
    toThickeningRing y n ≫ thickeningRingMap y h = toThickeningRing y k := by
  ext x
  rfl

lemma toThickeningRing_surjective (n : ℕ) : Function.Surjective (toThickeningRing y n) :=
  fun x => Ideal.Quotient.mk_surjective x

lemma thickeningRingMap_surjective {k n : ℕ} (h : k ≤ n) :
    Function.Surjective (thickeningRingMap y h) :=
  fun x => Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right h) x

instance {k n : ℕ} (h : k ≤ n) : IsClosedImmersion (Spec.map (thickeningRingMap y h)) :=
  IsClosedImmersion.spec_of_surjective _ (thickeningRingMap_surjective y h)

/-- The morphism `Spec (𝒪_{Y,y} ⧸ m_y ^ n) ⟶ Spec 𝒪_{Y,y} ⟶ Y`. -/
def toScheme (n : ℕ) : Spec (thickeningRing y n) ⟶ Y :=
  Spec.map (toThickeningRing y n) ≫ Y.fromSpecStalk y

@[reassoc (attr := simp)]
lemma specMap_thickeningRingMap_toScheme {k n : ℕ} (h : k ≤ n) :
    Spec.map (thickeningRingMap y h) ≫ toScheme y n = toScheme y k := by
  rw [toScheme, ← Category.assoc, ← Spec.map_comp, toThickeningRing_thickeningRingMap, toScheme]

lemma maximalIdeal_pow_ne_top {n : ℕ} (hn : n ≠ 0) :
    IsLocalRing.maximalIdeal (Y.presheaf.stalk y) ^ n ≠ ⊤ :=
  ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.pow_le_self hn)

instance nontrivial_thickeningRing {n : ℕ} [NeZero n] : Nontrivial (thickeningRing y n) :=
  Ideal.Quotient.nontrivial_iff.mpr (maximalIdeal_pow_ne_top y (NeZero.ne n))

/-- `Spec (𝒪_{Y,y} ⧸ m_y ^ n)` has at most one point: every prime of `𝒪_{Y,y}` containing
`m_y ^ n` is `m_y`. For `n ≥ 1` it is nonempty (`nonempty_spec_thickeningRing`), so it is one
point. -/
theorem subsingleton_spec_thickeningRing (n : ℕ) :
    Subsingleton (Spec (thickeningRing y n)) := by
  have key : ∀ p : PrimeSpectrum (thickeningRing y n),
      PrimeSpectrum.comap (toThickeningRing y n).hom p =
        IsLocalRing.closedPoint (Y.presheaf.stalk y) := by
    intro p
    ext1
    refine ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
      (PrimeSpectrum.comap (toThickeningRing y n).hom p).isPrime.ne_top ?_).symm
    refine Ideal.IsPrime.le_of_pow_le (n := n) ?_
    intro x hx
    have hx0 : (toThickeningRing y n).hom x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    show (toThickeningRing y n).hom x ∈ p.asIdeal
    rw [hx0]
    exact p.asIdeal.zero_mem
  refine ⟨fun p q => PrimeSpectrum.comap_injective_of_surjective (toThickeningRing y n).hom
    (toThickeningRing_surjective y n) ?_⟩
  exact (key p).trans (key q).symm

instance nonempty_spec_thickeningRing {n : ℕ} [NeZero n] :
    Nonempty (Spec (thickeningRing y n)) :=
  inferInstanceAs (Nonempty (PrimeSpectrum (thickeningRing y n)))

instance {k n : ℕ} [NeZero k] (h : k ≤ n) : Surjective (Spec.map (thickeningRingMap y h)) :=
  have := subsingleton_spec_thickeningRing y n
  inferInstance

/-- `𝒪_{Y,y} ⧸ m_y ^ 1` is the residue field `κ(y)`. -/
def thickeningRingOneIso : thickeningRing y 1 ≅ Y.residueField y :=
  (Ideal.quotEquivOfEq (pow_one _)).toCommRingCatIso

@[reassoc (attr := simp)]
lemma toThickeningRing_thickeningRingOneIso_hom :
    toThickeningRing y 1 ≫ (thickeningRingOneIso y).hom = Y.residue y := by
  ext x
  rfl

lemma specMap_thickeningRingOneIso_inv_fromSpecResidueField :
    Spec.map (thickeningRingOneIso y).inv ≫ Y.fromSpecResidueField y = toScheme y 1 := by
  rw [Scheme.fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    ← toThickeningRing_thickeningRingOneIso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, toScheme]

end InfinitesimalFiber

open InfinitesimalFiber

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)

/-- **Infinitesimal fibres** (Hartshorne III.11, p. 276). For `f : X ⟶ Y`, `y : Y` and
`n : ℕ`, the scheme `X_n = X ×_Y Spec (𝒪_{Y,y} ⧸ m_y ^ n)`, the base extension of `f` along
`Spec (𝒪_{Y,y} ⧸ m_y ^ n) ⟶ Spec 𝒪_{Y,y} ⟶ Y`. Hartshorne uses `n ≥ 1`; `X_1` is the fibre
(`Hartshorne.infinitesimalFiberOneIso`). -/
def infinitesimalFiber (n : ℕ) : Scheme.{u} :=
  baseExtension f (toScheme y n)

/-- The natural morphism `X_n ⟶ X`. -/
def infinitesimalFiberι (n : ℕ) : infinitesimalFiber f y n ⟶ X :=
  pullback.fst f (toScheme y n)

/-- The structure morphism `X_n ⟶ Spec (𝒪_{Y,y} ⧸ m_y ^ n)`. -/
def infinitesimalFiberToSpec (n : ℕ) :
    infinitesimalFiber f y n ⟶ Spec (thickeningRing y n) :=
  baseExtensionProjection f (toScheme y n)

lemma infinitesimalFiber_isPullback (n : ℕ) :
    IsPullback (infinitesimalFiberι f y n) (infinitesimalFiberToSpec f y n) f (toScheme y n) :=
  IsPullback.of_hasPullback f (toScheme y n)

/-- The morphism `X_k ⟶ X_n` for `k ≤ n`, induced by `𝒪_{Y,y} ⧸ m_y ^ n ⟶ 𝒪_{Y,y} ⧸ m_y ^ k`.
The case `h : n ≤ n + 1` is Hartshorne's `X_n ⟶ X_{n+1}`; it is a closed immersion
(`Hartshorne.isClosedImmersion_infinitesimalFiberTransition`). -/
def infinitesimalFiberTransition {k n : ℕ} (h : k ≤ n) :
    infinitesimalFiber f y k ⟶ infinitesimalFiber f y n :=
  pullback.map f (toScheme y k) f (toScheme y n) (𝟙 X) (Spec.map (thickeningRingMap y h)) (𝟙 Y)
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma infinitesimalFiberTransition_ι {k n : ℕ} (h : k ≤ n) :
    infinitesimalFiberTransition f y h ≫ infinitesimalFiberι f y n = infinitesimalFiberι f y k :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
lemma infinitesimalFiberTransition_toSpec {k n : ℕ} (h : k ≤ n) :
    infinitesimalFiberTransition f y h ≫ infinitesimalFiberToSpec f y n =
      infinitesimalFiberToSpec f y k ≫ Spec.map (thickeningRingMap y h) :=
  pullback.lift_snd _ _ _

lemma infinitesimalFiber_hom_ext {n : ℕ} {Z : Scheme.{u}} {a b : Z ⟶ infinitesimalFiber f y n}
    (h₁ : a ≫ infinitesimalFiberι f y n = b ≫ infinitesimalFiberι f y n)
    (h₂ : a ≫ infinitesimalFiberToSpec f y n = b ≫ infinitesimalFiberToSpec f y n) : a = b :=
  pullback.hom_ext h₁ h₂

@[simp]
lemma infinitesimalFiberTransition_refl (n : ℕ) :
    infinitesimalFiberTransition f y (le_refl n) = 𝟙 _ := by
  have : thickeningRingMap y (le_refl n) = 𝟙 _ := by
    ext x
    rfl
  refine infinitesimalFiber_hom_ext f y ?_ ?_
  · simp
  · simp [infinitesimalFiberTransition_toSpec, this]

@[reassoc (attr := simp)]
lemma infinitesimalFiberTransition_comp {j k n : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    infinitesimalFiberTransition f y hjk ≫ infinitesimalFiberTransition f y hkn =
      infinitesimalFiberTransition f y (hjk.trans hkn) := by
  have : thickeningRingMap y hkn ≫ thickeningRingMap y hjk =
      thickeningRingMap y (hjk.trans hkn) := by
    ext x
    rfl
  refine infinitesimalFiber_hom_ext f y ?_ ?_
  · simp
  · simp only [Category.assoc, infinitesimalFiberTransition_toSpec,
      infinitesimalFiberTransition_toSpec_assoc, ← Spec.map_comp, this]

/-- The square `X_k ⟶ X_n` over `Spec (𝒪_{Y,y} ⧸ m_y ^ k) ⟶ Spec (𝒪_{Y,y} ⧸ m_y ^ n)` is a
pullback, by pasting with the pullback square defining `X_n`. -/
lemma infinitesimalFiberTransition_isPullback {k n : ℕ} (h : k ≤ n) :
    IsPullback (infinitesimalFiberTransition f y h) (infinitesimalFiberToSpec f y k)
      (infinitesimalFiberToSpec f y n) (Spec.map (thickeningRingMap y h)) := by
  refine IsPullback.of_right ?_ (infinitesimalFiberTransition_toSpec f y h)
    (infinitesimalFiber_isPullback f y n)
  simpa using infinitesimalFiber_isPullback f y k

/-- **Generalising Hartshorne III.11, p. 276.** For `k ≤ n` the morphism `X_k ⟶ X_n` is a
closed immersion; in particular so is `X_n ⟶ X_{n+1}`. -/
instance isClosedImmersion_infinitesimalFiberTransition {k n : ℕ} (h : k ≤ n) :
    IsClosedImmersion (infinitesimalFiberTransition f y h) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (infinitesimalFiberTransition_isPullback f y h).flip inferInstance

instance surjective_infinitesimalFiberTransition {k n : ℕ} [NeZero k] (h : k ≤ n) :
    Surjective (infinitesimalFiberTransition f y h) :=
  MorphismProperty.of_isPullback (P := @Surjective)
    (infinitesimalFiberTransition_isPullback f y h).flip inferInstance

/-- **Generalising Hartshorne III.11, p. 276.** For `1 ≤ k ≤ n` the closed immersion
`X_k ⟶ X_n` is a homeomorphism: all infinitesimal fibres have the same underlying space. -/
theorem isHomeomorph_infinitesimalFiberTransition {k n : ℕ} (hk : 1 ≤ k) (h : k ≤ n) :
    IsHomeomorph (infinitesimalFiberTransition f y h) := by
  have : NeZero k := ⟨by omega⟩
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(infinitesimalFiberTransition f y h).isClosedEmbedding.isEmbedding,
      (infinitesimalFiberTransition f y h).surjective⟩

/-- **Hartshorne III.11, p. 276.** `X_1` is canonically the scheme-theoretic fibre `X_y`: the
isomorphism is induced by `𝒪_{Y,y} ⧸ m_y ^ 1 ≅ κ(y)` and commutes with the maps to `X`
(`Hartshorne.infinitesimalFiberOneIso_hom_fiberι`). -/
def infinitesimalFiberOneIso : infinitesimalFiber f y 1 ≅ f.fiber y where
  hom := pullback.map f (toScheme y 1) f (Y.fromSpecResidueField y) (𝟙 X)
    (Spec.map (thickeningRingOneIso y).inv) (𝟙 Y) (by simp)
    (by rw [Category.comp_id, specMap_thickeningRingOneIso_inv_fromSpecResidueField])
  inv := pullback.map f (Y.fromSpecResidueField y) f (toScheme y 1) (𝟙 X)
    (Spec.map (thickeningRingOneIso y).hom) (𝟙 Y) (by simp)
    (by rw [Category.comp_id, ← specMap_thickeningRingOneIso_inv_fromSpecResidueField,
      ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp])
  hom_inv_id := by
    refine (pullback.map_comp _ _ _ _ _ _ _ _ _ _).trans ?_
    simp only [Category.comp_id, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
    exact pullback.map_id
  inv_hom_id := by
    refine (pullback.map_comp _ _ _ _ _ _ _ _ _ _).trans ?_
    simp only [Category.comp_id, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
    exact pullback.map_id

@[reassoc (attr := simp)]
lemma infinitesimalFiberOneIso_hom_fiberι :
    (infinitesimalFiberOneIso f y).hom ≫ f.fiberι y = infinitesimalFiberι f y 1 :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
lemma infinitesimalFiberOneIso_hom_fiberToSpecResidueField :
    (infinitesimalFiberOneIso f y).hom ≫ f.fiberToSpecResidueField y =
      infinitesimalFiberToSpec f y 1 ≫ Spec.map (thickeningRingOneIso y).inv :=
  pullback.lift_snd _ _ _

/-- **Hartshorne III.11, p. 276.** For `n ≥ 1`, the scheme-theoretic fibre `X_y` and `X_n` have
the same underlying space: `X_y ≅ X_1 ⟶ X_n` is a homeomorphism. -/
def infinitesimalFiberHomeomorph {n : ℕ} (hn : 1 ≤ n) : f.fiber y ≃ₜ infinitesimalFiber f y n :=
  (infinitesimalFiberOneIso f y).symm.hom.homeomorph.trans
    (isHomeomorph_infinitesimalFiberTransition f y le_rfl hn).homeomorph

@[simp]
lemma infinitesimalFiberHomeomorph_apply {n : ℕ} (hn : 1 ≤ n) (x : f.fiber y) :
    infinitesimalFiberHomeomorph f y hn x =
      infinitesimalFiberTransition f y hn ((infinitesimalFiberOneIso f y).inv x) :=
  rfl

/-- For `n ≥ 1` the image of `X_n ⟶ X` is the set-theoretic fibre `f ⁻¹ {y}`. -/
theorem range_infinitesimalFiberι {n : ℕ} (hn : 1 ≤ n) :
    Set.range (infinitesimalFiberι f y n) = f ⁻¹' {y} := by
  rw [← Scheme.Hom.range_fiberι, ← (infinitesimalFiberTransition f y hn).surjective.range_comp,
    ← (infinitesimalFiberOneIso f y).hom.surjective.range_comp]
  congr 1
  funext x
  change (infinitesimalFiberTransition f y hn ≫ infinitesimalFiberι f y n) x =
    ((infinitesimalFiberOneIso f y).hom ≫ f.fiberι y) x
  rw [infinitesimalFiberTransition_ι, infinitesimalFiberOneIso_hom_fiberι]

/-- **Hartshorne III.11, p. 276.** For an `𝒪_X`-module `F`, the module `F_n` on `X_n`: the
pullback of `F` along `X_n ⟶ X`. -/
def infinitesimalFiberModule (F : X.Modules) (n : ℕ) : (infinitesimalFiber f y n).Modules :=
  (Scheme.Modules.pullback (infinitesimalFiberι f y n)).obj F

/-- If `F` is coherent, so is every `F_n` (Hartshorne II, Proposition 5.8(b)). -/
theorem isCoherent_infinitesimalFiberModule {F : X.Modules} (hF : IsCoherent F) (n : ℕ) :
    IsCoherent (infinitesimalFiberModule f y F n) :=
  isCoherent_pullback _ hF

/-- For `k ≤ n`, the pullback of `F_n` along `X_k ⟶ X_n` is `F_k`, since `X_k ⟶ X_n ⟶ X` is
`X_k ⟶ X`. -/
def infinitesimalFiberModulePullbackIso (F : X.Modules) {k n : ℕ} (h : k ≤ n) :
    (Scheme.Modules.pullback (infinitesimalFiberTransition f y h)).obj
        (infinitesimalFiberModule f y F n) ≅ infinitesimalFiberModule f y F k :=
  (Scheme.Modules.pullbackComp _ _).app F ≪≫
    (Scheme.Modules.pullbackCongr (infinitesimalFiberTransition_ι f y h)).app F

/-- **Hartshorne III.11, p. 276.** The module map `F_n ⟶ (X_k ⟶ X_n)_* F_k` along the closed
immersion `X_k ⟶ X_n` for `k ≤ n` (for `h : n ≤ n + 1`, Hartshorne's `F_{n+1} ⟶ F_n`): the
adjoint of `Hartshorne.infinitesimalFiberModulePullbackIso`. -/
def infinitesimalFiberModuleMap (F : X.Modules) {k n : ℕ} (h : k ≤ n) :
    infinitesimalFiberModule f y F n ⟶
      (Scheme.Modules.pushforward (infinitesimalFiberTransition f y h)).obj
        (infinitesimalFiberModule f y F k) :=
  (Scheme.Modules.pullbackPushforwardAdjunction _).homEquiv _ _
    (infinitesimalFiberModulePullbackIso f y F h).hom

end Hartshorne
