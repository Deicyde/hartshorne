/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LargestIdealOfDefinition
import Hartshorne.Scheme.IdealsOfDefinitionCofinal

/-!
# Powers of an ideal of definition

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.5(c) (p. 197).

* `Hartshorne.IsIdealOfDefinition.pow_succ`: if `J` is an ideal of definition of a Noetherian
  formal scheme `X`, then so is `J ^ (n + 1)` for every `n`.
* `Hartshorne.IsIdealOfDefinition.sheafSupport_quotientAb_pow`: `Supp (𝒪_X / J ^ (n + 1)) = X`.
* `Hartshorne.sheafSupport_quotientAb_of_le_vanishingIdealSubsheaf`: on a locally ringed space,
  an ideal subsheaf contained in `J_red` (the sections vanishing at every point) has quotient of
  full support.
* `Hartshorne.IdealSubsheaf.pow_le_pow_right`, `Hartshorne.IdealSubsheaf.pow_succ_le_self`:
  `J ^ l ⊆ J ^ k` for `k ≤ l`; in particular `J ^ (n + 1) ⊆ J`.
* `Hartshorne.IdealSubsheaf.stalkIdeal J x`: the stalk `J_x ⊆ R_x`, the germs of sections of `J`;
  `IdealSubsheaf.germ_mem_stalkIdeal_iff` and `IdealSubsheaf.stalkIdeal_pow`
  (`(J ^ k)_x = (J_x) ^ k`).
* `Hartshorne.IdealSubsheaf.IsKernelChart J g`: a morphism of locally ringed spaces `g : W ⟶ X`
  from a scheme which is an open embedding with surjective stalk maps whose stalk kernels are the
  stalks of `J` (`IdealSubsheaf.isKernelChart_iff`).
* `Hartshorne.IdealSubsheaf.exists_isNoetherian_iso_quotientSheafedSpace_of_charts`: if `X` is
  quasi-compact and every point of `X` lies in the image of a kernel chart `Spec R ⟶ X` of `J`
  with `R` Noetherian, then `(X, 𝒪_X / J)` is a Noetherian scheme.

Proof outline. The support statement holds because `J ^ (n + 1) ⊆ J ⊆ J_red`. For the scheme
structure we produce Noetherian affine kernel charts of `J ^ (n + 1)`. By cofinality
(Proposition 9.5(a)) and since `J_red` is an ideal of definition (Proposition 9.5(b)),
`J_red ^ a ⊆ J` for some `a > 0`. Near a point `x`, a chart `X ⊇ U ≅ Ŷ` and an affine open
`Spec B` of the thickening `Y_(m+1)`, `m + 1 = a (n + 1)`, give an open embedding
`g : Spec B ⟶ X` with surjective stalk maps whose stalk kernels are the `(m+1)`-st powers of the
stalks of `ker (𝒪_{Ŷ} ⟶ 𝒪_{Y_1})` (Proposition 9.4), hence lie in `J_red_x ^ (a (n + 1))`, hence
in `J_x ^ (n + 1)`. Since `(X, 𝒪_X / J)` is a scheme, the induced morphism from its open
subscheme `g(Spec B)` to `Spec B` is a closed immersion, so it is `Spec (B ⧸ c)` for an ideal `c`
whose localizations are the images of the stalks of `J`: this is the coherence of the image of
`J` on the Noetherian thickening. Then `Spec (B ⧸ c ^ (n + 1)) ⟶ Spec B ⟶ X` is a kernel chart of
`J ^ (n + 1)`. Gluing these charts (as for `J_red` in
`Hartshorne.Scheme.LargestIdealOfDefinition`) makes `(X, 𝒪_X / J ^ (n + 1))` a scheme, which is
Noetherian because the charts are Noetherian and `X` is quasi-compact.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Topology

namespace Hartshorne

universe u

namespace IdealSubsheaf

variable {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T} (J : IdealSubsheaf R)

/-! The following private lemmas are copied from `Hartshorne.Scheme.LargestIdealOfDefinition`,
where they are private. -/

private lemma quotientπ_hom_eq :
    J.quotientπ.hom = J.quotientPresheafπ ≫ toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap) := by
  rw [toSheafify_naturality]
  rfl

private lemma quotientπ_app_apply (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)).app (op U)
        (Ideal.Quotient.mk (J.ideal U) s) := by
  rw [quotientπ_hom_eq]
  rfl

/-- The kernel of `R(U) → (R / J)(U)` is `J(U)`. -/
private lemma quotientπ_app_eq_zero_iff (U : Opens T) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op U) s = 0 ↔ s ∈ J.ideal U := by
  constructor
  · intro hs
    rw [quotientπ_app_apply] at hs
    have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology T)
      (toSheafify (Opens.grothendieckTopology T)
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap)) (X := op U)
        (Ideal.Quotient.mk (J.ideal U) s) 0 (hs.trans (map_zero _).symm)
    refine J.mem_ideal_of_locally s fun x hx => ?_
    obtain ⟨V, f, hf, hxV⟩ := hmem x hx
    refine ⟨V, leOfHom f, hxV, ?_⟩
    have hf' : (idealQuotientPresheaf R J.ideal J.ideal_le_comap).map f.op
        (Ideal.Quotient.mk (J.ideal U) s) =
        (idealQuotientPresheaf R J.ideal J.ideal_le_comap).map f.op 0 := hf
    rw [map_zero] at hf'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hf'
  · intro hs
    rw [quotientπ_app_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hs]
    exact map_zero _

/-- The projection `R ⟶ R / J` is locally surjective. -/
private lemma exists_quotientπ_app_eq (U : Opens T) (t : J.quotient.presheaf.obj (op U)) (x : T)
    (hx : x ∈ U) :
    ∃ (V : Opens T) (hVU : V ≤ U) (s : R.presheaf.obj (op V)), x ∈ V ∧
      J.quotientπ.hom.app (op V) s = J.quotient.presheaf.map (homOfLE hVU).op t := by
  obtain ⟨V, hVU, ⟨q, hq⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff
    (toSheafify (Opens.grothendieckTopology T)
      (idealQuotientPresheaf R J.ideal J.ideal_le_comap))).mp
    (inferInstanceAs (Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) _)) U t x hx
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨V, hVU, s, hxV, by rw [quotientπ_app_apply]; exact hq⟩

/-- The projection `R ⟶ R / J` commutes with restriction. -/
private lemma quotientπ_app_res {U V : Opens T} (h : V ≤ U) (s : R.presheaf.obj (op U)) :
    J.quotientπ.hom.app (op V) (R.presheaf.map (homOfLE h).op s) =
      J.quotient.presheaf.map (homOfLE h).op (J.quotientπ.hom.app (op U) s) :=
  NatTrans.naturality_apply J.quotientπ.hom _ s

/-- Powers of an ideal subsheaf decrease: `J ^ l ⊆ J ^ k` for `k ≤ l`. -/
lemma pow_le_pow_right {k l : ℕ} (hkl : k ≤ l) : J ^ l ≤ J ^ k := by
  rw [le_iff]
  intro V s hs
  rw [ideal_pow] at hs ⊢
  intro x hx
  obtain ⟨W, h, hxW, hsW⟩ := hs x hx
  exact ⟨W, h, hxW, Ideal.pow_le_pow_right hkl hsW⟩

/-- `J ^ (n + 1) ⊆ J`. -/
lemma pow_succ_le_self (n : ℕ) : J ^ (n + 1) ≤ J := by
  simpa using J.pow_le_pow_right (Nat.succ_pos n)

/-- The `k`-th power of the ideal of sections of `J` over `V` consists of sections of `J ^ k`:
`J(V) ^ k ⊆ (J ^ k)(V)`. -/
lemma ideal_pow_le_ideal_pow (k : ℕ) (V : Opens T) : J.ideal V ^ k ≤ (J ^ k).ideal V := by
  intro s hs x hx
  refine ⟨V, le_rfl, hx, ?_⟩
  rw [show (homOfLE (le_refl V)).op = 𝟙 (op V) from rfl, CategoryTheory.Functor.map_id]
  exact hs

/-- **The stalk of an ideal subsheaf** `J_x ⊆ R_x`: the germs at `x` of sections of `J`. -/
def stalkIdeal (x : T) : Ideal (R.presheaf.stalk x) where
  carrier := {t | ∃ (V : Opens T) (hx : x ∈ V) (s : R.presheaf.obj (op V)),
    s ∈ J.ideal V ∧ R.presheaf.germ V x hx s = t}
  zero_mem' := ⟨⊤, trivial, 0, zero_mem _, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨V₁, hx₁, s₁, hs₁, rfl⟩ ⟨V₂, hx₂, s₂, hs₂, rfl⟩
    refine ⟨V₁ ⊓ V₂, (show x ∈ V₁ ⊓ V₂ from ⟨hx₁, hx₂⟩),
      R.presheaf.map (homOfLE inf_le_left).op s₁ + R.presheaf.map (homOfLE inf_le_right).op s₂,
      add_mem (J.ideal_le_comap inf_le_left hs₁) (J.ideal_le_comap inf_le_right hs₂), ?_⟩
    rw [map_add, R.presheaf.germ_res_apply, R.presheaf.germ_res_apply]
  smul_mem' := by
    rintro r _ ⟨V, hx, s, hs, rfl⟩
    obtain ⟨V₀, hx₀, r₀, rfl⟩ := R.presheaf.exists_germ_eq r
    refine ⟨V₀ ⊓ V, (show x ∈ V₀ ⊓ V from ⟨hx₀, hx⟩),
      R.presheaf.map (homOfLE inf_le_left).op r₀ * R.presheaf.map (homOfLE inf_le_right).op s,
      Ideal.mul_mem_left _ _ (J.ideal_le_comap inf_le_right hs), ?_⟩
    rw [map_mul, R.presheaf.germ_res_apply, R.presheaf.germ_res_apply, smul_eq_mul]

lemma germ_mem_stalkIdeal {x : T} {V : Opens T} (hx : x ∈ V) {s : R.presheaf.obj (op V)}
    (hs : s ∈ J.ideal V) : R.presheaf.germ V x hx s ∈ J.stalkIdeal x :=
  ⟨V, hx, s, hs, rfl⟩

lemma stalkIdeal_mono {J' : IdealSubsheaf R} (h : J ≤ J') (x : T) :
    J.stalkIdeal x ≤ J'.stalkIdeal x := by
  rintro _ ⟨V, hx, s, hs, rfl⟩
  exact ⟨V, hx, s, le_iff.mp h V hs, rfl⟩

/-- The germ of a section `s` lies in `J_x` exactly when `s` lies in `J` near `x`. -/
lemma germ_mem_stalkIdeal_iff {x : T} {V : Opens T} (hx : x ∈ V) (s : R.presheaf.obj (op V)) :
    R.presheaf.germ V x hx s ∈ J.stalkIdeal x ↔
      ∃ (V' : Opens T) (h : V' ≤ V), x ∈ V' ∧ R.presheaf.map (homOfLE h).op s ∈ J.ideal V' := by
  constructor
  · rintro ⟨V₁, hx₁, s₁, hs₁, he⟩
    obtain ⟨W, hxW, iV, iV₁, hW⟩ := R.presheaf.germ_eq x hx hx₁ s s₁ he.symm
    refine ⟨W, leOfHom iV, hxW, ?_⟩
    rw [show (homOfLE (leOfHom iV)).op = iV.op from rfl, hW]
    exact J.ideal_le_comap (leOfHom iV₁) hs₁
  · rintro ⟨V', h, hxV', hs⟩
    rw [← R.presheaf.germ_res_apply (homOfLE h) x hxV']
    exact J.germ_mem_stalkIdeal hxV' hs

/-- **Stalks of powers.** The stalk of `J ^ k` at `x` is the `k`-th power of the stalk `J_x`. -/
lemma stalkIdeal_pow (k : ℕ) (x : T) : (J ^ k).stalkIdeal x = J.stalkIdeal x ^ k := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨V, hx, s, hs, rfl⟩
    rw [ideal_pow] at hs
    obtain ⟨W, h, hxW, hsW⟩ := hs x hx
    rw [← R.presheaf.germ_res_apply (homOfLE h) x hxW]
    have hle : (J.ideal W).map (R.presheaf.germ W x hxW).hom ≤ J.stalkIdeal x :=
      Ideal.map_le_iff_le_comap.mpr fun t ht => J.germ_mem_stalkIdeal hxW ht
    exact Ideal.pow_right_mono hle k
      (Ideal.map_pow (R.presheaf.germ W x hxW).hom (J.ideal W) k ▸ Ideal.mem_map_of_mem _ hsW)
  · induction k with
    | zero =>
      rw [_root_.pow_zero, Ideal.one_eq_top, top_le_iff, Ideal.eq_top_iff_one]
      refine ⟨⊤, trivial, 1, ?_, map_one _⟩
      refine J.ideal_pow_le_ideal_pow 0 ⊤ ?_
      rw [_root_.pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ k ih =>
      rw [_root_.pow_succ]
      refine (Ideal.mul_mono_left ih).trans (Ideal.mul_le.mpr ?_)
      rintro _ ⟨V₁, hx₁, s₁, hs₁, rfl⟩ _ ⟨V₂, hx₂, s₂, hs₂, rfl⟩
      rw [ideal_pow] at hs₁
      obtain ⟨W, h, hxW, hsW⟩ := hs₁ x hx₁
      refine ⟨W ⊓ V₂, (show x ∈ W ⊓ V₂ from ⟨hxW, hx₂⟩), R.presheaf.map (homOfLE inf_le_left).op
        (R.presheaf.map (homOfLE h).op s₁) * R.presheaf.map (homOfLE inf_le_right).op s₂,
        J.ideal_pow_le_ideal_pow (k + 1) _ ?_, ?_⟩
      · rw [_root_.pow_succ]
        exact Ideal.mul_mem_mul (pow_le_comap_pow (J.ideal_le_comap inf_le_left) k hsW)
          (J.ideal_le_comap inf_le_right hs₂)
      · rw [map_mul, R.presheaf.germ_res_apply, R.presheaf.germ_res_apply,
          R.presheaf.germ_res_apply]

end IdealSubsheaf

section support

variable {X : LocallyRingedSpace.{u}}

/-- **Full support below `J_red`.** On a locally ringed space `X`, an ideal subsheaf `J` of `𝒪_X`
contained in `J_red` (the sections vanishing at every point) has `Supp (𝒪_X / J) = X`: the germ of
`1` at any point is a unit, so `1` lies in no `J(V)` with `V` nonempty. -/
theorem sheafSupport_quotientAb_of_le_vanishingIdealSubsheaf {J : IdealSubsheaf X.sheaf}
    (hJ : J ≤ vanishingIdealSubsheaf X) : sheafSupport J.quotientAb = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  let one : J.quotientAb.presheaf.obj (op ⊤) := J.quotientπ.hom.app (op ⊤) 1
  refine ⟨⟨J.quotientAb.presheaf.germ ⊤ x trivial one,
    J.quotientAb.presheaf.germ ⊤ x trivial 0, fun h => ?_⟩⟩
  obtain ⟨V, hxV, iV, iV', hres⟩ :=
    J.quotientAb.presheaf.germ_eq x (U := ⊤) (V := ⊤) trivial trivial _ _ h
  have h0 : J.quotient.presheaf.map (homOfLE (leOfHom iV)).op
      (J.quotientπ.hom.app (op ⊤) 1) = 0 := by
    rw [map_zero] at hres
    exact hres
  rw [← J.quotientπ_app_res, map_one, J.quotientπ_app_eq_zero_iff] at h0
  exact (mem_vanishingIdealSubsheaf_iff (X := X) _).mp ((IdealSubsheaf.le_iff.mp hJ) V h0) x hxV
    ((map_one (X.presheaf.germ V x hxV).hom).symm ▸ isUnit_one)

end support

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}

/-- **The quotient by a power has full support** (part of the proof of Hartshorne II,
Proposition 9.5(c), p. 197). If `J` is an ideal of definition of a Noetherian formal scheme `X`,
then `Supp (𝒪_X / J ^ (n + 1)) = X`: indeed `J ^ (n + 1) ⊆ J ⊆ J_red`. -/
theorem sheafSupport_quotientAb_pow (h : IsIdealOfDefinition X J) (n : ℕ) :
    sheafSupport (J ^ (n + 1)).quotientAb = Set.univ :=
  sheafSupport_quotientAb_of_le_vanishingIdealSubsheaf
    ((J.pow_succ_le_self n).trans ((isGreatest_vanishingIdealSubsheaf X).1.2 h))

end IsIdealOfDefinition

namespace IdealSubsheaf

section kernelChart

/-! ### Kernel charts

Let `J` be an ideal subsheaf of the structure sheaf of a locally ringed space `X`, and let
`g : W ⟶ X` be a morphism of locally ringed spaces from a scheme, which is an open embedding with
surjective stalk maps whose kernels are the germs of `J`. Then `g` kills `J`, hence factors
through the ringed space `(X, 𝒪_X / J)`, and the factorization is an open immersion. -/

variable {X : LocallyRingedSpace.{u}} (J : IdealSubsheaf X.sheaf)

/-- A **kernel chart** of an ideal subsheaf `J` of `𝒪_X`: a morphism of locally ringed spaces
`g : W ⟶ X` from a scheme which is an open embedding with surjective stalk maps, such that the
germ of a section `s` of `𝒪_X` at `g w` is killed by the stalk map at `w` exactly when `s` lies in
`J` near `g w`. -/
def IsKernelChart {W : Scheme.{u}} (g : W.toLocallyRingedSpace ⟶ X) : Prop :=
  IsOpenEmbedding g.base ∧ (∀ w, Function.Surjective (g.stalkMap w)) ∧
    ∀ (w : W) (V : Opens X) (hw : g.base w ∈ V) (s : X.presheaf.obj (op V)),
      g.stalkMap w (X.presheaf.germ V (g.base w) hw s) = 0 ↔
        ∃ (V' : Opens X) (hV'V : V' ≤ V), g.base w ∈ V' ∧
          X.sheaf.presheaf.map (homOfLE hV'V).op s ∈ J.ideal V'

/-- **Kernel charts, stalkwise.** `g` is a kernel chart of `J` exactly when it is an open
embedding with surjective stalk maps whose kernels are the stalks `J_{g w}`. -/
lemma isKernelChart_iff {W : Scheme.{u}} (g : W.toLocallyRingedSpace ⟶ X) :
    J.IsKernelChart g ↔ IsOpenEmbedding g.base ∧ (∀ w, Function.Surjective (g.stalkMap w)) ∧
      ∀ w, RingHom.ker (g.stalkMap w).hom = J.stalkIdeal (g.base w) := by
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h w => ?_, fun h w V hw s => ?_⟩)
  · ext a
    obtain ⟨V, hw, s, rfl⟩ := X.presheaf.exists_germ_eq a
    rw [RingHom.mem_ker]
    exact (h w V hw s).trans (J.germ_mem_stalkIdeal_iff hw s).symm
  · have := J.germ_mem_stalkIdeal_iff hw s
    rw [← h w] at this
    exact RingHom.mem_ker.symm.trans this

variable {J} {W : Scheme.{u}} {g : W.toLocallyRingedSpace ⟶ X}

/-- `g` kills `J`: the structure map of `g` vanishes on sections of `J`. -/
private def Kills (J : IdealSubsheaf X.sheaf) (g : W.toLocallyRingedSpace ⟶ X) : Prop :=
  ∀ (V : Opens X) (s : X.presheaf.obj (op V)), s ∈ J.ideal V → g.c.app (op V) s = 0

/-- A kernel chart of `J` kills `J`. -/
private lemma IsKernelChart.kills (hg : J.IsKernelChart g) : Kills J g := by
  intro V s hs
  refine TopCat.Presheaf.section_ext W.sheaf ((Opens.map g.base).obj V) _ 0 fun w hw => ?_
  have h0 := (hg.2.2 w V hw s).mpr ⟨V, le_rfl, hw, J.ideal_le_comap le_rfl hs⟩
  exact ((LocallyRingedSpace.stalkMap_germ_apply g V w hw s).symm.trans h0).trans
    (map_zero _).symm

private lemma isSheaf_pushforward :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (g.base _* W.presheaf) :=
  TopCat.Sheaf.pushforward_sheaf_of_sheaf g.base W.IsSheaf

/-- The map of presheaves `𝒪_X(V) ⧸ J(V) → 𝒪_W(g⁻¹ V)` induced by a kernel chart `g`. -/
private def quotientPresheafLift (hk : Kills J g) :
    idealQuotientPresheaf X.sheaf J.ideal J.ideal_le_comap ⟶ g.base _* W.presheaf where
  app V := CommRingCat.ofHom (Ideal.Quotient.lift (J.ideal V.unop)
    (g.c.app V).hom (fun s hs => hk _ s hs))
  naturality V V' i := by
    ext x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective
      (x : X.sheaf.presheaf.obj V ⧸ J.ideal V.unop)
    exact NatTrans.naturality_apply g.c i s

/-- The map of sheaves of rings `𝒪_X / J ⟶ g_* 𝒪_W` induced by a kernel chart `g`. -/
private def quotientLift (hk : Kills J g) :
    J.quotient.presheaf ⟶ g.base _* W.presheaf :=
  sheafifyLift (Opens.grothendieckTopology X) (quotientPresheafLift hk) isSheaf_pushforward

private lemma quotientLift_app_quotientπ (hk : Kills J g) {V : Opens X}
    (s : X.sheaf.presheaf.obj (op V)) :
    (quotientLift hk).app (op V) (J.quotientπ.hom.app (op V) s) = g.c.app (op V) s := by
  rw [quotientπ_app_apply]
  change (toSheafify (Opens.grothendieckTopology X) _ ≫ quotientLift hk).app (op V)
    (Ideal.Quotient.mk _ s) = _
  rw [quotientLift, toSheafify_sheafifyLift]
  rfl

/-- The morphism of ringed spaces `W ⟶ (X, 𝒪_X / J)` through which a kernel chart `g`
factors. -/
private def toQuotient (hk : Kills J g) : W.toSheafedSpace ⟶ J.quotientSheafedSpace :=
  InducedCategory.homMk { base := g.base, c := quotientLift hk }

private lemma toQuotient_stalkMap_germ (hk : Kills J g) (w : W) (V : Opens X)
    (hw : g.base w ∈ V) (s : X.sheaf.presheaf.obj (op V)) :
    (toQuotient hk).hom.stalkMap w (J.quotient.presheaf.germ V
        (g.base w) hw (J.quotientπ.hom.app (op V) s)) =
      g.stalkMap w (X.presheaf.germ V (g.base w) hw s) := by
  refine (PresheafedSpace.stalkMap_germ_apply (toQuotient hk).hom V w hw _).trans ?_
  refine Eq.trans ?_ (LocallyRingedSpace.stalkMap_germ_apply g V w hw s).symm
  exact congrArg _ (quotientLift_app_quotientπ hk s)

/-- The factorization of a kernel chart through `(X, 𝒪_X / J)` has bijective stalk maps. -/
private lemma isIso_toQuotient_stalkMap (hg : J.IsKernelChart g) (w : W) :
    IsIso ((toQuotient hg.kills).hom.stalkMap w) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · refine (injective_iff_map_eq_zero ((toQuotient hg.kills).hom.stalkMap w).hom).mpr
      fun a ha => ?_
    obtain ⟨V, hw, t, rfl⟩ := J.quotient.presheaf.exists_germ_eq a
    revert ha
    change ∀ _ : (toQuotient hg.kills).hom.stalkMap w
        (J.quotient.presheaf.germ V (g.base w) hw t) = 0,
      J.quotient.presheaf.germ V (g.base w) hw t = 0
    intro ha
    obtain ⟨V', hV'V, s, hwV', hs⟩ := J.exists_quotientπ_app_eq V t (g.base w) hw
    rw [← J.quotient.presheaf.germ_res_apply (homOfLE hV'V) (g.base w) hwV', ← hs] at ha ⊢
    rw [toQuotient_stalkMap_germ hg.kills w V' hwV' s] at ha
    obtain ⟨V'', hV''V', hwV'', hmem⟩ := (hg.2.2 w V' hwV' s).mp ha
    rw [← J.quotient.presheaf.germ_res_apply (homOfLE hV''V') (g.base w) hwV'',
      ← J.quotientπ_app_res, (J.quotientπ_app_eq_zero_iff _ _).mpr hmem, map_zero]
  · intro b
    obtain ⟨a, rfl⟩ := hg.2.1 w b
    obtain ⟨V, hw, s, rfl⟩ := X.presheaf.exists_germ_eq a
    exact ⟨_, toQuotient_stalkMap_germ hg.kills w V hw s⟩

/-- The factorization of a kernel chart through `(X, 𝒪_X / J)` is an open immersion. -/
private lemma isOpenImmersion_toQuotient (hg : J.IsKernelChart g) :
    SheafedSpace.IsOpenImmersion (toQuotient hg.kills) :=
  haveI := isIso_toQuotient_stalkMap hg
  SheafedSpace.IsOpenImmersion.of_stalk_iso (toQuotient hg.kills) hg.1

end kernelChart

section scheme

/-! ### `(X, 𝒪_X / J)` as a Noetherian scheme from Noetherian affine kernel charts -/

variable {X : LocallyRingedSpace.{u}} (J : IdealSubsheaf X.sheaf)
  (h : ∀ x : X, ∃ (R : CommRingCat.{u}) (_ : IsNoetherianRing R)
    (g : (Spec R).toLocallyRingedSpace ⟶ X), J.IsKernelChart g ∧ x ∈ Set.range g.base)

include h in
private lemma isLocalRing_stalk_quotient (x : X) :
    IsLocalRing (J.quotient.presheaf.stalk x) := by
  obtain ⟨R, -, g, hg, w, rfl⟩ := h x
  set φ := (toQuotient hg.kills).hom.stalkMap w
  have : IsIso φ := isIso_toQuotient_stalkMap hg w
  have hφ : Function.Surjective φ := (ConcreteCategory.bijective_of_isIso φ).2
  have : Nontrivial (J.quotient.presheaf.stalk (g.base w)) := hφ.nontrivial
  exact IsLocalRing.of_surjective' (inv φ).hom fun y => ⟨φ y, by
    change (φ ≫ inv φ) y = y
    rw [IsIso.hom_inv_id]
    rfl⟩

/-- The locally ringed space `(X, 𝒪_X / J)`, when `J` has Noetherian affine kernel charts. -/
private def quotientLRS : LocallyRingedSpace.{u} where
  toSheafedSpace := J.quotientSheafedSpace
  isLocalRing := isLocalRing_stalk_quotient J h

/-- A kernel chart `Spec R ⟶ X` of `J` as a morphism of locally ringed spaces
`Spec R ⟶ (X, 𝒪_X / J)`. -/
private def chartLRSHom {R : CommRingCat.{u}} {g : (Spec R).toLocallyRingedSpace ⟶ X}
    (hg : J.IsKernelChart g) :
    Spec.toLocallyRingedSpace.obj (op R) ⟶ quotientLRS J h :=
  ⟨(toQuotient hg.kills).hom, fun w =>
    @isLocalHom_of_isIso _ _ ((toQuotient hg.kills).hom.stalkMap w)
    (isIso_toQuotient_stalkMap hg w)⟩

private lemma isOpenImmersion_chartLRSHom {R : CommRingCat.{u}}
    {g : (Spec R).toLocallyRingedSpace ⟶ X} (hg : J.IsKernelChart g) :
    LocallyRingedSpace.IsOpenImmersion (chartLRSHom J h hg) :=
  isOpenImmersion_toQuotient hg

/-- The scheme `(X, 𝒪_X / J)`, when `J` has Noetherian affine kernel charts. -/
private def quotientSchemeOfCharts : Scheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.scheme (quotientLRS J h) fun x => by
    obtain ⟨R, -, g, hg, w, rfl⟩ := h x
    exact ⟨R, chartLRSHom J h hg, ⟨w, rfl⟩, isOpenImmersion_chartLRSHom J h hg⟩

private lemma isNoetherian_quotientSchemeOfCharts [CompactSpace X] :
    IsNoetherian (quotientSchemeOfCharts J h) := by
  have h' := h
  choose R hRN g hg hx using h'
  let f : ∀ x, Spec (R x) ⟶ quotientSchemeOfCharts J h := fun x =>
    Scheme.Hom.mk (chartLRSHom J h (hg x))
  have hf : ∀ x, IsOpenImmersion (f x) := fun x => isOpenImmersion_chartLRSHom J h (hg x)
  have hl : IsLocallyNoetherian (quotientSchemeOfCharts J h) := by
    refine isLocallyNoetherian_of_affine_cover
      (S := fun x => ⟨(f x).opensRange, isAffineOpen_opensRange _⟩) ?_ ?_
    · rw [eq_top_iff]
      intro y _
      exact Opens.mem_iSup.mpr ⟨y, hx y⟩
    · intro x
      exact isNoetherianRing_of_ringEquiv _
        ((Scheme.ΓSpecIso (R x)).symm ≪≫ IsOpenImmersion.ΓIsoTop (f x)).commRingCatIsoToRingEquiv
  exact { toIsLocallyNoetherian := hl, toCompactSpace := ‹CompactSpace X› }

include h in
/-- **Noetherian quotient schemes from kernel charts.** Let `J` be an ideal subsheaf of the
structure sheaf of a quasi-compact locally ringed space `X`. If every point of `X` lies in the
image of a kernel chart `Spec R ⟶ X` of `J` with `R` Noetherian (an open embedding with surjective
stalk maps whose kernels are the germs of `J`), then the ringed space `(X, 𝒪_X / J)` is a
Noetherian scheme. -/
theorem exists_isNoetherian_iso_quotientSheafedSpace_of_charts [CompactSpace X] :
    ∃ (Y : Scheme.{u}) (_ : IsNoetherian Y), Nonempty (Y.toSheafedSpace ≅ J.quotientSheafedSpace) :=
  ⟨quotientSchemeOfCharts J h, isNoetherian_quotientSchemeOfCharts J h, ⟨Iso.refl _⟩⟩

end scheme

end IdealSubsheaf

section specQuotient

/-! ### Stalks of `Spec (B ⧸ c) ⟶ Spec B` -/

open Spec (structureSheaf) in
open StructureSheaf in
/-- The stalk map of `Spec (B ⧸ c) ⟶ Spec B` at a point over `p` is the map `B_p → (B ⧸ c)_p`,
whose kernel is `c B_p`. -/
private lemma ker_stalkMap_specMap_quotient {B : CommRingCat.{u}} (c : Ideal B)
    (v : PrimeSpectrum (B ⧸ c)) :
    RingHom.ker ((Spec.sheafedSpaceMap (CommRingCat.ofHom (Ideal.Quotient.mk c))).hom.stalkMap
        v).hom =
      c.map (algebraMap B ((structureSheaf B).presheaf.stalk
        (PrimeSpectrum.comap (Ideal.Quotient.mk c) v))) := by
  set f : B ⟶ CommRingCat.of (B ⧸ c) := CommRingCat.ofHom (Ideal.Quotient.mk c)
  set p : PrimeSpectrum B := PrimeSpectrum.comap (Ideal.Quotient.mk c) v
  let ψ : (structureSheaf B).presheaf.stalk p →+* (structureSheaf (B ⧸ c)).presheaf.stalk v :=
    ((Spec.sheafedSpaceMap f).hom.stalkMap v).hom
  have hψ : ∀ b : B, ψ (algebraMap B ((structureSheaf B).presheaf.stalk p) b) =
      algebraMap (B ⧸ c) ((structureSheaf (B ⧸ c)).presheaf.stalk v) (Ideal.Quotient.mk c b) :=
    fun b => stalkMap_toStalk_apply f v b
  change RingHom.ker ψ = _
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun b hb => by
    rw [Ideal.mem_comap, RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem.mpr hb, map_zero])
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.asIdeal.primeCompl x
  have ha : ψ (algebraMap B ((structureSheaf B).presheaf.stalk p) a) = 0 := by
    rw [← IsLocalization.mk'_spec ((structureSheaf B).presheaf.stalk p) a s, map_mul]
    rw [show ψ (IsLocalization.mk' _ a s) = 0 from hx, zero_mul]
  rw [hψ, IsLocalization.map_eq_zero_iff v.asIdeal.primeCompl] at ha
  obtain ⟨⟨m, hm⟩, hma⟩ := ha
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective m
  have ht : t ∈ p.asIdeal.primeCompl := hm
  have hta : t * a ∈ c := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hma
  have hu := IsLocalization.map_units ((structureSheaf B).presheaf.stalk p) (⟨t, ht⟩ :
    p.asIdeal.primeCompl)
  refine (Ideal.unit_mul_mem_iff_mem _ hu).mp ?_
  change _ * IsLocalization.mk' _ a s ∈ _
  rw [IsLocalization.mk'_eq_mul_mk'_one, ← mul_assoc, ← map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hta)

open Spec (structureSheaf) in
/-- **Kernel charts from quotients.** Let `g : Spec B ⟶ X` be an open embedding with surjective
stalk maps, `L` an ideal subsheaf of `𝒪_X` with proper stalks, and `c` an ideal of `B` whose
localization at every `w ∈ Spec B` pulls back to `L_{g w}`. Then `Spec (B ⧸ c) ⟶ Spec B ⟶ X` is a
kernel chart of `L`. -/
private lemma isKernelChart_comp_specMap_quotient {X : LocallyRingedSpace.{u}}
    (L : IdealSubsheaf X.sheaf) {B : CommRingCat.{u}} (g : (Spec B).toLocallyRingedSpace ⟶ X)
    (hg : IsOpenEmbedding g.base) (hs : ∀ w, Function.Surjective (g.stalkMap w)) (c : Ideal B)
    (hc : ∀ w : PrimeSpectrum B, Ideal.comap (g.stalkMap w).hom
      (c.map (algebraMap B ((structureSheaf B).presheaf.stalk w))) = L.stalkIdeal (g.base w))
    (hL : ∀ x, L.stalkIdeal x ≠ ⊤) :
    L.IsKernelChart ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk c))).toLRSHom ≫ g) ∧
      Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk c))).base := by
  set f : B ⟶ CommRingCat.of (B ⧸ c) := CommRingCat.ofHom (Ideal.Quotient.mk c)
  have hcw : ∀ w : PrimeSpectrum B, c ≤ w.asIdeal := by
    intro w b hb
    by_contra hbw
    have hu := IsLocalization.map_units ((structureSheaf B).presheaf.stalk w)
      (⟨b, hbw⟩ : w.asIdeal.primeCompl)
    refine hL (g.base w) ?_
    rw [← hc w, Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hb) hu]
    exact Ideal.comap_top
  have hsurj : Function.Surjective (Spec.map f).base := by
    intro w
    have hw : w ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk c)) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
        Ideal.mk_ker]
      exact hcw w
    exact hw
  refine ⟨?_, hsurj⟩
  rw [IdealSubsheaf.isKernelChart_iff]
  refine ⟨?_, fun v => ?_, fun v => ?_⟩
  · rw [LocallyRingedSpace.comp_base, TopCat.coe_comp]
    exact hg.comp ((Spec.map f).isClosedEmbedding.isEmbedding.isOpenEmbedding_of_surjective hsurj)
  · rw [LocallyRingedSpace.stalkMap_comp]
    exact ((Spec.map f).stalkMap_surjective v).comp (hs _)
  · rw [LocallyRingedSpace.stalkMap_comp]
    change RingHom.ker (((Spec.map f).toLRSHom.stalkMap v).hom.comp (g.stalkMap _).hom) = _
    rw [← RingHom.comap_ker]
    have hk := ker_stalkMap_specMap_quotient c v
    exact (congrArg (Ideal.comap (g.stalkMap _).hom) hk).trans (hc _)

end specQuotient

section quotientIdeal

/-! ### The image of an ideal of definition in an affine chart

Let `g : Spec B ⟶ X` be an open embedding with surjective stalk maps into a Noetherian formal
scheme, whose stalk kernels lie in the stalks of an ideal of definition `J`. Since `(X, 𝒪_X / J)`
is a scheme, the induced morphism from its open subscheme `g(Spec B)` to `Spec B` is a closed
immersion; hence the image of `J` in `B` is the localization of an ideal of `B`. -/

open Spec (structureSheaf)

variable {X : LocallyRingedSpace.{u}} (J : IdealSubsheaf X.sheaf) {W : Scheme.{u}}
  (g : W.toLocallyRingedSpace ⟶ X)

/-- The ideal subsheaf `J ∩ ker g` of `𝒪_X`. -/
private def kerIdeal : IdealSubsheaf X.sheaf :=
  IdealSubsheaf.ofIdeals X.sheaf (fun V => J.ideal V ⊓ RingHom.ker (g.c.app (op V)).hom)
    (fun {V V'} h s hs => by
      refine ⟨J.ideal_le_comap h hs.1, ?_⟩
      have h0 : g.c.app (op V) s = 0 := hs.2
      change g.c.app (op V') (X.presheaf.map (homOfLE h).op s) = 0
      rw [NatTrans.naturality_apply g.c (homOfLE h).op s]
      erw [h0]
      exact map_zero _)
    (fun {U} s hs => by
      refine ⟨J.mem_ideal_of_locally s fun x hx => ?_, ?_⟩
      · obtain ⟨V, hVU, hxV, hsV⟩ := hs x hx
        exact ⟨V, hVU, hxV, hsV.1⟩
      · change g.c.app (op U) s = 0
        refine TopCat.Presheaf.section_ext W.sheaf ((Opens.map g.base).obj U) _ 0 fun w hw => ?_
        obtain ⟨V, hVU, hwV, hsV⟩ := hs (g.base w) hw
        have h0 : g.c.app (op V) (X.presheaf.map (homOfLE hVU).op s) = 0 := hsV.2
        calc W.presheaf.germ _ w hw (g.c.app (op U) s)
            = g.stalkMap w (X.presheaf.germ U (g.base w) hw s) :=
              (LocallyRingedSpace.stalkMap_germ_apply g U w hw s).symm
          _ = g.stalkMap w (X.presheaf.germ V (g.base w) hwV
                (X.presheaf.map (homOfLE hVU).op s)) :=
              congrArg _ (X.presheaf.germ_res_apply (homOfLE hVU) (g.base w) hwV s).symm
          _ = W.presheaf.germ _ w hwV (g.c.app (op V) (X.presheaf.map (homOfLE hVU).op s)) :=
              LocallyRingedSpace.stalkMap_germ_apply g V w hwV _
          _ = 0 := (congrArg _ h0).trans (map_zero _)
          _ = _ := (map_zero _).symm)

variable {J g}

/-- If the stalk kernels of `g` lie in `J`, then `g` is a kernel chart of `J ∩ ker g`. -/
private lemma isKernelChart_kerIdeal (hg : IsOpenEmbedding g.base)
    (hs : ∀ w, Function.Surjective (g.stalkMap w))
    (hker : ∀ w, RingHom.ker (g.stalkMap w).hom ≤ J.stalkIdeal (g.base w)) :
    (kerIdeal J g).IsKernelChart g := by
  rw [IdealSubsheaf.isKernelChart_iff]
  refine ⟨hg, hs, fun w => le_antisymm ?_ ?_⟩
  · intro a ha
    obtain ⟨V, hw, s, rfl⟩ := X.presheaf.exists_germ_eq a
    obtain ⟨V₁, h₁, hw₁, hs₁⟩ := (J.germ_mem_stalkIdeal_iff hw s).mp (hker w ha)
    rw [RingHom.mem_ker, LocallyRingedSpace.stalkMap_germ_apply] at ha
    obtain ⟨N, hwN, iN, iN', hN⟩ := W.presheaf.germ_eq (U := (Opens.map g.base).obj V)
      (V := (Opens.map g.base).obj V) w hw hw _ 0 (ha.trans (map_zero _).symm)
    rw [map_zero] at hN
    let V'' : Opens X := ⟨g.base '' (N : Set W), hg.isOpenMap _ N.2⟩ ⊓ V₁
    have hV''V₁ : V'' ≤ V₁ := inf_le_right
    have hV''V : V'' ≤ V := hV''V₁.trans h₁
    have hwV'' : g.base w ∈ V'' := ⟨⟨w, hwN, rfl⟩, hw₁⟩
    refine ((kerIdeal J g).germ_mem_stalkIdeal_iff hw s).mpr ⟨V'', hV''V, hwV'', ?_, ?_⟩
    · have := J.ideal_le_comap hV''V₁ hs₁
      rw [Ideal.mem_comap] at this
      erw [← CommRingCat.comp_apply, ← Functor.map_comp] at this
      exact this
    · change g.c.app (op V'') (X.presheaf.map (homOfLE hV''V).op s) = 0
      refine TopCat.Presheaf.section_ext W.sheaf ((Opens.map g.base).obj V'') _ 0
        fun w' hw' => ?_
      have hw'' := hw'
      obtain ⟨⟨n, hnN, hn⟩, -⟩ := hw''
      obtain rfl : n = w' := hg.injective hn
      refine Eq.trans ?_ (map_zero _).symm
      calc W.presheaf.germ _ n hw' (g.c.app (op V'') (X.presheaf.map (homOfLE hV''V).op s))
          = g.stalkMap n (X.presheaf.germ V'' (g.base n) hw'
              (X.presheaf.map (homOfLE hV''V).op s)) :=
            (LocallyRingedSpace.stalkMap_germ_apply g V'' n hw' _).symm
        _ = g.stalkMap n (X.presheaf.germ V (g.base n) (hV''V hw') s) :=
            congrArg _ (X.presheaf.germ_res_apply (homOfLE hV''V) (g.base n) hw' s)
        _ = W.presheaf.germ _ n (hV''V hw') (g.c.app (op V) s) :=
            LocallyRingedSpace.stalkMap_germ_apply g V n _ s
        _ = W.presheaf.germ N n hnN (W.presheaf.map iN.op (g.c.app (op V) s)) :=
            (W.presheaf.germ_res_apply iN n hnN _).symm
        _ = 0 := (congrArg _ hN).trans (map_zero _)
  · rintro _ ⟨V, hw, s, hs, rfl⟩
    have h0 : g.c.app (op V) s = 0 := hs.2
    show g.stalkMap w (X.presheaf.germ V (g.base w) hw s) = 0
    exact (LocallyRingedSpace.stalkMap_germ_apply g V w hw s).trans
      ((congrArg _ h0).trans (map_zero _))

/-- The germ of the image of `s` in `R / J` vanishes exactly when the germ of `s` lies in `J_x`. -/
private lemma germ_quotientπ_eq_zero_iff {T : TopCat.{u}} {R : TopCat.Sheaf CommRingCat.{u} T}
    (J : IdealSubsheaf R) {x : T} {V : Opens T} (hx : x ∈ V) (s : R.presheaf.obj (op V)) :
    J.quotient.presheaf.germ V x hx (J.quotientπ.hom.app (op V) s) = 0 ↔
      R.presheaf.germ V x hx s ∈ J.stalkIdeal x := by
  rw [J.germ_mem_stalkIdeal_iff hx s]
  constructor
  · intro h0
    obtain ⟨W, hxW, iU, iV, hW⟩ := J.quotient.presheaf.germ_eq x hx hx _ 0
      (h0.trans (map_zero _).symm)
    rw [map_zero, show iU = homOfLE (leOfHom iU) from rfl, ← J.quotientπ_app_res,
      J.quotientπ_app_eq_zero_iff] at hW
    exact ⟨W, leOfHom iU, hxW, hW⟩
  · rintro ⟨V', h, hxV', hs⟩
    rw [← J.quotient.presheaf.germ_res_apply (homOfLE h) x hxV', ← J.quotientπ_app_res,
      (J.quotientπ_app_eq_zero_iff _ _).mpr hs, map_zero]

private lemma surjective_comp_of {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (f ≫ g) :=
  fun c => by
    obtain ⟨b, rfl⟩ := hg c
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨a, CommRingCat.comp_apply f g a⟩

private lemma surjective_of_surjective_comp {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h : Function.Surjective (f ≫ g)) : Function.Surjective g :=
  fun c => by
    obtain ⟨a, ha⟩ := h c
    exact ⟨f a, (CommRingCat.comp_apply f g a).symm.trans ha⟩

/-- Transport of germs along an equality of points. -/
private lemma eqToHom_germ_apply {T : TopCat.{u}} (F : TopCat.Presheaf CommRingCat.{u} T)
    {x x' : T} (h : x = x') (p : F.stalk x = F.stalk x') {U : Opens T} (hx : x ∈ U)
    (t : F.obj (op U)) :
    (eqToHom p) (F.germ U x hx t) = F.germ U x' (h ▸ hx) t := by
  subst h
  simp

/-- If `ψ = e ≫ (Spec (B ⧸ a) ⟶ Spec B)`, the stalk kernels of `ψ` are the localizations of `a`. -/
private lemma ker_stalkMap_of_eq_comp {Z : Scheme.{u}} {B : CommRingCat.{u}} (ψ : Z ⟶ Spec B)
    (a : Ideal B) (e : Z ≅ Spec (CommRingCat.of (B ⧸ a)))
    (he : ψ = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk a))) (z : Z) :
    RingHom.ker (ψ.stalkMap z).hom =
      a.map (StructureSheaf.toStalk B (ψ.base z)).hom := by
  subst he
  rw [Scheme.Hom.stalkMap_comp]
  change RingHom.ker ((e.hom.stalkMap z).hom.comp
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk a))).stalkMap (e.hom z)).hom) = _
  rw [← RingHom.comap_ker]
  have hinj : Function.Injective (e.hom.stalkMap z).hom :=
    (ConcreteCategory.bijective_of_isIso (e.hom.stalkMap z)).1
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj, ← RingHom.ker_eq_comap_bot]
  exact ker_stalkMap_specMap_quotient a (e.hom.base z)

end quotientIdeal

section quotientSchemeHom

open Spec (structureSheaf)

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}
  (h : IsIdealOfDefinition X J)

/-- The morphism of ringed spaces `(X, 𝒪_X / J) ⟶ X` given by the projection `𝒪_X ⟶ 𝒪_X / J`. -/
private def quotientSchemePHom :
    h.quotientScheme.toPresheafedSpace ⟶ X.toLocallyRingedSpace.toPresheafedSpace where
  base := 𝟙 X.toLocallyRingedSpace.toTopCat
  c := J.quotientπ.hom

private lemma quotientSchemePHom_stalkMap_germ (x : X.toLocallyRingedSpace)
    (V : Opens X.toLocallyRingedSpace) (hx : x ∈ V)
    (s : X.toLocallyRingedSpace.presheaf.obj (op V)) :
    (quotientSchemePHom h).stalkMap x (X.toLocallyRingedSpace.presheaf.germ V x hx s) =
      J.quotient.presheaf.germ V x hx (J.quotientπ.hom.app (op V) s) :=
  PresheafedSpace.stalkMap_germ_apply (quotientSchemePHom h) V x hx s

private lemma surjective_stalkMap_quotientSchemePHom (x : X.toLocallyRingedSpace) :
    Function.Surjective ((quotientSchemePHom h).stalkMap x) := by
  intro b
  obtain ⟨V, hxV, t, rfl⟩ := J.quotient.presheaf.exists_germ_eq b
  obtain ⟨V', hV'V, s, hxV', hs⟩ := J.exists_quotientπ_app_eq V t x hxV
  refine ⟨X.toLocallyRingedSpace.presheaf.germ V' x hxV' s, ?_⟩
  refine (quotientSchemePHom_stalkMap_germ h x V' hxV' s).trans ?_
  exact (congrArg (J.quotient.presheaf.germ V' x hxV') hs).trans
    (J.quotient.presheaf.germ_res_apply (homOfLE hV'V) x hxV' t)

/-- The morphism of locally ringed spaces `(X, 𝒪_X / J) ⟶ X`. -/
private def quotientSchemeHom :
    h.quotientScheme.toLocallyRingedSpace ⟶ X.toLocallyRingedSpace :=
  ⟨quotientSchemePHom h, fun x =>
    haveI : IsLocalRing (X.toLocallyRingedSpace.presheaf.stalk x) :=
      X.toLocallyRingedSpace.isLocalRing x
    IsLocalHom.of_surjective _ (surjective_stalkMap_quotientSchemePHom h x)⟩

omit h in
/-- **The image of an ideal of definition in an affine chart.** Let `g : Spec B ⟶ X` be an open
embedding with surjective stalk maps whose stalk kernels lie in the stalks of the ideal of
definition `J`. Then there is an ideal `a` of `B` whose localization at every `w ∈ Spec B` is the
image of `J_{g w}`. -/
private lemma exists_ideal_map_eq (h : IsIdealOfDefinition X J) {B : CommRingCat.{u}}
    (g : (Spec B).toLocallyRingedSpace ⟶ X.toLocallyRingedSpace) (hg : IsOpenEmbedding g.base)
    (hs : ∀ w, Function.Surjective (g.stalkMap w))
    (hker : ∀ w, RingHom.ker (g.stalkMap w).hom ≤ J.stalkIdeal (g.base w)) :
    ∃ a : Ideal B, ∀ w : PrimeSpectrum B,
      a.map (StructureSheaf.toStalk B w).hom =
        (J.stalkIdeal (g.base w)).map (g.stalkMap w).hom := by
  set Z := h.quotientScheme
  have hK := isKernelChart_kerIdeal hg hs hker
  have hkill : IdealSubsheaf.Kills (kerIdeal J g) (quotientSchemeHom h) := fun V s hs =>
    (J.quotientπ_app_eq_zero_iff V s).mpr hs.1
  let q := IdealSubsheaf.toQuotient hkill
  let ιB := IdealSubsheaf.toQuotient hK.kills
  have : PresheafedSpace.IsOpenImmersion ιB.hom := IdealSubsheaf.isOpenImmersion_toQuotient hK
  let V : Z.Opens := ⟨Set.range g.base, hg.isOpenMap.isOpen_range⟩
  let f0 := (V.ι.toLRSHom.toShHom ≫ q).hom
  have hrange : Set.range f0.base ⊆ Set.range ιB.hom.base := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  let l := PresheafedSpace.IsOpenImmersion.lift ιB.hom f0 hrange
  have hl : l ≫ ιB.hom = f0 := PresheafedSpace.IsOpenImmersion.lift_fac _ _ _
  have hlbase : ∀ z, g.base (l.base z) = (z.1 : X.toLocallyRingedSpace) := fun z =>
    congrArg (fun φ => φ.base z) hl
  -- stalks of `q`
  have hq : ∀ (x : X.toLocallyRingedSpace) (U : Opens X.toLocallyRingedSpace) (hx : x ∈ U)
      (s : X.toLocallyRingedSpace.presheaf.obj (op U)),
      q.hom.stalkMap x ((kerIdeal J g).quotient.presheaf.germ U x hx
        ((kerIdeal J g).quotientπ.hom.app (op U) s)) =
        J.quotient.presheaf.germ U x hx (J.quotientπ.hom.app (op U) s) := fun x U hx s =>
    (IdealSubsheaf.toQuotient_stalkMap_germ hkill x U hx s).trans
      (quotientSchemePHom_stalkMap_germ h x U hx s)
  have hqsurj : ∀ x, Function.Surjective (q.hom.stalkMap x) := by
    intro x b
    obtain ⟨c, hc⟩ := surjective_stalkMap_quotientSchemePHom h x b
    obtain ⟨U, hx, s, rfl⟩ := X.toLocallyRingedSpace.presheaf.exists_germ_eq c
    exact ⟨_, (hq x U hx s).trans ((quotientSchemePHom_stalkMap_germ h x U hx s).symm.trans hc)⟩
  -- the composite identity on stalks
  have hcomp : ∀ z, (l ≫ ιB.hom).stalkMap z = eqToHom (by rw [hl]) ≫ f0.stalkMap z :=
    fun z => PresheafedSpace.stalkMap.congr_hom _ _ hl z
  have hf0surj : ∀ z, Function.Surjective (f0.stalkMap z) := by
    intro z
    change Function.Surjective ((V.ι.toLRSHom.toShHom.hom ≫ q.hom).stalkMap z)
    rw [PresheafedSpace.stalkMap.comp]
    exact surjective_comp_of _ _ (hqsurj _)
      (ConcreteCategory.bijective_of_isIso (V.ι.toLRSHom.toShHom.hom.stalkMap z)).2
  have hlsurj : ∀ z, Function.Surjective (l.stalkMap z) := by
    intro z
    have h1 : Function.Surjective ((l ≫ ιB.hom).stalkMap z) := by
      rw [hcomp]
      exact surjective_comp_of _ _ (ConcreteCategory.bijective_of_isIso (eqToHom _)).2
        (hf0surj z)
    rw [PresheafedSpace.stalkMap.comp] at h1
    exact surjective_of_surjective_comp _ _ h1
  let ψL : V.toScheme.toLocallyRingedSpace ⟶ (Spec B).toLocallyRingedSpace :=
    ⟨l, fun z =>
      haveI : IsLocalRing ((Spec B).presheaf.stalk (l.base z)) :=
        (Spec B).toLocallyRingedSpace.isLocalRing _
      IsLocalHom.of_surjective _ (hlsurj z)⟩
  let ψ : V.toScheme ⟶ Spec B := Scheme.Hom.mk ψL
  have hlemb : IsEmbedding l.base := by
    have e : (⇑g.base ∘ ⇑l.base) = fun z : V.toScheme => (z.1 : X.toLocallyRingedSpace) :=
      funext hlbase
    have h0 : IsEmbedding (⇑g.base ∘ ⇑l.base) := by
      rw [e]
      exact IsEmbedding.subtypeVal
    exact (IsEmbedding.of_comp_iff hg.isEmbedding).mp h0
  have hlbsurj : Function.Surjective l.base := by
    intro w
    refine ⟨⟨g.base w, w, rfl⟩, hg.injective ?_⟩
    exact hlbase _
  have : IsPreimmersion ψ :=
    { stalkMap_surjective := hlsurj
      isEmbedding := hlemb }
  have : IsClosedImmersion ψ := IsClosedImmersion.of_isPreimmersion ψ (by
    change IsClosed (Set.range l.base)
    rw [hlbsurj.range_eq]
    exact isClosed_univ)
  obtain ⟨a, e, he⟩ := IsClosedImmersion.Spec_iff.mp ‹IsClosedImmersion ψ›
  refine ⟨a, fun w => ?_⟩
  obtain ⟨z, rfl⟩ := hlbsurj w
  have hka : RingHom.ker (l.stalkMap z).hom = a.map (StructureSheaf.toStalk B (l.base z)).hom :=
    ker_stalkMap_of_eq_comp ψ a e he z
  refine hka.symm.trans ((Ideal.map_comap_of_surjective _ (hs (l.base z)) _).symm.trans
    (congrArg _ ?_))
  ext u
  obtain ⟨U, hU, s, rfl⟩ := X.toLocallyRingedSpace.presheaf.exists_germ_eq u
  rw [Ideal.mem_comap, RingHom.mem_ker]
  have hx : (z.1 : X.toLocallyRingedSpace) ∈ U := hlbase z ▸ hU
  let K := kerIdeal J g
  have key : l.stalkMap z (g.stalkMap (l.base z)
      (X.toLocallyRingedSpace.presheaf.germ U _ hU s)) =
      V.ι.toLRSHom.toShHom.hom.stalkMap z (J.quotient.presheaf.germ U _ hx
        (J.quotientπ.hom.app (op U) s)) := by
    calc l.stalkMap z (g.stalkMap (l.base z) (X.toLocallyRingedSpace.presheaf.germ U _ hU s))
        = l.stalkMap z (ιB.hom.stalkMap (l.base z)
            (K.quotient.presheaf.germ U _ hU (K.quotientπ.hom.app (op U) s))) :=
          congrArg _ (IdealSubsheaf.toQuotient_stalkMap_germ hK.kills (l.base z) U hU s).symm
      _ = (l ≫ ιB.hom).stalkMap z
            (K.quotient.presheaf.germ U _ hU (K.quotientπ.hom.app (op U) s)) := by
          rw [PresheafedSpace.stalkMap.comp]
          rfl
      _ = f0.stalkMap z (K.quotient.presheaf.germ U _ hx (K.quotientπ.hom.app (op U) s)) := by
          rw [hcomp]
          exact congrArg (f0.stalkMap z) (eqToHom_germ_apply _ (hlbase z) _ hU _)
      _ = V.ι.toLRSHom.toShHom.hom.stalkMap z (q.hom.stalkMap _
            (K.quotient.presheaf.germ U _ hx (K.quotientπ.hom.app (op U) s))) := by
          change (V.ι.toLRSHom.toShHom.hom ≫ q.hom).stalkMap z _ = _
          rw [PresheafedSpace.stalkMap.comp]
          rfl
      _ = _ := congrArg _ (hq _ U hx s)
  have hinj := (ConcreteCategory.bijective_of_isIso (V.ι.toLRSHom.toShHom.hom.stalkMap z)).1
  rw [key]
  refine ((injective_iff_map_eq_zero' _).mp hinj _).trans ?_
  refine (germ_quotientπ_eq_zero_iff J hx s).trans ((J.germ_mem_stalkIdeal_iff hx s).trans ?_)
  refine Iff.trans ?_ (J.germ_mem_stalkIdeal_iff hU s).symm
  rw [hlbase z]

end quotientSchemeHom

section thickeningCharts

/-! ### Affine charts of a Noetherian formal scheme from the thickenings `Y_(m+1)` -/

/-- Restriction of germs of `𝒪_X`. Copied from the private lemma of the same name in
`Hartshorne.Scheme.LargestIdealOfDefinition`. -/
private lemma germ_sheaf_res (X : LocallyRingedSpace.{u}) {U V : Opens X} (h : V ≤ U) (x : X)
    (hx : x ∈ V) (s : X.sheaf.presheaf.obj (op U)) :
    X.presheaf.germ V x hx (X.sheaf.presheaf.map (homOfLE h).op s) =
      X.presheaf.germ U x (h hx) s :=
  X.presheaf.germ_res_apply (homOfLE h) x hx s

/-- If the base map of `f : A ⟶ X` is open, the stalk kernels of `f` lie in `J_red`. -/
private lemma ker_stalkMap_le_stalkIdeal_vanishing {A X : LocallyRingedSpace.{u}} (f : A ⟶ X)
    (hopen : IsOpenMap f.base) (a : A) :
    RingHom.ker (f.stalkMap a).hom ≤ (vanishingIdealSubsheaf X).stalkIdeal (f.base a) := by
  intro u hu
  obtain ⟨V, ha, s, rfl⟩ := X.presheaf.exists_germ_eq u
  rw [RingHom.mem_ker, LocallyRingedSpace.stalkMap_germ_apply] at hu
  obtain ⟨N, haN, iN, iN', hN⟩ := A.presheaf.germ_eq (U := (Opens.map f.base).obj V)
    (V := (Opens.map f.base).obj V) a ha ha _ 0 (hu.trans (map_zero _).symm)
  rw [map_zero] at hN
  let V' : Opens X := ⟨f.base '' (SetLike.coe N), hopen _ N.2⟩ ⊓ V
  have hV'V : V' ≤ V := inf_le_right
  refine ((vanishingIdealSubsheaf X).germ_mem_stalkIdeal_iff ha s).mpr
    ⟨V', hV'V, ⟨⟨a, haN, rfl⟩, ha⟩, ?_⟩
  refine (mem_vanishingIdealSubsheaf_iff (X := X) _).mpr fun y hy hunit => ?_
  rw [germ_sheaf_res X hV'V y hy s] at hunit
  obtain ⟨n, hnN, rfl⟩ : ∃ n ∈ SetLike.coe N, f.base n = y := hy.1
  have hu' := hunit.map (f.stalkMap n).hom
  change IsUnit (f.stalkMap n (X.presheaf.germ V (f.base n) _ s)) at hu'
  rw [LocallyRingedSpace.stalkMap_germ_apply f V n _ s,
    ← A.presheaf.germ_res_apply iN n hnN, hN, map_zero] at hu'
  exact not_isUnit_zero hu'

/-- Kernels of stalk maps of a composite whose first factor has injective stalk maps. -/
private lemma ker_stalkMap_comp_of_injective {A B C : LocallyRingedSpace.{u}} (f : A ⟶ B)
    (k : B ⟶ C) (hf : ∀ a, Function.Injective (f.stalkMap a)) (a : A) :
    RingHom.ker ((f ≫ k).stalkMap a).hom = RingHom.ker (k.stalkMap (f.base a)).hom := by
  rw [LocallyRingedSpace.stalkMap_comp]
  change RingHom.ker ((f.stalkMap a).hom.comp (k.stalkMap (f.base a)).hom) = _
  rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (hf a),
    ← RingHom.ker_eq_comap_bot]

/-- Two open immersions of locally ringed spaces with the same image have isomorphic sources.
Copied from the private declaration of the same name in
`Hartshorne.Scheme.NoetherianFormalScheme`. -/
private def isoOfRangeEqOpenImmersion {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (e : Set.range f.base = Set.range g.base) : X ≅ Y where
  hom := LocallyRingedSpace.IsOpenImmersion.lift g f e.le
  inv := LocallyRingedSpace.IsOpenImmersion.lift f g e.ge
  hom_inv_id := by rw [← cancel_mono f]; simp
  inv_hom_id := by rw [← cancel_mono g]; simp

/-! The constructions below are stated for an arbitrary open embedding `f : Y_1 ⟶ Z` (later
`Y_1 ⟶ Y_(m+1)`) and a morphism `π : 𝒪_{X̂} ⟶ f⁻¹ 𝒪_Z` (later `πₘ`), which keeps kernel
type checking cheap. -/

variable {Y : Scheme.{u}} (I : QuasicoherentIdealSubsheaf Y) {Z : Scheme.{u}}
  (f : I.infinitesimalNeighborhood 1 ⟶ Z) (hf : IsOpenEmbedding f)
  (π : I.formalCompletionSheaf.presheaf ⟶ hf.functor.op ⋙ Z.presheaf)

/-- The morphism of ringed spaces `Z ⟶ X̂` given by `π`, on `Z` restricted along `f`. -/
private def fromNeighborhoodHom :
    (Z.toLocallyRingedSpace.restrict hf).toPresheafedSpace ⟶
      I.formalCompletion.toPresheafedSpace where
  base := 𝟙 _
  c := π

private lemma fromNeighborhoodHom_stalkMap_germ (y : Z.toLocallyRingedSpace.restrict hf)
    (V : Opens I.formalCompletion) (hy : y ∈ V) (s : I.formalCompletion.presheaf.obj (op V)) :
    (fromNeighborhoodHom I f hf π).stalkMap y (I.formalCompletion.presheaf.germ V y hy s) =
      (Z.toLocallyRingedSpace.restrict hf).presheaf.germ V y hy (π.app (op V) s) :=
  PresheafedSpace.stalkMap_germ_apply (fromNeighborhoodHom I f hf π) V y hy s

variable {π} in
private lemma surjective_stalkMap_fromNeighborhoodHom (hπ : TopCat.Presheaf.IsLocallySurjective π)
    (y : Z.toLocallyRingedSpace.restrict hf) :
    Function.Surjective ((fromNeighborhoodHom I f hf π).stalkMap y) := by
  intro b
  obtain ⟨V, hyV, t, rfl⟩ := (Z.toLocallyRingedSpace.restrict hf).presheaf.exists_germ_eq b
  obtain ⟨V', hV'V, ⟨s, hs⟩, hyV'⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hπ V t y hyV
  refine ⟨I.formalCompletion.presheaf.germ V' y hyV' s, ?_⟩
  refine (fromNeighborhoodHom_stalkMap_germ I f hf π y V' hyV' s).trans ?_
  exact (congrArg ((Z.toLocallyRingedSpace.restrict hf).presheaf.germ V' y hyV') hs).trans
    ((Z.toLocallyRingedSpace.restrict hf).presheaf.germ_res_apply (homOfLE hV'V) y hyV' t)

variable {π} in
/-- The morphism of locally ringed spaces `Z ⟶ X̂` given by `π`. -/
private def fromNeighborhood (hπ : TopCat.Presheaf.IsLocallySurjective π) :
    Z.toLocallyRingedSpace.restrict hf ⟶ I.formalCompletion :=
  ⟨fromNeighborhoodHom I f hf π, fun y =>
    haveI : IsLocalRing (I.formalCompletion.presheaf.stalk
        ((fromNeighborhoodHom I f hf π).base y)) :=
      I.formalCompletion.isLocalRing _
    IsLocalHom.of_surjective _ (surjective_stalkMap_fromNeighborhoodHom I f hf hπ y)⟩

/-- For surjective `f`, the identification of `Z` with its restriction along `f`. -/
private def neighborhoodIso (hfs : Function.Surjective f) :
    Z.toLocallyRingedSpace ≅ Z.toLocallyRingedSpace.restrict hf :=
  isoOfRangeEqOpenImmersion (𝟙 _) (Z.toLocallyRingedSpace.ofRestrict hf)
    ((hfs.range_eq.trans (Set.range_id (α := Z)).symm).symm)

/-- The ideal `J = ker π₀` of `𝒪_{X̂}` as an ideal subsheaf. -/
private def formalIdeal : IdealSubsheaf I.formalCompletionSheaf :=
  IdealSubsheaf.ofIdeals _ I.formalCompletionIdeal (fun h => I.formalCompletionIdeal_le_comap h)
    (fun s hs => I.mem_formalCompletionIdeal_of_locally s hs)

variable {π} in
/-- If the kernel of `π` is `J ^ k`, the stalk kernels of `Z ⟶ X̂` are the `k`-th powers of the
stalks of `J`. -/
private lemma ker_stalkMap_fromNeighborhood (hπ : TopCat.Presheaf.IsLocallySurjective π) (k : ℕ)
    (hker : ∀ (V : Opens (I.infinitesimalNeighborhood 1))
      (s : I.formalCompletionSheaf.presheaf.obj (op V)),
      s ∈ I.formalCompletionIdealPow k V ↔ π.app (op V) s = 0)
    (y : Z.toLocallyRingedSpace.restrict hf) :
    RingHom.ker ((fromNeighborhood I f hf hπ).stalkMap y).hom =
      (formalIdeal I).stalkIdeal y ^ k := by
  refine Eq.trans ?_ (IdealSubsheaf.stalkIdeal_pow _ k y)
  ext u
  obtain ⟨V, hy, s, rfl⟩ := I.formalCompletion.presheaf.exists_germ_eq u
  rw [RingHom.mem_ker]
  refine Iff.trans ?_ ((formalIdeal I ^ k).germ_mem_stalkIdeal_iff hy s).symm
  refine (Iff.of_eq (congrArg (· = 0) (fromNeighborhoodHom_stalkMap_germ I f hf π y V hy s))).trans
    ?_
  constructor
  · intro h0
    obtain ⟨W, hyW, iU, iV, hW⟩ := (Z.toLocallyRingedSpace.restrict hf).presheaf.germ_eq y hy hy
      _ 0 (h0.trans (map_zero _).symm)
    rw [map_zero] at hW
    exact ⟨W, leOfHom iU, hyW, (hker W _).mpr ((NatTrans.naturality_apply π iU.op s).trans hW)⟩
  · rintro ⟨W, hWV, hyW, hsW⟩
    have h0 := (hker W _).mp hsW
    exact ((Z.toLocallyRingedSpace.restrict hf).presheaf.germ_res_apply (homOfLE hWV) y hyW
      _).symm.trans ((congrArg _ ((NatTrans.naturality_apply π (homOfLE hWV).op s).symm.trans
        h0)).trans (map_zero _))

end thickeningCharts

section main

/-- A morphism of locally ringed spaces which is an open embedding with surjective stalk maps.
Copied from the private declaration of the same name in
`Hartshorne.Scheme.LargestIdealOfDefinition`. -/
private def IsChartMap {A B : LocallyRingedSpace.{u}} (f : A ⟶ B) : Prop :=
  IsOpenEmbedding f.base ∧ ∀ a, Function.Surjective (f.stalkMap a)

private lemma IsChartMap.comp {A B C : LocallyRingedSpace.{u}} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsChartMap f) (hg : IsChartMap g) : IsChartMap (f ≫ g) := by
  refine ⟨?_, fun a => ?_⟩
  · rw [LocallyRingedSpace.comp_base, TopCat.coe_comp]
    exact hg.1.comp hf.1
  · rw [LocallyRingedSpace.stalkMap_comp]
    exact (hf.2 a).comp (hg.2 _)

private lemma isChartMap_of_isOpenImmersion {A B : LocallyRingedSpace.{u}} (f : A ⟶ B)
    [H : LocallyRingedSpace.IsOpenImmersion f] : IsChartMap f :=
  ⟨H.base_open, fun a =>
    (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ (f.stalkMap a)
      (LocallyRingedSpace.IsOpenImmersion.stalk_iso f a)).2⟩

private lemma injective_stalkMap_of_isOpenImmersion {A B : LocallyRingedSpace.{u}} (f : A ⟶ B)
    [LocallyRingedSpace.IsOpenImmersion f] (a : A) : Function.Injective (f.stalkMap a) :=
  (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ (f.stalkMap a)
    (LocallyRingedSpace.IsOpenImmersion.stalk_iso f a)).1

/-- A Noetherian formal scheme is quasi-compact. Copied from the private lemma of the same name in
`Hartshorne.Scheme.LargestIdealOfDefinition`. -/
private lemma compactSpace_noetherianFormalScheme (X : NoetherianFormalScheme.{u}) :
    CompactSpace X.toLocallyRingedSpace := by
  obtain ⟨ι, hι, U, hU, hchart⟩ := X.isNoetherianFormalScheme
  have hcpt : ∀ i, IsCompact (SetLike.coe (U i)) := by
    intro i
    obtain ⟨Y, hY, I, ⟨e⟩⟩ := hchart i
    have : CompactSpace (I.infinitesimalNeighborhood 1) :=
      (I.infinitesimalNeighborhoodι 1).isClosedEmbedding.compactSpace
    have : CompactSpace I.formalCompletion.toPresheafedSpace :=
      inferInstanceAs (CompactSpace (I.infinitesimalNeighborhood 1))
    let f := e.inv ≫ X.toLocallyRingedSpace.ofRestrict (U i).isOpenEmbedding
    have hrange : SetLike.coe (U i) = Set.range f.base := by
      ext y
      constructor
      · intro hy
        refine ⟨e.hom.base ⟨y, hy⟩, ?_⟩
        exact (congrArg (fun p => (X.toLocallyRingedSpace.ofRestrict (U i).isOpenEmbedding).base p)
          (LocallyRingedSpace.iso_hom_base_inv_base_apply e ⟨y, hy⟩)).trans rfl
      · rintro ⟨p, rfl⟩
        exact (e.inv.base p).2
    rw [hrange]
    exact isCompact_range f.base.hom.continuous
  refine ⟨?_⟩
  have hcov : Set.univ = ⋃ i, SetLike.coe (U i) := by
    rw [← Opens.coe_iSup, hU]
    rfl
  rw [hcov]
  exact isCompact_iUnion hcpt

/-- **Affine charts with small kernels.** Every point of a Noetherian formal scheme `X` lies in the
image of an open embedding `Spec B ⟶ X` with surjective stalk maps, `B` Noetherian, whose stalk
kernels lie in the `(m+1)`-st powers of the stalks of `J_red`: take an affine open of the thickening
`Y_(m+1)` of a chart `X ⊇ U ≅ Ŷ`. -/
private lemma exists_chart (X : NoetherianFormalScheme.{u}) (x : X.toLocallyRingedSpace) (m : ℕ) :
    ∃ (B : CommRingCat.{u}) (_ : IsNoetherianRing B)
      (g : (Spec B).toLocallyRingedSpace ⟶ X.toLocallyRingedSpace), IsOpenEmbedding g.base ∧
        (∀ w, Function.Surjective (g.stalkMap w)) ∧ x ∈ Set.range g.base ∧
        ∀ w, RingHom.ker (g.stalkMap w).hom ≤
          (vanishingIdealSubsheaf X.toLocallyRingedSpace).stalkIdeal (g.base w) ^ (m + 1) := by
  obtain ⟨ι, hι, U, hU, hchart⟩ := X.isNoetherianFormalScheme
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := Opens.mem_iSup.mp (hU.symm ▸ trivial)
  obtain ⟨Y, hY, I, ⟨e⟩⟩ := hchart i
  let T := e.inv ≫ X.toLocallyRingedSpace.ofRestrict (U i).isOpenEmbedding
  have hT : IsChartMap T := (isChartMap_of_isOpenImmersion e.inv).comp
    (isChartMap_of_isOpenImmersion _)
  let FN := fromNeighborhood I (I.infinitesimalNeighborhoodFromOne m)
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne m)
    (I.isLocallySurjective_formalCompletionπ m)
  have hFN : IsChartMap FN :=
    ⟨IsOpenEmbedding.id, surjective_stalkMap_fromNeighborhoodHom I _ _
      (I.isLocallySurjective_formalCompletionπ m)⟩
  let F0 := fromNeighborhood I (I.infinitesimalNeighborhoodFromOne 0)
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne 0)
    (I.isLocallySurjective_formalCompletionπ 0)
  let ι0 := (neighborhoodIso I (I.infinitesimalNeighborhoodFromOne m)
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne m)
    (I.infinitesimalNeighborhoodFromOne_surjective m))
  let Z := I.infinitesimalNeighborhood (m + 1)
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (I.infinitesimalNeighborhoodι (m + 1))
  let y : I.formalCompletion := e.hom.base ⟨x, hi⟩
  let z : Z := ι0.inv.base y
  obtain ⟨V, hV, hzV, -⟩ := Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens
    (show z ∈ (⊤ : Z.Opens) from trivial)
  obtain ⟨w, hw⟩ : z ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hzV
  have : LocallyRingedSpace.IsOpenImmersion hV.fromSpec.toLRSHom :=
    IsAffineOpen.isOpenImmersion_fromSpec hV
  let F1 := hV.fromSpec.toLRSHom ≫ ι0.hom
  have hF1 : IsChartMap F1 := (isChartMap_of_isOpenImmersion _).comp
    (isChartMap_of_isOpenImmersion _)
  have hF1inj : ∀ a, Function.Injective (F1.stalkMap a) := fun a => by
    change Function.Injective ((hV.fromSpec.toLRSHom ≫ ι0.hom).stalkMap a)
    rw [LocallyRingedSpace.stalkMap_comp]
    exact (injective_stalkMap_of_isOpenImmersion _ _).comp
      (injective_stalkMap_of_isOpenImmersion _ _)
  have hg := hF1.comp (hFN.comp hT)
  refine ⟨Γ(Z, V), IsLocallyNoetherian.component_noetherian ⟨V, hV⟩, F1 ≫ FN ≫ T, hg.1, hg.2,
    ⟨w, ?_⟩, fun w' => ?_⟩
  · change T.base (FN.base (ι0.hom.base (hV.fromSpec w))) = x
    rw [hw]
    change T.base (ι0.hom.base (ι0.inv.base y)) = x
    refine (congrArg (fun p => T.base p)
      (LocallyRingedSpace.iso_inv_base_hom_base_apply ι0 y)).trans ?_
    exact (congrArg (fun p => (X.toLocallyRingedSpace.ofRestrict (U i).isOpenEmbedding).base p)
      (LocallyRingedSpace.iso_hom_base_inv_base_apply e ⟨x, hi⟩)).trans rfl
  rw [ker_stalkMap_comp_of_injective F1 (FN ≫ T) hF1inj w', LocallyRingedSpace.stalkMap_comp]
  set y' := F1.base w'
  change Ideal.comap (T.stalkMap y').hom (RingHom.ker (FN.stalkMap y').hom) ≤ _
  refine (le_of_eq (congrArg (Ideal.comap (T.stalkMap y').hom)
    (ker_stalkMap_fromNeighborhood I _ _ _ (m + 1) (I.mem_formalCompletionIdealPow_iff m)
      y'))).trans ?_
  have hτ : Function.Bijective (T.stalkMap y').hom :=
    ⟨injective_stalkMap_of_isOpenImmersion T y', hT.2 y'⟩
  set K := (formalIdeal I).stalkIdeal y'
  have hK : K.comap (T.stalkMap y').hom ≤
      (vanishingIdealSubsheaf X.toLocallyRingedSpace).stalkIdeal (T.base y') := by
    intro u hu
    have hker0 := ker_stalkMap_fromNeighborhood I _ _ (I.isLocallySurjective_formalCompletionπ 0)
      1 (I.mem_formalCompletionIdealPow_iff 0) y'
    rw [_root_.pow_one] at hker0
    have h0 : (F0.stalkMap y').hom ((T.stalkMap y').hom u) = 0 :=
      (SetLike.ext_iff.mp hker0 _).mpr hu
    have hu0 : u ∈ RingHom.ker ((F0 ≫ T).stalkMap y').hom :=
      RingHom.mem_ker.mpr ((congrArg (fun φ => (CommRingCat.Hom.hom φ) u)
        (LocallyRingedSpace.stalkMap_comp F0 T y')).trans h0)
    exact ker_stalkMap_le_stalkIdeal_vanishing (F0 ≫ T)
      ((isChartMap_of_isOpenImmersion T).1.isOpenMap) y' hu0
  calc (K ^ (m + 1)).comap (T.stalkMap y').hom
      = Ideal.comap (T.stalkMap y').hom
          (Ideal.map (T.stalkMap y').hom (K.comap (T.stalkMap y').hom ^ (m + 1))) :=
        congrArg _ ((Ideal.map_pow _ _ _).trans
          (congrArg (· ^ (m + 1)) (Ideal.map_comap_of_surjective _ hτ.2 K))).symm
    _ = K.comap (T.stalkMap y').hom ^ (m + 1) := Ideal.comap_map_of_bijective _ hτ
    _ ≤ _ := Ideal.pow_right_mono hK _

end main

namespace IsIdealOfDefinition

variable {X : NoetherianFormalScheme.{u}} {J : IdealSubsheaf X.toLocallyRingedSpace.sheaf}

/-- **Powers of an ideal of definition** (Hartshorne II, Proposition 9.5(c), p. 197). If `J` is an
ideal of definition of a Noetherian formal scheme `X`, then so is `J ^ (n + 1)` for every `n`. -/
theorem pow_succ (h : IsIdealOfDefinition X J) (n : ℕ) : IsIdealOfDefinition X (J ^ (n + 1)) where
  support_eq_univ := h.sheafSupport_quotientAb_pow n
  isNoetherianScheme := by
    have := compactSpace_noetherianFormalScheme X
    set JR := vanishingIdealSubsheaf X.toLocallyRingedSpace
    obtain ⟨a, -, ha, -, hab, -⟩ :=
      exists_pow_le_and_pow_le h (isIdealOfDefinition_vanishingIdealSubsheaf X)
    have hJR : J ^ (n + 1) ≤ JR :=
      (J.pow_succ_le_self n).trans ((isGreatest_vanishingIdealSubsheaf X).1.2 h)
    have hL : ∀ x, (J ^ (n + 1)).stalkIdeal x ≠ ⊤ := by
      intro x htop
      have h1 := (J ^ (n + 1)).stalkIdeal_mono hJR x (htop ▸ Submodule.mem_top :
        (1 : X.toLocallyRingedSpace.sheaf.presheaf.stalk x) ∈ (J ^ (n + 1)).stalkIdeal x)
      obtain ⟨V, hx, s, hs, h1⟩ := h1
      refine (mem_vanishingIdealSubsheaf_iff (X := X.toLocallyRingedSpace) s).mp hs x hx ?_
      exact h1 ▸ isUnit_one
    refine IdealSubsheaf.exists_isNoetherian_iso_quotientSheafedSpace_of_charts _ fun x => ?_
    obtain ⟨B, hB, g, hg, hs, hx, hker⟩ := exists_chart X x (a * (n + 1) - 1)
    have hexp : a * (n + 1) - 1 + 1 = a * (n + 1) :=
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ha.ne' n.succ_ne_zero))
    have hkerJ : ∀ w, RingHom.ker (g.stalkMap w).hom ≤ J.stalkIdeal (g.base w) ^ (n + 1) := by
      intro w
      refine (hker w).trans ?_
      rw [hexp, pow_mul, ← IdealSubsheaf.stalkIdeal_pow]
      exact Ideal.pow_right_mono (IdealSubsheaf.stalkIdeal_mono _ hab _) _
    obtain ⟨c, hc⟩ := exists_ideal_map_eq h g hg hs fun w =>
      (hkerJ w).trans (Ideal.pow_le_self n.succ_ne_zero)
    have hc' : ∀ w : PrimeSpectrum B, Ideal.comap (g.stalkMap w).hom
        ((c ^ (n + 1)).map (algebraMap B ((Spec.structureSheaf B).presheaf.stalk w))) =
          (J ^ (n + 1)).stalkIdeal (g.base w) := by
      intro w
      have e1 : (c ^ (n + 1)).map (StructureSheaf.toStalk B w).hom =
          (J.stalkIdeal (g.base w)).map (g.stalkMap w).hom ^ (n + 1) :=
        (Ideal.map_pow _ c (n + 1)).trans (congrArg (· ^ (n + 1)) (hc w))
      have step2 : Ideal.comap (g.stalkMap w).hom
          ((J.stalkIdeal (g.base w) ^ (n + 1)).map (g.stalkMap w).hom) =
            J.stalkIdeal (g.base w) ^ (n + 1) := by
        refine (Ideal.comap_map_of_surjective (g.stalkMap w).hom (hs w) _).trans ?_
        rw [← RingHom.ker_eq_comap_bot]
        exact sup_eq_left.mpr (hkerJ w)
      exact (congrArg _ (e1.trans (Ideal.map_pow _ _ _).symm)).trans
        (step2.trans (IdealSubsheaf.stalkIdeal_pow _ _ _).symm)
    obtain ⟨hK, hsurj⟩ := isKernelChart_comp_specMap_quotient (J ^ (n + 1)) g hg hs (c ^ (n + 1))
      hc' hL
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hsurj w
    exact ⟨CommRingCat.of (B ⧸ c ^ (n + 1)), inferInstance, _, hK, v, rfl⟩

end IsIdealOfDefinition

end Hartshorne
