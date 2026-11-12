/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.LargestIdealOfDefinition

/-!
# Powers of an ideal of definition

Hartshorne, *Algebraic Geometry*, II.9, Proposition 9.5(c) (p. 197).

* `Hartshorne.IdealSubsheaf.pow_le_pow_right`, `Hartshorne.IdealSubsheaf.pow_succ_le_self`:
  `J ^ l ⊆ J ^ k` for `k ≤ l`; in particular `J ^ (n + 1) ⊆ J`.
* `Hartshorne.sheafSupport_quotientAb_of_le_vanishingIdealSubsheaf`: on a locally ringed space,
  an ideal subsheaf contained in `J_red` (the sections vanishing at every point) has quotient of
  full support.
* `Hartshorne.IsIdealOfDefinition.sheafSupport_quotientAb_pow`: if `J` is an ideal of definition
  of a Noetherian formal scheme `X`, then `Supp (𝒪_X / J ^ (n + 1)) = X`.
* `Hartshorne.IdealSubsheaf.IsKernelChart J g`: a morphism of locally ringed spaces `g : W ⟶ X`
  from a scheme which is an open embedding with surjective stalk maps, and whose stalk maps have
  kernel exactly the germs of `J`.
* `Hartshorne.IdealSubsheaf.exists_isNoetherian_iso_quotientSheafedSpace_of_charts`: if `X` is
  quasi-compact and every point of `X` lies in the image of a kernel chart `Spec R ⟶ X` of `J`
  with `R` Noetherian, then `(X, 𝒪_X / J)` is a Noetherian scheme.

The last two items generalize the chart construction used for `J_red` in
`Hartshorne.Scheme.LargestIdealOfDefinition`: a kernel chart `g` kills `J`, so it factors through
the ringed space `(X, 𝒪_X / J)`, and the factorization is an open immersion because its stalk
maps are bijective.
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
    L.IsKernelChart ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk c))).toLRSHom ≫ g) := by
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

end quotientSchemeHom

end Hartshorne
