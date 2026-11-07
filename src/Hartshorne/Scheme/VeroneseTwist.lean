/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.VeroneseProj
import Hartshorne.Scheme.ProjTwistingSheaf

/-!
# `𝒪_{Proj S^{(d)}}(1)` corresponds to `𝒪_{Proj S}(d)`

Hartshorne, *Algebraic Geometry*, II, Exercise 5.13 (p. 126).

Let `S` be an `ℕ`-graded ring, `d > 0`, and `t : Proj S ≅ Proj S^{(d)}` the isomorphism
`𝔭 ↦ 𝔭 ∩ S^{(d)}`. The pushforward of `𝒪_{Proj S}(d)` along `t` is `𝒪_{Proj S^{(d)}}(1)`.

At a point `𝔭` of `Proj S`, the fiber of `𝒪_{Proj S^{(d)}}(1)` at `𝔭 ∩ S^{(d)}` consists of the
fractions `m / b` with `b ∈ S^{(d)}_n = S_{nd}` and `m ∈ S^{(d)}(1)_n = S_{(n+1)d}`; the fiber of
`𝒪_{Proj S}(d)` at `𝔭` consists of the fractions `m / b` with `b ∈ S_k` and `m ∈ S(d)_k =
S_{d+k}`. Sending a fraction to itself is a bijection between them: a fraction `m / b` with
`b ∈ S_k` is `m b^{d-1} / b^d` with `b^d ∈ S^{(d)}_k` and `m b^{d-1} ∈ S_{(k+1)d}`. These fiber
maps glue to an isomorphism of sheaves of modules.

## Main definitions and results

* `Hartshorne.Veronese.twistFiber`: the fiber map `S^{(d)}(1)_{(P)} → S(d)_{(Q)}`.
* `Hartshorne.Veronese.twistHom`: `𝒪_{Proj S^{(d)}}(1) ⟶ t_* 𝒪_{Proj S}(d)`.
* `Hartshorne.Veronese.twistIso`: `t_* 𝒪_{Proj S}(d) ≅ 𝒪_{Proj S^{(d)}}(1)`.
-/

universe u

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Hartshorne

namespace Veronese

open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite HomogeneousLocalization
  DirectSum

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} [NeZero d]

/-! ### Degrees -/

omit [NeZero d] in
theorem mem_of_mem_gradedTwist_one {n : ℕ} {m : veroneseSubring 𝒜 d}
    (hm : m ∈ gradedTwist (veronese 𝒜 d) 1 n) : (m : A) ∈ 𝒜 ((n + 1) * d) := by
  have := mem_of_mem_gradedTwist hm
  rwa [show ((1 : ℤ) + (n : ℤ)).toNat = n + 1 by omega] at this

omit [NeZero d] in
theorem coe_mem_gradedTwist {n : ℕ} {m : veroneseSubring 𝒜 d}
    (hm : m ∈ gradedTwist (veronese 𝒜 d) 1 n) :
    (m : A) ∈ gradedTwist 𝒜 (d : ℤ) ((n * d : ℕ) : ℤ) :=
  (mem_gradedTwist_of_eq (k := (n + 1) * d) (by push_cast; ring)).2
    (mem_of_mem_gradedTwist_one hm)

omit [NeZero d] in
theorem mem_gradedTwist_one_of_mem {n : ℕ} {a : A} (ha : a ∈ 𝒜 ((n + 1) * d)) :
    ofMem ha ∈ gradedTwist (veronese 𝒜 d) 1 n :=
  (mem_gradedTwist_of_eq (k := n + 1) (by push_cast; ring)).2 ha

theorem mul_pow_mem {k : ℕ} {m b : A} (hm : m ∈ gradedTwist 𝒜 (d : ℤ) (k : ℤ))
    (hb : b ∈ 𝒜 k) : m * b ^ (d - 1) ∈ 𝒜 ((k + 1) * d) := by
  have hm' : m ∈ 𝒜 (d + k) := (mem_gradedTwist_of_eq (by push_cast; ring)).1 hm
  have := SetLike.mul_mem_graded hm' (SetLike.pow_mem_graded (d - 1) hb)
  convert this using 2
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne d)).symm⟩
  simp only [smul_eq_mul, Nat.add_sub_cancel]
  ring

omit [NeZero d] in
theorem pow_mem_mul {k : ℕ} {b : A} (hb : b ∈ 𝒜 k) : b ^ d ∈ 𝒜 (k * d) := by
  simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded d hb

/-! ### Localized modules -/

variable {P : Submonoid (veroneseSubring 𝒜 d)} {Q : Submonoid A}

omit [NeZero d] in
/-- The map `P⁻¹ S^{(d)} → Q⁻¹ S`, `m / s ↦ m / s`, for submonoids with `P ⊆ Q`. -/
def locMap (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype) :
    LocalizedModule P (veroneseSubring 𝒜 d) →+ LocalizedModule Q A where
  toFun y := y.liftOn (fun p => LocalizedModule.mk (p.1 : A) ⟨(p.2.1 : A), h p.2.2⟩)
    fun p p' e => by
      obtain ⟨u, hu⟩ := e
      refine LocalizedModule.mk_eq.2 ⟨⟨(u.1 : A), h u.2⟩, ?_⟩
      have := congrArg Subtype.val hu
      simpa [Submonoid.smul_def, smul_eq_mul] using this
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.liftOn_mk]
    exact LocalizedModule.zero_mk _
  map_add' y z := by
    induction y, z using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk, LocalizedModule.liftOn_mk,
        LocalizedModule.liftOn_mk, LocalizedModule.mk_add_mk]
      rfl

omit [NeZero d] in
theorem locMap_mk (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (m : veroneseSubring 𝒜 d) (s : P) :
    locMap h (LocalizedModule.mk m s) = LocalizedModule.mk (m : A) ⟨(s.1 : A), h s.2⟩ := by
  rw [locMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LocalizedModule.liftOn_mk]

omit [NeZero d] in
theorem locMap_smul (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (a : veroneseSubring 𝒜 d) (s : P) (y : LocalizedModule P (veroneseSubring 𝒜 d)) :
    locMap h (Localization.mk a s • y) =
      Localization.mk (a : A) ⟨(s.1 : A), h s.2⟩ • locMap h y := by
  induction y using LocalizedModule.induction_on with
  | h m t =>
    rw [LocalizedModule.mk_smul_mk, locMap_mk, locMap_mk, LocalizedModule.mk_smul_mk]
    rfl

/-! ### The fiber map -/

/-- The fiber map `S^{(d)}(1)_{(P)} → S(d)_{(Q)}`, `m / b ↦ m / b`, for submonoids with
`P ⊆ Q`: a fraction with `b ∈ S^{(d)}_n = S_{nd}` and `m ∈ S^{(d)}(1)_n = S_{(n+1)d}` is a
fraction of degree `nd` in `S(d)`. -/
def twistFiber (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype) :
    HomogeneousLocalizedModule (veronese 𝒜 d) (gradedTwist (veronese 𝒜 d) 1) P →+
      HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 (d : ℤ)) Q where
  toFun y := ⟨locMap h y.val, by
    obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective y
    exact ⟨n * d, m, s, coe_mem_gradedTwist hm, hs, h hsx, by
      rw [HomogeneousLocalizedModule.val_mk, locMap_mk]⟩⟩
  map_zero' := by
    ext
    exact map_zero (locMap h)
  map_add' y z := by
    ext
    exact map_add (locMap h) y.val z.val

theorem val_twistFiber (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (y : HomogeneousLocalizedModule (veronese 𝒜 d) (gradedTwist (veronese 𝒜 d) 1) P) :
    (twistFiber h y).val = locMap h y.val :=
  rfl

theorem twistFiber_mk (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype) (n : ℕ)
    (m : veroneseSubring 𝒜 d) (hm : m ∈ gradedTwist (veronese 𝒜 d) 1 n)
    (s : veroneseSubring 𝒜 d) (hs : s ∈ veronese 𝒜 d n) (hsx : s ∈ P) :
    twistFiber h (HomogeneousLocalizedModule.mk n m hm s hs hsx) =
      HomogeneousLocalizedModule.mk (n * d) (m : A) (coe_mem_gradedTwist hm) (s : A) hs
        (h hsx) := by
  ext
  rw [val_twistFiber, HomogeneousLocalizedModule.val_mk, locMap_mk,
    HomogeneousLocalizedModule.val_mk]

theorem twistFiber_smul (h : P ≤ Q.comap (veroneseSubring 𝒜 d).subtype)
    (c : HomogeneousLocalization (veronese 𝒜 d) P)
    (y : HomogeneousLocalizedModule (veronese 𝒜 d) (gradedTwist (veronese 𝒜 d) 1) P) :
    twistFiber h (c • y) = hlMap h c • twistFiber h y := by
  obtain ⟨⟨i, ⟨a, ha⟩, ⟨b, hb⟩, hbx⟩, rfl⟩ := HomogeneousLocalization.mk_surjective c
  ext
  rw [val_twistFiber, HomogeneousLocalizedModule.val_smul, HomogeneousLocalizedModule.val_smul,
    val_twistFiber, val_hlMap, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk', ← Localization.mk_eq_mk', ← Localization.mk_eq_mk', locMap_smul]
  rfl

/-- `𝔮` lies over `𝔭`: the homogeneous prime `𝔮` of `S^{(d)}` is `𝔭 ∩ S^{(d)}`. -/
def LiesOver (x : ProjectiveSpectrum (veronese 𝒜 d)) (y : ProjectiveSpectrum 𝒜) : Prop :=
  ∀ r : veroneseSubring 𝒜 d, r ∈ x.asHomogeneousIdeal ↔ (r : A) ∈ y.asHomogeneousIdeal

theorem liesOver_comapPoint (y : ProjectiveSpectrum 𝒜) : LiesOver (comapPoint d y) y :=
  fun _ => Iff.rfl

theorem liesOver_iff_eq {x : ProjectiveSpectrum (veronese 𝒜 d)} {y : ProjectiveSpectrum 𝒜} :
    LiesOver x y ↔ comapPoint d y = x := by
  constructor
  · intro h
    have : (comapPoint d y).asHomogeneousIdeal = x.asHomogeneousIdeal :=
      HomogeneousIdeal.ext (Ideal.ext fun r => (h r).symm)
    cases x
    cases y
    simp only [comapPoint] at this ⊢
    subst this
    rfl
  · rintro rfl
    exact liesOver_comapPoint y

theorem primeCompl_le_of_liesOver {x : ProjectiveSpectrum (veronese 𝒜 d)}
    {y : ProjectiveSpectrum 𝒜} (hxy : LiesOver x y) :
    x.asHomogeneousIdeal.toIdeal.primeCompl ≤
      y.asHomogeneousIdeal.toIdeal.primeCompl.comap (veroneseSubring 𝒜 d).subtype :=
  fun r hr hr' => hr ((hxy r).2 hr')

/-- The fiber map `S^{(d)}(1)_{(𝔮)} → S(d)_{(𝔭)}` for `𝔮 = 𝔭 ∩ S^{(d)}`. -/
abbrev fiberMap (x : ProjectiveSpectrum (veronese 𝒜 d)) (y : ProjectiveSpectrum 𝒜)
    (hxy : LiesOver x y) :
    HomogeneousLocalizedModule (veronese 𝒜 d) (gradedTwist (veronese 𝒜 d) 1)
        x.asHomogeneousIdeal.toIdeal.primeCompl →+
      HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 (d : ℤ))
        y.asHomogeneousIdeal.toIdeal.primeCompl :=
  twistFiber (primeCompl_le_of_liesOver hxy)

theorem fiberMap_injective (x : ProjectiveSpectrum (veronese 𝒜 d)) (y : ProjectiveSpectrum 𝒜)
    (hxy : LiesOver x y) : Function.Injective (fiberMap x y hxy) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, m, hm, s, hs, hsx, rfl⟩ := HomogeneousLocalizedModule.mk_surjective z
  rw [fiberMap, twistFiber_mk] at hz
  have hz' := congrArg HomogeneousLocalizedModule.val hz
  rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_zero,
    ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hz'
  obtain ⟨⟨u, hu⟩, hu'⟩ := hz'
  have hum : u * (m : A) = 0 := by simpa [Submonoid.smul_def, smul_eq_mul] using hu'
  obtain ⟨i, hi⟩ : ∃ i, (decompose 𝒜 u i : A) ∉ y.asHomogeneousIdeal.toIdeal := by
    by_contra! H
    exact hu ((y.asHomogeneousIdeal.isHomogeneous.mem_iff 𝒜).2 H)
  have hcomp : (decompose 𝒜 u i : A) * m = 0 := by
    have := coe_decompose_mul_add_of_right_mem 𝒜 (a := u) (i := i)
      (mem_of_mem_gradedTwist_one hm)
    rw [hum, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at this
    exact this.symm
  have hcd := pow_mem_mul (d := d) (decompose 𝒜 u i).2
  apply HomogeneousLocalizedModule.ext
  rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_zero,
    ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
  refine ⟨⟨ofMem hcd, fun hmem => hi (y.isPrime.mem_of_pow_mem d ((hxy _).1 hmem))⟩, ?_⟩
  apply Subtype.ext
  simp only [Submonoid.smul_def, smul_eq_mul, mul_zero, OneMemClass.coe_one, one_mul,
    Subring.coe_mul, coe_ofMem, ZeroMemClass.coe_zero]
  rw [show (decompose 𝒜 u i : A) ^ d * (m : A) =
      (decompose 𝒜 u i : A) ^ (d - 1) * ((decompose 𝒜 u i : A) * m) by
    rw [← pow_sub_one_mul (NeZero.ne d), mul_assoc], hcomp, mul_zero]

theorem fiberMap_mk_mul_pow (x : ProjectiveSpectrum (veronese 𝒜 d)) (y : ProjectiveSpectrum 𝒜)
    (hxy : LiesOver x y) {k : ℕ} {m b : A} (hm : m ∈ gradedTwist 𝒜 (d : ℤ) (k : ℤ))
    (hb : b ∈ 𝒜 k) (hby : b ∈ y.asHomogeneousIdeal.toIdeal.primeCompl) :
    fiberMap x y hxy (HomogeneousLocalizedModule.mk k (ofMem (mul_pow_mem hm hb))
        (mem_gradedTwist_one_of_mem _) (ofMem (pow_mem_mul (d := d) hb)) (ofMem_mem _)
        (fun hmem => hby (y.isPrime.mem_of_pow_mem d ((hxy _).1 hmem)))) =
      HomogeneousLocalizedModule.mk k m hm b hb hby := by
  rw [fiberMap, twistFiber_mk]
  apply HomogeneousLocalizedModule.ext
  rw [HomogeneousLocalizedModule.val_mk, HomogeneousLocalizedModule.val_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, smul_eq_mul, coe_ofMem]
  obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne d)).symm⟩
  rw [he, Nat.add_sub_cancel]
  ring

theorem fiberMap_surjective (x : ProjectiveSpectrum (veronese 𝒜 d)) (y : ProjectiveSpectrum 𝒜)
    (hxy : LiesOver x y) : Function.Surjective (fiberMap x y hxy) := by
  intro z
  obtain ⟨k, m, hm, b, hb, hby, rfl⟩ := HomogeneousLocalizedModule.mk_surjective z
  exact ⟨_, fiberMap_mk_mul_pow x y hxy hm hb hby⟩

/-- The fiber map as an additive equivalence. -/
def fiberEquiv (x : ProjectiveSpectrum (veronese 𝒜 d)) (y : ProjectiveSpectrum 𝒜)
    (hxy : LiesOver x y) :
    HomogeneousLocalizedModule (veronese 𝒜 d) (gradedTwist (veronese 𝒜 d) 1)
        x.asHomogeneousIdeal.toIdeal.primeCompl ≃+
      HomogeneousLocalizedModule 𝒜 (gradedTwist 𝒜 (d : ℤ))
        y.asHomogeneousIdeal.toIdeal.primeCompl :=
  AddEquiv.ofBijective (fiberMap x y hxy)
    ⟨fiberMap_injective x y hxy, fiberMap_surjective x y hxy⟩

@[simp] theorem fiberEquiv_apply (x : ProjectiveSpectrum (veronese 𝒜 d))
    (y : ProjectiveSpectrum 𝒜) (hxy : LiesOver x y) (z) :
    fiberEquiv x y hxy z = fiberMap x y hxy z :=
  rfl

/-! ### Sections -/

theorem comapPoint_inv_apply (x : Proj (veronese 𝒜 d)) :
    comapPoint d (inv (toProj d) x) = x := by
  rw [← toProj_apply, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
  rfl

theorem inv_apply_comapPoint (y : Proj 𝒜) : inv (toProj d) (comapPoint d y) = y := by
  rw [← toProj_apply, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
  rfl

theorem liesOver_inv_apply (x : Proj (veronese 𝒜 d)) : LiesOver x (inv (toProj d) x) :=
  liesOver_iff_eq.2 (comapPoint_inv_apply x)

variable (d) in
/-- The map on sections over `U` of `𝒪_{Proj S^{(d)}}(1) ⟶ t_* 𝒪_{Proj S}(d)`: a section `s`
goes to `𝔭 ↦ s(𝔭 ∩ S^{(d)})`, through the fiber maps. -/
def twistSections (U : (Proj (veronese 𝒜 d)).Opens) :
    (ProjGradedModuleSheaf.sheafInType (veronese 𝒜 d) (gradedTwist (veronese 𝒜 d) 1)).1.obj
        (op U) →+
      (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 (d : ℤ))).1.obj
        (op (toProj d ⁻¹ᵁ U)) where
  toFun s := ⟨fun y => fiberMap (comapPoint d y.1) y.1 (liesOver_comapPoint y.1)
      (s.1 ⟨comapPoint d y.1, y.2⟩), by
    intro y
    obtain ⟨W, hyW, iWU, n, m, hm, f, hf, f_nin, w⟩ := s.2 ⟨comapPoint d y.1, y.2⟩
    refine ⟨toProj d ⁻¹ᵁ W, hyW, homOfLE fun z hz => iWU.le hz, n * d, (m : A),
      coe_mem_gradedTwist hm, (f : A), hf, fun z => f_nin ⟨comapPoint d z.1, z.2⟩, fun z => ?_⟩
    exact (congrArg (fiberMap _ _ _) (w ⟨comapPoint d z.1, z.2⟩)).trans
      (twistFiber_mk _ _ _ _ _ _ _)⟩
  map_zero' := Subtype.ext <| funext fun _ => map_zero (fiberMap _ _ _)
  map_add' _ _ := Subtype.ext <| funext fun _ => map_add (fiberMap _ _ _) _ _

variable (d) in
/-- The morphism of underlying abelian presheaves. -/
def twistPresheafHom :
    (projTwistingSheaf (veronese 𝒜 d) 1).presheaf ⟶
      ((Scheme.Modules.pushforward (toProj d)).obj (projTwistingSheaf 𝒜 (d : ℤ))).presheaf where
  app U := AddCommGrpCat.ofHom (twistSections d U.unop)
  naturality _ _ _ := rfl

variable (d) in
/-- **The morphism `𝒪_{Proj S^{(d)}}(1) ⟶ t_* 𝒪_{Proj S}(d)`** of sheaves of modules on
`Proj S^{(d)}`, where `t : Proj S ⟶ Proj S^{(d)}`, `𝔭 ↦ 𝔭 ∩ S^{(d)}`. -/
def twistHom : projTwistingSheaf (veronese 𝒜 d) 1 ⟶
    (Scheme.Modules.pushforward (toProj d)).obj (projTwistingSheaf 𝒜 (d : ℤ)) :=
  ⟨PresheafOfModules.homMk (twistPresheafHom d) fun _ _ _ => Subtype.ext <| funext fun _ =>
    twistFiber_smul _ _ _⟩

theorem twistSections_injective (U : (Proj (veronese 𝒜 d)).Opens) :
    Function.Injective (twistSections d U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  apply Subtype.ext
  funext x
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ : ∃ y : Proj 𝒜, comapPoint d y = x :=
    ⟨inv (toProj d) x, comapPoint_inv_apply x⟩
  have := congrArg (fun t => t.1 ⟨y, hx⟩) hs
  exact fiberMap_injective _ _ _ (this.trans (map_zero _).symm)

variable (d) in
/-- The candidate preimage section: its value at `x` is the preimage under the fiber map of the
value of `t` at a point `y` over `x`. -/
def preimageValue (U : (Proj (veronese 𝒜 d)).Opens)
    (t : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 (d : ℤ))).1.obj
      (op (toProj d ⁻¹ᵁ U)))
    (x : Proj (veronese 𝒜 d)) (y : Proj 𝒜) (hy : y ∈ toProj d ⁻¹ᵁ U) (hxy : LiesOver x y) :
    HomogeneousLocalizedModule (veronese 𝒜 d) (gradedTwist (veronese 𝒜 d) 1)
      x.asHomogeneousIdeal.toIdeal.primeCompl :=
  (fiberEquiv x y hxy).symm (t.1 ⟨y, hy⟩)

theorem preimageValue_congr (U : (Proj (veronese 𝒜 d)).Opens)
    (t : (ProjGradedModuleSheaf.sheafInType 𝒜 (gradedTwist 𝒜 (d : ℤ))).1.obj
      (op (toProj d ⁻¹ᵁ U)))
    (x : Proj (veronese 𝒜 d)) {y y' : Proj 𝒜} (hy : y ∈ toProj d ⁻¹ᵁ U)
    (hy' : y' ∈ toProj d ⁻¹ᵁ U) (hxy : LiesOver x y) (hxy' : LiesOver x y') (h : y = y') :
    preimageValue d U t x y hy hxy = preimageValue d U t x y' hy' hxy' := by
  subst h
  rfl

theorem twistSections_surjective (U : (Proj (veronese 𝒜 d)).Opens) :
    Function.Surjective (twistSections d U) := by
  intro t
  have hmem : ∀ x : U, inv (toProj d) x.1 ∈ toProj d ⁻¹ᵁ U := fun x => by
    change toProj d (inv (toProj d) x.1) ∈ U
    rw [toProj_apply, comapPoint_inv_apply]
    exact x.2
  refine ⟨⟨fun x => preimageValue d U t x.1 _ (hmem x) (liesOver_inv_apply x.1), ?_⟩, ?_⟩
  · intro x
    obtain ⟨W, hW, iW, n, m, hm, b, hb, b_nin, w⟩ := t.2 ⟨inv (toProj d) x.1, hmem x⟩
    refine ⟨(inv (toProj d) ⁻¹ᵁ W) ⊓ U, ⟨hW, x.2⟩, homOfLE inf_le_right, n,
      ofMem (mul_pow_mem hm hb), mem_gradedTwist_one_of_mem _, ofMem (pow_mem_mul (d := d) hb),
      ofMem_mem _, fun z hz => ?_, fun z => ?_⟩
    · exact b_nin ⟨inv (toProj d) z.1, z.2.1⟩
        ((inv (toProj d) z.1).isPrime.mem_of_pow_mem d ((liesOver_inv_apply z.1 _).1 hz))
    · change preimageValue d U t z.1 _ _ _ = _
      rw [preimageValue, AddEquiv.symm_apply_eq, fiberEquiv_apply]
      exact (w ⟨inv (toProj d) z.1, z.2.1⟩).trans (fiberMap_mk_mul_pow _ _ _ hm hb _).symm
  · apply Subtype.ext
    funext y
    obtain ⟨y, hy⟩ := y
    change fiberMap (comapPoint d y) y (liesOver_comapPoint y)
      (preimageValue d U t (comapPoint d y) _ _ _) = t.1 ⟨y, hy⟩
    rw [preimageValue_congr U t (comapPoint d y) _ hy _ (liesOver_comapPoint y)
      (inv_apply_comapPoint y), preimageValue, ← fiberEquiv_apply, AddEquiv.apply_symm_apply]

instance isIso_twistHom : IsIso (twistHom (𝒜 := 𝒜) d) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨twistSections_injective U, twistSections_surjective U⟩

variable (𝒜 d) in
/-- **Hartshorne II, Exercise 5.13, twists: `𝒪_{Proj S^{(d)}}(1)` corresponds to
`𝒪_{Proj S}(d)`.** Under the isomorphism `t : Proj S ≅ Proj S^{(d)}`, the pushforward of
`𝒪_{Proj S}(d)` is `𝒪_{Proj S^{(d)}}(1)`. -/
def twistIso :
    (Scheme.Modules.pushforward (projIso 𝒜 d).hom).obj (projTwistingSheaf 𝒜 (d : ℤ)) ≅
      projTwistingSheaf (veronese 𝒜 d) 1 :=
  (asIso (twistHom d)).symm

end Veronese

end Hartshorne
