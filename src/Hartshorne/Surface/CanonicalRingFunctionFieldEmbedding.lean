/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.CanonicalSectionRingDivisor
import Hartshorne.Scheme.CartierClassPicardIntegral
import Hartshorne.Scheme.CartierLinearEquivalenceSheaf
import Hartshorne.Scheme.DimensionAtClosedPoint

/-!
# Section rings embed in a polynomial ring over the function field

Background for Hartshorne, *Algebraic Geometry*, V.6, canonical ring and Kodaira dimension
(pp. 421–422).

Let `X` be an integral scheme with function field `K(X)` and `L` an invertible sheaf on `X`.

* For a Cartier divisor `K`, sending a section `s` of `𝒪_X(nK)` (a rational function) to `s tⁿ`
  is an injective ring map `⨁ₙ H⁰(X, 𝒪_X(nK)) → K(X)[t]`
  (`Hartshorne.DivisorMultipleSectionRing.toPolynomial`,
  `Hartshorne.DivisorMultipleSectionRing.toPolynomial_injective`).
* A rational trivialization of `L`, presented as an isomorphism `α : 𝒪_X(D) ≅ L` (one exists by
  `AlgebraicGeometry.Scheme.exists_cartierDivisor_sheaf_iso`), transports this to an injective
  graded ring map `⨁ₙ H⁰(X, L^{⊗ n}) → K(X)[t]`
  (`Hartshorne.TensorPowerSectionRing.toPolynomialOfIso`), so the section ring is a domain
  (`Hartshorne.TensorPowerSectionRing.isDomain_of_isInvertible`).
* Two rational trivializations give embeddings that differ by the graded `K(X)`-algebra
  automorphism `t ↦ c t` for a nonzero rational function `c`
  (`Hartshorne.TensorPowerSectionRing.exists_toPolynomialOfIso_eq_aeval`).
* If `X` is of finite type over a field `k` and of dimension `d`, the embedding is a map of
  `k`-algebras, so the section ring has transcendence degree at most
  `trdeg_k K(X)[t] = d + 1` over `k` (`Hartshorne.TensorPowerSectionRing.trdeg_le`).
* For `L = ω_X` this gives the corresponding statements for the canonical ring
  (`Hartshorne.canonicalSectionRing_exists_injective_toPolynomial`,
  `Hartshorne.canonicalSectionRing_isDomain`, `Hartshorne.canonicalSectionRing_trdeg_le`).
-/

open CategoryTheory Opposite TopologicalSpace
open scoped DirectSum

namespace Hartshorne

open AlgebraicGeometry Polynomial

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} [IsIntegral X]

namespace DivisorMultipleSectionRing

variable (K : X.CartierDivisor)

/-- The rational function `s ∈ K(X)` underlying a global section `s` of `𝒪_X(nK)`. -/
def ratFun {n : ℕ} (s : (n • K).sheafR.val.obj (op ⊤)) : X.functionField :=
  Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial ((n • K).kVal s)

theorem ratFun_add {n : ℕ} (s t : (n • K).sheafR.val.obj (op ⊤)) :
    ratFun K (s + t) = ratFun K s + ratFun K t :=
  map_add (Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial) _ _

theorem ratFun_zero {n : ℕ} : ratFun K (0 : (n • K).sheafR.val.obj (op ⊤)) = 0 :=
  map_zero (Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial)

theorem ratFun_injective {n : ℕ} :
    Function.Injective (ratFun K : (n • K).sheafR.val.obj (op ⊤) → X.functionField) :=
  (Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial).injective.comp Subtype.val_injective

/-- The degree-`n` part `s ↦ s tⁿ` of the embedding into `K(X)[t]`. -/
def embComponent (n : ℕ) : (n • K).sheafR.val.obj (op ⊤) →+ X.functionField[X] where
  toFun s := monomial n (ratFun K s)
  map_zero' := by rw [ratFun_zero, map_zero]
  map_add' s t := by rw [ratFun_add, map_add]

/-- The additive map `⨁ₙ H⁰(X, 𝒪_X(nK)) → K(X)[t]`, `s ↦ s tⁿ` in degree `n`. -/
def embAddHom : (⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤)) →+ X.functionField[X] :=
  DirectSum.toAddMonoid (embComponent K)

theorem embAddHom_of (n : ℕ) (s : (n • K).sheafR.val.obj (op ⊤)) :
    embAddHom K (DirectSum.of (fun i : ℕ => (i • K).sheafR.val.obj (op ⊤)) n s) =
      monomial n (ratFun K s) :=
  DirectSum.toAddMonoid_of _ _ _

/-- A homogeneous decomposition of an element of `⨁ₙ H⁰(X, 𝒪_X(nK))`, as a family of sections. -/
def toDirectSum (x : DivisorMultipleSectionRing K) : ⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤) := x

theorem coeff_embAddHom (x : ⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤)) (n : ℕ) :
    (embAddHom K x).coeff n = ratFun K (x n) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, coeff_zero, DirectSum.zero_apply, ratFun_zero]
  | of i s =>
    rw [embAddHom_of, coeff_monomial]
    by_cases h : i = n
    · subst h
      rw [if_pos rfl, DirectSum.of_eq_same]
    · rw [if_neg h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), ratFun_zero]
  | add x y hx hy => rw [map_add, coeff_add, hx, hy, DirectSum.add_apply, ratFun_add]

omit [IsIntegral X] in
theorem add_def (x y : DivisorMultipleSectionRing K) :
    x + y = @HAdd.hAdd (⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤)) _ _ instHAdd x y := by
  change (divisorMultipleSectionsAddEquiv K).symm
    (divisorMultipleSectionsAddEquiv K x + divisorMultipleSectionsAddEquiv K y) = _
  rw [← map_add, AddEquiv.symm_apply_apply]

omit [IsIntegral X] in
theorem zero_def : (0 : DivisorMultipleSectionRing K) =
    @OfNat.ofNat (⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤)) 0 _ := by
  change (divisorMultipleSectionsAddEquiv K).symm 0 = _
  rw [map_zero]

omit [IsIntegral X] in
/-- Induction principle for `⨁ₙ H⁰(X, 𝒪_X(nK))` along its ring structure. -/
theorem induction_on {C : DivisorMultipleSectionRing K → Prop} (x : DivisorMultipleSectionRing K)
    (h0 : C 0) (hof : ∀ n s, C (of K n s)) (hadd : ∀ x y, C x → C y → C (x + y)) : C x := by
  change C (toDirectSum K x)
  induction toDirectSum K x using DirectSum.induction_on with
  | zero => rw [zero_def] at h0; exact h0
  | of i s => exact hof i s
  | add x y hx hy =>
    have := hadd x y hx hy
    rw [add_def] at this
    exact this

theorem embAddHom_ring_add (x y : DivisorMultipleSectionRing K) :
    embAddHom K (x + y) = embAddHom K x + embAddHom K y := by
  rw [add_def]
  exact map_add _ _ _

theorem embAddHom_ring_zero : embAddHom K (0 : DivisorMultipleSectionRing K) = 0 := by
  rw [zero_def]
  exact map_zero _

/-- **The divisor section ring embeds in `K(X)[t]`.** On an integral scheme, `⨁ₙ H⁰(X, 𝒪_X(nK))`
maps to `K(X)[t]` by sending a section `s` of `𝒪_X(nK)`, a rational function, to `s tⁿ`
(`toPolynomial_of`); the map is injective (`toPolynomial_injective`). -/
def toPolynomial : DivisorMultipleSectionRing K →+* X.functionField[X] where
  toFun x := embAddHom K x
  map_one' := by
    obtain ⟨u, h1, hu⟩ := one_eq K
    rw [h1]
    change embAddHom K (DirectSum.of _ 0 u) = 1
    rw [embAddHom_of, ratFun, hu, map_one, monomial_zero_one]
  map_mul' x y := by
    induction x using induction_on with
    | h0 => rw [zero_mul, embAddHom_ring_zero, zero_mul]
    | hadd x x' hx hx' => rw [add_mul, embAddHom_ring_add, embAddHom_ring_add, hx, hx', add_mul]
    | hof m s =>
      induction y using induction_on with
      | h0 => rw [mul_zero, embAddHom_ring_zero, mul_zero]
      | hadd y y' hy hy' => rw [mul_add, embAddHom_ring_add, embAddHom_ring_add, hy, hy', mul_add]
      | hof n t =>
        obtain ⟨w, hw, hkw⟩ := of_mul_of K s t
        rw [hw]
        change embAddHom K (DirectSum.of _ (m + n) w) =
          embAddHom K (DirectSum.of _ m s) * embAddHom K (DirectSum.of _ n t)
        rw [embAddHom_of, embAddHom_of, embAddHom_of, monomial_mul_monomial, ratFun, hkw,
          map_mul]
        rfl
  map_zero' := embAddHom_ring_zero K
  map_add' := embAddHom_ring_add K

theorem toPolynomial_of (n : ℕ) (s : (n • K).sheafR.val.obj (op ⊤)) :
    toPolynomial K (of K n s) = monomial n (ratFun K s) :=
  embAddHom_of K n s


theorem coeff_toPolynomial (x : DivisorMultipleSectionRing K) (n : ℕ) :
    (toPolynomial K x).coeff n = ratFun K (toDirectSum K x n) :=
  coeff_embAddHom K x n

theorem toPolynomial_injective : Function.Injective (toPolynomial K) := by
  intro x y h
  change toDirectSum K x = toDirectSum K y
  refine DFinsupp.ext fun n => ratFun_injective K ?_
  rw [← coeff_toPolynomial, ← coeff_toPolynomial, h]

/-! ### Multipliers of morphisms between divisor sheaves -/

omit [IsIntegral X] in
/-- On an open `V` carrying a local equation `f` of `D`, the local generator `f⁻¹` of `𝒪_X(D)` is a
unit of `K_X(V)`. -/
theorem isUnit_kVal_generator (D : X.CartierDivisor) {V : X.Opens}
    {f : X.totalQuotientUnitsSheaf.obj.obj (op V)}
    (hf : D.restrict V = X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul f)) :
    IsUnit (D.kVal (D.generator hf le_rfl)) :=
  (Units.isUnit (f⁻¹ : (X.totalQuotientSheaf.obj.obj (op V))ˣ)).map
    (X.totalQuotientSheaf.obj.map (homOfLE (le_rfl : V ≤ V)).op).hom

omit [IsIntegral X] in
/-- **A morphism `𝒪_X(D₁) ⟶ 𝒪_X(D₂)` that is multiplication by `m` induces multiplication by `mⁿ`
on `𝒪_X(nD₁) ⟶ 𝒪_X(nD₂)`**, read on an open set carrying a local equation of `D₁`. -/
theorem multiplier_nsmul {D₁ D₂ : X.CartierDivisor} (β : D₁.sheaf ⟶ D₂.sheaf)
    (m : X.totalQuotientSheaf.obj.obj (op ⊤))
    (hm : ∀ (U : X.Opens) (s : D₁.sheaf.val.obj (op U)),
      D₂.secVal (β.val.app (op U) s) =
        D₁.secVal s * X.totalQuotientSheaf.obj.map (homOfLE le_top).op m)
    (n : ℕ) (mₙ : X.totalQuotientSheaf.obj.obj (op ⊤))
    (hmₙ : ∀ (U : X.Opens) (s : (n • D₁).sheaf.val.obj (op U)),
      (n • D₂).secVal ((((D₁.nsmulSheafIso n).hom ≫ TensorPowerSectionRing.powMap β n ≫
        (D₂.nsmulSheafIso n).inv) : (n • D₁).sheafR ⟶ (n • D₂).sheafR).val.app (op U) s) =
        (n • D₁).secVal s * X.totalQuotientSheaf.obj.map (homOfLE le_top).op mₙ)
    {V : X.Opens} {f : X.totalQuotientUnitsSheaf.obj.obj (op V)}
    (hf : D₁.restrict V = X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul f)) :
    X.totalQuotientSheaf.obj.map (homOfLE le_top).op mₙ =
      (X.totalQuotientSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op m) ^ n := by
  set g := D₁.generator hf le_rfl
  set t := (moduleSheafTensorPowerMultilinear n D₁.sheafR).app (op V) (fun _ => g)
  have h := hmₙ V ((D₁.nsmulSheafIso n).inv.val.app (op V) t)
  have e1 : (D₁.nsmulSheafIso n).hom.val.app (op V) ((D₁.nsmulSheafIso n).inv.val.app (op V) t) =
      t := (sectionsAddEquiv (D₁.nsmulSheafIso n) (op V)).apply_symm_apply t
  have e2 : (n • D₂).secVal ((D₂.nsmulSheafIso n).inv.val.app (op V)
      ((TensorPowerSectionRing.powMap β n).val.app (op V) t)) =
      (D₁.kVal g * X.totalQuotientSheaf.obj.map (homOfLE le_top).op m) ^ n := by
    rw [TensorPowerSectionRing.powMap_tprod]
    refine (Scheme.CartierDivisor.kVal_nsmulSheafIso_inv_tprod D₂ n _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact congrArg (· ^ n) (hm V g)
  have e3 : (n • D₁).secVal ((D₁.nsmulSheafIso n).inv.val.app (op V) t) = D₁.kVal g ^ n := by
    refine (Scheme.CartierDivisor.kVal_nsmulSheafIso_inv_tprod D₁ n _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change (n • D₂).secVal ((D₂.nsmulSheafIso n).inv.val.app (op V)
      ((TensorPowerSectionRing.powMap β n).val.app (op V)
        ((D₁.nsmulSheafIso n).hom.val.app (op V) ((D₁.nsmulSheafIso n).inv.val.app (op V) t)))) =
    _ at h
  rw [e1, e2, e3, mul_pow] at h
  exact ((isUnit_kVal_generator D₁ hf).pow n).mul_left_cancel h.symm

end DivisorMultipleSectionRing

namespace TensorPowerSectionRing

variable {L : X.Modules}

omit [IsIntegral X] in
theorem divisorMultipleSectionRingEquiv_symm_of (D : X.CartierDivisor) (n : ℕ)
    (b : divisorSectionRingComponent D n) :
    (divisorMultipleSectionRingEquiv D).symm (DirectSum.of _ n b) =
      DivisorMultipleSectionRing.of D n ((D.nsmulSheafIso n).inv.val.app (op ⊤) b) := by
  rw [RingEquiv.symm_apply_eq, divisorMultipleSectionRingEquiv_of]
  exact congrArg (DirectSum.of _ n)
    ((sectionsAddEquiv (D.nsmulSheafIso n) (op ⊤)).apply_symm_apply b).symm

/-- The rational function `f ∈ K(X)` attached to a global section `a` of `L^{⊗ n}` by a rational
trivialization `α : 𝒪_X(D) ≅ L`: the section of `𝒪_X(nD) ≅ 𝒪_X(D)^{⊗ n} ≅ L^{⊗ n}` corresponding to
`a`, as a rational function. -/
def ratFunOfIso (D : X.CartierDivisor) (α : D.sheaf ≅ L) {n : ℕ}
    (a : Component (R := X.sheaf) L (op ⊤) n) : X.functionField :=
  DivisorMultipleSectionRing.ratFun D
    ((D.nsmulSheafIso n).inv.val.app (op ⊤) ((powIso α.symm n).hom.val.app (op ⊤) a))

/-- **The section ring of an invertible sheaf in `K(X)[t]`.** A
rational trivialization `α : 𝒪_X(D) ≅ L` of `L` gives the ring map
`⨁ₙ H⁰(X, L^{⊗ n}) → K(X)[t]` sending a section `a` of `L^{⊗ n}` to `f tⁿ`, where `f` is its
rational function (`toPolynomialOfIso_of`). It is injective (`toPolynomialOfIso_injective`). -/
def toPolynomialOfIso (D : X.CartierDivisor) (α : D.sheaf ≅ L) :
    (⨁ n, Component (R := X.sheaf) L (op ⊤) n) →+* X.functionField[X] :=
  (DivisorMultipleSectionRing.toPolynomial D).comp
    ((divisorMultipleSectionRingEquiv D).symm.toRingHom.comp (ringEquiv α.symm (op ⊤)).toRingHom)

theorem toPolynomialOfIso_of (D : X.CartierDivisor) (α : D.sheaf ≅ L) (n : ℕ)
    (a : Component (R := X.sheaf) L (op ⊤) n) :
    toPolynomialOfIso D α (DirectSum.of _ n a) = monomial n (ratFunOfIso D α a) := by
  change DivisorMultipleSectionRing.toPolynomial D
    ((divisorMultipleSectionRingEquiv D).symm (ringEquiv α.symm (op ⊤) (DirectSum.of _ n a))) = _
  rw [ringEquiv_of, divisorMultipleSectionRingEquiv_symm_of,
    DivisorMultipleSectionRing.toPolynomial_of]
  rfl

theorem toPolynomialOfIso_injective (D : X.CartierDivisor) (α : D.sheaf ≅ L) :
    Function.Injective (toPolynomialOfIso D α) :=
  (DivisorMultipleSectionRing.toPolynomial_injective D).comp
    ((divisorMultipleSectionRingEquiv D).symm.injective.comp (ringEquiv α.symm (op ⊤)).injective)

/-- **Section rings embed in `K(X)[t]`.** On an integral scheme, the section ring
`⨁ₙ H⁰(X, L^{⊗ n})` of an invertible sheaf `L` embeds as a graded ring in `K(X)[t]`: there is an
injective ring map sending each section of `L^{⊗ n}` to a monomial `f tⁿ`. -/
theorem exists_injective_toPolynomial (hL : L.IsInvertible) :
    ∃ ι : (⨁ n, Component (R := X.sheaf) L (op ⊤) n) →+* X.functionField[X],
      Function.Injective ι ∧
        ∀ (n : ℕ) (a : Component (R := X.sheaf) L (op ⊤) n),
          ∃ g : X.functionField, ι (DirectSum.of _ n a) = monomial n g := by
  obtain ⟨D, ⟨α⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
  exact ⟨toPolynomialOfIso D α, toPolynomialOfIso_injective D α,
    fun n a => ⟨_, toPolynomialOfIso_of D α n a⟩⟩

/-- **Section rings are domains.** On an integral scheme, the section ring of an invertible
sheaf is a domain. -/
theorem isDomain_of_isInvertible (hL : L.IsInvertible) :
    IsDomain (⨁ n, Component (R := X.sheaf) L (op ⊤) n) := by
  obtain ⟨ι, hι, -⟩ := exists_injective_toPolynomial hL
  exact Function.Injective.isDomain ι hι

/-! ### Changing the rational trivialization -/

section Rescaling

open Scheme.CartierDivisor

/-- **Changing the rational trivialization rescales the embedding.** For two rational
trivializations `α₁ : 𝒪_X(D₁) ≅ L` and `α₂ : 𝒪_X(D₂) ≅ L` there is a nonzero rational function `c`
such that the second embedding is the first followed by the graded
`K(X)`-algebra automorphism `t ↦ c t` of `K(X)[t]`, which multiplies the degree-`n` part by `cⁿ`. -/
theorem exists_toPolynomialOfIso_eq_aeval (D₁ D₂ : X.CartierDivisor) (α₁ : D₁.sheaf ≅ L)
    (α₂ : D₂.sheaf ≅ L) :
    ∃ c : X.functionFieldˣ, ∀ x : ⨁ n, Component (R := X.sheaf) L (op ⊤) n,
      toPolynomialOfIso D₂ α₂ x = aeval (C (c : X.functionField) * Polynomial.X) (toPolynomialOfIso D₁ α₁ x) := by
  set β : D₁.sheaf ⟶ D₂.sheaf := α₁.hom ≫ α₂.inv with hβ
  set β' : D₂.sheaf ⟶ D₁.sheaf := α₂.hom ≫ α₁.inv with hβ'
  obtain ⟨m, hm⟩ := exists_mul_of_hom β
  obtain ⟨m', hm'⟩ := exists_mul_of_hom β'
  obtain ⟨V, f, hV, hf⟩ := D₁.exists_localEquation (genericPoint X)
  have hmm' : Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial m *
      Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial m' = 1 := by
    set g := D₁.generator hf le_rfl
    have h1 := hm' V (β.val.app (op V) g)
    have hβg : β'.val.app (op V) (β.val.app (op V) g) = g := by
      change (β ≫ β').val.app (op V) g = g
      rw [show β ≫ β' = 𝟙 _ by simp [hβ, hβ']]
      rfl
    rw [hβg, hm V g, mul_assoc] at h1
    have h2 : X.totalQuotientSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op m *
        X.totalQuotientSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op m' = 1 :=
      (DivisorMultipleSectionRing.isUnit_kVal_generator D₁ hf).mul_left_cancel (h1.symm.trans (mul_one _).symm)
    have h3 := congrArg (Scheme.totalQuotientSheafEquivFunctionField V hV) h2
    rwa [map_mul, map_one, Scheme.totalQuotientSheafEquivFunctionField_map,
      Scheme.totalQuotientSheafEquivFunctionField_map] at h3
  refine ⟨Units.mkOfMulEqOne _ _ hmm', fun x => ?_⟩
  have hring : toPolynomialOfIso D₂ α₂ =
      (aeval (C (Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial m) * Polynomial.X)).toRingHom.comp
        (toPolynomialOfIso D₁ α₁) := by
    refine DirectSum.ringHom_ext fun n a => ?_
    obtain ⟨mₙ, hmₙ⟩ := exists_mul_of_hom
      (((D₁.nsmulSheafIso n).hom ≫ TensorPowerSectionRing.powMap β n ≫
        (D₂.nsmulSheafIso n).inv) : (n • D₁).sheafR ⟶ (n • D₂).sheafR)
    have hpow := DivisorMultipleSectionRing.multiplier_nsmul β m hm n mₙ hmₙ hf
    have hpowK : Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial mₙ =
        Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial m ^ n := by
      have := congrArg (Scheme.totalQuotientSheafEquivFunctionField V hV) hpow
      rwa [map_pow, Scheme.totalQuotientSheafEquivFunctionField_map,
        Scheme.totalQuotientSheafEquivFunctionField_map] at this
    have hcomp : powMap α₂.inv n = powMap α₁.inv n ≫ powMap β n := by
      rw [← powMap_comp, hβ, Iso.inv_hom_id_assoc]
    set b := (D₁.nsmulSheafIso n).inv.val.app (op ⊤) ((powIso α₁.symm n).hom.val.app (op ⊤) a)
    have key : (D₂.nsmulSheafIso n).inv.val.app (op ⊤) ((powIso α₂.symm n).hom.val.app (op ⊤) a) =
        (((D₁.nsmulSheafIso n).hom ≫ TensorPowerSectionRing.powMap β n ≫
          (D₂.nsmulSheafIso n).inv) : (n • D₁).sheafR ⟶ (n • D₂).sheafR).val.app (op ⊤) b := by
      change (D₂.nsmulSheafIso n).inv.val.app (op ⊤) ((powMap α₂.inv n).val.app (op ⊤) a) =
        (D₂.nsmulSheafIso n).inv.val.app (op ⊤) ((powMap β n).val.app (op ⊤)
          ((D₁.nsmulSheafIso n).hom.val.app (op ⊤) ((D₁.nsmulSheafIso n).inv.val.app (op ⊤)
            ((powMap α₁.inv n).val.app (op ⊤) a))))
      have e1 : (D₁.nsmulSheafIso n).hom.val.app (op ⊤) ((D₁.nsmulSheafIso n).inv.val.app (op ⊤)
          ((powMap α₁.inv n).val.app (op ⊤) a)) = (powMap α₁.inv n).val.app (op ⊤) a :=
        (sectionsAddEquiv (D₁.nsmulSheafIso n) (op ⊤)).apply_symm_apply _
      rw [e1, hcomp]
      rfl
    have hval : ratFunOfIso D₂ α₂ a =
        ratFunOfIso D₁ α₁ a * Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial m ^ n := by
      change Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial ((n • D₂).secVal
        ((D₂.nsmulSheafIso n).inv.val.app (op ⊤) ((powIso α₂.symm n).hom.val.app (op ⊤) a))) =
        Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial ((n • D₁).secVal b) * _
      rw [key]
      refine (congrArg (Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial) (hmₙ ⊤ b)).trans ?_
      rw [map_mul, Scheme.totalQuotientSheafEquivFunctionField_map, hpowK]
    rw [RingHom.comp_apply, toPolynomialOfIso_of, toPolynomialOfIso_of]
    change _ = aeval _ _
    rw [aeval_monomial, algebraMap_eq, mul_pow, ← C_pow, ← mul_assoc, ← C_mul,
      C_mul_X_pow_eq_monomial, hval]
  rw [hring]
  rfl

end Rescaling

/-! ### The transcendence degree bound -/

section Trdeg

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (L : X.Modules)

/-- The scalar `c ∈ k` as a homogeneous element of degree `0` of `⨁ₙ H⁰(X, L^{⊗ n})`. -/
def scalar (c : k) : ⨁ n, Component (R := X.sheaf) L (op ⊤) n :=
  DirectSum.of _ 0 ((show (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤) from
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c) • oneSec (R := X.sheaf) L (op ⊤))

variable {L}

theorem toPolynomialOfIso_scalar (D : X.CartierDivisor) (α : D.sheaf ≅ L) (c : k) :
    toPolynomialOfIso D α (scalar f L c) =
      C (@algebraMap k X.functionField _ _ (functionFieldAlgebra f) c) := by
  set r : (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c
  rw [scalar, toPolynomialOfIso_of, monomial_zero_left]
  congr 1
  have h1 : (powIso α.symm 0).hom.val.app (op ⊤) (r • oneSec (R := X.sheaf) L (op ⊤)) =
      r • oneSec (R := X.sheaf) D.sheaf (op ⊤) := by
    rw [map_smul]
    exact congrArg (r • ·) (powMap_oneSec α.inv (op ⊤))
  have h2 : (D.nsmulSheafIso 0).inv.val.app (op ⊤) (r • oneSec (R := X.sheaf) D.sheaf (op ⊤)) =
      r • (D.nsmulSheafIso 0).inv.val.app (op ⊤) (oneSec (R := X.sheaf) D.sheaf (op ⊤)) :=
    map_smul _ _ _
  have h3 : ((0 : ℕ) • D).kVal ((D.nsmulSheafIso 0).inv.val.app (op ⊤)
      (oneSec (R := X.sheaf) D.sheaf (op ⊤))) = 1 := by
    have e : oneSec (R := X.sheaf) D.sheaf (op ⊤) =
        (moduleSheafTensorPowerMultilinear 0 D.sheafR).app (op ⊤) Fin.elim0 :=
      congrArg _ TensorPower.gOne_def
    rw [e, Scheme.CartierDivisor.kVal_nsmulSheafIso_inv_tprod, Fin.prod_univ_zero]
  change Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial (((0 : ℕ) • D).kVal
    ((D.nsmulSheafIso 0).inv.val.app (op ⊤)
      ((powIso α.symm 0).hom.val.app (op ⊤) (r • oneSec (R := X.sheaf) L (op ⊤))))) = _
  rw [h1, h2]
  change Scheme.totalQuotientSheafEquivFunctionField ⊤ trivial
    (X.toK ⊤ r * ((0 : ℕ) • D).kVal ((D.nsmulSheafIso 0).inv.val.app (op ⊤)
      (oneSec (R := X.sheaf) D.sheaf (op ⊤)))) = _
  rw [h3, mul_one]
  exact Scheme.totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf ⊤ trivial r

/-- The structure map `k → ⨁ₙ H⁰(X, L^{⊗ n})` into degree `0`, for an invertible sheaf `L` on an
integral scheme over `k`. -/
def scalarRingHom (hL : L.IsInvertible) : k →+* ⨁ n, Component (R := X.sheaf) L (op ⊤) n where
  toFun := scalar f L
  map_one' := by
    obtain ⟨D, ⟨α⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
    apply toPolynomialOfIso_injective D α
    rw [toPolynomialOfIso_scalar, map_one, map_one, map_one]
  map_mul' a b := by
    obtain ⟨D, ⟨α⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
    apply toPolynomialOfIso_injective D α
    rw [map_mul, toPolynomialOfIso_scalar, toPolynomialOfIso_scalar, toPolynomialOfIso_scalar,
      map_mul, C_mul]
  map_zero' := by
    obtain ⟨D, ⟨α⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
    apply toPolynomialOfIso_injective D α
    rw [toPolynomialOfIso_scalar, map_zero, map_zero, map_zero]
  map_add' a b := by
    obtain ⟨D, ⟨α⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
    apply toPolynomialOfIso_injective D α
    rw [map_add, toPolynomialOfIso_scalar, toPolynomialOfIso_scalar, toPolynomialOfIso_scalar,
      map_add, C_add]

/-- The `k`-algebra structure of the (commutative) section ring of an invertible sheaf. -/
@[instance_reducible]
def sectionRingAlgebra (hL : L.IsInvertible) :
    letI := commRing (R := X.sheaf) L (op ⊤) ((Scheme.Modules.isInvertible_iff_ringed L).1 hL)
    Algebra k (⨁ n, Component (R := X.sheaf) L (op ⊤) n) :=
  letI := commRing (R := X.sheaf) L (op ⊤) ((Scheme.Modules.isInvertible_iff_ringed L).1 hL)
  (scalarRingHom f hL).toAlgebra

/-- The embedding `toPolynomialOfIso D α` as a map of `k`-algebras. -/
def toPolynomialOfIsoAlgHom (hL : L.IsInvertible) (D : X.CartierDivisor) (α : D.sheaf ≅ L) :
    letI := commRing (R := X.sheaf) L (op ⊤) ((Scheme.Modules.isInvertible_iff_ringed L).1 hL)
    letI := sectionRingAlgebra f hL
    letI := functionFieldAlgebra f
    (⨁ n, Component (R := X.sheaf) L (op ⊤) n) →ₐ[k] X.functionField[X] :=
  letI := commRing (R := X.sheaf) L (op ⊤) ((Scheme.Modules.isInvertible_iff_ringed L).1 hL)
  letI := sectionRingAlgebra f hL
  letI := functionFieldAlgebra f
  { toPolynomialOfIso D α with
    commutes' := fun c => by
      change toPolynomialOfIso D α (scalar f L c) = _
      rw [toPolynomialOfIso_scalar, Polynomial.algebraMap_apply] }

/-- **Transcendence degree bound.** On an integral scheme `X` of finite type and of dimension `d`
over a field `k`, the section ring of an invertible sheaf has transcendence degree at most `d + 1`
over `k`. -/
theorem trdeg_le (hf : FiniteType f) (hL : L.IsInvertible) {d : ℕ}
    (hd : topologicalKrullDim X = d) :
    letI := commRing (R := X.sheaf) L (op ⊤) ((Scheme.Modules.isInvertible_iff_ringed L).1 hL)
    letI := sectionRingAlgebra f hL
    Algebra.trdeg k (⨁ n, Component (R := X.sheaf) L (op ⊤) n) ≤ d + 1 := by
  let _ := commRing (R := X.sheaf) L (op ⊤) ((Scheme.Modules.isInvertible_iff_ringed L).1 hL)
  let _ := sectionRingAlgebra f hL
  let _ := functionFieldAlgebra f
  obtain ⟨D, ⟨α⟩⟩ := Scheme.exists_cartierDivisor_sheaf_iso hL
  have h1 := trdeg_le_of_injective (toPolynomialOfIsoAlgHom f hL D α)
    (toPolynomialOfIso_injective D α)
  obtain ⟨r, hr, htr⟩ := exists_topologicalKrullDim_eq_trdeg f hf
  have hrd : r = d := by
    rw [hd] at hr
    exact_mod_cast hr.symm
  have : FaithfulSMul k X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k X.functionField).injective
  have h2 : Algebra.trdeg k X.functionField[X] = d + 1 := by
    rw [← trdeg_add_eq k X.functionField (A := X.functionField[X]), htr,
      Polynomial.trdeg_of_isDomain, hrd]
  exact h1.trans h2.le

end Trdeg

end TensorPowerSectionRing

/-! ### The canonical ring -/

section Canonical

variable {k : Type u} [Field k] [IsAlgClosed k] (f : X ⟶ Spec (.of k)) (hf : FiniteType f)
  (hX : X.IsRegular) (n : ℕ) (hn : topologicalKrullDim X = n)

include hf hX hn

/-- **The canonical ring embeds in `K(X)[t]`.** For `X` integral, regular and of finite type
over an algebraically closed field, there is an injective ring map
`R(X, K) = ⨁ₘ H⁰(X, ω_X^{⊗ m}) → K(X)[t]` sending each section of `ω_X^{⊗ m}` to a monomial
`g tᵐ`. -/
theorem canonicalSectionRing_exists_injective_toPolynomial :
    ∃ ι : CanonicalSectionRing f →+* X.functionField[X], Function.Injective ι ∧
      ∀ (m : ℕ) (a : CanonicalSectionRing.Component f m),
        ∃ g : X.functionField, ι (DirectSum.of _ m a) = monomial m g :=
  TensorPowerSectionRing.exists_injective_toPolynomial (canonicalSheaf_isInvertible f hf hX n hn)

/-- **The canonical ring is a domain** for `X` integral, regular and of finite type over an
algebraically closed field. -/
theorem canonicalSectionRing_isDomain : IsDomain (CanonicalSectionRing f) :=
  TensorPowerSectionRing.isDomain_of_isInvertible (canonicalSheaf_isInvertible f hf hX n hn)

/-- **The canonical ring has transcendence degree at most `n + 1`** over `k`, for `X` integral,
regular, of finite type and of dimension `n` over an algebraically closed field `k`. -/
theorem canonicalSectionRing_trdeg_le :
    letI := canonicalSectionRingCommRing f hf hX n hn
    letI := TensorPowerSectionRing.sectionRingAlgebra f (canonicalSheaf_isInvertible f hf hX n hn)
    Algebra.trdeg k (CanonicalSectionRing f) ≤ n + 1 :=
  TensorPowerSectionRing.trdeg_le f hf (canonicalSheaf_isInvertible f hf hX n hn) hn

end Canonical

end

end Hartshorne
