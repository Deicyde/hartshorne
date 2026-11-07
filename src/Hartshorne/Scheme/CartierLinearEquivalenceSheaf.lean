/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CartierDivisorSheafArithmetic

/-!
# Linear equivalence and isomorphism of the sheaves `O_X(D)`

Hartshorne, *Algebraic Geometry*, II.6, Proposition 6.13(c) (p. 144).

For Cartier divisors `D₁`, `D₂` on a scheme `X`, `D₁ ∼ D₂` if and only if `O_X(D₁) ≅ O_X(D₂)` as
abstract `O_X`-modules, forgetting the embeddings into `K_X` (`linearEquivalent_iff_nonempty_iso`).

* If `D = D' + (f)` for a global section `f` of `K_X^*`, multiplication by `f` maps `O_X(D)` onto
  `O_X(D')`, with inverse multiplication by `f⁻¹` (`isoOfEqAddPrincipal`).
* Conversely, every morphism `φ : O_X(D₁) ⟶ O_X(D₂)` is multiplication by a global section `m` of
  `K_X` (`exists_mul_of_hom`): on an open `V` carrying a local equation `f` of `D₁`, the sections
  of `O_X(D₁)` are the multiples `r f⁻¹`, so `φ` is multiplication by `φ(f⁻¹) f` on `V`, and these
  local multipliers glue. If `φ` is an isomorphism, the multipliers of `φ` and `φ⁻¹` are inverse
  to each other, so `m` is a global section of `K_X^*`, and comparing local equations gives
  `D₁ - D₂ = (m)`.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}}

/-- The restriction to `V` of the principal Cartier divisor of `f` is the class of `f|_V`. -/
theorem principalCartierDivisor_restrict (f : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))
    (V : X.Opens) :
    (X.principalCartierDivisor f).restrict V = X.toCartierDivisorSheaf.hom.app (op V)
      (Additive.ofMul (X.totalQuotientUnitsSheaf.obj.map (homOfLE le_top).op f)) :=
  X.toCartierDivisorSheaf_naturality_apply le_top f

/-- The principal divisor of `f⁻¹` is the negative of the principal divisor of `f`. -/
theorem principalCartierDivisor_inv (f : X.totalQuotientUnitsSheaf.obj.obj (op ⊤)) :
    X.principalCartierDivisor f⁻¹ = -X.principalCartierDivisor f :=
  map_neg X.principalCartierDivisorHom (Additive.ofMul f)

/-- Restricting a section of `K_X^*` commutes with taking its value in `K_X`. -/
theorem kUnitVal_map {U V : X.Opens} (h : V ≤ U) (f : X.totalQuotientUnitsSheaf.obj.obj (op U)) :
    kUnitVal (X.totalQuotientUnitsSheaf.obj.map (homOfLE h).op f) =
      X.totalQuotientSheaf.obj.map (homOfLE h).op (kUnitVal f) :=
  rfl

theorem kUnitVal_inv_mul_self {U : X.Opens} (f : X.totalQuotientUnitsSheaf.obj.obj (op U)) :
    kUnitVal f⁻¹ * kUnitVal f = 1 :=
  Units.inv_mul _

theorem kUnitVal_mul_inv_self {U : X.Opens} (f : X.totalQuotientUnitsSheaf.obj.obj (op U)) :
    kUnitVal f * kUnitVal f⁻¹ = 1 :=
  Units.mul_inv _

/-- The underlying section of `K_X` of a section of `O_X(D)`. -/
abbrev secVal (D : X.CartierDivisor) {U : X.Opens} (s : D.sheaf.val.obj (op U)) :
    X.totalQuotientSheaf.obj.obj (op U) :=
  s.1

/-! ### Multiplication by a global section of `K_X^*` -/

/-- If `D = D' + (f)`, multiplication by `f` sends sections of `O_X(D)` to sections of
`O_X(D')`. -/
theorem isSection_mul_unit {D D' : X.CartierDivisor} {f : X.totalQuotientUnitsSheaf.obj.obj (op ⊤)}
    (hD : D = D' + X.principalCartierDivisor f) {U : X.Opens}
    {s : X.totalQuotientSheaf.obj.obj (op U)} (hs : D.IsSection s) :
    D'.IsSection (s * X.totalQuotientSheaf.obj.map (homOfLE le_top).op (kUnitVal f)) := by
  have hD' : D' = D + -X.principalCartierDivisor f := by rw [hD]; abel
  apply isSection_of_locally
  intro x hx
  obtain ⟨V, g, hxV, hg⟩ := D.exists_localEquation x
  have h₁ : V ⊓ U ≤ V := inf_le_left
  have h₂ : V ⊓ U ≤ U := inf_le_right
  have hg' := D.restrict_eq_of_le h₁ hg
  have hloc := restrict_add_eq hg' (restrict_neg_eq (principalCartierDivisor_restrict f (V ⊓ U)))
  rw [← hD'] at hloc
  obtain ⟨r, hr⟩ := hs (V ⊓ U) h₂ _ hg'
  refine ⟨V ⊓ U, h₂, _, ⟨hxV, hx⟩, hloc, r, ?_⟩
  rw [hr, map_mul, kUnitVal_mul, kMap_map]
  have hu := kUnitVal_inv_mul_self (X.totalQuotientUnitsSheaf.obj.map
    (homOfLE (le_top : V ⊓ U ≤ ⊤)).op f)
  rw [kUnitVal_map] at hu
  linear_combination
    (-(X.totalQuotientSheaf.obj.map (homOfLE h₂).op s *
      kUnitVal (X.totalQuotientUnitsSheaf.obj.map (homOfLE h₁).op g))) * hu

/-- If `D = D' + (f)`, multiplication by `f` as a morphism `O_X(D) ⟶ O_X(D')`. -/
def mulUnitHom {D D' : X.CartierDivisor} (f : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))
    (hD : D = D' + X.principalCartierDivisor f) : D.sheaf ⟶ D'.sheaf where
  val :=
    { app U := ModuleCat.ofHom
        { toFun s := ⟨tqMul s.1 (X.totalQuotientSheaf.obj.map (homOfLE le_top).op (kUnitVal f)),
            isSection_mul_unit hD s.2⟩
          map_add' s t := Subtype.ext (add_mul (R := X.totalQuotientSheaf.obj.obj U) _ _ _)
          map_smul' r s := Subtype.ext (mul_assoc (G := X.totalQuotientSheaf.obj.obj U) _ _ _) }
      naturality {U V} i := by
        ext s
        have h : X.totalQuotientSheaf.obj.map i
            (X.totalQuotientSheaf.obj.map (homOfLE (le_top : U.unop ≤ ⊤)).op (kUnitVal f)) =
              X.totalQuotientSheaf.obj.map (homOfLE (le_top : V.unop ≤ ⊤)).op (kUnitVal f) := by
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
          rfl
        exact Subtype.ext (((map_mul (X.totalQuotientSheaf.obj.map i).hom _ _).trans
          (congrArg (_ * ·) h)).symm) }

theorem mulUnitHom_app_val {D D' : X.CartierDivisor} (f : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))
    (hD : D = D' + X.principalCartierDivisor f) (U : X.Opens) (s : D.sheaf.val.obj (op U)) :
    D'.secVal ((mulUnitHom f hD).val.app (op U) s) =
      D.secVal s * X.totalQuotientSheaf.obj.map (homOfLE le_top).op (kUnitVal f) :=
  rfl

/-- **Hartshorne II.6, Proposition 6.13(c), forward direction.** If `D = D' + (f)` for a global
section `f` of `K_X^*`, then multiplication by `f` is an isomorphism `O_X(D) ≅ O_X(D')`. -/
def isoOfEqAddPrincipal {D D' : X.CartierDivisor} (f : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))
    (hD : D = D' + X.principalCartierDivisor f) : D.sheaf ≅ D'.sheaf where
  hom := mulUnitHom f hD
  inv := mulUnitHom f⁻¹ (by rw [principalCartierDivisor_inv, hD]; abel)
  hom_inv_id := by
    ext U s
    apply Subtype.ext
    change (show X.totalQuotientSheaf.obj.obj _ from s.1) * X.totalQuotientSheaf.obj.map (homOfLE le_top).op (kUnitVal f) *
        X.totalQuotientSheaf.obj.map (homOfLE le_top).op (kUnitVal f⁻¹) = (show X.totalQuotientSheaf.obj.obj _ from s.1)
    rw [mul_assoc, ← map_mul, kUnitVal_mul_inv_self, map_one, mul_one]
  inv_hom_id := by
    ext U s
    apply Subtype.ext
    change (show X.totalQuotientSheaf.obj.obj _ from s.1) * X.totalQuotientSheaf.obj.map (homOfLE le_top).op (kUnitVal f⁻¹) *
        X.totalQuotientSheaf.obj.map (homOfLE le_top).op (kUnitVal f) = (show X.totalQuotientSheaf.obj.obj _ from s.1)
    rw [mul_assoc, ← map_mul, kUnitVal_inv_mul_self, map_one, mul_one]

/-! ### Morphisms `O_X(D₁) ⟶ O_X(D₂)` are multiplications -/

/-- The restriction to `V ⊆ V₀` of the inverse `f⁻¹` of a local equation `f` of `D` on `V₀`, as a
section of `O_X(D)` over `V`. -/
def localGen (D : X.CartierDivisor) {V₀ : X.Opens} {f : X.totalQuotientUnitsSheaf.obj.obj (op V₀)}
    (hf : D.restrict V₀ = X.toCartierDivisorSheaf.hom.app (op V₀) (Additive.ofMul f))
    {V : X.Opens} (h : V ≤ V₀) : D.sheaf.val.obj (op V) :=
  ⟨X.totalQuotientSheaf.obj.map (homOfLE h).op (kUnitVal f⁻¹), D.isSection_inv hf h⟩

theorem localGen_val (D : X.CartierDivisor) {V₀ : X.Opens}
    {f : X.totalQuotientUnitsSheaf.obj.obj (op V₀)}
    (hf : D.restrict V₀ = X.toCartierDivisorSheaf.hom.app (op V₀) (Additive.ofMul f))
    {V : X.Opens} (h : V ≤ V₀) :
    D.secVal (D.localGen hf h) = X.totalQuotientSheaf.obj.map (homOfLE h).op (kUnitVal f⁻¹) :=
  rfl

theorem localGen_restrict (D : X.CartierDivisor) {V₀ : X.Opens}
    {f : X.totalQuotientUnitsSheaf.obj.obj (op V₀)}
    (hf : D.restrict V₀ = X.toCartierDivisorSheaf.hom.app (op V₀) (Additive.ofMul f))
    {V W : X.Opens} (h : W ≤ V) (hV : V ≤ V₀) :
    D.sheaf.val.map (homOfLE h).op (D.localGen hf hV) = D.localGen hf (h.trans hV) :=
  Subtype.ext (kMap_map (X := X) _ _ _)

/-- The local multiplier `φ(f⁻¹) f` of a morphism `φ : O_X(D₁) ⟶ O_X(D₂)` on an open carrying a
local equation `f` of `D₁`. -/
def localMultiplier {D₁ D₂ : X.CartierDivisor} (φ : D₁.sheaf ⟶ D₂.sheaf) {V₀ : X.Opens}
    {f : X.totalQuotientUnitsSheaf.obj.obj (op V₀)}
    (hf : D₁.restrict V₀ = X.toCartierDivisorSheaf.hom.app (op V₀) (Additive.ofMul f)) :
    X.totalQuotientSheaf.obj.obj (op V₀) :=
  D₂.secVal (φ.val.app (op V₀) (D₁.localGen hf le_rfl)) * kUnitVal f

/-- On an open `V₀` carrying a local equation `f` of `D₁`, a morphism `φ : O_X(D₁) ⟶ O_X(D₂)` is
multiplication by `φ(f⁻¹) f`. -/
theorem hom_app_val_eq_mul_localMultiplier {D₁ D₂ : X.CartierDivisor} (φ : D₁.sheaf ⟶ D₂.sheaf)
    {V₀ : X.Opens} {f : X.totalQuotientUnitsSheaf.obj.obj (op V₀)}
    (hf : D₁.restrict V₀ = X.toCartierDivisorSheaf.hom.app (op V₀) (Additive.ofMul f))
    {V : X.Opens} (h : V ≤ V₀) (s : D₁.sheaf.val.obj (op V)) :
    D₂.secVal (φ.val.app (op V) s) =
      D₁.secVal s * X.totalQuotientSheaf.obj.map (homOfLE h).op (localMultiplier φ hf) := by
  obtain ⟨r, hr⟩ := s.2 V le_rfl _ (D₁.restrict_eq_of_le h hf)
  have hr' : X.toK V r =
      D₁.secVal s * X.totalQuotientSheaf.obj.map (homOfLE h).op (kUnitVal f) := by
    rw [hr, kMap_id]
    rfl
  have hfinv := congrArg (X.totalQuotientSheaf.obj.map (homOfLE h).op) (kUnitVal_mul_inv_self f)
  rw [map_mul, map_one] at hfinv
  have hs : s = (r : X.ringCatSheaf.obj.obj (op V)) •
      D₁.sheaf.val.map (homOfLE h).op (D₁.localGen hf le_rfl) := by
    rw [localGen_restrict]
    apply Subtype.ext
    change D₁.secVal s = X.toK V r * X.totalQuotientSheaf.obj.map (homOfLE (le_rfl.trans h)).op
      (kUnitVal f⁻¹)
    rw [hr']
    linear_combination (-D₁.secVal s) * hfinv
  rw [hs, map_smul, PresheafOfModules.naturality_apply]
  change X.toK V r * X.totalQuotientSheaf.obj.map (homOfLE h).op
      (D₂.secVal (φ.val.app (op V₀) (D₁.localGen hf le_rfl))) =
    (X.toK V r * D₁.secVal (D₁.sheaf.val.map (homOfLE h).op (D₁.localGen hf le_rfl))) *
      X.totalQuotientSheaf.obj.map (homOfLE h).op
        (D₂.secVal (φ.val.app (op V₀) (D₁.localGen hf le_rfl)) * kUnitVal f)
  rw [localGen_restrict, localGen_val, map_mul]
  have hfinv' := congrArg (X.totalQuotientSheaf.obj.map (homOfLE h).op)
    (kUnitVal_inv_mul_self f)
  rw [map_mul, map_one] at hfinv'
  linear_combination (-(X.toK V r * X.totalQuotientSheaf.obj.map (homOfLE h).op
    (D₂.secVal (φ.val.app (op V₀) (D₁.localGen hf le_rfl))))) * hfinv'

/-- Every morphism `φ : O_X(D₁) ⟶ O_X(D₂)` is multiplication by a global section of `K_X`. -/
theorem exists_mul_of_hom {D₁ D₂ : X.CartierDivisor} (φ : D₁.sheaf ⟶ D₂.sheaf) :
    ∃ m : X.totalQuotientSheaf.obj.obj (op ⊤), ∀ (U : X.Opens) (s : D₁.sheaf.val.obj (op U)),
      D₂.secVal (φ.val.app (op U) s) =
        D₁.secVal s * X.totalQuotientSheaf.obj.map (homOfLE le_top).op m := by
  choose V f hxV hf using D₁.exists_localEquation
  have hloc : ∀ (x : X) {W : X.Opens} (h : W ≤ V x) (s : D₁.sheaf.val.obj (op W)),
      D₂.secVal (φ.val.app (op W) s) =
        D₁.secVal s * X.totalQuotientSheaf.obj.map (homOfLE h).op (localMultiplier φ (hf x)) :=
    fun x _ h s ↦ hom_app_val_eq_mul_localMultiplier φ (hf x) h s
  have compat : TopCat.Presheaf.IsCompatible X.totalQuotientSheaf.obj V
      (fun x ↦ localMultiplier φ (hf x)) := by
    intro x y
    have h₁ : V x ⊓ V y ≤ V x := inf_le_left
    have h₂ : V x ⊓ V y ≤ V y := inf_le_right
    have e := (hloc x h₁ (D₁.localGen (hf x) h₁)).symm.trans (hloc y h₂ (D₁.localGen (hf x) h₁))
    rw [localGen_val] at e
    have hfinv := congrArg (X.totalQuotientSheaf.obj.map (homOfLE h₁).op)
      (kUnitVal_mul_inv_self (f x))
    rw [map_mul, map_one] at hfinv
    change X.totalQuotientSheaf.obj.map (homOfLE h₁).op (localMultiplier φ (hf x)) =
      X.totalQuotientSheaf.obj.map (homOfLE h₂).op (localMultiplier φ (hf y))
    linear_combination
      (X.totalQuotientSheaf.obj.map (homOfLE h₂).op (localMultiplier φ (hf y)) -
        X.totalQuotientSheaf.obj.map (homOfLE h₁).op (localMultiplier φ (hf x))) * hfinv +
      X.totalQuotientSheaf.obj.map (homOfLE h₁).op (kUnitVal (f x)) * e
  obtain ⟨m, hm, -⟩ := X.totalQuotientSheaf.existsUnique_gluing' V ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV x⟩) _ compat
  refine ⟨m, fun U s ↦ ?_⟩
  have cover : U ≤ ⨆ x : U, V x ⊓ U := fun x hx ↦
    Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x, hx⟩
  refine X.totalQuotientSheaf.eq_of_locally_eq' (fun x : U ↦ V x ⊓ U) U
    (fun _ ↦ homOfLE inf_le_right) cover _ _ fun x ↦ ?_
  have h₁ : V x ⊓ U ≤ V x := inf_le_left
  have h₂ : V x ⊓ U ≤ U := inf_le_right
  have e := hloc x h₁ (D₁.sheaf.val.map (homOfLE h₂).op s)
  rw [PresheafOfModules.naturality_apply] at e
  change X.totalQuotientSheaf.obj.map (homOfLE h₂).op (D₂.secVal (φ.val.app (op U) s)) =
    X.totalQuotientSheaf.obj.map (homOfLE h₂).op
      (D₁.secVal s * X.totalQuotientSheaf.obj.map (homOfLE le_top).op m)
  refine e.trans ?_
  rw [map_mul, kMap_map, ← hm x, kMap_map]
  rfl

/-- **Hartshorne II.6, Proposition 6.13(c), converse direction.** If `O_X(D₁) ≅ O_X(D₂)` as
abstract `O_X`-modules, then `D₁` and `D₂` are linearly equivalent. -/
theorem linearEquivalent_of_iso {D₁ D₂ : X.CartierDivisor} (e : D₁.sheaf ≅ D₂.sheaf) :
    D₁.LinearEquivalent D₂ := by
  obtain ⟨m, hm⟩ := exists_mul_of_hom e.hom
  obtain ⟨m', hm'⟩ := exists_mul_of_hom e.inv
  have hmm' : m * m' = 1 := by
    choose V f hxV hf using D₁.exists_localEquation
    refine X.totalQuotientSheaf.eq_of_locally_eq' V ⊤ (fun _ ↦ homOfLE le_top)
      (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV x⟩) _ _ fun x ↦ ?_
    have h := congrArg (fun φ ↦ D₁.secVal ((φ : D₁.sheaf ⟶ D₁.sheaf).val.app (op (V x))
      (D₁.localGen (hf x) le_rfl))) e.hom_inv_id
    change D₁.secVal (e.inv.val.app (op (V x)) (e.hom.val.app (op (V x))
      (D₁.localGen (hf x) le_rfl))) = D₁.secVal (D₁.localGen (hf x) le_rfl) at h
    rw [hm', hm, localGen_val] at h
    have hfinv := congrArg (X.totalQuotientSheaf.obj.map (homOfLE (le_refl (V x))).op)
      (kUnitVal_mul_inv_self (f x))
    rw [map_mul, map_one] at hfinv
    rw [map_mul, map_one]
    linear_combination
      (1 - X.totalQuotientSheaf.obj.map (homOfLE le_top).op m *
        X.totalQuotientSheaf.obj.map (homOfLE le_top).op m') * hfinv +
      X.totalQuotientSheaf.obj.map (homOfLE (le_refl (V x))).op (kUnitVal (f x)) * h
  let u : X.totalQuotientUnitsSheaf.obj.obj (op ⊤) :=
    (show (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ from
      ⟨m, m', hmm', by rw [mul_comm, hmm']⟩)
  rw [linearEquivalent_iff]
  refine ⟨u, ?_⟩
  have hloc : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      (D₁ - D₂).restrict W = (X.principalCartierDivisor u).restrict W := by
    intro x
    obtain ⟨V₁, f₁, hx₁, hf₁⟩ := D₁.exists_localEquation x
    obtain ⟨V₂, g₂, hx₂, hg₂⟩ := D₂.exists_localEquation x
    have i₁ : V₁ ⊓ V₂ ≤ V₁ := inf_le_left
    have i₂ : V₁ ⊓ V₂ ≤ V₂ := inf_le_right
    have hf := D₁.restrict_eq_of_le i₁ hf₁
    have hg := D₂.restrict_eq_of_le i₂ hg₂
    set W := V₁ ⊓ V₂
    set f := X.totalQuotientUnitsSheaf.obj.map (homOfLE i₁).op f₁
    set g := X.totalQuotientUnitsSheaf.obj.map (homOfLE i₂).op g₂
    have hsub : (D₁ - D₂).restrict W =
        X.toCartierDivisorSheaf.hom.app (op W) (Additive.ofMul (f * g⁻¹)) := by
      rw [sub_eq_add_neg]
      exact restrict_add_eq hf (restrict_neg_eq hg)
    obtain ⟨a, ha⟩ := (e.hom.val.app (op W) (D₁.localGen hf le_rfl)).2 W le_rfl _ hg
    obtain ⟨b, hb⟩ := (e.inv.val.app (op W) (D₂.localGen hg le_rfl)).2 W le_rfl _ hf
    refine ⟨W, ⟨hx₁, hx₂⟩, restrict_eq_of_ratio hsub (principalCartierDivisor_restrict u W)
      (a := a) (b := b) ?_ ?_⟩
    · have ha' : X.toK W a = D₂.secVal (e.hom.val.app (op W) (D₁.localGen hf le_rfl)) * kUnitVal g := by
        rw [ha, kMap_id]
      rw [ha', hm, localGen_val, kMap_id]
      change _ = kUnitVal (f * g⁻¹)⁻¹ * X.totalQuotientSheaf.obj.map (homOfLE le_top).op m
      rw [mul_inv, inv_inv, kUnitVal_mul]
      ring
    · have hb' : X.toK W b = D₁.secVal (e.inv.val.app (op W) (D₂.localGen hg le_rfl)) * kUnitVal f := by
        rw [hb, kMap_id]
      rw [hb', hm', localGen_val, kMap_id]
      change _ = X.totalQuotientSheaf.obj.map (homOfLE le_top).op m' * kUnitVal (f * g⁻¹)
      rw [kUnitVal_mul]
      ring
  choose W hxW hW using hloc
  exact X.cartierDivisorSheaf.eq_of_locally_eq' W ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩) _ _ hW

/-- **Hartshorne II.6, Proposition 6.13(c).** Two Cartier divisors `D₁`, `D₂` on a scheme `X` are
linearly equivalent if and only if `O_X(D₁) ≅ O_X(D₂)` as abstract `O_X`-modules, forgetting their
embeddings into `K_X`. -/
theorem linearEquivalent_iff_nonempty_iso (D₁ D₂ : X.CartierDivisor) :
    D₁.LinearEquivalent D₂ ↔ Nonempty (D₁.sheaf ≅ D₂.sheaf) := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := (linearEquivalent_iff D₁ D₂).1 h
    exact ⟨isoOfEqAddPrincipal f (eq_add_of_sub_eq' hf)⟩
  · rintro ⟨e⟩
    exact linearEquivalent_of_iso e

end Scheme.CartierDivisor

end

end AlgebraicGeometry
