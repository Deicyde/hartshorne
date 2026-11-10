/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.EffectiveCartierDivisor
import Hartshorne.Scheme.TotalQuotientIntegral
import Hartshorne.Scheme.LocallyFactorialWeilCartier
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Divisors of zeros of sections of invertible sheaves

Hartshorne, *Algebraic Geometry*, II.7, the divisor of zeros of a global section and
Proposition 7.7 (pp. 156–157).

For a global section `s` of an `𝒪_X`-module `L`, a Cartier divisor `D` is the *divisor of zeros*
`(s)₀` (`Scheme.CartierDivisor.IsDivisorOfZeros`) if over every open `U` with a trivialization
`ψ : L|_U ≅ 𝒪_U`, the regular function `ψ(s)` is a local equation of `D`.

A trivialization of `𝒪_X(D₀)` over `U` is multiplication by the inverse of a local equation of
`D₀` (`Scheme.CartierDivisor.exists_restrict_eq_trivGen`). Hence if `L ≅ 𝒪_X(D₀)` and the section
`s` corresponds to a unit `u` of `K_X`, then `(s)₀ = D₀ + div u`
(`Scheme.CartierDivisor.isDivisorOfZeros_add_principal`). On an integral scheme this gives:

* (a) a nonzero section has a divisor of zeros, which is effective and linearly equivalent to
  `D₀` (`Scheme.CartierDivisor.exists_isDivisorOfZeros`);
* (b) every effective divisor linearly equivalent to `D₀` is a divisor of zeros
  (`Scheme.CartierDivisor.exists_section_isDivisorOfZeros`);
* (c) if `X` is moreover universally closed over an algebraically closed field `k` (e.g.
  projective), so that `Γ(X, 𝒪_X) = k` (`Scheme.globalScalar_bijective`), two nonzero sections
  have the same divisor of zeros iff they differ by a scalar in `kˣ`
  (`Scheme.CartierDivisor.isDivisorOfZeros_eq_iff`).

On an integral separated Noetherian locally factorial scheme (e.g. a nonsingular projective
variety), effectivity and linear equivalence agree for Weil and Cartier divisors, which gives the
Weil-divisor form of the proposition (`Scheme.weil_isDivisorOfZeros`,
`Scheme.weil_isDivisorOfZeros_eq_iff`).
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}}

namespace Scheme.CartierDivisor

/-- The regular function on `U` corresponding, under a trivialization `ψ : L|_U ≅ 𝒪_U`, to a
section `s` of `L` over `U`. -/
def trivApply {L : X.Modules} {U : X.Opens} (ψ : L.over U ≅ SheafOfModules.unit _)
    (s : L.val.obj (op U)) : Γ(X, U) :=
  ψ.hom.val.app (op (Over.mk (𝟙 U))) s

/-- The generator `ψ⁻¹(1)` of `𝒪_X(D)|_U` attached to a trivialization `ψ`, as a section of
`K_X` over `U`. -/
def trivGen {D : X.CartierDivisor} {U : X.Opens} (ψ : D.sheaf.over U ≅ SheafOfModules.unit _) :
    X.totalQuotientSheaf.obj.obj (op U) :=
  (((D.sheaf.over U).unitHomEquiv ψ.inv).val (op (Over.mk (𝟙 U)))).1

/-- The generator of a trivialization of `𝒪_X(D)` is a section of `𝒪_X(D)`. -/
theorem trivGen_isSection {D : X.CartierDivisor} {U : X.Opens}
    (ψ : D.sheaf.over U ≅ SheafOfModules.unit _) : D.IsSection (trivGen ψ) :=
  (((D.sheaf.over U).unitHomEquiv ψ.inv).val (op (Over.mk (𝟙 U)))).2

/-- The inverse of a trivialization of `𝒪_X(D)` is multiplication by its generator. -/
theorem inv_app_val {D : X.CartierDivisor} {U : X.Opens}
    (ψ : D.sheaf.over U ≅ SheafOfModules.unit _) (V : X.Opens) (h : V ≤ U) (r : Γ(X, V)) :
    (ψ.inv.val.app (op (Over.mk (homOfLE h))) r).1 =
      X.toK V r * X.totalQuotientSheaf.obj.map (homOfLE h).op (trivGen ψ) := by
  set σ := (D.sheaf.over U).unitHomEquiv ψ.inv
  have hφ : ψ.inv = (D.sheaf.over U).unitHomEquiv.symm σ := (Equiv.symm_apply_apply _ _).symm
  rw [hφ]
  have hσ := σ.2 (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U)).op
  change X.toK V r * (show X.totalQuotientSheaf.obj.obj (op V) from
    (σ.val (op (Over.mk (homOfLE h)))).1) = _
  rw [← hσ]
  rfl

/-- A section `t` of `𝒪_X(D)` over `U` is `ψ(t) ψ⁻¹(1)`. -/
theorem toK_trivApply_mul {D : X.CartierDivisor} {U : X.Opens}
    (ψ : D.sheaf.over U ≅ SheafOfModules.unit _) (t : D.sheaf.val.obj (op U)) :
    X.toK U (trivApply ψ t) * trivGen ψ = (show X.totalQuotientSheaf.obj.obj (op U) from t.1) := by
  have h1 := inv_app_val ψ U le_rfl (trivApply ψ t)
  rw [kMap_id] at h1
  rw [← h1]
  have := congrArg Subtype.val (ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.val.app (op (Over.mk (𝟙 U)))) ψ.hom_inv_id) t)
  exact this

/-- A section of `K_X` which is locally a unit is a unit. -/
theorem isUnit_of_locally {U : X.Opens} (t : X.totalQuotientSheaf.obj.obj (op U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      IsUnit (X.totalQuotientSheaf.obj.map (homOfLE hVU).op t)) :
    IsUnit t := by
  choose V hVU hxV hu using fun x : U ↦ h x.1 x.2
  have cover : U ≤ ⨆ x, V x := fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV _⟩
  let w : ∀ x, ToType (X.totalQuotientSheaf.obj.obj (op (V x))) := fun x ↦
    (((hu x).unit⁻¹ : (X.totalQuotientSheaf.obj.obj (op (V x)))ˣ) :
      X.totalQuotientSheaf.obj.obj (op (V x)))
  have compat : TopCat.Presheaf.IsCompatible X.totalQuotientSheaf.obj V w := by
    intro i j
    have e1 : X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i) *
        X.totalQuotientSheaf.obj.map (homOfLE (inf_le_left.trans (hVU i))).op t = 1 := by
      rw [← kMap_map inf_le_left (hVU i), ← map_mul, (hu i).val_inv_mul, map_one]
    have e2 : X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j) *
        X.totalQuotientSheaf.obj.map (homOfLE (inf_le_right.trans (hVU j))).op t = 1 := by
      rw [← kMap_map inf_le_right (hVU j), ← map_mul, (hu j).val_inv_mul, map_one]
    exact left_inv_eq_right_inv e1 (by rw [mul_comm]; exact e2)
  obtain ⟨u, hu', -⟩ := X.totalQuotientSheaf.existsUnique_gluing' V U
    (fun i ↦ homOfLE (hVU i)) cover w compat
  refine IsUnit.of_mul_eq_one u ?_
  apply X.totalQuotientSheaf.eq_of_locally_eq' V U (fun i ↦ homOfLE (hVU i)) cover
  intro i
  rw [map_mul, map_one, hu' i]
  exact (hu i).mul_val_inv

/-- **A trivialization of `𝒪_X(D)` over `U` is multiplication by the inverse of a local equation
of `D`**: the generator `ψ⁻¹(1)` is a unit `g` of `K_X(U)` and `g⁻¹` is a local equation of `D`
on `U`. -/
theorem exists_restrict_eq_trivGen {D : X.CartierDivisor} {U : X.Opens}
    (ψ : D.sheaf.over U ≅ SheafOfModules.unit _) :
    ∃ g : X.totalQuotientUnitsSheaf.obj.obj (op U), kUnitVal g = trivGen ψ ∧
      D.restrict U = X.toCartierDivisorSheaf.hom.app (op U)
        (Additive.ofMul (g⁻¹ : X.totalQuotientUnitsSheaf.obj.obj (op U))) := by
  -- locally, `trivGen ψ` differs from the inverse of a local equation by a regular unit
  have hloc : ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U) (f : X.totalQuotientUnitsSheaf.obj.obj (op V)),
      x ∈ V ∧ D.restrict V = X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul f) ∧
      ∃ a b : Γ(X, V), a * b = 1 ∧
        X.toK V a = X.totalQuotientSheaf.obj.map (homOfLE hVU).op (trivGen ψ) * kUnitVal f := by
    intro x hx
    obtain ⟨W, f, hxW, hf⟩ := D.exists_localEquation x
    have h₁ : U ⊓ W ≤ U := inf_le_left
    have h₂ : U ⊓ W ≤ W := inf_le_right
    have hf' := D.restrict_eq_of_le h₂ hf
    set f' := X.totalQuotientUnitsSheaf.obj.map (homOfLE h₂).op f
    obtain ⟨a, ha⟩ := trivGen_isSection ψ (U ⊓ W) h₁ f' hf'
    let t : D.sheaf.val.obj (op (U ⊓ W)) :=
      ⟨X.totalQuotientSheaf.obj.map (homOfLE le_rfl).op (kUnitVal f'⁻¹),
        D.isSection_inv hf' le_rfl⟩
    let b : Γ(X, U ⊓ W) := ψ.hom.val.app (op (Over.mk (homOfLE h₁))) t
    have hb : X.toK _ b * X.totalQuotientSheaf.obj.map (homOfLE h₁).op (trivGen ψ) =
        kUnitVal f'⁻¹ := by
      rw [← inv_app_val ψ _ h₁ b]
      have := congrArg Subtype.val (ConcreteCategory.congr_hom
        (congrArg (fun φ ↦ φ.val.app (op (Over.mk (homOfLE h₁)))) ψ.hom_inv_id) t)
      refine this.trans ?_
      exact kMap_id _
    refine ⟨U ⊓ W, h₁, f', ⟨hx, hxW⟩, hf', a, b, ?_, ha⟩
    apply X.toK_injective
    rw [map_mul, map_one, ha, mul_comm, ← mul_assoc, hb,
      show kUnitVal f'⁻¹ * kUnitVal f' = 1 from Units.inv_mul _]
  have hunit : IsUnit (trivGen ψ) := by
    refine isUnit_of_locally _ fun x hx ↦ ?_
    obtain ⟨V, hVU, f, hxV, -, a, b, hab, ha⟩ := hloc x hx
    refine ⟨V, hVU, hxV, ?_⟩
    have : X.totalQuotientSheaf.obj.map (homOfLE hVU).op (trivGen ψ) =
        X.toK V a * kUnitVal f⁻¹ := by
      rw [ha, mul_assoc, show kUnitVal f * kUnitVal f⁻¹ = 1 from Units.mul_inv _, mul_one]
    rw [this]
    exact (IsUnit.of_mul_eq_one (X.toK V b) (by rw [← map_mul, hab, map_one])).mul
      (Units.isUnit (show (X.totalQuotientSheaf.obj.obj (op V))ˣ from f⁻¹))
  let g : X.totalQuotientUnitsSheaf.obj.obj (op U) :=
    (show (X.totalQuotientSheaf.obj.obj (op U))ˣ from hunit.unit)
  refine ⟨g, hunit.unit_spec, ?_⟩
  choose V hVU f hxV hf a b hab ha using fun x : U ↦ hloc x.1 x.2
  apply X.cartierDivisorSheaf.eq_of_locally_eq' V U (fun i ↦ homOfLE (hVU i))
    (fun x hx ↦ Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV _⟩)
  intro i
  change X.cartierDivisorSheaf.obj.map (homOfLE (hVU i)).op (D.restrict U) =
    X.cartierDivisorSheaf.obj.map (homOfLE (hVU i)).op
      (X.toCartierDivisorSheaf.hom.app (op U)
        (Additive.ofMul (g⁻¹ : X.totalQuotientUnitsSheaf.obj.obj (op U))))
  rw [D.restrict_restrict, hf i, toCartierDivisorSheaf_naturality_apply]
  refine (X.toCartierDivisorSheaf_apply_eq_iff_ratio _ _ _).2
    ⟨(show Γ(X, V i)ˣ from ⟨a i, b i, hab i, by rw [mul_comm, hab i]⟩), Units.ext ?_⟩
  change X.toK _ (a i) = kUnitVal (f i) * kUnitVal (X.totalQuotientUnitsSheaf.obj.map
    (homOfLE (hVU i)).op g⁻¹)⁻¹
  rw [ha i, mul_comm, map_inv, inv_inv]
  rfl

/-- The restriction of a global section of an `𝒪_X`-module to an open `U`. -/
abbrev resTop (L : X.Modules) (U : X.Opens) (s : L.val.obj (op ⊤)) : L.val.obj (op U) :=
  L.val.map (homOfLE le_top).op s

/-- **The divisor of zeros** (Hartshorne II.7, p.157). `D` is the divisor of zeros `(s)₀` of the
global section `s` of `L` if over every open `U` with a trivialization `ψ : L|_U ≅ 𝒪_U`, the
regular function `ψ(s)` is a local equation of `D`. -/
def IsDivisorOfZeros (L : X.Modules) (s : L.val.obj (op ⊤)) (D : X.CartierDivisor) : Prop :=
  ∀ (U : X.Opens) (ψ : L.over U ≅ SheafOfModules.unit _),
    ∃ f : X.totalQuotientUnitsSheaf.obj.obj (op U),
      X.toK U (trivApply ψ (resTop L U s)) = kUnitVal f ∧
        D.restrict U = X.toCartierDivisorSheaf.hom.app (op U) (Additive.ofMul f)

/-- A module isomorphic to `𝒪_X(D)` is trivial near every point. -/
theorem exists_trivialization {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf)
    (x : X) : ∃ U : X.Opens, x ∈ U ∧ Nonempty (L.over U ≅ SheafOfModules.unit _) := by
  obtain ⟨V, f, hx, hf⟩ := D₀.exists_localEquation x
  exact ⟨V, hx, ⟨(SheafOfModules.overFunctor _ V).mapIso φ ≪≫ D₀.overIsoFree hf ≪≫
    coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit _)⟩⟩

/-- The divisor of zeros of a section is unique. -/
theorem IsDivisorOfZeros.unique {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf)
    {s : L.val.obj (op ⊤)} {D D' : X.CartierDivisor} (hD : IsDivisorOfZeros L s D)
    (hD' : IsDivisorOfZeros L s D') : D = D' := by
  have hloc : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ D.restrict U = D'.restrict U := by
    intro x
    obtain ⟨U, hx, ⟨ψ⟩⟩ := exists_trivialization φ x
    obtain ⟨f, hf, hDU⟩ := hD U ψ
    obtain ⟨f', hf', hD'U⟩ := hD' U ψ
    have : f = f' := Units.ext (hf.symm.trans hf')
    exact ⟨U, hx, by rw [hDU, hD'U, this]⟩
  choose W hxW hW using hloc
  exact X.cartierDivisorSheaf.eq_of_locally_eq' W ⊤ (fun _ ↦ homOfLE le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxW x⟩) D D' hW

/-- A divisor of zeros is effective. -/
theorem IsDivisorOfZeros.isEffective {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf)
    {s : L.val.obj (op ⊤)} {D : X.CartierDivisor} (hD : IsDivisorOfZeros L s D) :
    D.IsEffective := by
  intro x
  obtain ⟨U, hx, ⟨ψ⟩⟩ := exists_trivialization φ x
  obtain ⟨f, hf, hDU⟩ := hD U ψ
  exact ⟨U, f, hx, hDU, _, hf⟩

/-- The section of `K_X` underlying a global section of `L ≅ 𝒪_X(D₀)`. -/
def sectionToK {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf)
    (s : L.val.obj (op ⊤)) : X.totalQuotientSheaf.obj.obj (op ⊤) :=
  (φ.hom.val.app (op ⊤) s).1

set_option backward.isDefEq.respectTransparency false in
/-- If the section `s` of `L ≅ 𝒪_X(D₀)` is a unit `u` of `K_X`, its divisor of zeros is
`D₀ + div u`. -/
theorem isDivisorOfZeros_add_principal {L : X.Modules} {D₀ : X.CartierDivisor}
    (φ : L ≅ D₀.sheaf) (s : L.val.obj (op ⊤)) (u : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))
    (hu : kUnitVal u = sectionToK φ s) :
    IsDivisorOfZeros L s (D₀ + X.principalCartierDivisor u) := by
  intro U ψ'
  let ψ : D₀.sheaf.over U ≅ SheafOfModules.unit _ :=
    ((SheafOfModules.overFunctor _ U).mapIso φ).symm ≪≫ ψ'
  obtain ⟨g, hg, hD₀⟩ := exists_restrict_eq_trivGen ψ
  have key := toK_trivApply_mul ψ (φ.hom.val.app (op U) (resTop L U s))
  have h1 : trivApply ψ (φ.hom.val.app (op U) (resTop L U s)) = trivApply ψ' (resTop L U s) := by
    change ψ'.hom.val.app (op (Over.mk (𝟙 U)))
      (φ.inv.val.app (op U) (φ.hom.val.app (op U) (resTop L U s))) =
        ψ'.hom.val.app (op (Over.mk (𝟙 U))) (resTop L U s)
    congr 1
    exact ConcreteCategory.congr_hom
      (congrArg (fun α ↦ α.val.app (op U)) φ.hom_inv_id) _
  have h2 : (show X.totalQuotientSheaf.obj.obj (op U) from
      (φ.hom.val.app (op U) (resTop L U s)).1) =
      X.totalQuotientSheaf.obj.map (homOfLE le_top).op (sectionToK φ s) := by
    have := ConcreteCategory.congr_hom (φ.hom.val.naturality (homOfLE (le_top : U ≤ ⊤)).op) s
    exact congrArg Subtype.val this
  rw [h1, h2, ← hu, ← hg] at key
  set u' := X.totalQuotientUnitsSheaf.obj.map (homOfLE (le_top : U ≤ ⊤)).op u
  have key' : X.toK U (trivApply ψ' (resTop L U s)) * kUnitVal g = kUnitVal u' := key
  refine ⟨u' * g⁻¹, ?_, ?_⟩
  · change _ = kUnitVal u' * kUnitVal g⁻¹
    rw [← key', mul_assoc, show kUnitVal g * kUnitVal g⁻¹ = 1 from Units.mul_inv _, mul_one]
  · change X.cartierDivisorSheaf.obj.map (homOfLE le_top).op (D₀ + X.principalCartierDivisor u) = _
    rw [map_add]
    change D₀.restrict U + X.cartierDivisorSheaf.obj.map (homOfLE le_top).op
      (X.toCartierDivisorSheaf.hom.app (op ⊤) (Additive.ofMul u)) = _
    rw [hD₀, toCartierDivisorSheaf_naturality_apply]
    change _ = X.toCartierDivisorSheaf.hom.app (op U)
      (Additive.ofMul u' + Additive.ofMul (g⁻¹ : X.totalQuotientUnitsSheaf.obj.obj (op U)))
    rw [map_add, add_comm]
    rfl

/-- A morphism `φ : L ≅ 𝒪_X(D₀)` is injective on global sections, through `K_X`. -/
theorem sectionToK_injective {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf) :
    Function.Injective (sectionToK φ) := by
  intro s t h
  have h' : φ.hom.val.app (op ⊤) s = φ.hom.val.app (op ⊤) t := Subtype.ext h
  have hinv := fun x ↦ ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.val.app (op ⊤)) φ.hom_inv_id) x
  exact (hinv s).symm.trans ((congrArg (φ.inv.val.app (op ⊤)) h').trans (hinv t))

/-- The zero section goes to zero in `K_X`. -/
theorem sectionToK_zero {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf) :
    sectionToK φ 0 = 0 := by
  unfold sectionToK
  rw [map_zero]
  rfl

/-- Scalars act on `K_X` through `𝒪_X → K_X`. -/
theorem sectionToK_smul {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf)
    (c : X.ringCatSheaf.obj.obj (op ⊤)) (s : L.val.obj (op ⊤)) :
    sectionToK φ (c • s) = X.toK ⊤ c * sectionToK φ s := by
  unfold sectionToK
  rw [map_smul]
  rfl

/-- Every section of `𝒪_X(D₀)` comes from `L ≅ 𝒪_X(D₀)`. -/
theorem sectionToK_inv {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf)
    (t : D₀.sheaf.val.obj (op ⊤)) :
    sectionToK φ (φ.inv.val.app (op ⊤) t) = (show X.totalQuotientSheaf.obj.obj (op ⊤) from t.1) :=
  congrArg Subtype.val (ConcreteCategory.congr_hom
    (congrArg (fun α ↦ α.val.app (op ⊤)) φ.inv_hom_id) t)

/-- On an integral scheme, a nonzero section of `K_X` over an open containing the generic point
is a unit. -/
theorem isUnit_totalQuotient_of_ne_zero [IsIntegral X] {U : X.Opens} (hU : genericPoint X ∈ U)
    {t : X.totalQuotientSheaf.obj.obj (op U)} (ht : t ≠ 0) : IsUnit t := by
  set e := totalQuotientSheafEquivFunctionField U hU
  have he : e t ≠ 0 := (map_ne_zero_iff e e.injective).mpr ht
  have h := (isUnit_iff_ne_zero.mpr he).map e.symm
  rwa [RingEquiv.symm_apply_apply] at h

/-- On an integral scheme, `K_X(X)` is a nonzero ring. -/
theorem nontrivial_totalQuotient_top [IsIntegral X] :
    Nontrivial (X.totalQuotientSheaf.obj.obj (op ⊤)) :=
  (totalQuotientSheafEquivFunctionField (X := X) ⊤ trivial).symm.injective.nontrivial

/-- **Hartshorne II, Proposition 7.7(a)**, for any integral scheme (Hartshorne: a nonsingular
projective variety over an algebraically closed field). A nonzero global section `s` of
`L ≅ 𝒪_X(D₀)` has a divisor of zeros, which is effective and linearly equivalent to `D₀`. -/
theorem exists_isDivisorOfZeros [IsIntegral X] {L : X.Modules} {D₀ : X.CartierDivisor}
    (φ : L ≅ D₀.sheaf) {s : L.val.obj (op ⊤)} (hs : s ≠ 0) :
    ∃ D : X.CartierDivisor, IsDivisorOfZeros L s D ∧ D.IsEffective ∧ D.LinearEquivalent D₀ := by
  have hσ : sectionToK φ s ≠ 0 := fun h ↦
    hs (sectionToK_injective φ (h.trans (sectionToK_zero φ).symm))
  have hu := isUnit_totalQuotient_of_ne_zero (U := ⊤) trivial hσ
  let u : X.totalQuotientUnitsSheaf.obj.obj (op ⊤) :=
    (show (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ from hu.unit)
  have hD := isDivisorOfZeros_add_principal φ s u hu.unit_spec
  refine ⟨_, hD, hD.isEffective φ, Additive.ofMul u, ?_⟩
  change X.principalCartierDivisor u = D₀ + X.principalCartierDivisor u - D₀
  rw [add_sub_cancel_left]

set_option backward.isDefEq.respectTransparency false in
/-- `D₀ + div h` has local equations `h f` where `f` are local equations of `D₀`. -/
theorem restrict_add_principal (D₀ : X.CartierDivisor)
    (h : X.totalQuotientUnitsSheaf.obj.obj (op ⊤)) {V : X.Opens}
    {f : X.totalQuotientUnitsSheaf.obj.obj (op V)}
    (hf : D₀.restrict V = X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul f)) :
    (D₀ + X.principalCartierDivisor h).restrict V =
      X.toCartierDivisorSheaf.hom.app (op V) (Additive.ofMul
        (X.totalQuotientUnitsSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op h * f)) := by
  change X.cartierDivisorSheaf.obj.map (homOfLE le_top).op (D₀ + X.principalCartierDivisor h) = _
  rw [map_add]
  change D₀.restrict V + X.cartierDivisorSheaf.obj.map (homOfLE le_top).op
    (X.toCartierDivisorSheaf.hom.app (op ⊤) (Additive.ofMul h)) = _
  rw [hf, toCartierDivisorSheaf_naturality_apply]
  change _ = X.toCartierDivisorSheaf.hom.app (op V)
    (Additive.ofMul (X.totalQuotientUnitsSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op h) +
      Additive.ofMul f)
  rw [map_add, add_comm]
  rfl

/-- If `D₀ + div h` is effective, then `h` is a global section of `𝒪_X(D₀)`. -/
theorem isSection_of_isEffective_add_principal (D₀ : X.CartierDivisor)
    (h : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))
    (hD : (D₀ + X.principalCartierDivisor h).IsEffective) : D₀.IsSection (kUnitVal h) := by
  intro V hV f hf
  apply exists_toK_eq_of_locally
  intro x hx
  obtain ⟨W, fW, hxW, hDW, gW, hgW⟩ := hD x
  have h₁ : V ⊓ W ≤ V := inf_le_left
  have h₂ : V ⊓ W ≤ W := inf_le_right
  have e₁ := (D₀ + X.principalCartierDivisor h).restrict_eq_of_le h₁ (restrict_add_principal D₀ h hf)
  have e₂ := (D₀ + X.principalCartierDivisor h).restrict_eq_of_le h₂ hDW
  obtain ⟨a, ha⟩ := (D₀ + X.principalCartierDivisor h).exists_eq_mul_of_restrict_eq e₂ e₁
  refine ⟨V ⊓ W, h₁, ⟨hx, hxW⟩, a * X.presheaf.map (homOfLE h₂).op gW, ?_⟩
  rw [map_mul, ← toK_naturality, hgW]
  exact Eq.trans rfl ha.symm

/-- **Hartshorne II, Proposition 7.7(b)**, for any integral scheme (Hartshorne: a nonsingular
projective variety over an algebraically closed field). Every effective divisor linearly
equivalent to `D₀` is the divisor of zeros of a nonzero global section of `L ≅ 𝒪_X(D₀)`. -/
theorem exists_section_isDivisorOfZeros [IsIntegral X] {L : X.Modules} {D₀ : X.CartierDivisor}
    (φ : L ≅ D₀.sheaf) {D : X.CartierDivisor} (hD : D.IsEffective) (hlin : D.LinearEquivalent D₀) :
    ∃ s : L.val.obj (op ⊤), s ≠ 0 ∧ IsDivisorOfZeros L s D := by
  obtain ⟨h', hh'⟩ := hlin
  set h : X.totalQuotientUnitsSheaf.obj.obj (op ⊤) := h'.toMul
  have hDeq : D = D₀ + X.principalCartierDivisor h := by
    rw [← sub_eq_iff_eq_add']
    exact hh'.symm
  have hsec := isSection_of_isEffective_add_principal D₀ h (hDeq ▸ hD)
  let t : D₀.sheaf.val.obj (op ⊤) := ⟨kUnitVal h, hsec⟩
  have ht := sectionToK_inv φ t
  have := nontrivial_totalQuotient_top (X := X)
  refine ⟨φ.inv.val.app (op ⊤) t, fun h0 ↦ ?_, hDeq ▸ isDivisorOfZeros_add_principal φ _ h ht.symm⟩
  rw [h0, sectionToK_zero] at ht
  exact (Units.ne_zero (show (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ from h)) ht.symm

end Scheme.CartierDivisor

namespace Scheme

variable {k : Type u} [Field k]

/-- The structure map `k → Γ(X, 𝒪_X)` of a scheme over `k`. -/
def globalScalar (p : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom

/-- For an integral scheme universally closed over an algebraically closed field `k` (e.g. a
projective variety), the global regular functions are exactly the constants `k`. -/
theorem globalScalar_bijective [IsAlgClosed k] [IsIntegral X] (p : X ⟶ Spec (.of k))
    [UniversallyClosed p] : Function.Bijective (globalScalar p) := by
  refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
  apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed p

end Scheme

namespace Scheme.CartierDivisor

variable {k : Type u} [Field k]

/-- **Hartshorne II, Proposition 7.7(c)**, for an integral scheme universally closed over an
algebraically closed field `k` (e.g. a projective variety), two nonzero global sections of
`L ≅ 𝒪_X(D₀)` have the same divisor of zeros if and only if they differ by a nonzero scalar in
`k`. -/
theorem isDivisorOfZeros_eq_iff [IsAlgClosed k] [IsIntegral X] (p : X ⟶ Spec (.of k))
    [UniversallyClosed p] {L : X.Modules} {D₀ : X.CartierDivisor} (φ : L ≅ D₀.sheaf)
    {s s' : L.val.obj (op ⊤)} (hs : s ≠ 0) (hs' : s' ≠ 0) {D D' : X.CartierDivisor}
    (hD : IsDivisorOfZeros L s D) (hD' : IsDivisorOfZeros L s' D') :
    D = D' ↔ ∃ c : kˣ, s' = (show X.ringCatSheaf.obj.obj (op ⊤) from globalScalar p c) • s := by
  have hσ : sectionToK φ s ≠ 0 := fun h ↦
    hs (sectionToK_injective φ (h.trans (sectionToK_zero φ).symm))
  have hσ' : sectionToK φ s' ≠ 0 := fun h ↦
    hs' (sectionToK_injective φ (h.trans (sectionToK_zero φ).symm))
  have hu := isUnit_totalQuotient_of_ne_zero (U := ⊤) trivial hσ
  have hu' := isUnit_totalQuotient_of_ne_zero (U := ⊤) trivial hσ'
  let u : X.totalQuotientUnitsSheaf.obj.obj (op ⊤) :=
    (show (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ from hu.unit)
  let u' : X.totalQuotientUnitsSheaf.obj.obj (op ⊤) :=
    (show (X.totalQuotientSheaf.obj.obj (op ⊤))ˣ from hu'.unit)
  have huv : kUnitVal u = sectionToK φ s := hu.unit_spec
  have huv' : kUnitVal u' = sectionToK φ s' := hu'.unit_spec
  rw [hD.unique φ (isDivisorOfZeros_add_principal φ s u huv),
    hD'.unique φ (isDivisorOfZeros_add_principal φ s' u' huv'), add_right_inj]
  change X.toCartierDivisorSheaf.hom.app (op ⊤) (Additive.ofMul u) =
    X.toCartierDivisorSheaf.hom.app (op ⊤) (Additive.ofMul u') ↔ _
  rw [eq_comm, toCartierDivisorSheaf_apply_eq_iff_ratio]
  constructor
  · rintro ⟨a, ha⟩
    have hval : sectionToK φ s' = X.toK ⊤ (oUnitVal a) * sectionToK φ s := by
      have := congrArg (fun v : X.totalQuotientUnitsSheaf.obj.obj (op ⊤) ↦ kUnitVal v) ha
      change X.toK ⊤ (oUnitVal a) = kUnitVal u' * kUnitVal u⁻¹ at this
      rw [this, ← huv, ← huv', mul_assoc, show kUnitVal u⁻¹ * kUnitVal u = 1 from Units.inv_mul _,
        mul_one]
    obtain ⟨c, hc⟩ := (Scheme.globalScalar_bijective p).2 (oUnitVal a)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      have := nontrivial_totalQuotient_top (X := X)
      have h0 : X.toK ⊤ (oUnitVal a) = 0 := by rw [← hc, map_zero]
      rw [h0, zero_mul] at hval
      exact hσ' hval
    refine ⟨Units.mk0 c hc0, sectionToK_injective φ ?_⟩
    rw [sectionToK_smul, hval]
    change _ = X.toK ⊤ (globalScalar p c) * _
    rw [hc]
  · rintro ⟨c, rfl⟩
    have hc : IsUnit (globalScalar p c) := (Units.isUnit c).map _
    refine ⟨(show Γ(X, ⊤)ˣ from hc.unit), Units.ext ?_⟩
    change X.toK ⊤ (globalScalar p c) = kUnitVal u' * kUnitVal u⁻¹
    rw [huv', sectionToK_smul, ← huv, mul_assoc,
      show kUnitVal u * kUnitVal u⁻¹ = 1 from Units.mul_inv _, mul_one]

/-- The order of vanishing of a nonzero regular function is nonnegative. -/
theorem ord_germToFunctionField_nonneg [IsIntegral X] [IsNoetherian X] {U : X.Opens}
    [Nonempty U] {a : Γ(X, U)} (ha : a ≠ 0) {x : X} (hx : x ∈ U) :
    0 ≤ X.ord (X.germToFunctionField U a) x := by
  have h1 : X.ord (1 : X.functionField) x = 0 := by
    have h := X.ord_mul (x := x) (one_ne_zero (α := X.functionField)) one_ne_zero
    rw [mul_one] at h
    omega
  have := X.ord_le_smul hx ha (1 : X.functionField)
  rw [h1, Algebra.smul_def, mul_one] at this
  exact this

/-- The Weil divisor of an effective Cartier divisor is effective. -/
theorem isEffective_cartierToWeil [IsIntegral X] [IsNoetherian X] {D : X.CartierDivisor}
    (hD : D.IsEffective) : WeilDivisor.IsEffective (cartierToWeil D) := by
  intro x
  obtain ⟨V, f, hxV, hf, g, hg⟩ := hD x
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hη := genericPoint_mem_opens_of_mem hxV
  rw [cartierToWeil_apply D f hf hxV]
  change 0 ≤ X.ord (totalQuotientSheafEquivFunctionField V hη (kUnitVal f)) x
  have hgerm : totalQuotientSheafEquivFunctionField V hη (X.toK V g) =
      X.germToFunctionField V g :=
    totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf V hη g
  rw [← hg, hgerm]
  refine ord_germToFunctionField_nonneg (fun h0 ↦ ?_) hxV
  have : Nontrivial (X.totalQuotientSheaf.obj.obj (op V)) :=
    (totalQuotientSheafEquivFunctionField (X := X) V hη).symm.injective.nontrivial
  apply Units.ne_zero (show (X.totalQuotientSheaf.obj.obj (op V))ˣ from f)
  change kUnitVal f = 0
  rw [← hg, h0, map_zero]

/-- On a normal scheme, a Cartier divisor whose Weil divisor is effective is effective. -/
theorem isEffective_of_isEffective_cartierToWeil [IsIntegral X] [IsNoetherian X]
    [Hartshorne.IsNormal X] {D : X.CartierDivisor}
    (hD : WeilDivisor.IsEffective (cartierToWeil D)) :
    D.IsEffective := by
  intro x
  obtain ⟨V, f, hxV, hf⟩ := D.exists_localEquation x
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hη := genericPoint_mem_opens_of_mem hxV
  set e := totalQuotientSheafEquivFunctionField V hη
  have hk : e (kUnitVal f) ≠ 0 :=
    ((Units.isUnit (show (X.totalQuotientSheaf.obj.obj (op V))ˣ from f)).map e).ne_zero
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_ord_nonneg_of_opens (W := V) hk
    fun y hy _ ↦ by
      have := hD y
      rw [cartierToWeil_apply D f hf hy] at this
      exact this
  refine ⟨V, f, hxV, hf, a, e.injective ?_⟩
  exact (totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf V hη a).trans ha

end Scheme.CartierDivisor

namespace Scheme

variable [IsIntegral X] [IsNoetherian X] [X.IsSeparated]

/-- Under `weilCartierEquiv`, a Weil divisor is effective iff the Cartier divisor is. -/
theorem isEffective_weilCartierEquiv_iff (hlf : X.IsLocallyFactorial) (D : X.WeilDivisor) :
    (weilCartierEquiv hlf D).IsEffective ↔ WeilDivisor.IsEffective D := by
  have := isNormal_of_isLocallyFactorial hlf
  have hD : D = cartierToWeil (weilCartierEquiv hlf D) := by
    rw [← weilCartierEquiv_symm_apply hlf, AddEquiv.symm_apply_apply]
  constructor
  · intro h
    rw [hD]
    exact CartierDivisor.isEffective_cartierToWeil h
  · intro h
    rw [hD] at h
    exact CartierDivisor.isEffective_of_isEffective_cartierToWeil h

/-- Under `weilCartierEquiv`, linear equivalence of Weil divisors is linear equivalence of Cartier
divisors. -/
theorem linearEquivalent_weilCartierEquiv_iff (hlf : X.IsLocallyFactorial)
    (D E : X.WeilDivisor) :
    (weilCartierEquiv hlf D).LinearEquivalent (weilCartierEquiv hlf E) ↔
      WeilDivisor.LinearEquivalent (satisfiesConditionStar_of_isLocallyFactorial hlf) D E := by
  change weilCartierEquiv hlf D - weilCartierEquiv hlf E ∈ X.principalCartierDivisorSubgroup ↔
    D - E ∈ X.principalDivisorSubgroup (satisfiesConditionStar_of_isLocallyFactorial hlf)
  rw [← map_sub, ← map_principalDivisorSubgroup_weilCartierEquiv hlf, AddSubgroup.mem_map_equiv,
    AddEquiv.symm_apply_apply]

/-- **Hartshorne II, Proposition 7.7, for Weil divisors.** Let `X` be an integral separated
Noetherian locally factorial scheme (e.g. a nonsingular projective variety), `D₀` a Weil divisor
and `L ≅ 𝒪_X(D₀)`. (a) A nonzero global section of `L` has a divisor of zeros, which is effective
and linearly equivalent to `D₀`; (b) every effective divisor linearly equivalent to `D₀` is the
divisor of zeros of a nonzero global section. Divisors of zeros are Cartier divisors, identified
with Weil divisors by `weilCartierEquiv`. -/
theorem weil_isDivisorOfZeros (hlf : X.IsLocallyFactorial) {D₀ : X.WeilDivisor} {L : X.Modules}
    (φ : L ≅ (weilCartierEquiv hlf D₀).sheaf) :
    (∀ s : L.val.obj (op ⊤), s ≠ 0 → ∃ D : X.WeilDivisor,
      CartierDivisor.IsDivisorOfZeros L s (weilCartierEquiv hlf D) ∧ WeilDivisor.IsEffective D ∧
        WeilDivisor.LinearEquivalent (satisfiesConditionStar_of_isLocallyFactorial hlf) D D₀) ∧
    (∀ D : X.WeilDivisor, WeilDivisor.IsEffective D →
      WeilDivisor.LinearEquivalent (satisfiesConditionStar_of_isLocallyFactorial hlf) D D₀ →
        ∃ s : L.val.obj (op ⊤), s ≠ 0 ∧
          CartierDivisor.IsDivisorOfZeros L s (weilCartierEquiv hlf D)) := by
  refine ⟨fun s hs ↦ ?_, fun D hD hlin ↦ ?_⟩
  · obtain ⟨E, hE, hEeff, hElin⟩ := CartierDivisor.exists_isDivisorOfZeros φ hs
    refine ⟨(weilCartierEquiv hlf).symm E, ?_, ?_, ?_⟩
    · rwa [AddEquiv.apply_symm_apply]
    · rwa [← isEffective_weilCartierEquiv_iff hlf, AddEquiv.apply_symm_apply]
    · rwa [← linearEquivalent_weilCartierEquiv_iff hlf, AddEquiv.apply_symm_apply]
  · exact CartierDivisor.exists_section_isDivisorOfZeros φ
      ((isEffective_weilCartierEquiv_iff hlf D).2 hD)
      ((linearEquivalent_weilCartierEquiv_iff hlf D D₀).2 hlin)

/-- **Hartshorne II, Proposition 7.7(c), for Weil divisors.** If moreover `X` is universally
closed over an algebraically closed field `k` (e.g. a nonsingular projective variety), two nonzero
global sections of `L ≅ 𝒪_X(D₀)` have the same divisor of zeros if and only if they differ by a
nonzero scalar in `k`. -/
theorem weil_isDivisorOfZeros_eq_iff {k : Type u} [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k)) [UniversallyClosed p] (hlf : X.IsLocallyFactorial)
    {D₀ : X.WeilDivisor} {L : X.Modules} (φ : L ≅ (weilCartierEquiv hlf D₀).sheaf)
    {s s' : L.val.obj (op ⊤)} (hs : s ≠ 0) (hs' : s' ≠ 0) {D D' : X.WeilDivisor}
    (hD : CartierDivisor.IsDivisorOfZeros L s (weilCartierEquiv hlf D))
    (hD' : CartierDivisor.IsDivisorOfZeros L s' (weilCartierEquiv hlf D')) :
    D = D' ↔ ∃ c : kˣ, s' = (show X.ringCatSheaf.obj.obj (op ⊤) from globalScalar p c) • s :=
  (weilCartierEquiv hlf).injective.eq_iff.symm.trans
    (CartierDivisor.isDivisorOfZeros_eq_iff p φ hs hs' hD hD')

end Scheme

end

end AlgebraicGeometry
