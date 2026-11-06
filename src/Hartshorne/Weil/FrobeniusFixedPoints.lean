/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Weil.FiniteFieldFrobenius
import Hartshorne.Weil.FiniteRationalPoints

/-!
# Frobenius iterates and rational points

Hartshorne, *Algebraic Geometry*, Appendix C, §4 (p. 454).

Let `X` be a scheme over `k = 𝔽_q`, let `X̄` be its base change to the fixed algebraic closure
`𝔽̄_q`, and let `F : X̄ ⟶ X̄` be Hartshorne's `q`-power Frobenius. A geometric point of `X̄` is a
`𝔽̄_q`-point, i.e. a section of `X̄ ⟶ Spec 𝔽̄_q`. An `𝔽_{q^r}`-rational point of `X` is a morphism
`Spec 𝔽_{q^r} ⟶ X` over `Spec 𝔽_q`, where `𝔽_{q^r}` is the canonical degree-`r` subfield of
`𝔽̄_q`; composing with `Spec 𝔽̄_q ⟶ Spec 𝔽_{q^r}` gives a geometric point.

* `F ^ m` acts on geometric points by raising coordinates to their `q ^ m`-th powers.
* For `r ≥ 1`, the map from `𝔽_{q^r}`-rational points to geometric points is injective, and its
  image is exactly the set of geometric points fixed by `F ^ r`.
* Consequently, for `X` of finite type, `N_r = # Fix(F ^ r)`.

The proof uses the description of a morphism from the spectrum of a field as a point together
with an embedding of its residue field. A morphism `Spec 𝔽̄_q ⟶ X` is fixed by the `q ^ r`-power
map exactly when its residue-field embedding lands in the fixed field of `a ↦ a ^ (q ^ r)`, which is
`𝔽_{q^r}`.
-/

noncomputable section

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

universe u

open Scheme FiniteFieldFrobenius Hartshorne

namespace FiniteFieldFrobeniusFixedPoints

private theorem specToEquivOfField_apply_fromSpecResidueField {K : Type u} [Field K]
    {X : Scheme.{u}} (x : X) (ψ : X.residueField x ⟶ .of K) :
    SpecToEquivOfField K X (Spec.map ψ ≫ X.fromSpecResidueField x) = ⟨x, ψ⟩ :=
  (SpecToEquivOfField K X).apply_symm_apply ⟨x, ψ⟩

/-- A morphism from the spectrum of a field is determined by its restriction along any field
extension. -/
theorem spec_map_comp_cancel {K L : Type u} [Field K] [Field L] (f : K →+* L)
    {X : Scheme.{u}} {h₁ h₂ : Spec (.of K) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom f) ≫ h₁ = Spec.map (CommRingCat.ofHom f) ≫ h₂) :
    h₁ = h₂ := by
  obtain ⟨⟨x₁, ι₁⟩, rfl⟩ := (SpecToEquivOfField K X).symm.surjective h₁
  obtain ⟨⟨x₂, ι₂⟩, rfl⟩ := (SpecToEquivOfField K X).symm.surjective h₂
  simp only [SpecToEquivOfField_symm_apply, ← Category.assoc, ← Spec.map_comp] at h ⊢
  have h' := congrArg (SpecToEquivOfField L X) h
  rw [specToEquivOfField_apply_fromSpecResidueField,
    specToEquivOfField_apply_fromSpecResidueField] at h'
  obtain ⟨rfl, h''⟩ := Sigma.mk.inj_iff.mp h'
  have hι : ι₁ = ι₂ := by
    ext a
    exact f.injective congr($(eq_of_heq h'') a)
  rw [hι]

/-- A morphism from the spectrum of a field `Ω` which is invariant under a ring endomorphism `σ`
of `Ω` factors through the spectrum of any intermediate field containing the fixed points of
`σ`. -/
theorem exists_spec_map_comp_eq {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    (E : IntermediateField k Ω) (σ : Ω →+* Ω) (hE : ∀ a, σ a = a → a ∈ E)
    {X : Scheme.{u}} (g : Spec (.of Ω) ⟶ X)
    (hg : Spec.map (CommRingCat.ofHom σ) ≫ g = g) :
    ∃ h : Spec (.of E) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap E Ω)) ≫ h = g := by
  obtain ⟨⟨x, ι⟩, rfl⟩ := (SpecToEquivOfField Ω X).symm.surjective g
  simp only [SpecToEquivOfField_symm_apply, ← Category.assoc, ← Spec.map_comp] at hg ⊢
  have h' := congrArg (SpecToEquivOfField Ω X) hg
  rw [specToEquivOfField_apply_fromSpecResidueField,
    specToEquivOfField_apply_fromSpecResidueField] at h'
  have hι : ι ≫ CommRingCat.ofHom σ = ι := eq_of_heq (Sigma.mk.inj_iff.mp h').2
  have hmem : ∀ a, ι.hom a ∈ E := fun a ↦ hE _ congr($hι a)
  refine ⟨Spec.map (CommRingCat.ofHom (ι.hom.codRestrict E hmem)) ≫ X.fromSpecResidueField x, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end FiniteFieldFrobeniusFixedPoints

open FiniteFieldFrobeniusFixedPoints

section Tower

variable (k : Type u) [Field k] [Finite k]

private theorem finiteFieldExtensionPolynomial_ne_zero_aux (r : ℕ+) :
    finiteFieldExtensionPolynomial k r ≠ 0 := by
  let _ := Fintype.ofFinite k
  simpa [finiteFieldExtensionPolynomial, Nat.card_eq_fintype_card] using
    (FiniteField.X_pow_card_pow_sub_X_ne_zero k r.ne_zero Fintype.one_lt_card)

/-- The canonical copy of `𝔽_{q^r}` in `𝔽̄_q` consists exactly of the elements fixed by the
`q ^ r`-th power map. -/
theorem _root_.Hartshorne.mem_finiteFieldExtension_iff (r : ℕ+) (a : AlgebraicClosure k) :
    a ∈ finiteFieldExtension k r ↔ a ^ Nat.card k ^ (r : ℕ) = a := by
  obtain ⟨p, hp⟩ := CharP.exists k
  let _ : CharP k p := hp
  let _ : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  constructor
  · intro ha
    let σ : AlgebraicClosure k →+* AlgebraicClosure k :=
      iterateFrobenius (AlgebraicClosure k) p (exponent p k * r)
    have hσ (b : AlgebraicClosure k) : σ b = b ^ Nat.card k ^ (r : ℕ) := by
      rw [iterateFrobenius_def, pow_mul, pow_exponent]
    let T : IntermediateField k (AlgebraicClosure k) :=
      (σ.eqLocusField (RingHom.id _)).toIntermediateField fun c ↦ by
        rw [RingHom.mem_eqLocusField, hσ, RingHom.id_apply, ← map_pow]
        congr 1
        let _ := Fintype.ofFinite k
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card_pow _ c
    have hle : finiteFieldExtension k r ≤ T := by
      refine IntermediateField.adjoin_le_iff.mpr fun b hb ↦ ?_
      rw [mem_rootSet_of_ne (finiteFieldExtensionPolynomial_ne_zero_aux k r)] at hb
      change σ b = b
      rw [hσ]
      simpa [finiteFieldExtensionPolynomial, sub_eq_zero] using hb
    have := hle ha
    change σ a = a at this
    rwa [hσ] at this
  · intro ha
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet_of_ne (finiteFieldExtensionPolynomial_ne_zero_aux k r)]
    simp [finiteFieldExtensionPolynomial, ha]

end Tower

variable {p : ℕ} [Fact p.Prime] (k : Type u) [Field k] [Finite k] [CharP k p]

/-- The `m`-th iterate `F ^ m` of Hartshorne's `q`-power Frobenius `F : X̄ ⟶ X̄`. -/
def finiteFieldQFrobeniusIterate (X : Over (Spec (.of k))) (m : ℕ) :
    finiteFieldBaseChange k X ⟶ finiteFieldBaseChange k X :=
  (fun f ↦ f ≫ finiteFieldQFrobenius (p := p) k X)^[m] (𝟙 _)

theorem finiteFieldQFrobeniusIterate_succ (X : Over (Spec (.of k))) (m : ℕ) :
    finiteFieldQFrobeniusIterate (p := p) k X (m + 1) =
      finiteFieldQFrobeniusIterate (p := p) k X m ≫ finiteFieldQFrobenius (p := p) k X :=
  Function.iterate_succ_apply' _ m _

/-- `F ^ m` acts on geometric points by raising coordinates to their `q ^ m`-th powers. -/
theorem finiteFieldQFrobeniusIterate_point (X : Over (Spec (.of k))) {K : Type u} [Field K]
    [CharP K p] (m : ℕ) (x : Spec (.of K) ⟶ (finiteFieldBaseChange k X).left) :
    x ≫ (finiteFieldQFrobeniusIterate (p := p) k X m).left ≫ finiteFieldBaseChangeFst k X =
      Spec.map (CommRingCat.ofHom (iterateFrobenius K p (exponent p k * m))) ≫ x ≫
        finiteFieldBaseChangeFst k X := by
  induction m with
  | zero =>
    simp [finiteFieldQFrobeniusIterate]
  | succ m ih =>
    rw [finiteFieldQFrobeniusIterate_succ, Over.comp_left, Category.assoc,
      finiteFieldQFrobenius_left_fst, ← Category.assoc, ← Category.assoc, Category.assoc x, ih,
      comp_iterateAbsoluteFrobenius (p := p),
      iterateAbsoluteFrobenius_spec K (exponent p k) (iterateFrobenius K p (exponent p k))
        (fun a ↦ iterateFrobenius_def _ _ _),
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    ext a
    simp only [RingHom.comp_apply, iterateFrobenius_def, ← pow_mul, ← pow_add]
    ring_nf

/-- The geometric point of `X̄` underlying an `𝔽_{q^r}`-rational point of `X`: the composite
`Spec 𝔽̄_q ⟶ Spec 𝔽_{q^r} ⟶ X`, viewed as a `𝔽̄_q`-point of the base change. -/
def finiteFieldRationalPointToGeometricPoint (X : Over (Spec (.of k))) (r : ℕ+)
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (finiteFieldExtension k r)))) ⟶ X) :
    Over.mk (𝟙 (Spec (.of (AlgebraicClosure k)))) ⟶ finiteFieldBaseChange k X :=
  Over.homMk
    (pullback.lift
      (Spec.map (CommRingCat.ofHom (algebraMap (finiteFieldExtension k r) (AlgebraicClosure k))) ≫
        y.left) (𝟙 _) (by
          rw [Category.assoc, Over.w y, Category.id_comp]
          simp only [Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          rfl)) (pullback.lift_snd _ _ _)

theorem finiteFieldRationalPointToGeometricPoint_left_fst (X : Over (Spec (.of k))) (r : ℕ+)
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (finiteFieldExtension k r)))) ⟶ X) :
    (finiteFieldRationalPointToGeometricPoint k X r y).left ≫ finiteFieldBaseChangeFst k X =
      Spec.map (CommRingCat.ofHom (algebraMap (finiteFieldExtension k r) (AlgebraicClosure k))) ≫
        y.left :=
  pullback.lift_fst _ _ _

omit [Finite k] in
theorem finiteFieldGeometricPoint_left_hom (X : Over (Spec (.of k)))
    (x : Over.mk (𝟙 (Spec (.of (AlgebraicClosure k)))) ⟶ finiteFieldBaseChange k X) :
    x.left ≫ (finiteFieldBaseChange k X).hom = 𝟙 _ :=
  Over.w x

/-- **Frobenius iterates and rational points** (Hartshorne, Appendix C, §4, p. 454).
For every `r ≥ 1`, the canonical map from the `𝔽_{q^r}`-rational points of `X` to the geometric
points of `X̄` is injective, and its image is exactly the set of geometric points fixed by
`F ^ r`. -/
theorem finiteFieldQFrobeniusIterate_fixedPoints (X : Over (Spec (.of k))) (r : ℕ+) :
    Function.Injective (finiteFieldRationalPointToGeometricPoint k X r) ∧
      Set.range (finiteFieldRationalPointToGeometricPoint k X r) =
        {x | x ≫ finiteFieldQFrobeniusIterate (p := p) k X r = x} := by
  let E := finiteFieldExtension k r
  let σ := iterateFrobenius (AlgebraicClosure k) p (exponent p k * r)
  have hσ (b : AlgebraicClosure k) : σ b = b ^ Nat.card k ^ (r : ℕ) := by
    rw [iterateFrobenius_def, pow_mul, pow_exponent]
  have hfix (x : Over.mk (𝟙 (Spec (.of (AlgebraicClosure k)))) ⟶ finiteFieldBaseChange k X) :
      x ≫ finiteFieldQFrobeniusIterate (p := p) k X r = x ↔
        Spec.map (CommRingCat.ofHom σ) ≫ x.left ≫ finiteFieldBaseChangeFst k X =
          x.left ≫ finiteFieldBaseChangeFst k X := by
    rw [← finiteFieldQFrobeniusIterate_point]
    constructor
    · intro h
      rw [← Category.assoc, ← Over.comp_left, h]
    · intro h
      ext1
      rw [Over.comp_left]
      apply pullback.hom_ext
      · exact (Category.assoc _ _ _).trans h
      · change _ ≫ (finiteFieldBaseChange k X).hom = _ ≫ (finiteFieldBaseChange k X).hom
        rw [Category.assoc, Over.w (finiteFieldQFrobeniusIterate (p := p) k X r)]
  refine ⟨fun y₁ y₂ h ↦ ?_, ?_⟩
  · ext1
    apply spec_map_comp_cancel (algebraMap E (AlgebraicClosure k))
    rw [← finiteFieldRationalPointToGeometricPoint_left_fst,
      ← finiteFieldRationalPointToGeometricPoint_left_fst, h]
  ext x
  rw [Set.mem_ofPred_eq, hfix]
  constructor
  · rintro ⟨y, rfl⟩
    rw [finiteFieldRationalPointToGeometricPoint_left_fst, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    ext a
    rw [RingHom.comp_apply, hσ]
    exact (mem_finiteFieldExtension_iff k r _).mp a.2
  · intro hx
    obtain ⟨h, hh⟩ := exists_spec_map_comp_eq E σ
      (fun a ha ↦ (mem_finiteFieldExtension_iff k r a).mpr (by rwa [← hσ])) _ hx
    have hcond : finiteFieldBaseChangeFst k X ≫ X.hom =
        (finiteFieldBaseChange k X).hom ≫ finiteFieldClosureSpecMap k :=
      pullback.condition
    have hover : h ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
      apply spec_map_comp_cancel (algebraMap E (AlgebraicClosure k))
      rw [← Category.assoc, hh, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq, Category.assoc, hcond, ← Category.assoc,
        finiteFieldGeometricPoint_left_hom]
      exact Category.id_comp _
    refine ⟨Over.homMk h hover, ?_⟩
    ext1
    apply pullback.hom_ext
    · exact (finiteFieldRationalPointToGeometricPoint_left_fst k X r _).trans hh
    · exact (pullback.lift_snd _ _ _).trans (finiteFieldGeometricPoint_left_hom k X x).symm

/-- **`N_r = # Fix(F ^ r)`** (Hartshorne, Appendix C, §4, p. 454). For a finite-type scheme `X`
over `𝔽_q`, the number of `𝔽_{q^r}`-rational points equals the number of geometric points of `X̄`
fixed by `F ^ r`. -/
theorem pointCountSequence_eq_card_finiteFieldQFrobeniusIterate_fixedPoints
    (X : Over (Spec (.of k))) (hX : FiniteType X.hom) (r : ℕ+) :
    pointCountSequence k X.left X.hom hX r =
      Nat.card {x : Over.mk (𝟙 (Spec (.of (AlgebraicClosure k)))) ⟶ finiteFieldBaseChange k X //
        x ≫ finiteFieldQFrobeniusIterate (p := p) k X r = x} := by
  obtain ⟨hinj, hrange⟩ := finiteFieldQFrobeniusIterate_fixedPoints (p := p) k X r
  exact Nat.card_congr ((Equiv.ofInjective _ hinj).trans (Equiv.setCongr hrange))

end AlgebraicGeometry
