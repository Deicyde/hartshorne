/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.SegreProductGradedAlgebra
import Hartshorne.Scheme.ProjectiveBundleTrivialization

/-!
# The diagonal product with a free rank-one graded algebra

Supplements Hartshorne, *Algebraic Geometry*, II.7, Lemma 7.9 (p. 161). Let `S` be a graded
`A`-algebra and `T` a graded `A`-algebra which is free of rank one in every degree on the powers
of an element `t ∈ T_1` (for instance `T = Sym(M)` for a free `A`-module `M` of rank one with
basis `t`). Then `s ↦ s ⊗ t^d` (for `s ∈ S_d`) is an isomorphism of graded rings
`S ≅ S ×_A T = ⊕_d S_d ⊗_A T_d` (`Hartshorne.SegreProduct.ofGenerator`,
`Hartshorne.SegreProduct.ofGenerator_bijective`), so `Proj (S ×_A T) ≅ Proj S`
(`Hartshorne.SegreProduct.projIsoOfGenerator`).

Changing the generator `t` to `u t` for a unit `u ∈ A` composes this isomorphism with the graded
automorphism `σ_u : s ↦ u^d s` of `S` (`Hartshorne.SegreProduct.ofGenerator_smul`), which induces
the identity on `Proj S` (`Hartshorne.SegreProduct.projMap_scale`). Hence the isomorphism
`Proj (S ×_A T) ≅ Proj S` does not depend on the generator
(`Hartshorne.SegreProduct.projIsoOfGenerator_smul`).
-/

noncomputable section

open TensorProduct DirectSum CategoryTheory AlgebraicGeometry

universe u

namespace Hartshorne

namespace SegreProduct

variable {A S T : Type u} [CommRing A] [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
  {𝒮 : ℕ → AddSubgroup S} {𝒯 : ℕ → AddSubgroup T} [GradedRing 𝒮] [GradedRing 𝒯]

/-- Two ring maps out of a graded ring which agree on homogeneous elements are equal. -/
theorem ringHom_ext_of_homogeneous {R : Type*} [Semiring R] {f g : S →+* R}
    (h : ∀ d, ∀ s ∈ 𝒮 d, f s = g s) : f = g := by
  classical
  ext x
  rw [← sum_support_decompose 𝒮 x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun d _ => h d _ (decompose 𝒮 x d).2

omit [GradedRing 𝒮] in
theorem pow_mem_of_mem_one {t : T} (ht : t ∈ 𝒯 1) (d : ℕ) : t ^ d ∈ 𝒯 d := by
  simpa using SetLike.pow_mem_graded d ht

omit [GradedRing 𝒯] in
theorem smul_mem_of_mem (𝒮 : ℕ → AddSubgroup S) [GradedRing 𝒮]
    (h𝒮 : ∀ a : A, algebraMap A S a ∈ 𝒮 0) (a : A) {d : ℕ} {s : S} (hs : s ∈ 𝒮 d) :
    a • s ∈ 𝒮 d := by
  rw [Algebra.smul_def]
  simpa using SetLike.mul_mem_graded (h𝒮 a) hs

variable (𝒮 𝒯) (h𝒮 : ∀ a : A, algebraMap A S a ∈ 𝒮 0) (h𝒯 : ∀ a : A, algebraMap A T a ∈ 𝒯 0)
  {t : T} (ht : t ∈ 𝒯 1)

variable (A) in
/-- The additive map `S_d → S ×_A T`, `s ↦ s ⊗ t^d`. -/
def ofGeneratorComponent (d : ℕ) : 𝒮 d →+ diagonal A 𝒮 𝒯 :=
  AddMonoidHom.mk' (fun s => ⟨(s : S) ⊗ₜ[A] (t ^ d),
      mem_diagonal_of_mem (tmul_mem_component s.2 (pow_mem_of_mem_one ht d))⟩)
    (fun x y => Subtype.ext (by simp [add_tmul]))

variable (A) in
/-- The ring map `S → S ×_A T`, `s ↦ s ⊗ t^d` for `s ∈ S_d`. -/
def ofGeneratorRingHom : S →+* diagonal A 𝒮 𝒯 :=
  (DirectSum.toSemiring (ofGeneratorComponent A 𝒮 𝒯 ht)
      (Subtype.ext (by
        change ((1 : S) ⊗ₜ[A] (t ^ 0)) = 1
        rw [pow_zero, Algebra.TensorProduct.one_def]))
      (fun {i j} x y => Subtype.ext (by
        change ((x : S) * y) ⊗ₜ[A] (t ^ (i + j)) = ((x : S) ⊗ₜ[A] (t ^ i)) * ((y : S) ⊗ₜ[A] (t ^ j))
        rw [Algebra.TensorProduct.tmul_mul_tmul, pow_add]))).comp
    (decomposeRingEquiv 𝒮).toRingHom

theorem ofGeneratorRingHom_of_mem {d : ℕ} {s : S} (hs : s ∈ 𝒮 d) :
    (ofGeneratorRingHom A 𝒮 𝒯 ht s : S ⊗[A] T) = s ⊗ₜ (t ^ d) := by
  simp [ofGeneratorRingHom, decomposeRingEquiv, decompose_of_mem 𝒮 hs, ofGeneratorComponent]

variable (A) in
/-- **The graded ring map** `S → S ×_A T`, `s ↦ s ⊗ t^d` for `s ∈ S_d`, given `t ∈ T_1`. -/
def ofGenerator : 𝒮 →+*ᵍ grading A 𝒮 𝒯 where
  __ := ofGeneratorRingHom A 𝒮 𝒯 ht
  map_mem {d s} hs := mem_grading_iff.2 (by
    rw [ofGeneratorRingHom_of_mem 𝒮 𝒯 ht hs]
    exact tmul_mem_component hs (pow_mem_of_mem_one ht d))

theorem coe_ofGenerator_of_mem {d : ℕ} {s : S} (hs : s ∈ 𝒮 d) :
    (ofGenerator A 𝒮 𝒯 ht s : S ⊗[A] T) = s ⊗ₜ (t ^ d) :=
  ofGeneratorRingHom_of_mem 𝒮 𝒯 ht hs

include h𝒮 in
theorem ofGenerator_algebraMap (a : A) :
    ofGenerator A 𝒮 𝒯 ht (algebraMap A S a) = algebraMap A (diagonal A 𝒮 𝒯) a := by
  refine Subtype.ext ?_
  rw [coe_ofGenerator_of_mem 𝒮 𝒯 ht (h𝒮 a), pow_zero]
  rfl

/-! ### Bijectivity when `T` is free on the powers of `t` -/

section Free

variable (hfree : ∀ d, ∀ x ∈ 𝒯 d, ∃! a : A, a • t ^ d = x)

/-- The coefficient of `t^d` in the degree-`d` component of an element of `T`. -/
def coeff (d : ℕ) : T →ₗ[A] A where
  toFun x := (hfree d _ (decompose 𝒯 x d).2).exists.choose
  map_add' x y := (hfree d _ (decompose 𝒯 (x + y) d).2).unique
    (hfree d _ (decompose 𝒯 (x + y) d).2).exists.choose_spec (by
      rw [add_smul, (hfree d _ (decompose 𝒯 x d).2).exists.choose_spec,
        (hfree d _ (decompose 𝒯 y d).2).exists.choose_spec, decompose_add, DirectSum.add_apply,
        AddMemClass.coe_add])
  map_smul' a x := (hfree d _ (decompose 𝒯 (a • x) d).2).unique
    (hfree d _ (decompose 𝒯 (a • x) d).2).exists.choose_spec (by
      rw [RingHom.id_apply, smul_eq_mul, mul_smul,
        (hfree d _ (decompose 𝒯 x d).2).exists.choose_spec]
      exact (projLinear 𝒯 h𝒯 d).map_smul a x |>.symm)

theorem coeff_smul_pow (d : ℕ) (x : T) :
    coeff 𝒯 h𝒯 hfree d x • t ^ d = decompose 𝒯 x d :=
  (hfree d _ (decompose 𝒯 x d).2).exists.choose_spec

include ht in
theorem coeff_pow (d : ℕ) : coeff 𝒯 h𝒯 hfree d (t ^ d) = 1 :=
  (hfree d _ (decompose 𝒯 (t ^ d) d).2).unique (coeff_smul_pow 𝒯 h𝒯 hfree d _)
    (by rw [one_smul, decompose_of_mem_same 𝒯 (pow_mem_of_mem_one ht d)])

/-- The `A`-linear map `S ⊗_A T → S`, `s ⊗ x ↦ (coefficient of t^d in x_d) • s_d`, recovering
the degree-`d` component from `s ↦ s ⊗ t^e`. -/
def extract (d : ℕ) : S ⊗[A] T →ₗ[A] S :=
  (TensorProduct.rid A S).toLinearMap ∘ₗ
    TensorProduct.map (projLinear 𝒮 h𝒮 d) (coeff 𝒯 h𝒯 hfree d)

theorem extract_ofGenerator (d : ℕ) (s : S) :
    extract 𝒮 𝒯 h𝒮 h𝒯 hfree d (ofGenerator A 𝒮 𝒯 ht s) = decompose 𝒮 s d := by
  induction s using DirectSum.Decomposition.inductionOn 𝒮 with
  | zero => simp
  | @homogeneous e x =>
    obtain ⟨x, hx⟩ := x
    rw [coe_ofGenerator_of_mem 𝒮 𝒯 ht hx]
    change coeff 𝒯 h𝒯 hfree d (t ^ e) • (decompose 𝒮 x d : S) = _
    by_cases hed : e = d
    · subst hed
      rw [coeff_pow 𝒯 h𝒯 ht, one_smul]
    · rw [decompose_of_mem_ne 𝒮 hx hed, smul_zero]
  | add x y hx hy =>
    rw [map_add, Subalgebra.coe_add, map_add, hx, hy, decompose_add, DirectSum.add_apply,
      AddMemClass.coe_add]

include h𝒮 h𝒯 hfree in
theorem ofGenerator_injective : Function.Injective (ofGenerator A 𝒮 𝒯 ht) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine (decompose 𝒮).injective (DFinsupp.ext fun d => Subtype.ext ?_)
  rw [← extract_ofGenerator 𝒮 𝒯 h𝒮 h𝒯 ht hfree, hs]
  simp

include h𝒮 hfree in
theorem exists_ofGenerator_of_mem_component {d : ℕ} {x : S ⊗[A] T}
    (hx : x ∈ component A 𝒮 𝒯 d) : ∃ s, (ofGenerator A 𝒮 𝒯 ht s : S ⊗[A] T) = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, hs, y, hy, rfl⟩ := hx
    obtain ⟨a, rfl, -⟩ := hfree d y hy
    refine ⟨a • s, ?_⟩
    rw [coe_ofGenerator_of_mem 𝒮 𝒯 ht (smul_mem_of_mem 𝒮 h𝒮 a hs), smul_tmul]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    exact ⟨s + s', by rw [map_add, Subalgebra.coe_add, hs, hs']⟩
  | smul a x _ hx =>
    obtain ⟨s, hs⟩ := hx
    refine ⟨algebraMap A S a * s, ?_⟩
    rw [map_mul, Subalgebra.coe_mul, hs, ofGenerator_algebraMap 𝒮 𝒯 h𝒮 ht,
      Subalgebra.coe_algebraMap, Algebra.smul_def]

include h𝒮 hfree in
theorem ofGenerator_surjective : Function.Surjective (ofGenerator A 𝒮 𝒯 ht) := by
  rintro ⟨x, hx⟩
  obtain ⟨s, hs⟩ := Submodule.iSup_induction _
    (motive := fun x => ∃ s, (ofGenerator A 𝒮 𝒯 ht s : S ⊗[A] T) = x) hx
    (fun _ _ hx => exists_ofGenerator_of_mem_component 𝒮 𝒯 h𝒮 ht hfree hx) ⟨0, by simp⟩
    (fun x y ⟨s, hs⟩ ⟨s', hs'⟩ => ⟨s + s', by rw [map_add, Subalgebra.coe_add, hs, hs']⟩)
  exact ⟨s, Subtype.ext hs⟩

include h𝒮 h𝒯 hfree in
theorem ofGenerator_bijective : Function.Bijective (ofGenerator A 𝒮 𝒯 ht) :=
  ⟨ofGenerator_injective 𝒮 𝒯 h𝒮 h𝒯 ht hfree, ofGenerator_surjective 𝒮 𝒯 h𝒮 ht hfree⟩

/-- **The local isomorphism** `Proj (S ×_A T) ≅ Proj S` induced by `s ↦ s ⊗ t^d`, when every
`T_d` is free on `t^d`. -/
def projIsoOfGenerator :
    letI := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
    Proj (grading A 𝒮 𝒯) ≅ Proj 𝒮 :=
  letI := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
  projIsoOfBijective (ofGenerator A 𝒮 𝒯 ht) (ofGenerator_bijective 𝒮 𝒯 h𝒮 h𝒯 ht hfree)

theorem projIsoOfGenerator_hom :
    letI := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
    ∃ h, (projIsoOfGenerator 𝒮 𝒯 h𝒮 h𝒯 ht hfree).hom = Proj.map (ofGenerator A 𝒮 𝒯 ht) h :=
  let := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
  ⟨_, projIsoOfBijective_hom _ _⟩

end Free

/-! ### Changing the generator -/

section Scale

variable (u : A)

/-- The scaling component `S_d → S`, `s ↦ u^d s`. -/
def scaleComponent (d : ℕ) : 𝒮 d →+ S :=
  AddMonoidHom.mk' (fun s => u ^ d • (s : S)) (fun x y => by simp [smul_add])

/-- The ring endomorphism `S → S`, `s ↦ u^d s` for `s ∈ S_d`. -/
def scaleRingHom : S →+* S :=
  (DirectSum.toSemiring (scaleComponent 𝒮 u)
      (by change u ^ 0 • (1 : S) = 1; rw [pow_zero, one_smul])
      (fun {i j} x y => by
        change u ^ (i + j) • ((x : S) * y) = (u ^ i • (x : S)) * (u ^ j • (y : S))
        rw [smul_mul_smul_comm, ← pow_add])).comp
    (decomposeRingEquiv 𝒮).toRingHom

theorem scaleRingHom_of_mem {d : ℕ} {s : S} (hs : s ∈ 𝒮 d) : scaleRingHom 𝒮 u s = u ^ d • s := by
  simp [scaleRingHom, decomposeRingEquiv, decompose_of_mem 𝒮 hs, scaleComponent]

/-- The graded ring endomorphism `σ_u : S → S`, `s ↦ u^d s` for `s ∈ S_d`. -/
def scale : 𝒮 →+*ᵍ 𝒮 where
  __ := scaleRingHom 𝒮 u
  map_mem {d s} hs := by
    rw [scaleRingHom_of_mem 𝒮 u hs]
    exact smul_mem_of_mem 𝒮 h𝒮 _ hs

theorem scale_of_mem {d : ℕ} {s : S} (hs : s ∈ 𝒮 d) : scale 𝒮 h𝒮 u s = u ^ d • s :=
  scaleRingHom_of_mem 𝒮 u hs

/-- **Changing the generator**: replacing `t` by `u t` composes `s ↦ s ⊗ t^d` with `σ_u`. -/
theorem ofGenerator_smul (ht' : u • t ∈ 𝒯 1) (s : S) :
    ofGenerator A 𝒮 𝒯 ht' s = ofGenerator A 𝒮 𝒯 ht (scale 𝒮 h𝒮 u s) := by
  have := ringHom_ext_of_homogeneous (𝒮 := 𝒮) (R := diagonal A 𝒮 𝒯)
    (f := (ofGenerator A 𝒮 𝒯 ht').toRingHom)
    (g := (ofGenerator A 𝒮 𝒯 ht).toRingHom.comp (scale 𝒮 h𝒮 u).toRingHom) fun d s hs => by
      refine Subtype.ext ?_
      change (ofGenerator A 𝒮 𝒯 ht' s : S ⊗[A] T) =
        (ofGenerator A 𝒮 𝒯 ht (scale 𝒮 h𝒮 u s) : S ⊗[A] T)
      rw [coe_ofGenerator_of_mem 𝒮 𝒯 ht' hs, scale_of_mem 𝒮 h𝒮 u hs,
        coe_ofGenerator_of_mem 𝒮 𝒯 ht (smul_mem_of_mem 𝒮 h𝒮 _ hs), smul_pow, smul_tmul]
  exact congr($this s)

variable {u}

theorem irrelevant_le_scale (hu : IsUnit u) :
    HomogeneousIdeal.irrelevant 𝒮 ≤ (HomogeneousIdeal.irrelevant 𝒮).map (scale 𝒮 h𝒮 u) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi s hs
  obtain ⟨v, rfl⟩ := hu
  have hs' : scale 𝒮 h𝒮 (v : A) ((↑v⁻¹ : A) ^ i • s) = s := by
    rw [scale_of_mem 𝒮 h𝒮 _ (smul_mem_of_mem 𝒮 h𝒮 _ hs), smul_smul, ← mul_pow, Units.mul_inv,
      one_pow, one_smul]
  change s ∈ ((HomogeneousIdeal.irrelevant 𝒮).map (scale 𝒮 h𝒮 (v : A))).toIdeal
  rw [← hs']
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒮 hi
    (smul_mem_of_mem 𝒮 h𝒮 _ hs))

set_option backward.isDefEq.respectTransparency false in
/-- **`σ_u` induces the identity of `Proj S`** for a unit `u`: on the chart `D₊(s)` it sends
`a / s^n` to `u^{dn} a / (u^d s)^n = a / s^n`. -/
theorem projMap_scale (hu : IsUnit u) :
    Proj.map (scale 𝒮 h𝒮 u) (irrelevant_le_scale 𝒮 h𝒮 hu) = 𝟙 (Proj 𝒮) := by
  refine (Proj.mapAffineOpenCover _ (irrelevant_le_scale 𝒮 h𝒮 hu)).openCover.hom_ext _ _
    fun s => ?_
  rw [Category.comp_id]
  change Proj.awayι 𝒮 (scale 𝒮 h𝒮 u s.2) ((scale 𝒮 h𝒮 u).map_mem s.2.2) s.1.2 ≫ _ =
    Proj.awayι 𝒮 (scale 𝒮 h𝒮 u s.2) ((scale 𝒮 h𝒮 u).map_mem s.2.2) s.1.2
  rw [Proj.awayι_comp_map _ _ s.1.2 _ s.2.2]
  have hx : scale 𝒮 h𝒮 u s.2 = s.2 * algebraMap A S (u ^ (s.1 : ℕ)) := by
    rw [scale_of_mem 𝒮 h𝒮 u s.2.2, Algebra.smul_def, mul_comm]
  rw [← Proj.SpecMap_awayMap_awayι (𝒜 := 𝒮) (f_deg := s.2.2) (hm := s.1.2)
    (g_deg := h𝒮 (u ^ (s.1 : ℕ))) (hx := hx)]
  congr 2
  ext z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒮 s.2.2 z
  simp only [CommRingCat.hom_ofHom]
  rw [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.Away.val_mk]
  erw [HomogeneousLocalization.val_awayMap_mk]
  congr 1
  rw [scale_of_mem 𝒮 h𝒮 u ha, Algebra.smul_def, ← map_pow, ← pow_mul, mul_comm]
  change a * _ = a * _
  rw [smul_eq_mul, Nat.mul_comm]

private theorem projMap_congr {B : Type u} [CommRing B] {𝒜 : ℕ → AddSubgroup S}
    {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
    {φ ψ : 𝒜 →+*ᵍ ℬ} (e : φ = ψ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map φ) (hψ : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map ψ) : Proj.map φ hφ = Proj.map ψ hψ := by
  subst e
  rfl

/-- **Independence of the generator**: for a unit `u`, the isomorphisms
`Proj (S ×_A T) ≅ Proj S` defined by the generators `t` and `u t` agree. -/
theorem projIsoOfGenerator_smul (hu : IsUnit u) (ht' : u • t ∈ 𝒯 1)
    (hfree : ∀ d, ∀ x ∈ 𝒯 d, ∃! a : A, a • t ^ d = x)
    (hfree' : ∀ d, ∀ x ∈ 𝒯 d, ∃! a : A, a • (u • t) ^ d = x) :
    projIsoOfGenerator 𝒮 𝒯 h𝒮 h𝒯 ht' hfree' = projIsoOfGenerator 𝒮 𝒯 h𝒮 h𝒯 ht hfree := by
  let := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
  refine Iso.ext ?_
  obtain ⟨h₁, e₁⟩ := projIsoOfGenerator_hom 𝒮 𝒯 h𝒮 h𝒯 ht' hfree'
  obtain ⟨h₂, e₂⟩ := projIsoOfGenerator_hom 𝒮 𝒯 h𝒮 h𝒯 ht hfree
  rw [e₁, e₂]
  have e : ofGenerator A 𝒮 𝒯 ht' = (ofGenerator A 𝒮 𝒯 ht).comp (scale 𝒮 h𝒮 u) :=
    GradedRingHom.ext (ofGenerator_smul 𝒮 𝒯 h𝒮 ht u ht')
  exact (projMap_congr e _ _).trans ((Proj.map_comp _ _ (irrelevant_le_scale 𝒮 h𝒮 hu)
    h₂).trans (by rw [projMap_scale 𝒮 h𝒮 hu, Category.comp_id]))

/-- **Independence of the generator**: any two generators `t, t'` of `T` (elements of `T_1` such
that every `T_d` is free on `t^d`, resp. `t'^d`) give the same isomorphism
`Proj (S ×_A T) ≅ Proj S`. -/
theorem projIsoOfGenerator_eq {t' : T} (ht' : t' ∈ 𝒯 1)
    (hfree : ∀ d, ∀ x ∈ 𝒯 d, ∃! a : A, a • t ^ d = x)
    (hfree' : ∀ d, ∀ x ∈ 𝒯 d, ∃! a : A, a • t' ^ d = x) :
    projIsoOfGenerator 𝒮 𝒯 h𝒮 h𝒯 ht' hfree' = projIsoOfGenerator 𝒮 𝒯 h𝒮 h𝒯 ht hfree := by
  obtain ⟨a, ha, -⟩ := hfree 1 t' ht'
  obtain ⟨b, hb, -⟩ := hfree' 1 t ht
  rw [pow_one] at ha hb
  have hba : b * a = 1 := (hfree 1 t ht).unique (by rw [pow_one, mul_smul, ha, hb])
    (by rw [pow_one, one_smul])
  subst ha
  exact projIsoOfGenerator_smul 𝒮 𝒯 h𝒮 h𝒯 ht (IsUnit.of_mul_eq_one_right b hba) ht' hfree hfree'

end Scale

/-! ### Compatibility with base change -/

section Naturality

variable {A' S' T' : Type u} [CommRing A'] [CommRing S'] [CommRing T'] [Algebra A' S']
  [Algebra A' T'] {𝒮' : ℕ → AddSubgroup S'} {𝒯' : ℕ → AddSubgroup T'} [GradedRing 𝒮']
  [GradedRing 𝒯'] (h𝒮' : ∀ a : A', algebraMap A' S' a ∈ 𝒮' 0)
  (h𝒯' : ∀ a : A', algebraMap A' T' a ∈ 𝒯' 0) (α : A →+* A') (σ : 𝒮 →+*ᵍ 𝒮') (τ : 𝒯 →+*ᵍ 𝒯')
  (hσ : ∀ a, σ (algebraMap A S a) = algebraMap A' S' (α a))
  (hτ : ∀ a, τ (algebraMap A T a) = algebraMap A' T' (α a))

variable {𝒮 𝒯} in
/-- The map of diagonal products induced by `σ`, `τ` over `α`, as a graded ring map. -/
def diagonalGradedMap : grading A 𝒮 𝒯 →+*ᵍ grading A' 𝒮' 𝒯' where
  __ := diagonalMap α σ τ hσ hτ
  map_mem hx := diagonalMap_mem_grading α σ τ hσ hτ hx

theorem diagonalMap_ofGenerator (s : S) :
    diagonalMap α σ τ hσ hτ (ofGenerator A 𝒮 𝒯 ht s) =
      ofGenerator A' 𝒮' 𝒯' (τ.map_mem ht) (σ s) := by
  have := ringHom_ext_of_homogeneous (𝒮 := 𝒮) (R := diagonal A' 𝒮' 𝒯')
    (f := (diagonalMap α σ τ hσ hτ).comp (ofGenerator A 𝒮 𝒯 ht).toRingHom)
    (g := (ofGenerator A' 𝒮' 𝒯' (τ.map_mem ht)).toRingHom.comp σ.toRingHom) fun d s hs => by
      refine Subtype.ext ?_
      change tensorMap α σ τ hσ hτ (ofGenerator A 𝒮 𝒯 ht s : S ⊗[A] T) =
        (ofGenerator A' 𝒮' 𝒯' (τ.map_mem ht) (σ s) : S' ⊗[A'] T')
      rw [coe_ofGenerator_of_mem 𝒮 𝒯 ht hs, tensorMap_tmul, map_pow]
      exact (coe_ofGenerator_of_mem 𝒮' 𝒯' (τ.map_mem ht) (σ.map_mem hs)).symm
  exact congr($this s)

/-- **Naturality of the local isomorphism**: for graded maps `σ`, `τ` over `α` with `τ t` again a
generator, the isomorphisms `Proj (S ×_A T) ≅ Proj S` and `Proj (S' ×_{A'} T') ≅ Proj S'` commute
with the induced maps of `Proj`. -/
theorem projIsoOfGenerator_naturality (hfree : ∀ d, ∀ x ∈ 𝒯 d, ∃! a : A, a • t ^ d = x)
    (hfree' : ∀ d, ∀ x ∈ 𝒯' d, ∃! a : A', a • τ t ^ d = x) :
    letI := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
    letI := gradedRing A' 𝒮' 𝒯' h𝒮' h𝒯'
    ∀ (hD : HomogeneousIdeal.irrelevant (grading A' 𝒮' 𝒯') ≤
        (HomogeneousIdeal.irrelevant (grading A 𝒮 𝒯)).map (diagonalGradedMap α σ τ hσ hτ))
      (hS : HomogeneousIdeal.irrelevant 𝒮' ≤ (HomogeneousIdeal.irrelevant 𝒮).map σ),
    Proj.map (diagonalGradedMap α σ τ hσ hτ) hD ≫ (projIsoOfGenerator 𝒮 𝒯 h𝒮 h𝒯 ht hfree).hom =
      (projIsoOfGenerator 𝒮' 𝒯' h𝒮' h𝒯' (τ.map_mem ht) hfree').hom ≫ Proj.map σ hS := by
  let := gradedRing A 𝒮 𝒯 h𝒮 h𝒯
  let := gradedRing A' 𝒮' 𝒯' h𝒮' h𝒯'
  intro hD hS
  obtain ⟨h₁, e₁⟩ := projIsoOfGenerator_hom 𝒮 𝒯 h𝒮 h𝒯 ht hfree
  obtain ⟨h₂, e₂⟩ := projIsoOfGenerator_hom 𝒮' 𝒯' h𝒮' h𝒯' (τ.map_mem ht) hfree'
  rw [e₁, e₂, ← Proj.map_comp, ← Proj.map_comp]
  exact projMap_congr (GradedRingHom.ext (diagonalMap_ofGenerator 𝒮 𝒯 ht α σ τ hσ hτ)) _ _

end Naturality

end SegreProduct

end Hartshorne
