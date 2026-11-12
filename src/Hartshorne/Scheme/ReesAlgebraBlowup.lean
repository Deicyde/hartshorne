/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.ReesAlgebra
import Hartshorne.Scheme.RelativeProj
import Hartshorne.Scheme.ModuleIdealSheafData

noncomputable section

open CategoryTheory Polynomial AlgebraicGeometry

universe u

namespace Hartshorne

section Algebra

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)

/-- The degree-`n` part `Iⁿ tⁿ` of the Rees algebra `R[It] = ⨁ₙ Iⁿ tⁿ ⊆ R[t]`: the elements of
the Rees algebra which are monomials of degree `n`. -/
def reesGrading (n : ℕ) : AddSubgroup (reesAlgebra I) where
  carrier := {p | ∀ m, m ≠ n → (p : R[X]).coeff m = 0}
  add_mem' {p q} hp hq m hm := by
    simp [Subalgebra.coe_add, coeff_add, hp m hm, hq m hm]
  zero_mem' m _ := by simp
  neg_mem' {p} hp m hm := by
    simp [hp m hm]

variable {I} in
theorem mem_reesGrading {n : ℕ} {p : reesAlgebra I} :
    p ∈ reesGrading I n ↔ ∀ m, m ≠ n → (p : R[X]).coeff m = 0 :=
  Iff.rfl

variable {I} in
theorem mem_reesGrading_iff {n : ℕ} {p : reesAlgebra I} :
    p ∈ reesGrading I n ↔ (p : R[X]) = monomial n ((p : R[X]).coeff n) := by
  rw [mem_reesGrading]
  constructor
  · intro h
    ext m
    rw [coeff_monomial]
    split_ifs with hm
    · rw [hm]
    · exact h m (Ne.symm hm)
  · intro h m hm
    rw [h, coeff_monomial, if_neg (Ne.symm hm)]

/-- The degree-`n` component `p ↦ pₙ tⁿ` of an element of the Rees algebra. -/
def reesComponent (n : ℕ) : reesAlgebra I →+ reesGrading I n where
  toFun p := ⟨⟨monomial n ((p : R[X]).coeff n),
      reesAlgebra.monomial_mem.2 ((mem_reesAlgebra_iff I _).1 p.2 n)⟩,
    fun m hm => by simp [coeff_monomial, Ne.symm hm]⟩
  map_zero' := by ext; simp
  map_add' p q := by ext; simp

theorem coe_reesComponent (n : ℕ) (p : reesAlgebra I) :
    ((reesComponent I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) :=
  rfl

/-- The decomposition of an element of the Rees algebra into its homogeneous components. -/
def reesDecompose (p : reesAlgebra I) : DirectSum ℕ fun n => reesGrading I n :=
  DFinsupp.mk (p : R[X]).support fun n => reesComponent I n.1 p

theorem reesDecompose_apply (p : reesAlgebra I) (n : ℕ) :
    reesDecompose I p n = reesComponent I n p := by
  rw [reesDecompose, DFinsupp.mk_apply]
  split_ifs with h
  · rfl
  · ext
    rw [coe_reesComponent, notMem_support_iff.1 h, map_zero]
    rfl

theorem reesDecompose_support_subset [∀ (i : ℕ) (x : reesGrading I i), Decidable (x ≠ 0)]
    (p : reesAlgebra I) : (reesDecompose I p).support ⊆ (p : R[X]).support :=
  DFinsupp.support_mk_subset

/-- The decomposition of the Rees algebra into its homogeneous components, as an additive map. -/
def reesDecomposeHom : reesAlgebra I →+ DirectSum ℕ fun n => reesGrading I n where
  toFun := reesDecompose I
  map_zero' := DFinsupp.ext fun n => by rw [reesDecompose_apply, map_zero]; rfl
  map_add' p q := DFinsupp.ext fun n => by
    rw [reesDecompose_apply, map_add, DFinsupp.add_apply, reesDecompose_apply,
      reesDecompose_apply]

instance reesGrading_gradedMonoid : SetLike.GradedMonoid (reesGrading I) where
  one_mem m hm := by
    change (1 : R[X]).coeff m = 0
    rw [coeff_one, if_neg hm]
  mul_mem {i j p q} hp hq := by
    rw [mem_reesGrading_iff] at hp hq
    rw [mem_reesGrading]
    intro m hm
    change ((p : R[X]) * q).coeff m = 0
    rw [hp, hq, monomial_mul_monomial, coeff_monomial, if_neg (Ne.symm hm)]

open DirectSum in
/-- The Rees algebra `R[It] = ⨁ₙ Iⁿ tⁿ` is graded by the degree in `t`. -/
instance reesGrading_gradedRing : GradedRing (reesGrading I) where
  __ := reesGrading_gradedMonoid I
  __ := Decomposition.ofAddHom (reesGrading I) (reesDecomposeHom I)
    (by
      classical
      refine AddMonoidHom.ext fun p => Subtype.ext ?_
      change ((DirectSum.coeAddMonoidHom (reesGrading I) (reesDecompose I p) : reesAlgebra I) : R[X]) = p
      rw [coeAddMonoidHom_eq_dfinsuppSum,
        DFinsupp.sum_of_support_subset (reesDecompose_support_subset I p) (fun _ _ => rfl)]
      conv_rhs => rw [(p : R[X]).as_sum_support]
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [reesDecompose_apply, coe_reesComponent])
    (by
      apply DirectSum.addHom_ext
      intro i y
      refine DFinsupp.ext fun n => ?_
      rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
      change reesDecompose I y n = _
      rw [reesDecompose_apply]
      by_cases h : n = i
      · subst h
        rw [DirectSum.of_eq_same]
        ext
        rw [coe_reesComponent, ← mem_reesGrading_iff.1 y.2]
      · rw [DirectSum.of_eq_of_ne _ _ _ h]
        ext
        rw [coe_reesComponent, y.2 n h, map_zero]
        rfl)

variable {I}

theorem reesMap_mem (φ : R →+* S) {J : Ideal S} (h : I.map φ ≤ J) (p : reesAlgebra I) :
    (p : R[X]).map φ ∈ reesAlgebra J := fun n => by
  rw [coeff_map]
  exact Ideal.pow_right_mono h n
    (Ideal.map_pow φ I n ▸ Ideal.mem_map_of_mem φ ((mem_reesAlgebra_iff I _).1 p.2 n))

/-- The map of Rees algebras `R[It] → S[Jt]` induced by a ring map `φ : R → S` with
`φ(I) ⊆ J`, acting on coefficients. -/
def reesMap (φ : R →+* S) {J : Ideal S} (h : I.map φ ≤ J) : reesAlgebra I →+* reesAlgebra J :=
  ((mapRingHom φ).comp (reesAlgebra I).val.toRingHom).codRestrict (reesAlgebra J)
    (reesMap_mem φ h)

theorem coe_reesMap (φ : R →+* S) {J : Ideal S} (h : I.map φ ≤ J) (p : reesAlgebra I) :
    (reesMap φ h p : S[X]) = (p : R[X]).map φ :=
  rfl

theorem reesMap_eq_id (φ : R →+* R) (hφ : φ = RingHom.id R) (h : I.map φ ≤ I) :
    reesMap φ h = RingHom.id _ := by
  subst hφ
  ext p : 2
  simp [coe_reesMap]

theorem reesMap_comp_reesMap {T : Type*} [CommRing T] {J : Ideal S} {K : Ideal T}
    (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T) (hχ : χ = ψ.comp φ) (h₁ : I.map φ ≤ J)
    (h₂ : J.map ψ ≤ K) (h₃ : I.map χ ≤ K) :
    (reesMap ψ h₂).comp (reesMap φ h₁) = reesMap χ h₃ := by
  subst hχ
  ext p : 2
  simp [coe_reesMap, Polynomial.map_map]

theorem reesMap_mem_reesGrading (φ : R →+* S) {J : Ideal S} (h : I.map φ ≤ J) {n : ℕ}
    {p : reesAlgebra I} (hp : p ∈ reesGrading I n) : reesMap φ h p ∈ reesGrading J n :=
  fun m hm => by rw [coe_reesMap, coeff_map, hp m hm, map_zero]

/-- The Rees algebra is compatible with localization: if `S = R[1/r]` and `J = I S`, then
`S[Jt] = R[It][1/r]`. -/
theorem reesMap_isLocalizationAway (φ : R →+* S) {J : Ideal S} (hJ : I.map φ = J) (r : R)
    (hφ : letI := φ.toAlgebra; IsLocalization.Away r S) :
    letI := (reesMap φ hJ.le).toAlgebra
    IsLocalization.Away (algebraMap R (reesAlgebra I) r) (reesAlgebra J) := by
  let := φ.toAlgebra
  let := (reesMap φ hJ.le).toAlgebra
  have hu : IsUnit (φ r) := IsLocalization.Away.algebraMap_isUnit (S := S) r
  have hC : ∀ a : R, (algebraMap (reesAlgebra I) (reesAlgebra J) (algebraMap R _ a) : S[X]) =
      C (φ a) := fun a => by
    change ((algebraMap R (reesAlgebra I) a : R[X])).map φ = _
    simp
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [map_pow]
    refine IsUnit.pow k (IsUnit.of_mul_eq_one
      (⟨C (hu.unit⁻¹ : Sˣ).1, (reesAlgebra J).algebraMap_mem _⟩ : reesAlgebra J) (Subtype.ext ?_))
    change (algebraMap (reesAlgebra I) (reesAlgebra J) (algebraMap R _ r) : S[X]) * _ = 1
    rw [hC, ← C_mul, IsUnit.mul_val_inv, C_1]
  · intro z
    -- Every element of `S[Jt]` has the form `p / rᵏ` with `p ∈ R[It]`.
    let P : S[X] → Prop := fun q => ∃ p ∈ reesAlgebra I, ∃ k : ℕ, q * C (φ r ^ k) = p.map φ
    have hP : P (z : S[X]) := by
      rw [(z : S[X]).as_sum_support]
      refine Finset.sum_induction _ P ?_ ⟨0, zero_mem _, 0, by simp⟩ ?_
      · rintro q₁ q₂ ⟨p₁, hp₁, k₁, h₁⟩ ⟨p₂, hp₂, k₂, h₂⟩
        refine ⟨p₁ * C (r ^ k₂) + p₂ * C (r ^ k₁),
          add_mem (mul_mem hp₁ ((reesAlgebra I).algebraMap_mem _))
            (mul_mem hp₂ ((reesAlgebra I).algebraMap_mem _)), k₁ + k₂, ?_⟩
        rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, ← h₁, ← h₂]
        simp only [Polynomial.map_pow, map_C, map_pow, pow_add, C_mul]
        ring
      · intro n _
        have hn : (z : S[X]).coeff n ∈ (I ^ n).map (algebraMap R S) := by
          rw [Ideal.map_pow]
          exact hJ ▸ z.2 n
        obtain ⟨⟨⟨a, ha⟩, ⟨_, k, rfl⟩⟩, hak⟩ :=
          (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers r) S).1 hn
        refine ⟨monomial n a, reesAlgebra.monomial_mem.2 ha, k, ?_⟩
        have hak' : (z : S[X]).coeff n * φ r ^ k = φ a := by
          simpa [RingHom.algebraMap_toAlgebra] using hak
        rw [mul_comm, C_mul_monomial, map_monomial, mul_comm, hak']
    obtain ⟨p, hp, k, h⟩ := hP
    refine ⟨(⟨p, hp⟩, ⟨_, k, rfl⟩), Subtype.ext ?_⟩
    change (z : S[X]) * (algebraMap (reesAlgebra I) (reesAlgebra J)
      ((algebraMap R (reesAlgebra I) r) ^ k) : S[X]) = p.map φ
    rw [← map_pow (algebraMap R (reesAlgebra I)) r k, hC, map_pow, h]
  · intro x y hxy
    -- Coefficients killed by `S` are killed by a power of `r`.
    let P : R[X] → Prop := fun q => ∃ k : ℕ, C (r ^ k) * q = 0
    have hxy' : ((x : R[X]) - y).map φ = 0 := by
      rw [Polynomial.map_sub, ← coe_reesMap φ hJ.le, ← coe_reesMap φ hJ.le]
      exact sub_eq_zero.2 (congrArg Subtype.val hxy)
    have hP : P ((x : R[X]) - y) := by
      rw [((x : R[X]) - y).as_sum_support]
      refine Finset.sum_induction _ P ?_ ⟨0, by simp⟩ ?_
      · rintro q₁ q₂ ⟨k₁, h₁⟩ ⟨k₂, h₂⟩
        refine ⟨k₁ + k₂, ?_⟩
        rw [pow_add, C_mul]
        linear_combination C (r ^ k₂) * h₁ + C (r ^ k₁) * h₂
      · intro n _
        have h0 : algebraMap R S (((x : R[X]) - y).coeff n) = 0 := by
          change φ _ = 0
          rw [← coeff_map, hxy', coeff_zero]
        obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
          (IsLocalization.map_eq_zero_iff (Submonoid.powers r) S _).1 h0
        exact ⟨k, by rw [C_mul_monomial, hk, map_zero]⟩
    obtain ⟨k, hk⟩ := hP
    refine ⟨⟨_, k, rfl⟩, Subtype.ext ?_⟩
    change (algebraMap R (reesAlgebra I) r : R[X]) ^ k * x = (algebraMap R (reesAlgebra I) r) ^ k * y
    rw [← sub_eq_zero, ← mul_sub]
    simpa using hk

end Algebra

/-! ### The sheaf of Rees algebras -/

section Sheaf

open Scheme.AffineZariskiSite

variable {X : Scheme.{u}} (J : X.IdealSheafData)

namespace ReesAlgebraSheaf

/-- The ideal `J(U) ⊆ Γ(U, 𝒪_X)` over an object `U` of the affine Zariski site. -/
abbrev idealOn (U : X.AffineZariskiSite) : Ideal Γ(X, U.toOpens) :=
  J.ideal ⟨U.toOpens, U.2⟩

theorem map_idealOn {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    (idealOn J V).map (X.presheaf.map ((toOpensFunctor X).map f).op).hom = idealOn J U :=
  J.map_ideal' _

/-- The rings of sections `Γ(U, ⨁_d J^d) = ⨁_d J(U)^d tᵈ` over the affine opens `U`. -/
def functor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (reesAlgebra (idealOn J U.unop))
  map f := CommRingCat.ofHom
    (reesMap (X.presheaf.map ((toOpensFunctor X).map f.unop).op).hom (map_idealOn J f.unop).le)
  map_id U := CommRingCat.hom_ext (reesMap_eq_id _ (by simp; rfl) (map_idealOn J (𝟙 U).unop).le)
  map_comp f g := CommRingCat.hom_ext (reesMap_comp_reesMap _ _ _
    (by rw [unop_comp, Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp]; rfl)
    (map_idealOn J f.unop).le (map_idealOn J g.unop).le (map_idealOn J (f ≫ g).unop).le).symm

/-- The polynomial in `Γ(U, 𝒪_X)[t]` underlying a section of the sheaf of Rees algebras. -/
abbrev toPolynomial {U : X.AffineZariskiSiteᵒᵖ} (p : (functor J).obj U) : Γ(X, U.unop.toOpens)[X] :=
  (show reesAlgebra (idealOn J U.unop) from p).1

theorem toPolynomial_functor_map {U V : X.AffineZariskiSiteᵒᵖ} (f : U ⟶ V)
    (p : (functor J).obj U) :
    toPolynomial J ((functor J).map f p) =
      (toPolynomial J p).map (X.presheaf.map ((toOpensFunctor X).map f.unop).op).hom :=
  rfl

/-- The `𝒪_X`-algebra structure `Γ(U, 𝒪_X) → ⨁_d J(U)^d tᵈ` (constants, in degree zero). -/
def structureMap : (toOpensFunctor X).op ⋙ X.presheaf ⟶ functor J where
  app U := CommRingCat.ofHom (algebraMap Γ(X, U.unop.toOpens) (reesAlgebra (idealOn J U.unop)))
  naturality U V f := by
    ext r : 2
    refine Subtype.ext ?_
    exact (map_C _).symm

theorem toPolynomial_structureMap_app (U : X.AffineZariskiSiteᵒᵖ) (r : Γ(X, U.unop.toOpens)) :
    toPolynomial J ((structureMap J).app U r) = C r :=
  rfl

theorem coequifibered : (structureMap J).Coequifibered := by
  refine coequifibered_iff_forall_isLocalizationAway.mpr fun U r => ?_
  exact reesMap_isLocalizationAway
    (X.presheaf.map ((toOpensFunctor X).map (homOfLE (U.basicOpen_le r))).op).hom
    (map_idealOn J _) r (U.2.isLocalization_basicOpen r)

end ReesAlgebraSheaf

open ReesAlgebraSheaf in
/-- **The sheaf of Rees algebras** `⨁_{d ≥ 0} Jᵈ` of a quasi-coherent ideal sheaf `J` (Hartshorne
II.7, p. 163), as a quasi-coherent sheaf of graded `𝒪_X`-algebras: over an affine open `U` its
ring of sections is the Rees algebra `⨁_d J(U)ᵈ tᵈ ⊆ Γ(U, 𝒪_X)[t]`, graded by the degree in `t`. -/
def reesAlgebraSheaf : QuasiCoherentGradedAlgebra X where
  obj := functor J
  structureMap := structureMap J
  coequifibered := coequifibered J
  grading U := reesGrading (idealOn J U)
  gradedRing U := reesGrading_gradedRing (idealOn J U)
  map_mem f _ _ hx := reesMap_mem_reesGrading _ (map_idealOn J f.op.unop).le hx
  structureMap_mem U r m hm := by
    change (C r).coeff m = 0
    rw [coeff_C, if_neg hm]

end Sheaf

end Hartshorne
