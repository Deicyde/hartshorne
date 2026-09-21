/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Rational.ProductGeometry
import Hartshorne.Morphism.ChartIso

/-!
# Products of varieties

Hartshorne, *Algebraic Geometry*, I.3, Exercise 3.16 (p. 22).

The Segre product carries its induced quasi-projective variety structure.  Its
coordinate projections are morphisms, and every pair of morphisms into the
factors induces a morphism into the product.  The local proof uses normalized
coordinates on simultaneous standard charts, never the ordinary product
topology.

## Main results

* `Hartshorne.segreProductFstHom`, `Hartshorne.segreProductSndHom`
* `Hartshorne.segreProductLiftHom`
* `Hartshorne.product_variety`
-/

namespace Hartshorne

open MvPolynomial TopologicalSpace
open scoped Hartshorne

universe u

variable {k : Type u} [Field k]

/-- The part of a quasi-projective set lying in a standard chart. -/
def productChartOpen {σ : Type u} (Y : Set (ProjectiveSpace k σ)) (i : σ) : Opens Y where
  carrier := {y : Y | (y.1 : ProjectiveSpace k σ) ∈ standardChart i}
  is_open' := (isOpen_standardChart i).preimage continuous_subtype_val

/-- The same chart open, read on the associated variety. -/
noncomputable def productChartOpens {σ : Type u} {Y : Set (ProjectiveSpace k σ)}
    (hY : IsQuasiProjVariety Y) (i : σ) :
    Opens (Variety.ofQuasiProjective hY).carrier :=
  productChartOpen Y i

/-- A normalized projective coordinate on a standard chart. -/
noncomputable def productChartCoord {σ : Type u} (Y : Set (ProjectiveSpace k σ))
    (i l : σ) : productChartOpen Y i → k :=
  fun y => (y.1 : ProjectiveSpace k σ).rep l /
    (y.1 : ProjectiveSpace k σ).rep i

/-- Normalized projective coordinates are regular on their charts. -/
theorem productChartCoord_mem_regular {σ : Type u}
    {Y : Set (ProjectiveSpace k σ)} (hY : IsQuasiProjVariety Y) (i l : σ) :
    productChartCoord Y i l ∈
      (Variety.ofQuasiProjective hY).regular (productChartOpen Y i) := by
  intro z
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, X l, X i,
    isHomogeneous_X _ _, isHomogeneous_X _ _, fun x _ => ?_, fun x _ => ?_⟩
  · simpa using rep_ne_zero_of_mem_standardChart x.2
  · simp [productChartCoord, projOpenIota]

namespace Variety

/-- The open-set version of `continuous_of_coords_regular`. -/
theorem continuous_on_open_of_coords_regular
    {X : Variety k} {U : Opens X.carrier} {ι : Type u}
    (ψ : U → (ι → k))
    (hψ : ∀ i, (fun x : U => ψ x i) ∈ X.regular U) :
    Continuous ψ := by
  rw [continuous_iff_isClosed]
  intro C hC
  obtain ⟨T, rfl⟩ := isClosed_iff_isAlgebraicSet.1 hC
  have hpre : ψ ⁻¹' zeroSet T = ⋂ f ∈ T, {x : U | eval (ψ x) f = 0} := by
    ext x
    simp [mem_zeroSet_iff]
  rw [hpre]
  refine isClosed_biInter fun f _ => X.isClosed_zeroLocus ?_
  exact eval_comp_mem_regular ψ hψ f

end Variety

/-- A local chart criterion for a map to a quasi-projective variety to be a
morphism.  It is the projective analogue of Lemma 3.6. -/
theorem exists_varietyHom_iff_locally_chart_regular
    {X : Variety k} {σ : Type u} [DecidableEq σ]
    {Y : Set (ProjectiveSpace k σ)} (hY : IsQuasiProjVariety Y)
    (φ : X.carrier → Y) :
    (∃ F : VarietyHom X (Variety.ofQuasiProjective hY), F.toFun = φ) ↔
      ∀ x : X.carrier, ∃ i : σ, ∃ U : Opens X.carrier,
        x ∈ U ∧
        (∀ z : U, (φ z.1 : ProjectiveSpace k σ) ∈ standardChart i) ∧
        ∀ l : {l : σ // l ≠ i},
          (fun z : U => chartMap i (φ z.1 : ProjectiveSpace k σ) l) ∈ X.regular U := by
  constructor
  · rintro ⟨F, rfl⟩ x
    obtain ⟨i, hi⟩ := exists_mem_standardChart (F x).1
    let U : Opens X.carrier := Opens.comap ⟨F.toFun, F.continuous_toFun⟩ (productChartOpens hY i)
    refine ⟨i, U, hi, fun z => z.2, fun l => ?_⟩
    exact F.regular_comp (productChartOpens hY i) (productChartCoord Y i l.1)
      (productChartCoord_mem_regular hY i l.1)
  · intro hlocal
    have hcont : Continuous φ := by
      rw [continuous_iff_continuousAt]
      intro x
      obtain ⟨i, U, hxU, hφU, hcoord⟩ := hlocal x
      let ψ : U → ({l : σ // l ≠ i} → k) :=
        fun z => chartMap i (φ z.1 : ProjectiveSpace k σ)
      have hψ : Continuous ψ :=
        Variety.continuous_on_open_of_coords_regular ψ hcoord
      have heq : (fun z : U => φ z.1) =
          fun z : U => (⟨chartInv i (ψ z), by
            rw [chartInv_chartMap (hφU z)]
            exact (φ z.1).2⟩ : Y) := by
        funext z
        apply Subtype.ext
        exact (chartInv_chartMap (hφU z)).symm
      have hrestr : Continuous (fun z : U => φ z.1) := by
        rw [heq]
        exact ((continuous_chartInv i).comp hψ).subtype_mk _
      have hon : ContinuousOn φ U :=
        continuousOn_iff_continuous_domRestrict.mpr hrestr
      exact hon.continuousAt (U.isOpen.mem_nhds hxU)
    refine ⟨⟨φ, hcont, ?_⟩, rfl⟩
    intro V f hf
    let W : Opens X.carrier := Opens.comap ⟨φ, hcont⟩ V
    show (fun x : W => f ⟨φ x.1, x.2⟩) ∈ X.regular W
    apply X.regular_of_locally
    intro P
    obtain ⟨i, U, hPU, hφU, hcoord⟩ := hlocal P.1
    obtain ⟨O, hO, hφPO, n, g, q, hg, hq, hqne, heval⟩ :=
      (mem_projRegularSubalgebra.1 hf) ⟨φ P.1, P.2⟩
    rw [isOpen_induced_iff] at hO
    obtain ⟨O', hO', rfl⟩ := hO
    let OX : Opens X.carrier := Opens.comap ⟨φ, hcont⟩ ⟨O', hO'⟩
    let N : Opens X.carrier := W ⊓ U ⊓ OX
    have hNW : N ≤ W := fun _ hz => hz.1.1
    have hNU : N ≤ U := fun _ hz => hz.1.2
    have hPN : P.1 ∈ N := ⟨⟨P.2, hPU⟩, hφPO⟩
    refine ⟨N, hNW, hPN, ?_⟩
    let ψ : N → ({l : σ // l ≠ i} → k) :=
      fun z => chartMap i (φ z.1 : ProjectiveSpace k σ)
    have hψ : ∀ l, (fun z : N => ψ z l) ∈ X.regular N := fun l =>
      X.regular_restrict hNU (hcoord l)
    have hg' := Variety.eval_comp_mem_regular ψ hψ (dehomogenize i g)
    have hq' := Variety.eval_comp_mem_regular ψ hψ (dehomogenize i q)
    have hqne' : ∀ z : N, eval (ψ z) (dehomogenize i q) ≠ 0 := by
      intro z
      apply eval_dehomogenize_ne_zero k i hq (ψ z)
      rw [chartInv_chartMap (hφU ⟨z.1, hNU z.2⟩)]
      exact hqne ⟨φ z.1, z.2.1.1⟩ z.2.2
    have hEq :
        (fun z : N => f ⟨φ z.1, z.2.1.1⟩) =
          fun z : N => eval (ψ z) (dehomogenize i g) /
            eval (ψ z) (dehomogenize i q) := by
      funext z
      let y : V := ⟨φ z.1, z.2.1.1⟩
      have hev := heval y z.2.2
      change f y = _
      rw [hev]
      have hratio := eval_rep_chartInv_div k i hg hq (ψ z)
      rw [chartInv_chartMap (hφU ⟨z.1, hNU z.2⟩)] at hratio
      exact hratio
    rw [hEq]
    exact X.regular_div hg' hq' hqne'

section SegreProduct

variable {σ τ : Type u}

/-- A chosen pair represented by a point of the Segre product.  Injectivity
makes the choice canonical propositionally. -/
noncomputable def segreProductPreimage
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (R : segreProduct X Y) : ProjectiveSpace k σ × ProjectiveSpace k τ :=
  Classical.choose R.2

theorem segreProductPreimage_mem
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (R : segreProduct X Y) :
    segreProductPreimage R ∈ X ×ˢ Y :=
  (Classical.choose_spec R.2).1

theorem segreProductPreimage_map
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (R : segreProduct X Y) :
    segreMap (segreProductPreimage R).1 (segreProductPreimage R).2 = R.1 :=
  (Classical.choose_spec R.2).2

noncomputable def segreProductFst
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (R : segreProduct X Y) : X :=
  ⟨(segreProductPreimage R).1, (segreProductPreimage_mem R).1⟩

noncomputable def segreProductSnd
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (R : segreProduct X Y) : Y :=
  ⟨(segreProductPreimage R).2, (segreProductPreimage_mem R).2⟩

noncomputable def segreProductMk
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (P : X) (Q : Y) : segreProduct X Y :=
  ⟨segreMap P.1 Q.1, ⟨(P.1, Q.1), ⟨P.2, Q.2⟩, rfl⟩⟩

theorem segreMap_fst_snd
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (R : segreProduct X Y) :
    segreMap (segreProductFst R).1 (segreProductSnd R).1 = R.1 :=
  segreProductPreimage_map R

@[simp]
theorem segreProductFst_mk
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (P : X) (Q : Y) :
    segreProductFst (segreProductMk P Q) = P := by
  apply Subtype.ext
  exact (segreMap_eq_iff.mp (segreMap_fst_snd (segreProductMk P Q))).1

@[simp]
theorem segreProductSnd_mk
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (P : X) (Q : Y) :
    segreProductSnd (segreProductMk P Q) = Q := by
  apply Subtype.ext
  exact (segreMap_eq_iff.mp (segreMap_fst_snd (segreProductMk P Q))).2

theorem segreMap_mem_standardChart_iff
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ) (i : σ) (j : τ) :
    segreMap P Q ∈ standardChart (i, j) ↔
      P ∈ standardChart i ∧ Q ∈ standardChart j := by
  rw [mem_standardChart_iff, mem_standardChart_iff, mem_standardChart_iff]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k
    (segreVector P.rep Q.rep)
    (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero)
  unfold segreMap
  rw [← ha]
  simp only [Pi.smul_apply, Units.smul_def, smul_eq_mul, segreVector]
  exact ⟨fun h => ⟨fun hi => h (by simp [hi]), fun hj => h (by simp [hj])⟩,
    fun h => mul_ne_zero (Units.ne_zero a) (mul_ne_zero h.1 h.2)⟩

theorem chartMap_segreMap_fst
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ)
    (i : σ) (j : τ) (hj : Q.rep j ≠ 0) (l : {l : σ // l ≠ i}) :
    chartMap (i, j) (segreMap P Q) ⟨(l.1, j), fun h => l.2 (congrArg Prod.fst h)⟩ =
      chartMap i P l := by
  rw [show segreMap P Q = Projectivization.mk k (segreVector P.rep Q.rep)
      (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero) from rfl,
    chartMap_mk, chartMap]
  simp only [segreVector]
  exact mul_div_mul_right _ _ hj

theorem chartMap_segreMap_snd
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ)
    (i : σ) (j : τ) (hi : P.rep i ≠ 0) (m : {m : τ // m ≠ j}) :
    chartMap (i, j) (segreMap P Q) ⟨(i, m.1), fun h => m.2 (congrArg Prod.snd h)⟩ =
      chartMap j Q m := by
  rw [show segreMap P Q = Projectivization.mk k (segreVector P.rep Q.rep)
      (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero) from rfl,
    chartMap_mk, chartMap]
  simp only [segreVector]
  exact mul_div_mul_left _ _ hi

theorem chartMap_segreMap
    (P : ProjectiveSpace k σ) (Q : ProjectiveSpace k τ)
    (i : σ) (j : τ) (hi : P.rep i ≠ 0) (hj : Q.rep j ≠ 0)
    (lm : {lm : σ × τ // lm ≠ (i, j)}) :
    chartMap (i, j) (segreMap P Q) lm =
      (P.rep lm.1.1 / P.rep i) * (Q.rep lm.1.2 / Q.rep j) := by
  rw [show segreMap P Q = Projectivization.mk k (segreVector P.rep Q.rep)
      (segreVector_ne_zero P.rep_nonzero Q.rep_nonzero) from rfl,
    chartMap_mk]
  simp only [segreVector]
  field_simp

/-- The first projection of the Segre product is a morphism. -/
theorem exists_segreProductFstHom
    [DecidableEq σ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X)
    (hProd : IsQuasiProjVariety (segreProduct X Y)) :
    ∃ F : VarietyHom (Variety.ofQuasiProjective hProd)
        (Variety.ofQuasiProjective hX),
      F.toFun = segreProductFst := by
  refine (exists_varietyHom_iff_locally_chart_regular
    (X := Variety.ofQuasiProjective hProd) hX
    (segreProductFst (X := X) (Y := Y))).2 ?_
  intro R
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (segreProductFst R).1.rep_nonzero
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (segreProductSnd R).1.rep_nonzero
  let U : Opens (Variety.ofQuasiProjective hProd).carrier :=
    productChartOpen (segreProduct X Y) (i, j)
  refine ⟨i, U, ?_, ?_, ?_⟩
  · change R.1 ∈ standardChart (i, j)
    rw [← segreMap_fst_snd R, segreMap_mem_standardChart_iff]
    exact ⟨mem_standardChart_iff.2 hi, mem_standardChart_iff.2 hj⟩
  · intro z
    have hs : segreMap (segreProductFst z.1).1 (segreProductSnd z.1).1 ∈
        standardChart (i, j) := by
      rw [segreMap_fst_snd z.1]
      exact z.2
    exact (segreMap_mem_standardChart_iff _ _ i j).1 hs |>.1
  · intro l
    have hreg := productChartCoord_mem_regular hProd (i, j) (l.1, j)
    rw [show (fun z : U => chartMap i (segreProductFst z.1).1 l) =
        productChartCoord (segreProduct X Y) (i, j) (l.1, j) by
      funext z
      have hs : segreMap (segreProductFst z.1).1 (segreProductSnd z.1).1 ∈
          standardChart (i, j) := by
        rw [segreMap_fst_snd z.1]
        exact z.2
      have hjz := rep_ne_zero_of_mem_standardChart
        ((segreMap_mem_standardChart_iff _ _ i j).1 hs).2
      have he := chartMap_segreMap_fst
        (segreProductFst z.1).1 (segreProductSnd z.1).1 i j hjz l
      rw [segreMap_fst_snd z.1] at he
      exact he.symm]
    exact hreg

/-- The second projection of the Segre product is a morphism. -/
theorem exists_segreProductSndHom
    [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y)) :
    ∃ F : VarietyHom (Variety.ofQuasiProjective hProd)
        (Variety.ofQuasiProjective hY),
      F.toFun = segreProductSnd := by
  refine (exists_varietyHom_iff_locally_chart_regular
    (X := Variety.ofQuasiProjective hProd) hY
    (segreProductSnd (X := X) (Y := Y))).2 ?_
  intro R
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (segreProductFst R).1.rep_nonzero
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (segreProductSnd R).1.rep_nonzero
  let U : Opens (Variety.ofQuasiProjective hProd).carrier :=
    productChartOpen (segreProduct X Y) (i, j)
  refine ⟨j, U, ?_, ?_, ?_⟩
  · change R.1 ∈ standardChart (i, j)
    rw [← segreMap_fst_snd R, segreMap_mem_standardChart_iff]
    exact ⟨mem_standardChart_iff.2 hi, mem_standardChart_iff.2 hj⟩
  · intro z
    have hs : segreMap (segreProductFst z.1).1 (segreProductSnd z.1).1 ∈
        standardChart (i, j) := by
      rw [segreMap_fst_snd z.1]
      exact z.2
    exact (segreMap_mem_standardChart_iff _ _ i j).1 hs |>.2
  · intro m
    have hreg := productChartCoord_mem_regular hProd (i, j) (i, m.1)
    rw [show (fun z : U => chartMap j (segreProductSnd z.1).1 m) =
        productChartCoord (segreProduct X Y) (i, j) (i, m.1) by
      funext z
      have hs : segreMap (segreProductFst z.1).1 (segreProductSnd z.1).1 ∈
          standardChart (i, j) := by
        rw [segreMap_fst_snd z.1]
        exact z.2
      have hiz := rep_ne_zero_of_mem_standardChart
        ((segreMap_mem_standardChart_iff _ _ i j).1 hs).1
      have he := chartMap_segreMap_snd
        (segreProductFst z.1).1 (segreProductSnd z.1).1 i j hiz m
      rw [segreMap_fst_snd z.1] at he
      exact he.symm]
    exact hreg

/-- A pair of morphisms induces a morphism to their Segre product. -/
theorem exists_segreProductLiftHom
    [DecidableEq σ] [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y))
    {Z : Variety k}
    (f : VarietyHom Z (Variety.ofQuasiProjective hX))
    (g : VarietyHom Z (Variety.ofQuasiProjective hY)) :
    ∃ h : VarietyHom Z (Variety.ofQuasiProjective hProd),
      h.toFun = fun z => segreProductMk (f z) (g z) := by
  refine (exists_varietyHom_iff_locally_chart_regular
    (X := Z) hProd (fun z => segreProductMk (f z) (g z))).2 ?_
  intro z
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (f z).1.rep_nonzero
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (g z).1.rep_nonzero
  let U : Opens Z.carrier :=
    Opens.comap ⟨f.toFun, f.continuous_toFun⟩ (productChartOpens hX i) ⊓
      Opens.comap ⟨g.toFun, g.continuous_toFun⟩ (productChartOpens hY j)
  refine ⟨(i, j), U, ?_, ?_, ?_⟩
  · exact ⟨mem_standardChart_iff.2 hi, mem_standardChart_iff.2 hj⟩
  · intro w
    exact (segreMap_mem_standardChart_iff _ _ i j).2 ⟨w.2.1, w.2.2⟩
  · intro lm
    have ha :
        (fun w : U => (f w.1).1.rep lm.1.1 / (f w.1).1.rep i) ∈ Z.regular U := by
      simpa [productChartCoord, productChartOpens] using
        Z.regular_restrict (V := U) inf_le_left
          (f.regular_comp (productChartOpens hX i) (productChartCoord X i lm.1.1)
            (productChartCoord_mem_regular hX i lm.1.1))
    have hb :
        (fun w : U => (g w.1).1.rep lm.1.2 / (g w.1).1.rep j) ∈ Z.regular U := by
      simpa [productChartCoord, productChartOpens] using
        Z.regular_restrict (V := U) inf_le_right
          (g.regular_comp (productChartOpens hY j) (productChartCoord Y j lm.1.2)
            (productChartCoord_mem_regular hY j lm.1.2))
    rw [show (fun w : U =>
        chartMap (i, j) ((segreProductMk (f w.1) (g w.1)).1) lm) =
          fun w : U =>
            ((f w.1).1.rep lm.1.1 / (f w.1).1.rep i) *
              ((g w.1).1.rep lm.1.2 / (g w.1).1.rep j) by
      funext w
      exact chartMap_segreMap (f w.1).1 (g w.1).1 i j
        (rep_ne_zero_of_mem_standardChart w.2.1)
        (rep_ne_zero_of_mem_standardChart w.2.2) lm]
    exact mul_mem ha hb

noncomputable def segreProductFstHom
    [DecidableEq σ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X)
    (hProd : IsQuasiProjVariety (segreProduct X Y)) :
    VarietyHom (Variety.ofQuasiProjective hProd)
      (Variety.ofQuasiProjective hX) :=
  Classical.choose (exists_segreProductFstHom hX hProd)

theorem segreProductFstHom_toFun
    [DecidableEq σ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X)
    (hProd : IsQuasiProjVariety (segreProduct X Y)) :
    (segreProductFstHom hX hProd).toFun = segreProductFst :=
  Classical.choose_spec (exists_segreProductFstHom hX hProd)

@[simp]
theorem segreProductFstHom_apply
    [DecidableEq σ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X)
    (hProd : IsQuasiProjVariety (segreProduct X Y))
    (R : (Variety.ofQuasiProjective hProd).carrier) :
    segreProductFstHom hX hProd R = segreProductFst R :=
  congrFun (segreProductFstHom_toFun hX hProd) R

noncomputable def segreProductSndHom
    [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y)) :
    VarietyHom (Variety.ofQuasiProjective hProd)
      (Variety.ofQuasiProjective hY) :=
  Classical.choose (exists_segreProductSndHom hY hProd)

theorem segreProductSndHom_toFun
    [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y)) :
    (segreProductSndHom hY hProd).toFun = segreProductSnd :=
  Classical.choose_spec (exists_segreProductSndHom hY hProd)

@[simp]
theorem segreProductSndHom_apply
    [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y))
    (R : (Variety.ofQuasiProjective hProd).carrier) :
    segreProductSndHom hY hProd R = segreProductSnd R :=
  congrFun (segreProductSndHom_toFun hY hProd) R

noncomputable def segreProductLiftHom
    [DecidableEq σ] [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y))
    {Z : Variety k}
    (f : VarietyHom Z (Variety.ofQuasiProjective hX))
    (g : VarietyHom Z (Variety.ofQuasiProjective hY)) :
    VarietyHom Z (Variety.ofQuasiProjective hProd) :=
  Classical.choose (exists_segreProductLiftHom hX hY hProd f g)

theorem segreProductLiftHom_toFun
    [DecidableEq σ] [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y))
    {Z : Variety k}
    (f : VarietyHom Z (Variety.ofQuasiProjective hX))
    (g : VarietyHom Z (Variety.ofQuasiProjective hY)) :
    (segreProductLiftHom hX hY hProd f g).toFun =
      fun z => segreProductMk (f z) (g z) :=
  Classical.choose_spec (exists_segreProductLiftHom hX hY hProd f g)

@[simp]
theorem segreProductLiftHom_apply
    [DecidableEq σ] [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y))
    {Z : Variety k}
    (f : VarietyHom Z (Variety.ofQuasiProjective hX))
    (g : VarietyHom Z (Variety.ofQuasiProjective hY)) (z : Z.carrier) :
    segreProductLiftHom hX hY hProd f g z = segreProductMk (f z) (g z) :=
  congrFun (segreProductLiftHom_toFun hX hY hProd f g) z

theorem segreProductFst_mk_variety
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (P : (Variety.ofQuasiProjective hX).carrier)
    (Q : (Variety.ofQuasiProjective hY).carrier) :
    segreProductFst (segreProductMk P Q) = P := by
  exact segreProductFst_mk P Q

theorem segreProductSnd_mk_variety
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (P : (Variety.ofQuasiProjective hX).carrier)
    (Q : (Variety.ofQuasiProjective hY).carrier) :
    segreProductSnd (segreProductMk P Q) = Q := by
  exact segreProductSnd_mk P Q

theorem segreProductFstHom_comp_lift
    [DecidableEq σ] [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y))
    {Z : Variety k}
    (f : VarietyHom Z (Variety.ofQuasiProjective hX))
    (g : VarietyHom Z (Variety.ofQuasiProjective hY)) :
    (segreProductFstHom hX hProd).comp
      (segreProductLiftHom hX hY hProd f g) = f := by
  apply VarietyHom.ext
  funext z
  change (segreProductFstHom hX hProd).toFun
      ((segreProductLiftHom hX hY hProd f g).toFun z) = f.toFun z
  rw [segreProductFstHom_toFun hX hProd,
    segreProductLiftHom_toFun hX hY hProd f g,
    segreProductFst_mk_variety hX hY]

theorem segreProductSndHom_comp_lift
    [DecidableEq σ] [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y))
    {Z : Variety k}
    (f : VarietyHom Z (Variety.ofQuasiProjective hX))
    (g : VarietyHom Z (Variety.ofQuasiProjective hY)) :
    (segreProductSndHom hY hProd).comp
      (segreProductLiftHom hX hY hProd f g) = g := by
  apply VarietyHom.ext
  funext z
  change (segreProductSndHom hY hProd).toFun
      ((segreProductLiftHom hX hY hProd f g).toFun z) = g.toFun z
  rw [segreProductSndHom_toFun hY hProd,
    segreProductLiftHom_toFun hX hY hProd f g,
    segreProductSnd_mk_variety hX hY]

/-- The morphism part of Exercise 3.16(c): the two projections are morphisms,
and every pair of morphisms has a common arrow to the Segre product. -/
theorem segreProduct_morphism_universal
    [DecidableEq σ] [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y)
    (hProd : IsQuasiProjVariety (segreProduct X Y)) :
    ∃ p₁ : VarietyHom (Variety.ofQuasiProjective hProd)
        (Variety.ofQuasiProjective hX),
      ∃ p₂ : VarietyHom (Variety.ofQuasiProjective hProd)
        (Variety.ofQuasiProjective hY),
      ∀ (Z : Variety k)
        (f : VarietyHom Z (Variety.ofQuasiProjective hX))
        (g : VarietyHom Z (Variety.ofQuasiProjective hY)),
        ∃ h : VarietyHom Z (Variety.ofQuasiProjective hProd),
          p₁.comp h = f ∧ p₂.comp h = g := by
  refine ⟨segreProductFstHom hX hProd, segreProductSndHom hY hProd, ?_⟩
  intro Z f g
  exact ⟨segreProductLiftHom hX hY hProd f g,
    segreProductFstHom_comp_lift hX hY hProd f g,
    segreProductSndHom_comp_lift hX hY hProd f g⟩

/-- **Exercise 3.16(a),(b), and the existence part of (c).**  The Segre
product of quasi-projective varieties is quasi-projective, is projective when
both factors are, has the expected projection morphisms, and receives the
expected morphism from every pair of morphisms into the factors. -/
theorem product_variety
    [DecidableEq σ] [DecidableEq τ]
    {X : Set (ProjectiveSpace k σ)} {Y : Set (ProjectiveSpace k τ)}
    (hX : IsQuasiProjVariety X) (hY : IsQuasiProjVariety Y) :
    let hProd := isQuasiProjVariety_segreProduct hX hY
    IsQuasiProjVariety (segreProduct X Y) ∧
      (IsProjVariety X → IsProjVariety Y →
        IsProjVariety (segreProduct X Y)) ∧
      ∃ p₁ : VarietyHom (Variety.ofQuasiProjective hProd)
          (Variety.ofQuasiProjective hX),
        ∃ p₂ : VarietyHom (Variety.ofQuasiProjective hProd)
            (Variety.ofQuasiProjective hY),
          p₁.toFun = segreProductFst ∧
          p₂.toFun = segreProductSnd ∧
          ∀ (Z : Variety k)
            (f : VarietyHom Z (Variety.ofQuasiProjective hX))
            (g : VarietyHom Z (Variety.ofQuasiProjective hY)),
            ∃ h : VarietyHom Z (Variety.ofQuasiProjective hProd),
              h.toFun = (fun z => segreProductMk (f z) (g z)) ∧
              p₁.comp h = f ∧ p₂.comp h = g := by
  let hProd := isQuasiProjVariety_segreProduct hX hY
  refine ⟨hProd, fun hXp hYp => isProjVariety_segreProduct hXp hYp,
    segreProductFstHom hX hProd, segreProductSndHom hY hProd,
    segreProductFstHom_toFun hX hProd,
    segreProductSndHom_toFun hY hProd, ?_⟩
  intro Z f g
  exact ⟨segreProductLiftHom hX hY hProd f g,
    segreProductLiftHom_toFun hX hY hProd f g,
    segreProductFstHom_comp_lift hX hY hProd f g,
    segreProductSndHom_comp_lift hX hY hProd f g⟩

end SegreProduct

end Hartshorne
