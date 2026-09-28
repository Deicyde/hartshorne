/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Curve.ProjectiveChartExtensions
import Hartshorne.Rational.ProductVariety

/-!
# The projective diagonal model

Hartshorne, *Algebraic Geometry*, I.6, proof of Theorem 6.9 (p. 44).

The two projective extensions of the affine charts determine a morphism to
their Segre product.  Its image closure is projective, and corestricting the
diagonal morphism to that closure gives a morphism with dense image.  The
construction is packaged so its function-field and local-ring comparisons use
the same witnesses.
-/

namespace Hartshorne

open Set TopologicalSpace
open scoped Hartshorne

noncomputable section

universe u

namespace ValuationSpace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem closure_range_isProjVariety
    {A : Variety k} {ι : Type u} {Z : Set (ProjectiveSpace k ι)}
    (hZ : IsProjVariety Z)
    (f : VarietyHom A (Variety.ofProjective hZ)) :
    IsProjVariety (closure (Set.range fun x => (f x).1)) := by
  refine ⟨?_, isClosed_closure⟩
  have himage : IsIrreducible
      ((fun x : A.carrier => (f x).1) '' Set.univ) :=
    (IrreducibleSpace.isIrreducible_univ A.carrier).image _
      (continuous_subtype_val.comp f.continuous_toFun).continuousOn
  simpa only [Set.image_univ] using himage.closure

private theorem exists_codRestrictClosure
    {A : Variety k} {ι : Type u} [DecidableEq ι]
    {Z : Set (ProjectiveSpace k ι)}
    (hZ : IsProjVariety Z)
    (f : VarietyHom A (Variety.ofProjective hZ)) :
    ∃ g : VarietyHom A
        (Variety.ofProjective (closure_range_isProjVariety hZ f)),
      g.toFun = fun x =>
        ⟨(f x).1, subset_closure ⟨x, rfl⟩⟩ := by
  apply (exists_varietyHom_iff_locally_chart_regular
    (closure_range_isProjVariety hZ f).isQuasiProjVariety _).2
  intro x
  obtain ⟨i, U, hxU, hfU, hcoord⟩ :=
    (exists_varietyHom_iff_locally_chart_regular
      hZ.isQuasiProjVariety f.toFun).1 ⟨f, rfl⟩ x
  exact ⟨i, U, hxU, hfU, hcoord⟩

private noncomputable def codRestrictClosure
    {A : Variety k} {ι : Type u} [DecidableEq ι]
    {Z : Set (ProjectiveSpace k ι)}
    (hZ : IsProjVariety Z)
    (f : VarietyHom A (Variety.ofProjective hZ)) :
    VarietyHom A
      (Variety.ofProjective (closure_range_isProjVariety hZ f)) :=
  Classical.choose (exists_codRestrictClosure hZ f)

private theorem codRestrictClosure_toFun
    {A : Variety k} {ι : Type u} [DecidableEq ι]
    {Z : Set (ProjectiveSpace k ι)}
    (hZ : IsProjVariety Z)
    (f : VarietyHom A (Variety.ofProjective hZ)) :
    (codRestrictClosure hZ f).toFun = fun x =>
      ⟨(f x).1, subset_closure ⟨x, rfl⟩⟩ :=
  Classical.choose_spec (exists_codRestrictClosure hZ f)

private theorem codRestrictClosure_dense
    {A : Variety k} {ι : Type u} [DecidableEq ι]
    {Z : Set (ProjectiveSpace k ι)}
    (hZ : IsProjVariety Z)
    (f : VarietyHom A (Variety.ofProjective hZ)) :
    DenseRange (codRestrictClosure hZ f).toFun := by
  rw [codRestrictClosure_toFun]
  change DenseRange (fun x : A.carrier =>
    (⟨(f x).1, subset_closure ⟨x, rfl⟩⟩ :
      closure (Set.range fun x => (f x).1)))
  rw [DenseRange, Subtype.dense_iff]
  apply closure_mono
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨(f x).1, subset_closure ⟨x, rfl⟩⟩, ⟨x, rfl⟩, rfl⟩

/-- The data in Hartshorne's product-and-closure construction in the proof of
Theorem I.6.9.  In particular, both later comparison arguments refer to the
same chart models, extensions, image closure, and corestricted diagonal. -/
structure ProjectiveDiagonalModel [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) where
  M₀ : AffineNormalizationModel htrdeg
    (separableNormalizationCharts k K htrdeg).atZero
  M₁ : AffineNormalizationModel htrdeg
    (separableNormalizationCharts k K htrdeg).atInfinity
  cover :
    (M₀.imageOpen : Set
        (abstractNonsingularCurveOfFunctionField htrdeg).carrier) ∪
      (M₁.imageOpen : Set
        (abstractNonsingularCurveOfFunctionField htrdeg).carrier) = Set.univ
  Φ₀ : VarietyHom
    (abstractNonsingularCurveOfFunctionField htrdeg)
    (Variety.ofProjective M₀.projectiveClosure_isProjVariety)
  Φ₁ : VarietyHom
    (abstractNonsingularCurveOfFunctionField htrdeg)
    (Variety.ofProjective M₁.projectiveClosure_isProjVariety)
  extension₀ : Φ₀.comp M₀.embedding = M₀.affineToProjectiveClosure
  extension₁ : Φ₁.comp M₁.embedding = M₁.affineToProjectiveClosure
  productIsProjVariety :
    IsProjVariety (segreProduct M₀.projectiveClosure M₁.projectiveClosure)
  productFst : VarietyHom
    (Variety.ofProjective productIsProjVariety)
    (Variety.ofProjective M₀.projectiveClosure_isProjVariety)
  productSnd : VarietyHom
    (Variety.ofProjective productIsProjVariety)
    (Variety.ofProjective M₁.projectiveClosure_isProjVariety)
  productFst_toFun : productFst.toFun = segreProductFst
  productSnd_toFun : productSnd.toFun = segreProductSnd
  diagonal : VarietyHom
    (abstractNonsingularCurveOfFunctionField htrdeg)
    (Variety.ofProjective productIsProjVariety)
  diagonal_toFun : diagonal.toFun =
    fun x => segreProductMk (Φ₀ x) (Φ₁ x)
  productFst_comp_diagonal : productFst.comp diagonal = Φ₀
  productSnd_comp_diagonal : productSnd.comp diagonal = Φ₁
  Y : Set (ProjectiveSpace k (Option M₀.ι × Option M₁.ι))
  Y_eq_closure_range_diagonal :
    Y = closure (Set.range fun x => (diagonal x).1)
  isProjVariety : IsProjVariety Y
  φ : VarietyHom
    (abstractNonsingularCurveOfFunctionField htrdeg)
    (Variety.ofProjective isProjVariety)
  φ_val : ∀ x, (φ x).1 = (diagonal x).1
  φ_dense : DenseRange φ.toFun

namespace ProjectiveDiagonalModel

variable [IsAlgClosed k] [Algebra.EssFiniteType k K]
variable {htrdeg : Algebra.trdeg k K = 1}

/-- The diagonal image closure lies in the Segre product. -/
theorem Y_subset_product (D : ProjectiveDiagonalModel htrdeg) :
    D.Y ⊆ segreProduct D.M₀.projectiveClosure D.M₁.projectiveClosure := by
  rw [D.Y_eq_closure_range_diagonal]
  apply closure_minimal
  · rintro _ ⟨x, rfl⟩
    exact (D.diagonal x).2
  · exact D.productIsProjVariety.2

/-- Inclusion of the projective diagonal model into the Segre product. -/
noncomputable def productInclusion (D : ProjectiveDiagonalModel htrdeg) :
    VarietyHom (Variety.ofProjective D.isProjVariety)
      (Variety.ofProjective D.productIsProjVariety) :=
  inclHom D.productIsProjVariety.isQuasiProjVariety
    D.isProjVariety.isQuasiProjVariety D.Y_subset_product

/-- Corestricting the diagonal to its image closure and then including it back
into the product recovers the original diagonal morphism. -/
theorem productInclusion_comp_φ (D : ProjectiveDiagonalModel htrdeg) :
    D.productInclusion.comp D.φ = D.diagonal := by
  apply VarietyHom.ext
  funext x
  apply Subtype.ext
  exact D.φ_val x

/-- The first product projection restricted to the diagonal model. -/
noncomputable def projection₀ (D : ProjectiveDiagonalModel htrdeg) :
    VarietyHom (Variety.ofProjective D.isProjVariety)
      (Variety.ofProjective D.M₀.projectiveClosure_isProjVariety) :=
  D.productFst.comp D.productInclusion

/-- The second product projection restricted to the diagonal model. -/
noncomputable def projection₁ (D : ProjectiveDiagonalModel htrdeg) :
    VarietyHom (Variety.ofProjective D.isProjVariety)
      (Variety.ofProjective D.M₁.projectiveClosure_isProjVariety) :=
  D.productSnd.comp D.productInclusion

/-- The first restricted projection composed with the dense diagonal is the
first projective chart extension. -/
theorem projection₀_comp_φ (D : ProjectiveDiagonalModel htrdeg) :
    D.projection₀.comp D.φ = D.Φ₀ := by
  rw [projection₀, VarietyHom.comp_assoc, D.productInclusion_comp_φ,
    D.productFst_comp_diagonal]

/-- The second restricted projection composed with the dense diagonal is the
second projective chart extension. -/
theorem projection₁_comp_φ (D : ProjectiveDiagonalModel htrdeg) :
    D.projection₁.comp D.φ = D.Φ₁ := by
  rw [projection₁, VarietyHom.comp_assoc, D.productInclusion_comp_φ,
    D.productSnd_comp_diagonal]

end ProjectiveDiagonalModel

/-- **Hartshorne I.6, construction in the proof of Theorem 6.9.**  The two
projective chart extensions define a diagonal morphism into their Segre
product.  The closure of its image is projective, and the corestricted
diagonal has dense image. -/
theorem exists_dense_projective_diagonal [IsAlgClosed k]
    [Algebra.EssFiniteType k K]
    (htrdeg : Algebra.trdeg k K = 1) :
    Nonempty (ProjectiveDiagonalModel htrdeg) := by
  classical
  obtain ⟨M₀, M₁, hcover, Φ₀, Φ₁, hΦ₀, hΦ₁⟩ :=
    exists_two_projective_chart_extensions htrdeg
  let _ := M₀.finite_ι
  let _ := M₁.finite_ι
  let hProd :
      IsProjVariety (segreProduct M₀.projectiveClosure M₁.projectiveClosure) :=
    isProjVariety_segreProduct M₀.projectiveClosure_isProjVariety
      M₁.projectiveClosure_isProjVariety
  let p₀ : VarietyHom (Variety.ofProjective hProd)
      (Variety.ofProjective M₀.projectiveClosure_isProjVariety) :=
    segreProductFstHom M₀.projectiveClosure_isProjVariety.isQuasiProjVariety
      hProd.isQuasiProjVariety
  let p₁ : VarietyHom (Variety.ofProjective hProd)
      (Variety.ofProjective M₁.projectiveClosure_isProjVariety) :=
    segreProductSndHom M₁.projectiveClosure_isProjVariety.isQuasiProjVariety
      hProd.isQuasiProjVariety
  have hp₀fun : p₀.toFun = segreProductFst :=
    segreProductFstHom_toFun
      M₀.projectiveClosure_isProjVariety.isQuasiProjVariety
      hProd.isQuasiProjVariety
  have hp₁fun : p₁.toFun = segreProductSnd :=
    segreProductSndHom_toFun
      M₁.projectiveClosure_isProjVariety.isQuasiProjVariety
      hProd.isQuasiProjVariety
  let diagonal : VarietyHom
      (abstractNonsingularCurveOfFunctionField htrdeg)
      (Variety.ofProjective hProd) :=
    segreProductLiftHom
      M₀.projectiveClosure_isProjVariety.isQuasiProjVariety
      M₁.projectiveClosure_isProjVariety.isQuasiProjVariety
      hProd.isQuasiProjVariety Φ₀ Φ₁
  have hdiagonal : diagonal.toFun =
      fun x => segreProductMk (Φ₀ x) (Φ₁ x) :=
    segreProductLiftHom_toFun
      M₀.projectiveClosure_isProjVariety.isQuasiProjVariety
      M₁.projectiveClosure_isProjVariety.isQuasiProjVariety
      hProd.isQuasiProjVariety Φ₀ Φ₁
  have hp₀ : p₀.comp diagonal = Φ₀ :=
    segreProductFstHom_comp_lift
      M₀.projectiveClosure_isProjVariety.isQuasiProjVariety
      M₁.projectiveClosure_isProjVariety.isQuasiProjVariety
      hProd.isQuasiProjVariety Φ₀ Φ₁
  have hp₁ : p₁.comp diagonal = Φ₁ :=
    segreProductSndHom_comp_lift
      M₀.projectiveClosure_isProjVariety.isQuasiProjVariety
      M₁.projectiveClosure_isProjVariety.isQuasiProjVariety
      hProd.isQuasiProjVariety Φ₀ Φ₁
  let hY := closure_range_isProjVariety hProd diagonal
  let φ := codRestrictClosure hProd diagonal
  refine ⟨{
    M₀ := M₀
    M₁ := M₁
    cover := hcover
    Φ₀ := Φ₀
    Φ₁ := Φ₁
    extension₀ := hΦ₀
    extension₁ := hΦ₁
    productIsProjVariety := hProd
    productFst := p₀
    productSnd := p₁
    productFst_toFun := hp₀fun
    productSnd_toFun := hp₁fun
    diagonal := diagonal
    diagonal_toFun := hdiagonal
    productFst_comp_diagonal := hp₀
    productSnd_comp_diagonal := hp₁
    Y := closure (Set.range fun x => (diagonal x).1)
    Y_eq_closure_range_diagonal := rfl
    isProjVariety := hY
    φ := φ
    φ_val := fun x => by
      change ((codRestrictClosure hProd diagonal) x).1 = (diagonal x).1
      exact congrArg Subtype.val
        (congrFun (codRestrictClosure_toFun hProd diagonal) x)
    φ_dense := codRestrictClosure_dense hProd diagonal
  }⟩

end ValuationSpace

end

end Hartshorne
