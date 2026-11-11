/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.CanonicalPullback
import Hartshorne.Scheme.Differentials.ProductOfNonsingularVarieties
import Hartshorne.Scheme.ExteriorPowerExactFiltration
import Hartshorne.Scheme.PicardPullback

/-!
# The canonical sheaf of a product

Hartshorne, *Algebraic Geometry*, II, Exercise 8.3(b) (pp. 187–188): if `X` and `Y` are
nonsingular varieties over `k`, then `ω_{X ×_k Y} ≅ p_X^* ω_X ⊗ p_Y^* ω_Y`.

## Proof

Using part (a) and Ex. II.5.16(d):

* `Ω_{X ×_k Y} ≅ p_X^* Ω_X ⊕ p_Y^* Ω_Y` (Exercise 8.3(a),
  `AlgebraicGeometry.Scheme.relativeDifferentialsProductIso`), so `Ω_{X ×_k Y}` sits in the split
  short exact sequence `0 → p_X^* Ω_X → Ω_{X ×_k Y} → p_Y^* Ω_Y → 0`;
* if `Ω_X`, `Ω_Y` are locally free of ranks `m`, `n`, so are their pullbacks, and Exercise
  II.5.16(d) (`Hartshorne.ExteriorPowerExactFiltration.exteriorPower_exact_det`) gives
  `⋀^{m+n} Ω_{X ×_k Y} ≅ ⋀^m p_X^* Ω_X ⊗ ⋀^n p_Y^* Ω_Y`;
* pullback commutes with exterior powers of locally free sheaves of finite rank
  (`Hartshorne.pullbackExteriorPowerIso`): the comparison map `f^*(⋀^r F) ⟶ ⋀^r (f^*F)`, adjoint
  to `x₁ ∧ ⋯ ∧ x_r ↦ η(x₁) ∧ ⋯ ∧ η(x_r)`, carries the frame `η(e_K)` of `f^*(⋀^r F)` to the
  frame `η(e)_K` of `⋀^r (f^*F)`;
* for nonsingular varieties of dimensions `m` and `n`, `Ω_X` and `Ω_Y` are locally free of ranks
  `m` and `n` (Theorem II.8.15), and `X ×_k Y` is a nonsingular variety of dimension `m + n`, so
  `ω_{X ×_k Y} = ⋀^{m+n} Ω_{X ×_k Y}`.

## Main results

* `Hartshorne.pullbackExteriorPowerIso`: `f^*(⋀^r F) ≅ ⋀^r (f^*F)` for `F` locally free of finite
  rank.
* `Hartshorne.nonempty_exteriorPower_relativeDifferentials_product_iso`: for schemes `X`, `Y` over
  any `S` with `Ω_{X/S}`, `Ω_{Y/S}` locally free of ranks `m`, `n`,
  `⋀^{m+n} Ω_{X ×_S Y / S} ≅ p_X^*(⋀^m Ω_{X/S}) ⊗ p_Y^*(⋀^n Ω_{Y/S})`.
* `Hartshorne.canonicalSheaf_product`: Hartshorne's Exercise II.8.3(b).
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

noncomputable section

namespace Hartshorne

section PullbackExteriorPower

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical comparison map `f^*(⋀^r F) ⟶ ⋀^r (f^*F)`, adjoint to the morphism
`⋀^r F ⟶ f_*(⋀^r (f^*F))`, `x₁ ∧ ⋯ ∧ x_r ↦ η(x₁) ∧ ⋯ ∧ η(x_r)`. -/
def pullbackExteriorPowerMap (F : Y.Modules) (r : ℕ) :
    (Scheme.Modules.pullback f).obj (moduleSheafExteriorPower (R := Y.sheaf) r F) ⟶
      moduleSheafExteriorPower (R := X.sheaf) r ((Scheme.Modules.pullback f).obj F) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (exteriorPowerPushforwardMap f (Ringed.pullbackUnit f.toRingCatSheafHom F) r)

variable {f} in
/-- The comparison map sends `η(x₁ ∧ ⋯ ∧ x_r)` to `η(x₁) ∧ ⋯ ∧ η(x_r)`. -/
lemma pullbackExteriorPowerMap_etaSec {F : Y.Modules} {r : ℕ} {U : Y.Opens}
    (m : Fin r → F.val.obj (op U)) :
    Ringed.sectionsMap (pullbackExteriorPowerMap f F r) (f ⁻¹ᵁ U)
        (Ringed.etaSec (φ := f.toRingCatSheafHom)
          ((moduleSheafExteriorPowerMultilinear r F).app (op U) m)) =
      (moduleSheafExteriorPowerMultilinear r ((Scheme.Modules.pullback f).obj F)).app
        (op (f ⁻¹ᵁ U)) (fun i => Ringed.etaSec (φ := f.toRingCatSheafHom) (m i)) := by
  have h : Ringed.pullbackUnit f.toRingCatSheafHom (moduleSheafExteriorPower (R := Y.sheaf) r F) ≫
      (Scheme.Modules.pushforward f).map (pullbackExteriorPowerMap f F r) =
        exteriorPowerPushforwardMap f (Ringed.pullbackUnit f.toRingCatSheafHom F) r :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  have h1 := ConcreteCategory.congr_hom (congrArg (fun φ => Ringed.sectionsMap φ U) h)
    ((moduleSheafExteriorPowerMultilinear r F).app (op U) m)
  have h2 := exteriorPowerPushforwardMap_wedge f (Ringed.pullbackUnit f.toRingCatSheafHom F) r
    (op U) m
  exact h1.trans h2

/-- **Pullback commutes with exterior powers.** For an `𝒪_Y`-module `F` locally free of finite
rank, the comparison map `f^*(⋀^r F) ⟶ ⋀^r (f^*F)` is an isomorphism. -/
theorem pullbackExteriorPowerMap_isIso {F : Y.Modules} {n : ℕ} (hF : F.IsLocallyFreeOfRank n)
    (r : ℕ) : IsIso (pullbackExteriorPowerMap f F r) := by
  classical
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at hF
  refine Ringed.modules_isIso_of_locally_bijective (R := X.sheaf) _ fun x => ?_
  obtain ⟨U, e, hx, he⟩ := Ringed.exists_isLocalFrame_of_isLocallyFreeOfRank hF (f.base x)
  have hsrc := Ringed.IsLocalFrame.pullback (φ := f.toRingCatSheafHom)
    (ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame F he r)
  have htgt := ExteriorPerfectPairing.isLocalFrame_exteriorPowerFrame _
    (Ringed.IsLocalFrame.pullback (φ := f.toRingCatSheafHom) he) r
  exact ⟨f ⁻¹ᵁ U, hx, fun V hV =>
    Ringed.IsLocalFrame.app_bijective_of_map _ hsrc htgt
      (fun _ => pullbackExteriorPowerMap_etaSec _) hV⟩

/-- **Pullback commutes with exterior powers.** For an `𝒪_Y`-module `F` locally free of finite
rank, the canonical isomorphism `f^*(⋀^r F) ≅ ⋀^r (f^*F)`. -/
def pullbackExteriorPowerIso {F : Y.Modules} {n : ℕ} (hF : F.IsLocallyFreeOfRank n) (r : ℕ) :
    (Scheme.Modules.pullback f).obj (moduleSheafExteriorPower (R := Y.sheaf) r F) ≅
      moduleSheafExteriorPower (R := X.sheaf) r ((Scheme.Modules.pullback f).obj F) :=
  haveI := pullbackExteriorPowerMap_isIso f hF r
  asIso (pullbackExteriorPowerMap f F r)

end PullbackExteriorPower

section Product

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-- **The top exterior power of the differentials of a product.** Let `X` and `Y` be schemes over
`S` with `Ω_{X/S}` and `Ω_{Y/S}` locally free of ranks `m` and `n`. Then
`⋀^{m+n} Ω_{(X ×_S Y)/S} ≅ p_X^*(⋀^m Ω_{X/S}) ⊗ p_Y^*(⋀^n Ω_{Y/S})`. -/
theorem nonempty_exteriorPower_relativeDifferentials_product_iso {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) {m n : ℕ}
    (hf : (Scheme.relativeDifferentials f).IsLocallyFreeOfRank m)
    (hg : (Scheme.relativeDifferentials g).IsLocallyFreeOfRank n) :
    Nonempty (@Iso (pullback f g).Modules _
      (moduleSheafExteriorPower (R := (pullback f g).sheaf) (m + n)
        (Scheme.relativeDifferentials (pullback.fst f g ≫ f)))
      (moduleSheafTensor (R := (pullback f g).sheaf)
        ((Scheme.Modules.pullback (pullback.fst f g)).obj
          (moduleSheafExteriorPower (R := X.sheaf) m (Scheme.relativeDifferentials f)))
        ((Scheme.Modules.pullback (pullback.snd f g)).obj
          (moduleSheafExteriorPower (R := Y.sheaf) n (Scheme.relativeDifferentials g))))) := by
  let A := (Scheme.Modules.pullback (pullback.fst f g)).obj (Scheme.relativeDifferentials f)
  let B := (Scheme.Modules.pullback (pullback.snd f g)).obj (Scheme.relativeDifferentials g)
  have hA : A.IsLocallyFreeOfRank m := ProductNonsingular.isLocallyFreeOfRank_pullback _ hf
  have hB : B.IsLocallyFreeOfRank n := ProductNonsingular.isLocallyFreeOfRank_pullback _ hg
  let e := Scheme.relativeDifferentialsProductIso f g
  have hΩ : (Scheme.relativeDifferentials (pullback.fst f g ≫ f)).IsLocallyFreeOfRank (m + n) := by
    intro z
    obtain ⟨W, hz, ⟨α⟩⟩ := ProductNonsingular.isLocallyFreeOfRank_biprod hA hB z
    exact ⟨W, hz, ⟨(Scheme.Modules.restrictFunctor W.ι).mapIso e ≪≫ α⟩⟩
  -- the split short exact sequence `0 → p_X^* Ω_X → Ω_{X ×_S Y} → p_Y^* Ω_Y → 0`
  let T : ShortComplex (pullback f g).Modules :=
    ShortComplex.mk (biprod.inl ≫ e.inv) (e.hom ≫ biprod.snd) (by simp)
  have hT : T.ShortExact := by
    have h := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
    refine ShortComplex.shortExact_of_iso ?_ h
    exact ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) (by simp [T]; rfl) (by simp [T]; rfl)
  rw [Scheme.Modules.isLocallyFreeOfRank_iff_ringed] at hA hB hΩ
  obtain ⟨φ⟩ := ExteriorPowerExactFiltration.exteriorPower_exact_det T hT hA hΩ hB
  exact ⟨φ ≪≫ Ringed.moduleSheafTensorIsoOfIso
    (pullbackExteriorPowerIso (pullback.fst f g) hf m).symm
    (pullbackExteriorPowerIso (pullback.snd f g) hg n).symm⟩

/-- **Hartshorne II, Exercise 8.3(b).** Let `k` be an algebraically closed field and let `X`, `Y`
be nonsingular varieties over `k` (integral, separated, of finite type, with regular local rings),
with projections `p_X`, `p_Y` from `X ×_k Y`. Then
`ω_{X ×_k Y} ≅ p_X^* ω_X ⊗ p_Y^* ω_Y`. -/
theorem canonicalSheaf_product {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral Y]
    (hX : FiniteType pX) (hY : FiniteType pY) [IsSeparated pX] [IsSeparated pY]
    (hXr : X.IsRegular) (hYr : Y.IsRegular) :
    Nonempty (@Iso (pullback pX pY).Modules _ (canonicalSheaf (pullback.fst pX pY ≫ pX))
      (moduleSheafTensor (R := (pullback pX pY).sheaf)
        ((Scheme.Modules.pullback (pullback.fst pX pY)).obj (canonicalSheaf pX))
        ((Scheme.Modules.pullback (pullback.snd pX pY)).obj (canonicalSheaf pY)))) := by
  have := hX.1; have := hY.1
  obtain ⟨m, hm⟩ := ProductNonsingular.exists_topologicalKrullDim_eq pX hX
  obtain ⟨n, hn⟩ := ProductNonsingular.exists_topologicalKrullDim_eq pY hY
  obtain ⟨-, -, -, -, hdim⟩ := product_nonsingular_variety pX pY hX hY hXr hYr
  have hmn : topologicalKrullDim ↑(pullback pX pY) = ((m + n : ℕ) : WithBot ℕ∞) := by
    rw [hdim, hm, hn]
    rfl
  rw [canonicalSheaf_eq _ hmn, canonicalSheaf_eq _ hm, canonicalSheaf_eq _ hn]
  exact nonempty_exteriorPower_relativeDifferentials_product_iso pX pY
    ((isRegular_iff_relativeDifferentials_isLocallyFreeOfRank pX hX m hm).1 hXr)
    ((isRegular_iff_relativeDifferentials_isLocallyFreeOfRank pY hY n hn).1 hYr)

end Product

end Hartshorne
