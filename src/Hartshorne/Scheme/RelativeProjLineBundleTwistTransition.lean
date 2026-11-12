/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.RelativeProjLineBundleTwistFrames

/-!
# Transition functions of the frames of `𝒪_{Proj_X (S · L)}(1)`

Hartshorne, *Algebraic Geometry*, II.7, Lemma 7.9 (p. 161), the formula for `𝒪(1)`.

For two charts `(U, e, s)`, `(U, e', t)` over the same affine `U` (frames `e`, `e' = v • e` of `L`,
elements `s, t ∈ S(U)₁`), the frame `t ⊗ e'` of `𝒪_{Proj_X (S · L)}(1)` is `(t ⊗ e')/(s ⊗ e)` times
`s ⊗ e` over the open `D₊(s ⊗ e)`, and the frame `φ^* t ⊗ π^* e'` of
`φ^* 𝒪_{Proj_X S}(1) ⊗ π^* L` is `φ^#(t/s) · π^# v` times `φ^* s ⊗ π^* e`; the two coefficients
agree since `t ⊗ e' = v · (t ⊗ e)` (`exists_eq_smul_samePiece`). Restricting two arbitrary charts to
an affine open basic in both reduces the overlaps to this case (`exists_eq_smul_overlap`), and the
frames glue to an isomorphism (`nonempty_iso_tensorModule`).
-/

universe u

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

open scoped TensorProduct

namespace Hartshorne

namespace QuasiCoherentGradedAlgebra

attribute [local instance] sectionsAlgebra

variable {X : Scheme.{u}} {S : QuasiCoherentGradedAlgebra X} {L : X.Modules} (hL : L.IsInvertible)

set_option backward.isDefEq.respectTransparency false in
/-- If `e' = v • e`, then the section of `Sym¹ L` given by `e'` is `v` times that given by `e`. -/
theorem frameGenerator_eq_smul {U : X.AffineZariskiSite} {e e' : ULift.{u} (Fin 1) → Γ(L, U.1)}
    (v : Γ(X, U.1)) (hv : e' default = v • e default) :
    frameGenerator (hL := hL) e' =
      algebraMap Γ(X, U.1) ((lineBundleSym L hL).obj.obj (.op U)) v *
        frameGenerator (hL := hL) e := by
  change L.chartRingHom U.1 e' (MvPolynomial.rename ULift.up (MvPolynomial.X 0)) =
    _ * L.chartRingHom U.1 e (MvPolynomial.rename ULift.up (MvPolynomial.X 0))
  rw [MvPolynomial.rename_X, Scheme.Modules.chartRingHom_X, Scheme.Modules.chartRingHom_X]
  exact (congrArg _ hv).trans (Scheme.Modules.symDegreeOne_smul _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- If `e' = v • e`, then `t ⊗ e' = v · (t ⊗ e)` in `(S · L)(U)` for `t ∈ S(U)₁`. -/
theorem ofGenerator_eq_smul {U : X.AffineZariskiSite} {e e' : ULift.{u} (Fin 1) → Γ(L, U.1)}
    (v : Γ(X, U.1)) (hv : e' default = v • e default) {t : S.obj.obj (.op U)}
    (ht : t ∈ S.grading U 1) :
    SegreProduct.ofGenerator Γ(X, U.1) (S.grading U) ((lineBundleSym L hL).grading U)
        (frameGenerator_mem (hL := hL) (e := e')) t =
      algebraMap Γ(X, U.1) (S.diagonalSections (lineBundleSym L hL) U) v *
        SegreProduct.ofGenerator Γ(X, U.1) (S.grading U) ((lineBundleSym L hL).grading U)
          (frameGenerator_mem (hL := hL) (e := e)) t := by
  apply Subtype.ext
  change (SegreProduct.ofGenerator Γ(X, U.1) (S.grading U) ((lineBundleSym L hL).grading U)
        (frameGenerator_mem (hL := hL) (e := e')) t : S.obj.obj (.op U) ⊗[Γ(X, U.1)]
          (lineBundleSym L hL).obj.obj (.op U)) =
    algebraMap Γ(X, U.1) _ v * (SegreProduct.ofGenerator Γ(X, U.1) (S.grading U)
      ((lineBundleSym L hL).grading U) (frameGenerator_mem (hL := hL) (e := e)) t :
        S.obj.obj (.op U) ⊗[Γ(X, U.1)] (lineBundleSym L hL).obj.obj (.op U))
  rw [SegreProduct.coe_ofGenerator_of_mem _ _ _ ht, SegreProduct.coe_ofGenerator_of_mem _ _ _ ht,
    pow_one, pow_one, frameGenerator_eq_smul hL v hv, ← Algebra.smul_def, ← Algebra.smul_def,
    TensorProduct.tmul_smul]

/-- For an open immersion `f`, restricting `(f.appIso W).inv x` along `f` gives back `x`. -/
theorem appLE_image_appIso_inv_apply {P Y : Scheme.{u}} (f : P ⟶ Y) [IsOpenImmersion f]
    (W : P.Opens) (h : W ≤ f ⁻¹ᵁ (f ''ᵁ W)) (x : Γ(P, W)) :
    f.appLE (f ''ᵁ W) W h ((f.appIso W).inv x) = x := by
  rw [← Scheme.Hom.appIso_hom']
  exact Iso.inv_hom_id_apply _ _
/-- Pulling back the section `x ∈ A_{(s)}` of `D₊(s)` along `Proj B → Proj A` gives the image
of `x` in `B_{(f s)}`. -/

theorem map_appLE_awayToSection {A B σ τ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ}
    {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) {i : ℕ} {s : A}
    (hs : s ∈ 𝒜 i) (h : Proj.basicOpen ℬ (f s) ≤ Proj.map f hf ⁻¹ᵁ Proj.basicOpen 𝒜 s)
    (x : HomogeneousLocalization.Away 𝒜 s) :
    (Proj.map f hf).appLE (Proj.basicOpen 𝒜 s) (Proj.basicOpen ℬ (f s)) h
        (Proj.awayToSection 𝒜 s x) =
      Proj.awayToSection ℬ (f s) (HomogeneousLocalization.Away.map f s x) :=
  ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE f hf hs) x

/-- If `x = c • y` near `W ⊆ W'`, then the pulled-back sections `η x`, `η y` satisfy the same
relation with `f^# c` on any open inside `f⁻¹ W`. -/
theorem etaSec_map_eq_smul {Y Z : Scheme.{u}} (f : Y ⟶ Z) (M : Z.Modules) {W W' : Z.Opens}
    (hW : W ≤ W') {O : Y.Opens} (hO : O ≤ f ⁻¹ᵁ W) (x y : Γ(M, W')) (c : Γ(Z, W))
    (hxy : M.presheaf.map (homOfLE hW).op x = c • M.presheaf.map (homOfLE hW).op y) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE (hO.trans (f.preimage_mono hW))).op
        (Ringed.etaSec (φ := f.toRingCatSheafHom) x) =
      Y.presheaf.map (homOfLE hO).op (f.app W c) •
        ((Scheme.Modules.pullback f).obj M).presheaf.map
          (homOfLE (hO.trans (f.preimage_mono hW))).op
          (Ringed.etaSec (φ := f.toRingCatSheafHom) y) := by
  refine ((Scheme.Modules.map_map_homOfLE _ (f.preimage_mono hW) hO _).symm.trans ?_).trans
    (congrArg _ (Scheme.Modules.map_map_homOfLE _ (f.preimage_mono hW) hO _))
  refine (congrArg (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hO).op)
    (Ringed.etaSec_restrict (φ := f.toRingCatSheafHom) hW x).symm).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => Y.presheaf.map (homOfLE hO).op (f.app W c) •
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hO).op z)
      (Ringed.etaSec_restrict (φ := f.toRingCatSheafHom) hW y))
  dsimp only
  refine (congrArg (fun z => ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hO).op
    (Ringed.etaSec (φ := f.toRingCatSheafHom) z)) hxy).trans ?_
  refine (congrArg (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hO).op)
    (Ringed.etaSec_smul (φ := f.toRingCatSheafHom) c
      (M.presheaf.map (homOfLE hW).op y))).trans ?_
  exact Scheme.Modules.map_smul _ _ _ _

/-- Transport of a transition relation along restrictions: if `x_i, x_j` restrict to `x_i', x_j'`
on `P` and `x_j' = c • x_i'` on `O_k ⊆ P`, then the same holds, with `c|_O`, for the restrictions of
`x_i|_{O_i}, x_j|_{O_j}` to any `O ⊆ O_i ∩ O_j ∩ O_k`. -/
theorem map_eq_smul_of_restrict {Y : Scheme.{u}} (F : Y.Modules) {Pi Pj P Oi Oj Ok O : Y.Opens}
    (hi : Oi ≤ Pi) (hj : Oj ≤ Pj) (hPi : P ≤ Pi) (hPj : P ≤ Pj) (hk : Ok ≤ P)
    (hO : O ≤ Oi ⊓ Oj) (hOk : O ≤ Ok) (xi : Γ(F, Pi)) (xj : Γ(F, Pj)) (xi' xj' : Γ(F, P))
    (hxi : F.presheaf.map (homOfLE hPi).op xi = xi')
    (hxj : F.presheaf.map (homOfLE hPj).op xj = xj') (c : Γ(Y, Ok))
    (hc : F.presheaf.map (homOfLE hk).op xj' = c • F.presheaf.map (homOfLE hk).op xi') :
    F.presheaf.map (homOfLE (hO.trans inf_le_right)).op (F.presheaf.map (homOfLE hj).op xj) =
      Y.presheaf.map (homOfLE hOk).op c •
        F.presheaf.map (homOfLE (hO.trans inf_le_left)).op (F.presheaf.map (homOfLE hi).op xi) := by
  rw [Scheme.Modules.map_map_homOfLE, Scheme.Modules.map_map_homOfLE,
    ← Scheme.Modules.map_map_homOfLE F hPj (hOk.trans hk), hxj,
    ← Scheme.Modules.map_map_homOfLE F hPi (hOk.trans hk), hxi,
    ← Scheme.Modules.map_map_homOfLE F hk hOk, hc, Scheme.Modules.map_smul,
    Scheme.Modules.map_map_homOfLE]

namespace TwistChart

set_option backward.isDefEq.respectTransparency false in
/-- In `(S · L)(U)_{(s ⊗ e)}`, the product of `(t ⊗ e)/(s ⊗ e)` with `v/1` is
`(t ⊗ e')/(s ⊗ e)` when `e' = v • e`. -/
theorem away_map_gen_mul (i : TwistChart S L) {e' : ULift.{u} (Fin 1) → Γ(L, i.U.1)}
    (v : Γ(X, i.U.1)) (hv : e' default = v • i.e default) {t : S.obj.obj (.op i.U)}
    (ht : t ∈ S.grading i.U 1) :
    HomogeneousLocalization.Away.map (i.gen hL) i.s
        (HomogeneousLocalization.Away.mk (S.grading i.U) i.hs 1 t (by rwa [smul_eq_mul, mul_one])) *
      HomogeneousLocalization.fromZeroRingHom _ _ ((S.lineBundleTwist L hL).toZero i.U v) =
    HomogeneousLocalization.Away.mk _ (i.gen_mem hL) 1
      (SegreProduct.ofGenerator Γ(X, i.U.1) (S.grading i.U) ((lineBundleSym L hL).grading i.U)
        (frameGenerator_mem (hL := hL) (e := e')) t)
      (by rw [smul_eq_mul, mul_one]; exact (SegreProduct.ofGenerator _ _ _ _).map_mem ht) := by
  rw [HomogeneousLocalization.Away.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]
  change _ * Localization.mk _ 1 = _
  rw [Localization.mk_mul, mul_one]
  congr 1
  rw [ofGenerator_eq_smul hL v hv ht, mul_comm]
  rfl

/-- The open of a chart lies over the affine open `U` of the chart. -/
theorem opens_le_base (i : TwistChart S L) :
    i.opens hL ≤ (S.lineBundleTwist L hL).relProjToBase ⁻¹ᵁ i.U.1 :=
  (i.opens_le_piece hL).trans (i.piece_le_base hL)

set_option backward.isDefEq.respectTransparency false in
/-- **The transition scalar**: over the open of a chart `(U, e, s)`, the function
`(t ⊗ e')/(s ⊗ e)` is the product of `φ^#(t/s)` and `π^# v`, when `e' = v • e`. -/
theorem appIso_inv_awayToSection_eq_mul (i : TwistChart S L)
    {e' : ULift.{u} (Fin 1) → Γ(L, i.U.1)} (v : Γ(X, i.U.1)) (hv : e' default = v • i.e default)
    {t : S.obj.obj (.op i.U)} (ht : t ∈ S.grading i.U 1) :
    (((S.lineBundleTwist L hL).projι i.U).appIso (Proj.basicOpen _ (i.gen hL i.s))).inv
        (Proj.awayToSection _ (i.gen hL i.s) (HomogeneousLocalization.Away.mk _ (i.gen_mem hL) 1
          (SegreProduct.ofGenerator Γ(X, i.U.1) (S.grading i.U) ((lineBundleSym L hL).grading i.U)
            (frameGenerator_mem (hL := hL) (e := e')) t)
          (by rw [smul_eq_mul, mul_one]; exact (SegreProduct.ofGenerator _ _ _ _).map_mem ht))) =
      (S.lineBundleTwist L hL).relProj.presheaf.map (homOfLE (i.opens_le_preimage hL)).op
          ((S.lineBundleTwistHom hL).app _ (((S.projι i.U).appIso (Proj.basicOpen _ i.s)).inv
            (Proj.awayToSection _ i.s (HomogeneousLocalization.Away.mk _ i.hs 1 t
              (by rwa [smul_eq_mul, mul_one]))))) *
        (S.lineBundleTwist L hL).relProj.presheaf.map (homOfLE (i.opens_le_base hL)).op
          ((S.lineBundleTwist L hL).relProjToBase.app i.U.1 v) := by
  apply (ConcreteCategory.bijective_of_isIso
    (((S.lineBundleTwist L hL).projι i.U).appIso (Proj.basicOpen _ (i.gen hL i.s))).hom).1
  obtain ⟨h, hφ⟩ := i.projι_lineBundleTwistHom_eq hL
  have h1 := appIso_hom_map_app ((S.lineBundleTwist L hL).projι i.U) (S.lineBundleTwistHom hL)
    (Proj.basicOpen _ (i.gen hL i.s)) _ (i.opens_le_preimage hL) (by
      rw [hφ]; exact fun z hz => ⟨_, hz, rfl⟩) (((S.projι i.U).appIso (Proj.basicOpen _ i.s)).inv
            (Proj.awayToSection _ i.s (HomogeneousLocalization.Away.mk _ i.hs 1 t
              (by rwa [smul_eq_mul, mul_one]))))
  have h2 := appIso_hom_map_app ((S.lineBundleTwist L hL).projι i.U)
    (S.lineBundleTwist L hL).relProjToBase (Proj.basicOpen _ (i.gen hL i.s)) i.U.1
      (i.opens_le_base hL) (fun z _ => (i.piece_le_base hL) ⟨z, trivial, rfl⟩) v
  rw [Iso.inv_hom_id_apply, map_mul]
  refine Eq.trans ?_ (congrArg₂ (· * ·) h1.symm h2.symm)
  rw [projι_relProjToBase_appLE (hx := i.gen_mem hL), appLE_eq_of_eq hφ]
  have e₂ : Proj.basicOpen _ (i.gen hL i.s) ≤ Proj.map (i.gen hL) h ⁻¹ᵁ Proj.basicOpen _ i.s :=
    le_of_eq (Proj.map_preimage_basicOpen _ _ _).symm
  rw [← Scheme.Hom.appLE_comp_appLE (Proj.map (i.gen hL) h) (S.projι i.U) _
    (Proj.basicOpen _ i.s) _ (Scheme.Hom.preimage_image_eq _ _).ge e₂]
  rw [CommRingCat.comp_apply, appLE_image_appIso_inv_apply]
  have h3 := map_appLE_awayToSection (i.gen hL) h i.hs e₂
    (HomogeneousLocalization.Away.mk _ i.hs 1 t (by rwa [smul_eq_mul, mul_one]))
  refine Eq.trans ?_ (congrArg (· * _) h3.symm)
  refine Eq.trans ?_ (map_mul _ _ _)
  exact congrArg _ (away_map_gen_mul hL i v hv ht).symm

variable (MT : (S.lineBundleTwist L hL).relProj.Modules)
  (αT : ∀ U, MT.restrict ((S.lineBundleTwist L hL).projι U) ≅
    (S.lineBundleTwist L hL).twistingSheaf 1 U)
  (MS : S.relProj.Modules) (αS : ∀ U, MS.restrict (S.projι U) ≅ S.twistingSheaf 1 U)

/-- The tensor product of sections is bilinear: `(r a) ⊗ (r' b) = (r r') (a ⊗ b)`. -/
theorem bilinear_smul_smul {Y : Scheme.{u}} {F G : Y.Modules} {W : Y.Opens} (r r' : Γ(Y, W))
    (a : Γ(F, W)) (b : Γ(G, W)) :
    (moduleSheafTensorBilinear F G).app (op W) (r • a) (r' • b) =
      @HSMul.hSMul Γ(Y, W) Γ(tensorModule F G, W) Γ(tensorModule F G, W) _ (r * r')
        ((moduleSheafTensorBilinear F G).app (op W) a b) := by
  refine (((moduleSheafTensorBilinear F G).app (op W) (r • a)).map_smul r' b).trans ?_
  refine (congrArg (fun x : Γ(tensorModule F G, W) => r' • x)
    (LinearMap.map_smul₂ ((moduleSheafTensorBilinear F G).app (op W)) r a b)).trans ?_
  exact (smul_smul (α := Γ(tensorModule F G, W)) r' r _).trans
    (congrArg (fun c : Γ(Y, W) => (c • _ : Γ(tensorModule F G, W))) (mul_comm r' r))

/-- **Transition on one piece, tensor side**: for two charts over the same affine `U`, with frames
`e' = v • e` and elements `s, t ∈ S(U)₁`, the section `φ^* t ⊗ π^* e'` is `φ^#(t/s) · π^# v` times
`φ^* s ⊗ π^* e` over the open of the first chart. -/
theorem bTop_restrict_eq_smul (i : TwistChart S L) {e' : ULift.{u} (Fin 1) → Γ(L, i.U.1)}
    (he' : Ringed.IsLocalFrame (R := X.sheaf) L i.U.1 e') (v : Γ(X, i.U.1))
    (hv : e' default = v • i.e default) {t : S.obj.obj (.op i.U)} (ht : t ∈ S.grading i.U 1) :
    (tensorModule (pullS hL MS) (pullL L hL)).presheaf.map (homOfLE (i.opens_le_piece hL)).op
        ((⟨i.U, e', he', t, ht⟩ : TwistChart S L).bTop hL MS αS) =
      ((S.lineBundleTwist L hL).relProj.presheaf.map (homOfLE (i.opens_le_preimage hL)).op
          ((S.lineBundleTwistHom hL).app _ (((S.projι i.U).appIso (Proj.basicOpen _ i.s)).inv
            (Proj.awayToSection _ i.s (HomogeneousLocalization.Away.mk _ i.hs 1 t
              (by rwa [smul_eq_mul, mul_one]))))) *
        (S.lineBundleTwist L hL).relProj.presheaf.map (homOfLE (i.opens_le_base hL)).op
          ((S.lineBundleTwist L hL).relProjToBase.app i.U.1 v)) • i.bSec hL MS αS := by
  have hS := etaSec_map_eq_smul (S.lineBundleTwistHom hL) MS
    (Scheme.Hom.image_mono _ (le_top : Proj.basicOpen (S.grading i.U) i.s ≤ ⊤))
    (i.opens_le_preimage hL) _ _ _ (pieceDegreeOneSection_eq_smul αS i.hs ht)
  have hL' := etaSec_map_eq_smul (S.lineBundleTwist L hL).relProjToBase L (le_refl i.U.1)
    (i.opens_le_base hL) (e' default) (i.e default) v (by
      simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
      exact hv)
  rw [bSec, bTop, bTop, tmul_section_restrict, tmul_section_restrict]
  refine (congrArg₂ (fun a b => (moduleSheafTensorBilinear _ _).app _ a b)
    ((Scheme.Modules.map_map_homOfLE _ _ _ _).trans hS)
    ((Scheme.Modules.map_map_homOfLE _ _ _ _).trans hL')).trans ?_
  refine (bilinear_smul_smul _ _ _ _).trans ?_
  exact congrArg _ (congrArg₂ (fun a b => (moduleSheafTensorBilinear _ _).app _ a b)
    (Scheme.Modules.map_map_homOfLE _ _ _ _).symm (Scheme.Modules.map_map_homOfLE _ _ _ _).symm)

variable {MT αT MS αS} in
/-- **Transition on one piece**: for two charts over the same affine `U` (frames `e`, `e'` of `L`
and `s, t ∈ S(U)₁`), over the open of the first chart the frames `t ⊗ e'` and `φ^* t ⊗ π^* e'`
are the same multiple of `s ⊗ e` and `φ^* s ⊗ π^* e`, respectively. -/
theorem exists_eq_smul_samePiece (i : TwistChart S L) {e' : ULift.{u} (Fin 1) → Γ(L, i.U.1)}
    (he' : Ringed.IsLocalFrame (R := X.sheaf) L i.U.1 e') {t : S.obj.obj (.op i.U)}
    (ht : t ∈ S.grading i.U 1) :
    ∃ c : Γ((S.lineBundleTwist L hL).relProj, i.opens hL),
      MT.presheaf.map (homOfLE (i.opens_le_piece hL)).op
          (pieceDegreeOneSection MT αT i.U ((⟨i.U, e', he', t, ht⟩ : TwistChart S L).gen_mem hL)) =
        c • i.aSec hL MT αT ∧
      (tensorModule (pullS hL MS) (pullL L hL)).presheaf.map (homOfLE (i.opens_le_piece hL)).op
          ((⟨i.U, e', he', t, ht⟩ : TwistChart S L).bTop hL MS αS) =
        c • i.bSec hL MS αS := by
  obtain ⟨v, hv⟩ := (IsTrivializingSection.of_isLocalFrame (ι := ULift.{u} (Fin 1))
    i.he).exists_eq_smul_section (e' default)
  refine ⟨_, pieceDegreeOneSection_eq_smul αT (i.gen_mem hL)
    ((⟨i.U, e', he', t, ht⟩ : TwistChart S L).gen_mem hL), ?_⟩
  refine (bTop_restrict_eq_smul hL MS αS i he' v hv ht).trans ?_
  exact congrArg (fun c : Γ((S.lineBundleTwist L hL).relProj, i.opens hL) => c • i.bSec hL MS αS)
    (appIso_inv_awayToSection_eq_mul hL i v hv ht).symm

variable {MT αT MS αS} in
/-- **Transitions on overlaps**: near every point of the intersection of the opens of two charts,
the two families of frames have the same transition function. -/
theorem exists_eq_smul_overlap (hαT : PieceIsosCompatible MT αT)
    (hαS : PieceIsosCompatible MS αS) (i j : TwistChart S L) (y : (S.lineBundleTwist L hL).relProj)
    (hy : y ∈ i.opens hL ⊓ j.opens hL) :
    ∃ (O : (S.lineBundleTwist L hL).relProj.Opens) (hO : O ≤ i.opens hL ⊓ j.opens hL), y ∈ O ∧
      ∃ c : Γ((S.lineBundleTwist L hL).relProj, O),
        MT.presheaf.map (homOfLE (hO.trans inf_le_right)).op (j.aSec hL MT αT) =
            c • MT.presheaf.map (homOfLE (hO.trans inf_le_left)).op (i.aSec hL MT αT) ∧
          (tensorModule (pullS hL MS) (pullL L hL)).presheaf.map
              (homOfLE (hO.trans inf_le_right)).op (j.bSec hL MS αS) =
            c • (tensorModule (pullS hL MS) (pullL L hL)).presheaf.map
              (homOfLE (hO.trans inf_le_left)).op (i.bSec hL MS αS) := by
  obtain ⟨f, g, hfg, hx⟩ := exists_basicOpen_le_affine_inter i.U.2 j.U.2
    ((S.lineBundleTwist L hL).relProjToBase y) ⟨i.opens_le_base hL hy.1, j.opens_le_base hL hy.2⟩
  let V : X.AffineZariskiSite := i.U.basicOpen f
  let fi : V ⟶ i.U := homOfLE (i.U.basicOpen_le f)
  let fj : V ⟶ j.U := homOfLE ⟨g, hfg.symm⟩
  have hyV : y ∈ (S.lineBundleTwist L hL).projι V ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, ← relProjToBase_preimage]
    exact hx
  let O := i.opens hL ⊓ j.opens hL ⊓ (S.lineBundleTwist L hL).projι V ''ᵁ ⊤
  have hOk : O ≤ (i.restrictChart fi).opens hL := fun z hz =>
    i.mem_opens_restrictChart hL fi hz.1.1 hz.2
  obtain ⟨c, hca, hcb⟩ := exists_eq_smul_samePiece hL (MT := MT) (αT := αT) (MS := MS) (αS := αS)
    (i.restrictChart fi) (j.restrictChart fj).he (j.restrictChart fj).hs
  refine ⟨O, inf_le_left, ⟨hy, hyV⟩,
    (S.lineBundleTwist L hL).relProj.presheaf.map (homOfLE hOk).op c, ?_, ?_⟩
  · exact map_eq_smul_of_restrict MT _ _ (piece_le_piece fi _) (piece_le_piece fj _)
      ((i.restrictChart fi).opens_le_piece hL) inf_le_left hOk _ _ _ _
      (restrict_pieceDegreeOneSection_gen hL hαT i fi)
      (restrict_pieceDegreeOneSection_gen hL hαT j fj) c hca
  · exact map_eq_smul_of_restrict _ _ _ (piece_le_piece fi _) (piece_le_piece fj _)
      ((i.restrictChart fi).opens_le_piece hL) inf_le_left hOk _ _ _ _
      (restrict_bTop hL hαS i fi) (restrict_bTop hL hαS j fj) c hcb

variable {MT αT MS αS} in
/-- **Assembly**: a module `M_T` on `Proj_X (S · L)` and a module `M_S` on `Proj_X S`, with
compatible isomorphisms to the twisting sheaves `𝒪(1)` of the affine pieces, satisfy
`M_T ≅ φ^* M_S ⊗ π^* L` when `S` is generated by `S₁`: the frames `s ⊗ e` and `φ^* s ⊗ π^* e` on
the opens of the charts have the same transition functions. -/
theorem nonempty_iso_tensorModule (hαT : PieceIsosCompatible MT αT)
    (hαS : PieceIsosCompatible MS αS) (hS : S.GeneratedInDegreeOne) :
    Nonempty (MT ≅ tensorModule (pullS hL MS) (pullL L hL)) :=
  nonempty_iso_of_isTrivializingSection_local (fun i : TwistChart S L => i.opens hL)
    (iSup_opens hL hS) (fun i => i.aSec hL MT αT) (fun i => i.bSec hL MS αS)
    (fun i => i.isTrivializingSection_aSec hL MT αT)
    (fun i => i.isTrivializingSection_bSec hL MS αS)
    (fun i j y hy => exists_eq_smul_overlap hL hαT hαS i j y hy)

end TwistChart

end QuasiCoherentGradedAlgebra

end Hartshorne
