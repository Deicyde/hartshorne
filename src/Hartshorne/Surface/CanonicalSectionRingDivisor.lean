/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Surface.CanonicalSectionRing
import Hartshorne.Scheme.TensorPowerSectionRingMap
import Hartshorne.Scheme.CartierDivisorSheafArithmetic
import Hartshorne.RingedSpace.ModuleGluing

/-!
# The canonical section ring through a canonical divisor

Hartshorne writes the canonical ring as `R(X, K) = ⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` for a canonical
divisor `K`, while `Hartshorne.CanonicalSectionRing` is defined through `ω_X^{⊗ n}`. A chosen
isomorphism `φ : 𝒪_X(K) ≅ ω_X` induces isomorphisms `𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n} ≅ ω_X^{⊗ n}`
(`AlgebraicGeometry.Scheme.CartierDivisor.nsmulSheafIso`, `Hartshorne.canonicalDivisorPowIso`),
and a graded ring isomorphism `⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n}) ≃+* R(X, K)`
(`Hartshorne.canonicalSectionRingEquivOfIso`).
-/

open CategoryTheory Opposite TopologicalSpace
open scoped DirectSum

namespace AlgebraicGeometry

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Scheme.CartierDivisor

open Hartshorne Hartshorne.Ringed

variable {X : Scheme.{u}}

theorem zero_restrict_top : (0 : X.CartierDivisor).restrict ⊤ =
    X.toCartierDivisorSheaf.hom.app (op ⊤)
      (Additive.ofMul (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))) := by
  rw [show (0 : X.CartierDivisor).restrict ⊤ = 0 from map_zero _]
  exact (map_zero _).symm

/-- The morphism `𝒪_X ⟶ 𝒪_X(0)`, `r ↦ r`. -/
def fromStructureZero : structureModule X.sheaf ⟶ (0 : X.CartierDivisor).sheafR :=
  modulesHomMk (fun U => (0 : X.CartierDivisor).generatorMap zero_restrict_top le_top)
    (fun U V i x => by
      apply Subtype.ext
      change X.toK V (X.presheaf.map (homOfLE i).op x) *
          X.totalQuotientSheaf.obj.map (homOfLE le_top).op
            (kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹) =
        X.totalQuotientSheaf.obj.map (homOfLE i).op (X.toK U x *
          X.totalQuotientSheaf.obj.map (homOfLE le_top).op
            (kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹))
      have h1 : kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹ = 1 := by
        rw [inv_one]
        exact Units.val_one
      rw [h1, map_one, mul_one]
      refine (toK_naturality i x).symm.trans (congrArg _ ?_)
      rw [map_one, mul_one])

theorem isIso_fromStructureZero : IsIso (fromStructureZero (X := X)) :=
  ModuleGluing.isIso_of_bijective _ fun U =>
    (0 : X.CartierDivisor).generatorMap_bijective zero_restrict_top (le_top : U.unop ≤ ⊤)

/-- **`𝒪_X(0) ≅ 𝒪_X`.** -/
def zeroSheafIso : (0 : X.CartierDivisor).sheafR ≅ structureModule X.sheaf :=
  haveI := isIso_fromStructureZero (X := X)
  (asIso fromStructureZero).symm

/-- **`𝒪_X(nD) ≅ 𝒪_X(D)^{⊗ n}`**, by induction on `n` from `𝒪_X(0) ≅ 𝒪_X` and
`𝒪_X(nD) ⊗ 𝒪_X(D) ≅ 𝒪_X(nD + D)`. -/
noncomputable def nsmulSheafIso (D : X.CartierDivisor) :
    ∀ n : ℕ, (n • D).sheafR ≅ moduleSheafTensorPower n D.sheafR
  | 0 => eqToIso (congrArg sheafR (zero_nsmul D)) ≪≫ zeroSheafIso ≪≫
      (moduleSheafTensorPowerZeroIso D.sheafR).symm
  | n + 1 => eqToIso (congrArg sheafR (succ_nsmul D n)) ≪≫ (tensorIso (n • D) D).symm ≪≫
      moduleSheafTensorIsoOfIso (nsmulSheafIso D n) (Iso.refl _) ≪≫
      (moduleSheafTensorPowerSuccIso D.sheafR n).symm

theorem kVal_eqToHom {D D' : X.CartierDivisor} (hD : D = D') (h : D.sheafR = D'.sheafR)
    {U : X.Opens} (s : D.sheafR.val.obj (op U)) :
    D'.kVal ((eqToHom h).val.app (op U) s) = D.kVal s := by
  subst hD
  rfl

theorem kVal_one_inv_top {U : X.Opens} :
    X.totalQuotientSheaf.obj.map (homOfLE (le_top : U ≤ ⊤)).op
      (kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹) = 1 := by
  have h1 : kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹ = 1 := by
    rw [inv_one]
    exact Units.val_one
  rw [h1, map_one]

/-- **`𝒪_X(kD) ≅ 𝒪_X(D)^{⊗ k}` is multiplication in `K_X`:** its inverse sends
`s₁ ⊗ ⋯ ⊗ s_k` to the product `s₁ ⋯ s_k` of rational functions. -/
theorem kVal_nsmulSheafIso_inv_tprod (D : X.CartierDivisor) : ∀ (k : ℕ) {U : X.Opens}
    (x : Fin k → D.sheafR.val.obj (op U)),
    (k • D).kVal ((D.nsmulSheafIso k).inv.val.app (op U)
      ((moduleSheafTensorPowerMultilinear k D.sheafR).app (op U) x)) = ∏ i, D.kVal (x i)
  | 0, U, x => by
    have h0 := moduleSheafTensorPowerHomEquiv_symm_tprod (tensorPowerZeroMultilinear D.sheafR) U x
    change (0 • D).kVal ((eqToHom (congrArg sheafR (zero_nsmul D)).symm).val.app (op U)
      (fromStructureZero.val.app (op U) ((moduleSheafTensorPowerZeroIso D.sheafR).hom.val.app
        (op U) ((moduleSheafTensorPowerMultilinear 0 D.sheafR).app (op U) x)))) = _
    rw [kVal_eqToHom (zero_nsmul D).symm, Fin.prod_univ_zero]
    refine (generatorMap_val 0 zero_restrict_top le_top _).trans ?_
    refine (congrArg (fun r => X.toK U r * X.totalQuotientSheaf.obj.map (homOfLE le_top).op
      (kUnitVal (1 : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))⁻¹)) h0).trans ?_
    change X.toK U 1 * _ = 1
    rw [map_one, kVal_one_inv_top, mul_one]
  | k + 1, U, x => by
    have e1 := moduleSheafTensorPowerHomEquiv_symm_tprod (tensorPowerSuccMultilinear D.sheafR k) U x
    have e2 := modulesTensorMap_tmul (D.nsmulSheafIso k).inv (𝟙 D.sheafR)
      ((moduleSheafTensorPowerMultilinear k D.sheafR).app (op U) (Fin.init x)) (x (Fin.last k))
    have e3 := mulHom_tmul (k • D) D ((D.nsmulSheafIso k).inv.val.app (op U)
      ((moduleSheafTensorPowerMultilinear k D.sheafR).app (op U) (Fin.init x))) (x (Fin.last k))
    have ih := kVal_nsmulSheafIso_inv_tprod D k (Fin.init x)
    have step : (D.nsmulSheafIso (k + 1)).inv.val.app (op U)
        ((moduleSheafTensorPowerMultilinear (k + 1) D.sheafR).app (op U) x) =
        (eqToHom (congrArg sheafR (succ_nsmul D k)).symm).val.app (op U)
          ((mulBilinear (k • D) D).app (op U) ((D.nsmulSheafIso k).inv.val.app (op U)
            ((moduleSheafTensorPowerMultilinear k D.sheafR).app (op U) (Fin.init x)))
            (x (Fin.last k))) := by
      change (eqToHom (congrArg sheafR (succ_nsmul D k)).symm).val.app (op U)
        ((tensorIso (k • D) D).hom.val.app (op U)
          ((moduleSheafTensorIsoOfIso (D.nsmulSheafIso k) (Iso.refl _)).inv.val.app (op U)
            ((moduleSheafTensorPowerSuccIso D.sheafR k).hom.val.app (op U)
              ((moduleSheafTensorPowerMultilinear (k + 1) D.sheafR).app (op U) x)))) = _
      congr 1
      refine (congrArg (fun z => (tensorIso (k • D) D).hom.val.app (op U)
        ((moduleSheafTensorIsoOfIso (D.nsmulSheafIso k) (Iso.refl _)).inv.val.app (op U) z))
        e1).trans ?_
      refine (congrArg (fun z => (tensorIso (k • D) D).hom.val.app (op U) z) e2).trans ?_
      exact e3
    rw [step, kVal_eqToHom (succ_nsmul D k).symm, Fin.prod_univ_castSucc]
    change (k • D).kVal _ * D.kVal (x (Fin.last k)) = _
    rw [ih]
    rfl

/-- The multiplication `𝒪_X(mD) × 𝒪_X(nD) → K_X`, `(s, t) ↦ s t`, as a bilinear map of
presheaves. -/
def mulTotalQuotientPresheafBilinear (D D' : X.CartierDivisor) :
    SheafAlgebraOperations.PresheafBilinear D.sheafR.val D'.sheafR.val X.totalQuotientModule.val :=
  ⟨(mulTotalQuotientBilinear D D').app, (mulTotalQuotientBilinear D D').naturality⟩

/-- **The isomorphisms `𝒪_X(kD) ≅ 𝒪_X(D)^{⊗ k}` turn the product of tensor powers into
multiplication of rational functions.** -/
theorem kVal_nsmulSheafIso_inv_mul (D : X.CartierDivisor) (m n : ℕ) (U : X.Opens)
    (a : TensorPowerSectionRing.Component D.sheafR (op U) m)
    (b : TensorPowerSectionRing.Component D.sheafR (op U) n) :
    ((m + n) • D).kVal ((D.nsmulSheafIso (m + n)).inv.val.app (op U)
        (TensorPowerSectionRing.mul D.sheafR (op U) a b)) =
      (m • D).kVal ((D.nsmulSheafIso m).inv.val.app (op U) a) *
        (n • D).kVal ((D.nsmulSheafIso n).inv.val.app (op U) b) := by
  have base : ∀ (V : X.Opens) (x : Fin m → D.sheafR.val.obj (op V))
      (y : Fin n → D.sheafR.val.obj (op V)),
      ((m + n) • D).kVal ((D.nsmulSheafIso (m + n)).inv.val.app (op V)
          (TensorPowerSectionRing.mul D.sheafR (op V)
            ((moduleSheafTensorPowerMultilinear m D.sheafR).app (op V) x)
            ((moduleSheafTensorPowerMultilinear n D.sheafR).app (op V) y))) =
        (m • D).kVal ((D.nsmulSheafIso m).inv.val.app (op V)
            ((moduleSheafTensorPowerMultilinear m D.sheafR).app (op V) x)) *
          (n • D).kVal ((D.nsmulSheafIso n).inv.val.app (op V)
            ((moduleSheafTensorPowerMultilinear n D.sheafR).app (op V) y)) := by
    intro V x y
    rw [TensorPowerSectionRing.mul_tprod, kVal_nsmulSheafIso_inv_tprod,
      kVal_nsmulSheafIso_inv_tprod, kVal_nsmulSheafIso_inv_tprod, Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  have key : (moduleSheafTensorPowerMul m D.sheafR n).postcomp
        ((D.nsmulSheafIso (m + n)).inv ≫ ((m + n) • D).sheafι).val =
      ((mulTotalQuotientPresheafBilinear (m • D) (n • D)).precomp
        (D.nsmulSheafIso m).inv.val (D.nsmulSheafIso n).inv.val) := by
    apply SheafAlgebraOperations.bilinear_ext_of_unit
    intro ⟨V⟩ p q
    have hL : (((moduleSheafTensorPowerMul m D.sheafR n).app (op V)).compl₁₂
        ((SheafAlgebraOperations.sheafifyUnit (moduleSheafTensorPowerPresheaf m D.sheafR)).app
          (op V)).hom
        ((SheafAlgebraOperations.sheafifyUnit (moduleSheafTensorPowerPresheaf n D.sheafR)).app
          (op V)).hom).compr₂
          (((D.nsmulSheafIso (m + n)).inv ≫ ((m + n) • D).sheafι).val.app (op V)).hom =
        ((mulTotalQuotientBilinear (m • D) (n • D)).app (op V)).compl₁₂
          (((D.nsmulSheafIso m).inv.val.app (op V)).hom ∘ₗ
            ((SheafAlgebraOperations.sheafifyUnit (moduleSheafTensorPowerPresheaf m D.sheafR)).app
              (op V)).hom)
          (((D.nsmulSheafIso n).inv.val.app (op V)).hom ∘ₗ
            ((SheafAlgebraOperations.sheafifyUnit (moduleSheafTensorPowerPresheaf n D.sheafR)).app
              (op V)).hom) := by
      refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
      refine PiTensorProduct.ext (MultilinearMap.ext fun y => ?_)
      exact base V x y
    exact congrArg (fun L => L p q) hL
  exact congrArg (fun γ => γ.app (op U) a b) key

end Scheme.CartierDivisor

end

end AlgebraicGeometry

namespace Hartshorne

open AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The isomorphisms `𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n} ≅ ω_X^{⊗ n}` induced by `φ : 𝒪_X(K) ≅ ω_X`. -/
noncomputable def canonicalDivisorPowIso {K : X.CartierDivisor} (φ : K.sheaf ≅ canonicalSheaf f)
    (n : ℕ) : (n • K).sheafR ≅ moduleSheafTensorPower (R := X.sheaf) n (canonicalSheaf f) :=
  K.nsmulSheafIso n ≪≫ TensorPowerSectionRing.powIso φ n

/-- The degree-`n` part `H⁰(X, 𝒪_X(K)^{⊗ n})` of the section ring of `𝒪_X(K)`. -/
abbrev divisorSectionRingComponent (K : X.CartierDivisor) (n : ℕ) : Type u :=
  TensorPowerSectionRing.Component (R := X.sheaf) K.sheaf (op ⊤) n

/-- The graded ring structure on `n ↦ H⁰(X, 𝒪_X(K)^{⊗ n})`. -/
noncomputable instance divisorSectionRingComponent.gRing (K : X.CartierDivisor) :
    DirectSum.GRing (divisorSectionRingComponent K) :=
  TensorPowerSectionRing.gRing (R := X.sheaf) K.sheaf (op ⊤)

/-- **The canonical section ring through a canonical divisor.** An isomorphism
`φ : 𝒪_X(K) ≅ ω_X` induces a graded ring isomorphism `⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n}) ≃+* R(X, K)`,
which in degree `n` is `H⁰(X, φ^{⊗ n})` (`canonicalSectionRingEquivOfIso_of`). -/
noncomputable def canonicalSectionRingEquivOfIso {K : X.CartierDivisor}
    (φ : K.sheaf ≅ canonicalSheaf f) :
    (⨁ n, divisorSectionRingComponent K n) ≃+* CanonicalSectionRing f :=
  TensorPowerSectionRing.ringEquiv φ (op ⊤)

theorem canonicalSectionRingEquivOfIso_of {K : X.CartierDivisor} (φ : K.sheaf ≅ canonicalSheaf f)
    (n : ℕ) (a : divisorSectionRingComponent K n) :
    canonicalSectionRingEquivOfIso f φ (DirectSum.of _ n a) =
      DirectSum.of _ n ((TensorPowerSectionRing.powIso φ n).hom.val.app (op ⊤) a) :=
  TensorPowerSectionRing.ringEquiv_of φ (op ⊤) n a

/-- The sections over `U` of an isomorphism of sheaves of modules, as an additive equivalence. -/
noncomputable def sectionsAddEquiv {A B : SheafOfModules.{u} (ringCatSheafOf X.sheaf)} (e : A ≅ B)
    (U : X.Opensᵒᵖ) : A.val.obj U ≃+ B.val.obj U where
  toFun := e.hom.val.app U
  invFun := e.inv.val.app U
  left_inv x := by
    change (e.hom ≫ e.inv).val.app U x = x
    rw [e.hom_inv_id]
    rfl
  right_inv x := by
    change (e.inv ≫ e.hom).val.app U x = x
    rw [e.inv_hom_id]
    rfl
  map_add' := map_add _

/-- Hartshorne's presentation `⨁_{n ≥ 0} H⁰(X, 𝒪_X(nK))` of the section ring of a divisor `K`.
Its ring structure (`DivisorMultipleSectionRing.instRing`) is transported from
`⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n})` along the isomorphisms `𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n}`
(`AlgebraicGeometry.Scheme.CartierDivisor.nsmulSheafIso`). The transported product is
multiplication of rational functions in `K_X`: the product of homogeneous elements `s` and `t` is
the homogeneous element `s t` (`DivisorMultipleSectionRing.of_mul_of`), and the unit is the
rational function `1` in degree `0` (`DivisorMultipleSectionRing.one_eq`). -/
def DivisorMultipleSectionRing (K : X.CartierDivisor) : Type u :=
  ⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤)

/-- The additive equivalence `⨁ₙ H⁰(X, 𝒪_X(nK)) ≃+ ⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n})`, degreewise
`H⁰(X, 𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n})`. -/
noncomputable def divisorMultipleSectionsAddEquiv (K : X.CartierDivisor) :
    (⨁ n : ℕ, (n • K).sheafR.val.obj (op ⊤)) ≃+ ⨁ n, divisorSectionRingComponent K n :=
  DFinsupp.mapRange.addEquiv fun n => sectionsAddEquiv (K.nsmulSheafIso n) (op ⊤)

noncomputable instance DivisorMultipleSectionRing.instRing (K : X.CartierDivisor) :
    Ring (DivisorMultipleSectionRing K) :=
  (divisorMultipleSectionsAddEquiv K).toEquiv.ring

/-- The ring isomorphism `⨁ₙ H⁰(X, 𝒪_X(nK)) ≃+* ⨁ₙ H⁰(X, 𝒪_X(K)^{⊗ n})`. -/
noncomputable def divisorMultipleSectionRingEquiv (K : X.CartierDivisor) :
    DivisorMultipleSectionRing K ≃+* ⨁ n, divisorSectionRingComponent K n :=
  (divisorMultipleSectionsAddEquiv K).toEquiv.ringEquiv

/-- The homogeneous element of degree `i` of `⨁ₙ H⁰(X, 𝒪_X(nK))` given by a section `s`. -/
noncomputable def DivisorMultipleSectionRing.of (K : X.CartierDivisor) (i : ℕ)
    (s : (i • K).sheafR.val.obj (op ⊤)) : DivisorMultipleSectionRing K :=
  DirectSum.of (fun i : ℕ => (i • K).sheafR.val.obj (op ⊤)) i s

theorem divisorMultipleSectionRingEquiv_of (K : X.CartierDivisor) (i : ℕ)
    (s : (i • K).sheafR.val.obj (op ⊤)) :
    divisorMultipleSectionRingEquiv K (DivisorMultipleSectionRing.of K i s) =
      DirectSum.of _ i ((K.nsmulSheafIso i).hom.val.app (op ⊤) s) :=
  DFinsupp.mapRange_single (hf := fun _ => map_zero _)

/-- **The product of `⨁ₙ H⁰(X, 𝒪_X(nK))` is multiplication of rational functions:** for sections
`s` of `𝒪_X(mK)` and `t` of `𝒪_X(nK)`, the product of the homogeneous elements is the homogeneous
element of degree `m + n` whose underlying rational function is `s t`. -/
theorem DivisorMultipleSectionRing.of_mul_of (K : X.CartierDivisor) {m n : ℕ}
    (s : (m • K).sheafR.val.obj (op ⊤)) (t : (n • K).sheafR.val.obj (op ⊤)) :
    ∃ u : ((m + n) • K).sheafR.val.obj (op ⊤),
      DivisorMultipleSectionRing.of K m s * DivisorMultipleSectionRing.of K n t =
        DivisorMultipleSectionRing.of K (m + n) u ∧
      ((m + n) • K).kVal u = (m • K).kVal s * (n • K).kVal t := by
  refine ⟨(K.nsmulSheafIso (m + n)).inv.val.app (op ⊤)
    (TensorPowerSectionRing.mul K.sheafR (op ⊤) ((K.nsmulSheafIso m).hom.val.app (op ⊤) s)
      ((K.nsmulSheafIso n).hom.val.app (op ⊤) t)), ?_, ?_⟩
  · apply (divisorMultipleSectionRingEquiv K).injective
    rw [map_mul, divisorMultipleSectionRingEquiv_of, divisorMultipleSectionRingEquiv_of,
      divisorMultipleSectionRingEquiv_of, DirectSum.of_mul_of]
    exact congrArg (DirectSum.of _ (m + n))
      ((sectionsAddEquiv (K.nsmulSheafIso (m + n)) (op ⊤)).apply_symm_apply _).symm
  · rw [Scheme.CartierDivisor.kVal_nsmulSheafIso_inv_mul]
    exact congrArg₂ (· * ·)
      (congrArg _ ((sectionsAddEquiv (K.nsmulSheafIso m) (op ⊤)).symm_apply_apply s))
      (congrArg _ ((sectionsAddEquiv (K.nsmulSheafIso n) (op ⊤)).symm_apply_apply t))

/-- **The unit of `⨁ₙ H⁰(X, 𝒪_X(nK))` is the rational function `1` in degree `0`.** -/
theorem DivisorMultipleSectionRing.one_eq (K : X.CartierDivisor) :
    ∃ u : ((0 : ℕ) • K).sheafR.val.obj (op ⊤),
      (1 : DivisorMultipleSectionRing K) = DivisorMultipleSectionRing.of K 0 u ∧
      ((0 : ℕ) • K).kVal u = 1 := by
  refine ⟨(K.nsmulSheafIso 0).inv.val.app (op ⊤) (TensorPowerSectionRing.oneSec K.sheafR (op ⊤)),
    ?_, ?_⟩
  · apply (divisorMultipleSectionRingEquiv K).injective
    rw [map_one, divisorMultipleSectionRingEquiv_of]
    exact congrArg (DirectSum.of _ 0)
      ((sectionsAddEquiv (K.nsmulSheafIso 0) (op ⊤)).apply_symm_apply _).symm
  · have e : TensorPowerSectionRing.oneSec K.sheafR (op ⊤) =
        (moduleSheafTensorPowerMultilinear 0 K.sheafR).app (op ⊤) Fin.elim0 :=
      congrArg _ TensorPower.gOne_def
    rw [e, Scheme.CartierDivisor.kVal_nsmulSheafIso_inv_tprod, Fin.prod_univ_zero]

/-- **A canonical divisor presents the canonical section ring.** For a Cartier divisor `K` and an
isomorphism `φ : 𝒪_X(K) ≅ ω_X` (for instance from `Hartshorne.exists_cartierDivisor_canonicalDivisorClass`),
there is a graded ring isomorphism `⨁ₙ H⁰(X, 𝒪_X(nK)) ≃+* R(X, K) = ⨁ₙ H⁰(X, ω_X^{⊗ n})`, which in
degree `n` is `H⁰` of the isomorphism `𝒪_X(nK) ≅ 𝒪_X(K)^{⊗ n} ≅ ω_X^{⊗ n}` induced by `φ`
(`canonicalSectionRingEquivOfDivisor_of`). -/
noncomputable def canonicalSectionRingEquivOfDivisor {K : X.CartierDivisor}
    (φ : K.sheaf ≅ canonicalSheaf f) : DivisorMultipleSectionRing K ≃+* CanonicalSectionRing f :=
  (divisorMultipleSectionRingEquiv K).trans (canonicalSectionRingEquivOfIso f φ)

theorem canonicalSectionRingEquivOfDivisor_of {K : X.CartierDivisor}
    (φ : K.sheaf ≅ canonicalSheaf f) (n : ℕ) (s : (n • K).sheafR.val.obj (op ⊤)) :
    canonicalSectionRingEquivOfDivisor f φ
        (DirectSum.of (fun n : ℕ => (n • K).sheafR.val.obj (op ⊤)) n s) =
      DirectSum.of _ n ((canonicalDivisorPowIso f φ n).hom.val.app (op ⊤) s) := by
  change canonicalSectionRingEquivOfIso f φ (divisorMultipleSectionsAddEquiv K
    (DirectSum.of _ n s)) = _
  rw [show divisorMultipleSectionsAddEquiv K (DirectSum.of _ n s) =
      DirectSum.of _ n ((K.nsmulSheafIso n).hom.val.app (op ⊤) s) from
    DFinsupp.mapRange_single (hf := fun _ => map_zero _), canonicalSectionRingEquivOfIso_of]
  rfl

end Hartshorne
