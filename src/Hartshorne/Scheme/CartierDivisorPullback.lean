/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.PicardPullback
import Hartshorne.Scheme.LocallyFactorialClassPicard
import Hartshorne.Scheme.AffineLineClassGroup

/-!
# Pulling back the invertible sheaf of a Cartier divisor

Let `f : X ⟶ Y` be a morphism of integral schemes sending the generic point to the generic point,
and let `f^♯ : K(Y) → K(X)` be the induced map of function fields
(`Scheme.Hom.genericFunctionFieldMap`). Let `D` be a Cartier divisor on `Y` and `E` a Cartier
divisor on `X` such that, near every point of `X`, `E` is given by the pullback `f^♯ g` of a local
equation `g` of `D`. Then `f^* O_Y(D) ≅ O_X(E)`, so the Picard pullback
(`Hartshorne.Ringed.Pic.pullback`) sends the class of `O_Y(D)` to the class of `O_X(E)`
(`AlgebraicGeometry.Scheme.picPullback_cartierDivisorSheaf`).

On integral separated Noetherian locally factorial schemes this gives the Weil-divisor form
(`AlgebraicGeometry.Scheme.picPullback_weilClassEquivPicard`): if a Weil divisor `A` on `Y` and a
Weil divisor `B` on `X` are, near every point, the divisors of a rational function `g` on `Y` and of
its pullback `f^♯ g` on `X`, then the pullback of the Picard class of `A` is the Picard class
of `B`.

## Proof

Sections of `O_Y(D)` are rational functions `s` with `s g` regular wherever `g` is a local
equation; the map `s ↦ f^♯ s` sends them to sections of `O_X(E)`, giving a morphism
`O_Y(D) ⟶ f_* O_X(E)`. Its adjoint `f^* O_Y(D) ⟶ O_X(E)` sends the pulled-back local generator
`g⁻¹` to the local generator `(f^♯ g)⁻¹`, so it is an isomorphism by the frame criterion.
For the Weil form, a Cartier divisor on a normal scheme whose Weil divisor is the divisor of `g`
on an open set is the principal divisor of `g` near every point of that set
(`AlgebraicGeometry.Scheme.CartierDivisor.exists_restrict_eq_principal`).
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- Two sections of `K_X` over an open set agree if they agree in the function field whenever
the open set contains the generic point. -/
theorem totalQuotientSheaf_ext [IsIntegral X] {W : X.Opens}
    {a b : X.totalQuotientSheaf.obj.obj (op W)}
    (h : ∀ hη : genericPoint X ∈ W,
      totalQuotientSheafEquivFunctionField W hη a = totalQuotientSheafEquivFunctionField W hη b) :
    a = b := by
  by_cases hη : genericPoint X ∈ W
  · exact (totalQuotientSheafEquivFunctionField W hη).injective (h hη)
  · have hW : W = ⊥ := opens_eq_bot_of_genericPoint_notMem hη
    have : Subsingleton (X.totalQuotientSheaf.obj.obj (op W)) :=
      CommRingCat.subsingleton_of_isTerminal (X.totalQuotientSheaf.isTerminalOfEqEmpty hW)
    exact Subsingleton.elim _ _

/-- The identification of sections of `K_X` with the function field sends a regular function to
its germ at the generic point. -/
theorem totalQuotientSheafEquivFunctionField_toK [IsIntegral X] (U : X.Opens)
    (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    totalQuotientSheafEquivFunctionField U h (X.toK U a) = X.presheaf.germ U (genericPoint X) h a :=
  totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf U h a

/-- The restriction of a global section of `K_X^*` corresponds to the same rational function. -/
theorem totalQuotientUnitsEquivFunctionField_restrict_top [IsIntegral X] {W : X.Opens}
    (hη : genericPoint X ∈ W) (g : X.totalQuotientUnitsSheaf.obj.obj (op ⊤)) :
    totalQuotientUnitsEquivFunctionField W hη
        (X.totalQuotientUnitsSheaf.obj.map (homOfLE le_top).op g) =
      totalQuotientUnitsEquivFunctionField ⊤ trivial g :=
  totalQuotientUnitsEquivFunctionField_map le_top hη g

/-- The restriction of a principal Cartier divisor to an open set is given by the restricted
equation. -/
theorem principalCartierDivisor_restrict (g : X.totalQuotientUnitsSheaf.obj.obj (op ⊤))
    (W : X.Opens) :
    (X.principalCartierDivisor g).restrict W = X.toCartierDivisorSheaf.hom.app (op W)
      (Additive.ofMul (X.totalQuotientUnitsSheaf.obj.map (homOfLE le_top).op g)) :=
  X.toCartierDivisorSheaf_naturality_apply _ _

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.CartierDivisor

variable {X : Scheme.{u}}

open Hartshorne.Ringed in
/-- On an open set carrying a local equation `f` of `D`, the inverse `f⁻¹` is a one-element
frame of `O_X(D)`. -/
theorem isLocalFrame_inv (D : X.CartierDivisor) {V₀ : X.Opens}
    {f : X.totalQuotientUnitsSheaf.obj.obj (op V₀)}
    (hf : D.restrict V₀ = X.toCartierDivisorSheaf.hom.app (op V₀) (Additive.ofMul f)) :
    IsLocalFrame (R := X.sheaf) D.sheaf V₀ (fun _ : PUnit.{u + 1} =>
      (⟨kUnitVal f⁻¹, show D.IsSection (kUnitVal f⁻¹) by
        simpa only [kMap_id] using D.isSection_inv hf (le_refl V₀)⟩ :
        D.sheaf.val.presheaf.obj (op V₀))) := by
  intro V hV
  have hfV := D.restrict_eq_of_le hV hf
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    funext i
    obtain rfl : i = PUnit.unit := rfl
    rw [localFrameMap_apply, Fintype.sum_unique] at ha
    have h1 : X.toK V (a PUnit.unit) * X.totalQuotientSheaf.obj.map (homOfLE hV).op
        (kUnitVal f⁻¹) = 0 := congrArg Subtype.val ha
    apply toK_injective
    have h2 := congrArg (· * X.totalQuotientSheaf.obj.map (homOfLE hV).op (kUnitVal f)) h1
    simp only [mul_assoc, ← map_mul, show kUnitVal f⁻¹ * kUnitVal f = 1 from Units.inv_mul _,
      map_one, mul_one, zero_mul] at h2
    rw [h2]
    exact (map_zero (X.toK V)).symm
  · intro t
    obtain ⟨r, hr⟩ := t.2 V le_rfl _ hfV
    refine ⟨fun _ => r, ?_⟩
    rw [localFrameMap_apply, Fintype.sum_unique]
    apply Subtype.ext
    change X.toK V r * X.totalQuotientSheaf.obj.map (homOfLE hV).op (kUnitVal f⁻¹) = t.1
    rw [hr, kMap_id, mul_assoc]
    change _ * (X.totalQuotientSheaf.obj.map (homOfLE hV).op (kUnitVal f) * _) = _
    rw [← map_mul, show kUnitVal f * kUnitVal f⁻¹ = 1 from Units.mul_inv _, map_one, mul_one]

end AlgebraicGeometry.Scheme.CartierDivisor

namespace AlgebraicGeometry.Scheme

section Pullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
  (hf : f.base (genericPoint X) = genericPoint Y)

include hf in
theorem genericPoint_mem_preimage_of_mem {U : Y.Opens} (h : genericPoint Y ∈ U) :
    genericPoint X ∈ f ⁻¹ᵁ U := by
  change f.base (genericPoint X) ∈ U
  rw [hf]
  exact h

include hf in
theorem genericPoint_mem_of_mem_preimage {U : Y.Opens} (h : genericPoint X ∈ f ⁻¹ᵁ U) :
    genericPoint Y ∈ U := by
  rw [← hf]
  exact h

/-- Pullback of rational functions sends the germ of a regular function to the germ of its
pullback. -/
theorem genericFunctionFieldMap_germ {U : Y.Opens} (hU : genericPoint Y ∈ U) (r : Γ(Y, U)) :
    f.genericFunctionFieldMap hf (Y.presheaf.germ U (genericPoint Y) hU r) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (genericPoint_mem_preimage_of_mem f hf hU)
        (f.app U r) := by
  have hU' := genericPoint_mem_preimage_of_mem f hf hU
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hU'⟩⟩
  have h1 := f.genericFunctionFieldMap_algebraMap hf (genericPoint X)
    (Y.presheaf.germ U (f.base (genericPoint X)) hU' r)
  rw [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.Hom.germ_stalkMap_apply,
    Scheme.algebraMap_germ_eq_germToFunctionField] at h1
  exact h1

/-- A rational function on `Y` as a global section of `K_Y^*`. -/
abbrev globalUnit (Y : Scheme.{u}) [IsIntegral Y] (g : Y.functionFieldˣ) :
    Y.totalQuotientUnitsSheaf.obj.obj (op ⊤) :=
  (totalQuotientUnitsEquivFunctionField ⊤ trivial).symm g

/-- Pullback of nonzero rational functions. -/
abbrev genericFunctionFieldUnitsMap (g : Y.functionFieldˣ) : X.functionFieldˣ :=
  Units.map (f.genericFunctionFieldMap hf).hom.toMonoidHom g

open Classical in
/-- Pullback of sections of the total quotient sheaf, through the function fields. -/
def totalQuotientPullback (U : Y.Opens) (s : Y.totalQuotientSheaf.obj.obj (op U)) :
    X.totalQuotientSheaf.obj.obj (op (f ⁻¹ᵁ U)) :=
  if h : genericPoint Y ∈ U then
    (totalQuotientSheafEquivFunctionField (f ⁻¹ᵁ U) (genericPoint_mem_preimage_of_mem f hf h)).symm
      (f.genericFunctionFieldMap hf (totalQuotientSheafEquivFunctionField U h s))
  else 0

theorem totalQuotientPullback_spec {U : Y.Opens} {W : X.Opens} (hWU : W ≤ f ⁻¹ᵁ U)
    (hη : genericPoint X ∈ W) (s : Y.totalQuotientSheaf.obj.obj (op U)) :
    totalQuotientSheafEquivFunctionField W hη
        (X.totalQuotientSheaf.obj.map (homOfLE hWU).op (totalQuotientPullback f hf U s)) =
      f.genericFunctionFieldMap hf (totalQuotientSheafEquivFunctionField U
        (genericPoint_mem_of_mem_preimage f hf (hWU hη)) s) := by
  rw [totalQuotientSheafEquivFunctionField_map hWU hη, totalQuotientPullback,
    dif_pos (genericPoint_mem_of_mem_preimage f hf (hWU hη)), RingEquiv.apply_symm_apply]

theorem totalQuotientPullback_spec' {U : Y.Opens} (hη : genericPoint X ∈ f ⁻¹ᵁ U)
    (s : Y.totalQuotientSheaf.obj.obj (op U)) :
    totalQuotientSheafEquivFunctionField (f ⁻¹ᵁ U) hη (totalQuotientPullback f hf U s) =
      f.genericFunctionFieldMap hf (totalQuotientSheafEquivFunctionField U
        (genericPoint_mem_of_mem_preimage f hf hη) s) := by
  have := totalQuotientPullback_spec f hf (le_refl (f ⁻¹ᵁ U)) hη s
  rwa [CartierDivisor.kMap_id] at this

theorem totalQuotientPullback_add (U : Y.Opens) (a b : Y.totalQuotientSheaf.obj.obj (op U)) :
    totalQuotientPullback f hf U (a + b) =
      totalQuotientPullback f hf U a + totalQuotientPullback f hf U b := by
  apply totalQuotientSheaf_ext
  intro hη
  rw [map_add, totalQuotientPullback_spec', totalQuotientPullback_spec',
    totalQuotientPullback_spec', map_add, map_add]

theorem totalQuotientPullback_toK_mul (U : Y.Opens) (c : Γ(Y, U))
    (a : Y.totalQuotientSheaf.obj.obj (op U)) :
    totalQuotientPullback f hf U (Y.toK U c * a) =
      X.toK (f ⁻¹ᵁ U) (f.app U c) * totalQuotientPullback f hf U a := by
  apply totalQuotientSheaf_ext
  intro hη
  rw [map_mul, totalQuotientPullback_spec', totalQuotientPullback_spec', map_mul, map_mul,
    totalQuotientSheafEquivFunctionField_toK, totalQuotientSheafEquivFunctionField_toK,
    genericFunctionFieldMap_germ]

theorem totalQuotientPullback_map {U V : Y.Opens} (i : V ≤ U)
    (a : Y.totalQuotientSheaf.obj.obj (op U)) :
    totalQuotientPullback f hf V (Y.totalQuotientSheaf.obj.map (homOfLE i).op a) =
      X.totalQuotientSheaf.obj.map (homOfLE (f.preimage_mono i)).op
        (totalQuotientPullback f hf U a) := by
  apply totalQuotientSheaf_ext
  intro hη
  rw [totalQuotientPullback_spec', totalQuotientPullback_spec,
    totalQuotientSheafEquivFunctionField_map]

variable {f hf} {D : Y.CartierDivisor} {E : X.CartierDivisor}

/-- The hypothesis that `E` is, near every point of `X`, given by the pullback of a local
equation of `D`. -/
def CartierPullbackData (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y)
    (D : Y.CartierDivisor) (E : X.CartierDivisor) : Prop :=
  ∀ x : X, ∃ (V : Y.Opens) (W : X.Opens) (g : Y.functionFieldˣ),
    x ∈ W ∧ W ≤ f ⁻¹ᵁ V ∧ D.restrict V = (Y.principalCartierDivisor (globalUnit Y g)).restrict V ∧
      E.restrict W =
        (X.principalCartierDivisor (globalUnit X (genericFunctionFieldUnitsMap f hf g))).restrict W

theorem isSection_totalQuotientPullback (hDE : CartierPullbackData f hf D E) {U : Y.Opens}
    {s : Y.totalQuotientSheaf.obj.obj (op U)} (hs : D.IsSection s) :
    E.IsSection (totalQuotientPullback f hf U s) := by
  apply E.isSection_of_locally
  intro x hx
  obtain ⟨V, W, g, hxW, hWV, hD, hE⟩ := hDE x
  have hV'U : V ⊓ U ≤ V := inf_le_left
  have hW' : W ⊓ f ⁻¹ᵁ U ≤ f ⁻¹ᵁ (V ⊓ U) := fun z hz => ⟨hWV hz.1, hz.2⟩
  have hηW : genericPoint X ∈ W ⊓ f ⁻¹ᵁ U := genericPoint_mem_opens_of_mem ⟨hxW, hx⟩
  have hηV : genericPoint Y ∈ V ⊓ U := genericPoint_mem_of_mem_preimage f hf (hW' hηW)
  obtain ⟨r, hr⟩ := hs (V ⊓ U) inf_le_right _
    (D.restrict_eq_of_le hV'U (hD.trans (principalCartierDivisor_restrict _ V)))
  refine ⟨W ⊓ f ⁻¹ᵁ U, inf_le_right, X.totalQuotientUnitsSheaf.obj.map (homOfLE le_top).op
    (globalUnit X (genericFunctionFieldUnitsMap f hf g)), ⟨hxW, hx⟩,
    (E.restrict_eq_of_le inf_le_left (hE.trans (principalCartierDivisor_restrict _ W))).trans ?_,
    X.presheaf.map (homOfLE hW').op (f.app (V ⊓ U) r), ?_⟩
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · apply totalQuotientSheaf_ext
    intro hη'
    rw [map_mul, totalQuotientPullback_spec f hf inf_le_right hη' s]
    have e1 : totalQuotientSheafEquivFunctionField _ hη'
        (kUnitVal (X.totalQuotientUnitsSheaf.obj.map (homOfLE le_top).op
          (globalUnit X (genericFunctionFieldUnitsMap f hf g)))) =
        f.genericFunctionFieldMap hf (g : Y.functionField) := by
      rw [← coe_totalQuotientUnitsEquivFunctionField,
        totalQuotientUnitsEquivFunctionField_restrict_top, MulEquiv.apply_symm_apply]
      rfl
    have e2 : totalQuotientSheafEquivFunctionField _ hηV (Y.toK _ r) =
        totalQuotientSheafEquivFunctionField U (inf_le_right (a := V) hηV) s *
          (g : Y.functionField) := by
      rw [hr, map_mul, totalQuotientSheafEquivFunctionField_map,
        ← coe_totalQuotientUnitsEquivFunctionField, totalQuotientUnitsEquivFunctionField_map,
        totalQuotientUnitsEquivFunctionField_restrict_top, MulEquiv.apply_symm_apply]
    rw [e1, ← map_mul, ← e2, totalQuotientSheafEquivFunctionField_toK,
      totalQuotientSheafEquivFunctionField_toK, genericFunctionFieldMap_germ,
      TopCat.Presheaf.germ_res_apply]

open Hartshorne.Ringed in
/-- The morphism `O_Y(D) ⟶ f_* O_X(E)`, `s ↦ f^♯ s`. -/
def cartierPullbackHom (hDE : CartierPullbackData f hf D E) :
    D.sheaf ⟶ (Scheme.Modules.pushforward f).obj E.sheaf :=
  modulesHomMk (R := Y.sheaf) (fun U =>
    { toFun := fun s => (⟨totalQuotientPullback f hf U s.1,
        isSection_totalQuotientPullback hDE s.2⟩ : E.sheaf.val.presheaf.obj (op (f ⁻¹ᵁ U)))
      map_add' := fun s t => Subtype.ext (totalQuotientPullback_add f hf U s.1 t.1)
      map_smul' := fun c s => Subtype.ext (totalQuotientPullback_toK_mul f hf U c s.1) })
    (fun _ _ i s => Subtype.ext (totalQuotientPullback_map f hf i s.1))

/-- The adjoint morphism `f^* O_Y(D) ⟶ O_X(E)`. -/
def cartierPullbackMap (hDE : CartierPullbackData f hf D E) :
    (Scheme.Modules.pullback f).obj D.sheaf ⟶ E.sheaf :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (cartierPullbackHom hDE)

open Hartshorne.Ringed in
theorem cartierPullbackMap_etaSec (hDE : CartierPullbackData f hf D E) {U : Y.Opens}
    (s : D.sheaf.val.presheaf.obj (op U)) :
    sectionsMap (R := X.sheaf) (cartierPullbackMap hDE) (f ⁻¹ᵁ U)
        (etaSec (φ := f.toRingCatSheafHom) s) =
      sectionsMap (R := Y.sheaf) (cartierPullbackHom hDE) U s := by
  have h : pullbackUnit f.toRingCatSheafHom D.sheaf ≫
      (Scheme.Modules.pushforward f).map (cartierPullbackMap hDE) = cartierPullbackHom hDE :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  exact ConcreteCategory.congr_hom (congrArg (fun φ => sectionsMap (R := Y.sheaf) φ U) h) s

open Hartshorne.Ringed in
theorem isIso_cartierPullbackMap (hDE : CartierPullbackData f hf D E) :
    IsIso (cartierPullbackMap hDE) := by
  refine modules_isIso_of_locally_bijective (R := X.sheaf) _ fun x => ?_
  obtain ⟨V, W, g, hxW, hWV, hD, hE⟩ := hDE x
  have hDV := hD.trans (principalCartierDivisor_restrict _ V)
  have hEW := hE.trans (principalCartierDivisor_restrict _ W)
  have hsrc := (IsLocalFrame.pullback (φ := f.toRingCatSheafHom)
    (D.isLocalFrame_inv hDV)).restrictLE hWV
  have htgt := E.isLocalFrame_inv hEW
  refine ⟨W, hxW, fun V' hV' => IsLocalFrame.app_bijective_of_map _ hsrc htgt (fun _ => ?_) hV'⟩
  have hnat : ∀ t, sectionsMap (R := X.sheaf) (cartierPullbackMap hDE) W
      (((Scheme.Modules.pullback f).obj D.sheaf).val.presheaf.map (homOfLE hWV).op t) =
      E.sheaf.val.presheaf.map (homOfLE hWV).op
        (sectionsMap (R := X.sheaf) (cartierPullbackMap hDE) (f ⁻¹ᵁ V) t) := fun t =>
    ConcreteCategory.congr_hom
      ((modulesMapPresheaf (R := X.sheaf) (cartierPullbackMap hDE)).naturality (homOfLE hWV).op) t
  refine (hnat _).trans ((congrArg _ (cartierPullbackMap_etaSec hDE _)).trans ?_)
  apply Subtype.ext
  change X.totalQuotientSheaf.obj.map (homOfLE hWV).op (totalQuotientPullback f hf V _) = _
  apply totalQuotientSheaf_ext
  intro hη
  rw [totalQuotientPullback_spec, ← coe_totalQuotientUnitsEquivFunctionField,
    ← coe_totalQuotientUnitsEquivFunctionField, map_inv, map_inv,
    totalQuotientUnitsEquivFunctionField_restrict_top,
    totalQuotientUnitsEquivFunctionField_restrict_top, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]
  simp [genericFunctionFieldUnitsMap]

open Hartshorne Hartshorne.Ringed in
/-- **Pullback of the invertible sheaf of a Cartier divisor.** If `E` is, near every point, the
pullback of a local equation of `D`, then `f^*` sends the class of `O_Y(D)` in `Pic Y` to the class
of `O_X(E)` in `Pic X`. -/
theorem picPullback_cartierDivisorSheaf (hDE : CartierPullbackData f hf D E) :
    Pic.pullback f (Pic.mk (R := Y.sheaf) D.sheaf
        ((Modules.isInvertible_iff_ringed _).1 D.isInvertible_sheaf)) =
      Pic.mk (R := X.sheaf) E.sheaf
        ((Modules.isInvertible_iff_ringed _).1 E.isInvertible_sheaf) := by
  rw [Pic.pullback_mk]
  have := isIso_cartierPullbackMap hDE
  exact (Pic.mk_eq_mk_iff _ _).mpr ⟨asIso (cartierPullbackMap hDE)⟩

end Pullback

/-- On a normal integral Noetherian scheme, a Cartier divisor whose Weil divisor agrees with the
divisor of a rational function `g` on an open set `V` is, near every point of `V`, the principal
divisor of `g`. -/
theorem CartierDivisor.exists_restrict_eq_principal {X : Scheme.{u}} [IsIntegral X]
    [IsNoetherian X] [Hartshorne.IsNormal X] (D : X.CartierDivisor) (g : X.functionFieldˣ)
    {V : X.Opens}
    (h : ∀ y ∈ V, Order.coheight y = 1 → (cartierToWeil D).1 y = X.ord (g : X.functionField) y)
    {x : X} (hx : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ W ≤ V ∧
      D.restrict W = (X.principalCartierDivisor (globalUnit X g)).restrict W := by
  set D' := D - X.principalCartierDivisor (globalUnit X g)
  have hD' : ∀ y ∈ V, Order.coheight y = 1 → (cartierToWeil D').1 y = 0 := by
    intro y hy hy1
    have hP := cartierToWeil_apply (X.principalCartierDivisor (globalUnit X g)) (globalUnit X g)
      (X.principalCartierDivisor (globalUnit X g)).restrict_top
      (show y ∈ (⊤ : X.Opens) from trivial)
    rw [MulEquiv.apply_symm_apply] at hP
    have hsub := congrArg (fun A : X.WeilDivisor => A.1 y)
      (map_sub (cartierToWeil (X := X)) D (X.principalCartierDivisor (globalUnit X g)))
    refine hsub.trans ?_
    change (cartierToWeil D).1 y -
      (cartierToWeil (X.principalCartierDivisor (globalUnit X g))).1 y = 0
    rw [hP, h y hy hy1, sub_self]
  obtain ⟨⟨U, f⟩, hxU, hf⟩ := D'.exists_local_representative x
  obtain ⟨_, ⟨W, -, rfl⟩, hxW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ U ⊓ V from ⟨hxU, hx⟩)
      (U ⊓ V).isOpen
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hηW := genericPoint_mem_opens_of_mem hxW
  have hWU' : W ≤ U := hWU.trans inf_le_left
  have hfW := D'.restrict_eq_of_le hWU' hf
  obtain ⟨a, ha⟩ := exists_unit_germToFunctionField_eq_of_ord_eq_zero
    (totalQuotientUnitsEquivFunctionField W hηW
      (X.totalQuotientUnitsSheaf.obj.map (homOfLE hWU').op f)) fun y hy hy1 ↦ by
        refine (cartierToWeil_apply D' _ hfW hy).symm.trans ?_
        exact hD' y (hWU hy).2 hy1
  refine ⟨W, hxW, hWU.trans inf_le_right, ?_⟩
  have heq : X.structureUnitsToTotalQuotientUnits.hom.app (op W) a =
      X.totalQuotientUnitsSheaf.obj.map (homOfLE hWU').op f := by
    apply (totalQuotientUnitsEquivFunctionField W hηW).injective
    ext
    rw [totalQuotientUnitsEquivFunctionField_structureUnits W hηW a]
    exact ha
  have h0 : D'.restrict W = 0 := by
    rw [hfW]
    refine (congrArg (fun t ↦ X.toCartierDivisorSheaf.hom.app (op W) (Additive.ofMul t))
      heq.symm).trans ?_
    exact toCartierDivisorSheaf_structureUnits W a
  have hsub : D'.restrict W = D.restrict W -
      (X.principalCartierDivisor (globalUnit X g)).restrict W :=
    map_sub _ _ _
  rw [hsub, sub_eq_zero] at h0
  exact h0

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

open Hartshorne Hartshorne.Ringed

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
  [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y) (hf : f.base (genericPoint X) = genericPoint Y)

/-- Let `X` and `Y` be integral separated Noetherian locally factorial schemes and `f : X ⟶ Y` a
morphism sending the generic point to the generic point. Suppose that every point `x` of `X` has an
open neighbourhood `W` mapping into an open `V` of `Y`, with a rational function `g` on `Y` such
that the Weil divisor `A` on `Y` is the divisor of `g` on `V` and the Weil divisor `B` on `X` is the
divisor of `f^♯ g` on `W`. Then the Cartier divisor of `B` is, near every point, the pullback of a
local equation of the Cartier divisor of `A`. -/
theorem cartierPullbackData_weilCartierEquiv (hX : X.IsLocallyFactorial)
    (hY : Y.IsLocallyFactorial) (A : Y.WeilDivisor) (B : X.WeilDivisor)
    (hAB : ∀ x : X, ∃ (V : Y.Opens) (W : X.Opens) (g : Y.functionFieldˣ), x ∈ W ∧
      W ≤ f ⁻¹ᵁ V ∧ (∀ y ∈ V, Order.coheight y = 1 → A.1 y = Y.ord (g : Y.functionField) y) ∧
      ∀ z ∈ W, Order.coheight z = 1 →
        B.1 z = X.ord (f.genericFunctionFieldMap hf (g : Y.functionField)) z) :
    CartierPullbackData f hf (weilCartierEquiv hY A) (weilCartierEquiv hX B) := by
  have := isNormal_of_isLocallyFactorial hX
  have := isNormal_of_isLocallyFactorial hY
  intro x
  obtain ⟨V, W₀, g, hxW₀, hW₀V, hA, hB⟩ := hAB x
  have hxV : f.base x ∈ V := hW₀V hxW₀
  have hA' : ∀ y ∈ V, Order.coheight y = 1 →
      (cartierToWeil (weilCartierEquiv hY A)).1 y = Y.ord (g : Y.functionField) y := by
    intro y hy hy1
    rw [← weilCartierEquiv_symm_apply hY, AddEquiv.symm_apply_apply]
    exact hA y hy hy1
  obtain ⟨V', hxV', hV'V, hD⟩ := (weilCartierEquiv hY A).exists_restrict_eq_principal g hA' hxV
  have hB' : ∀ z ∈ W₀ ⊓ f ⁻¹ᵁ V', Order.coheight z = 1 →
      (cartierToWeil (weilCartierEquiv hX B)).1 z =
        X.ord ((genericFunctionFieldUnitsMap f hf g : X.functionFieldˣ) : X.functionField) z := by
    intro z hz hz1
    rw [← weilCartierEquiv_symm_apply hX, AddEquiv.symm_apply_apply]
    exact hB z hz.1 hz1
  obtain ⟨W, hxW, hWV', hE⟩ :=
    (weilCartierEquiv hX B).exists_restrict_eq_principal _ hB'
      (show x ∈ W₀ ⊓ f ⁻¹ᵁ V' from ⟨hxW₀, hxV'⟩)
  exact ⟨V', W, g, hxW, hWV'.trans inf_le_right, hD, hE⟩

/-- **Pullback of Picard classes of Weil divisors.** Let `X` and `Y` be integral separated
Noetherian locally factorial schemes and `f : X ⟶ Y` a morphism sending the generic point to the
generic point. Suppose that every point `x` of `X` has an open neighbourhood `W` mapping into an
open `V` of `Y`, with a rational function `g` on `Y` such that the Weil divisor `A` on `Y` is the
divisor of `g` on `V` and the Weil divisor `B` on `X` is the divisor of `f^♯ g` on `W`. Then the
Picard pullback sends the class corresponding to `A` (under `Cl Y ≅ Pic Y`) to the class
corresponding to `B`. -/
theorem picPullback_weilClassEquivPicard (hX : X.IsLocallyFactorial) (hY : Y.IsLocallyFactorial)
    (A : Y.WeilDivisor) (B : X.WeilDivisor)
    (hAB : ∀ x : X, ∃ (V : Y.Opens) (W : X.Opens) (g : Y.functionFieldˣ), x ∈ W ∧
      W ≤ f ⁻¹ᵁ V ∧ (∀ y ∈ V, Order.coheight y = 1 → A.1 y = Y.ord (g : Y.functionField) y) ∧
      ∀ z ∈ W, Order.coheight z = 1 →
        B.1 z = X.ord (f.genericFunctionFieldMap hf (g : Y.functionField)) z) :
    Pic.pullback f (Additive.toMul (weilClassEquivPicard hY
        (Y.weilDivisorClassHom (satisfiesConditionStar_of_isLocallyFactorial hY) A))) =
      Additive.toMul (weilClassEquivPicard hX
        (X.weilDivisorClassHom (satisfiesConditionStar_of_isLocallyFactorial hX) B)) := by
  rw [weilClassEquivPicard_weilDivisorClassHom, weilClassEquivPicard_weilDivisorClassHom,
    toMul_ofMul, toMul_ofMul]
  exact picPullback_cartierDivisorSheaf (cartierPullbackData_weilCartierEquiv f hf hX hY A B hAB)

end AlgebraicGeometry.Scheme
