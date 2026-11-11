/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.ImmersionConormalSheaf

/-!
# Relative differentials and the conormal sheaf of the diagonal

Hartshorne, *Algebraic Geometry*, II.8, p. 175; Stacks Project, tag 08S2.

Let `f : X ⟶ Y` be a morphism of schemes and `Δ : X ⟶ X ×_Y X` its diagonal, factored as the
closed immersion `j = Δ.liftCoborder : X ⟶ W` into the open `W = Δ.coborderRange` followed by
the inclusion. Let `I` be the ideal sheaf of `j` and `N^*_Δ = j^* I` the conormal sheaf.

For a section `a` of `𝒪_X` over `U`, the difference `p₁^* a - p₂^* a` of its two pullbacks is a
section of `𝒪_W` over `p₁⁻¹ U ∩ p₂⁻¹ U` which `j^♯` sends to `a - a = 0`; hence it is a section
of `I`, and its image under the unit `I ⟶ j_* j^* I` is a section of `N^*_Δ` over
`j⁻¹(p₁⁻¹ U ∩ p₂⁻¹ U) = U`. This is a derivation `𝒪_X ⟶ N^*_Δ` over `Y`
(`Hartshorne.DiagonalConormal.diagonalConormalDerivation`), and the universal property of
`Ω_{X/Y}` gives the comparison morphism `Ω_{X/Y} ⟶ N^*_Δ`
(`Hartshorne.DiagonalConormal.relativeDifferentialsToDiagonalConormal`) sending `d a` to the class
of `p₁^* a - p₂^* a`.

The derivation is built more generally for any morphism `j : X ⟶ W` with two retractions
`q₁, q₂ : W ⟶ X` that agree after composing with `f`.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne.DiagonalConormal

variable {X Y W : Scheme.{u}}

section Retractions

variable (j : X ⟶ W) (q₁ q₂ : W ⟶ X)

/-- The open `q₁⁻¹ U ∩ q₂⁻¹ U` of `W` on which both pullbacks of a section over `U` live. -/
abbrev nbhd (U : X.Opens) : W.Opens := q₁ ⁻¹ᵁ U ⊓ q₂ ⁻¹ᵁ U

variable {j q₁ q₂} (h₁ : j ≫ q₁ = 𝟙 X) (h₂ : j ≫ q₂ = 𝟙 X)

include h₁ h₂ in
/-- If `q₁` and `q₂` are retractions of `j`, then `j⁻¹(q₁⁻¹ U ∩ q₂⁻¹ U) = U`. -/
theorem preimage_nbhd (U : X.Opens) : j ⁻¹ᵁ nbhd q₁ q₂ U = U := by
  ext x
  change j.base x ∈ q₁ ⁻¹ᵁ U ∧ j.base x ∈ q₂ ⁻¹ᵁ U ↔ x ∈ U
  change (j ≫ q₁).base x ∈ U ∧ (j ≫ q₂).base x ∈ U ↔ x ∈ U
  rw [h₁, h₂]
  exact and_self_iff

/-- `appLE` of a morphism equal to the identity is a restriction map. -/
theorem appLE_of_eq_id {k : X ⟶ X} (hk : k = 𝟙 X) {U V : X.Opens} (e : V ≤ k ⁻¹ᵁ U)
    (hVU : V ≤ U) : k.appLE U V e = X.presheaf.map (homOfLE hVU).op := by
  subst hk
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact Category.id_comp _

/-- If `j ≫ g = 𝟙`, then `j^♯` sends a restriction of `g^♯ a` to a restriction of `a`. -/
theorem app_res_app (g : W ⟶ X) (hg : j ≫ g = 𝟙 X) {U : X.Opens} {V : W.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) (hU : j ⁻¹ᵁ V ≤ U) (a : Γ(X, U)) :
    j.app V (W.presheaf.map (homOfLE hV).op (g.app U a)) =
      X.presheaf.map (homOfLE hU).op a := by
  change (g.appLE U V hV ≫ j.app V) a = _
  rw [Scheme.Hom.app_eq_appLE j, Scheme.Hom.appLE_comp_appLE, appLE_of_eq_id hg _ hU]

variable (j q₁ q₂) in
/-- The difference `q₁^* a - q₂^* a` of the two pullbacks of a section `a` over `U`, a section of
`𝒪_W` over `q₁⁻¹ U ∩ q₂⁻¹ U`. -/
noncomputable def diffSection (U : X.Opens) : Γ(X, U) →+ Γ(W, nbhd q₁ q₂ U) :=
  (W.presheaf.map (homOfLE (inf_le_left : nbhd q₁ q₂ U ≤ q₁ ⁻¹ᵁ U)).op).hom.toAddMonoidHom.comp
      (q₁.app U).hom.toAddMonoidHom -
    (W.presheaf.map (homOfLE (inf_le_right : nbhd q₁ q₂ U ≤ q₂ ⁻¹ᵁ U)).op).hom.toAddMonoidHom.comp
      (q₂.app U).hom.toAddMonoidHom

variable (j q₁ q₂) in
/-- `diffSection` on elements. -/
theorem diffSection_apply (U : X.Opens) (a : Γ(X, U)) :
    diffSection q₁ q₂ U a =
      W.presheaf.map (homOfLE (inf_le_left : nbhd q₁ q₂ U ≤ q₁ ⁻¹ᵁ U)).op (q₁.app U a) -
        W.presheaf.map (homOfLE (inf_le_right : nbhd q₁ q₂ U ≤ q₂ ⁻¹ᵁ U)).op (q₂.app U a) :=
  rfl

include h₁ h₂ in
/-- `j^♯` kills the difference of the two pullbacks. -/
theorem app_diffSection (U : X.Opens) (a : Γ(X, U)) :
    j.app (nbhd q₁ q₂ U) (diffSection q₁ q₂ U a) = 0 := by
  rw [diffSection_apply, map_sub, app_res_app q₁ h₁ _ (preimage_nbhd h₁ h₂ U).le,
    app_res_app q₂ h₂ _ (preimage_nbhd h₁ h₂ U).le, sub_self]

include h₁ h₂ in
/-- The difference of the two pullbacks is a section of the ideal sheaf of `j`. -/
theorem exists_idealSection (U : X.Opens) (a : Γ(X, U)) :
    ∃ t : Γ(closedImmersionIdealSheaf j, nbhd q₁ q₂ U),
      (closedImmersionIdealSheafι j).app _ t = diffSection q₁ q₂ U a := by
  let S : ShortComplex W.Modules := ShortComplex.mk
    (closedImmersionIdealSheafι j) (structureSheafToPushforward j)
    (kernel.condition (structureSheafToPushforward j))
  have : Mono S.f := inferInstanceAs (Mono (closedImmersionIdealSheafι j))
  exact modules_sections_exact (S := S)
    (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) (U := nbhd q₁ q₂ U)
    (diffSection q₁ q₂ U a) (app_diffSection h₁ h₂ U a)

/-- The difference `q₁^* a - q₂^* a`, as a section of the ideal sheaf `I` of `j`. -/
noncomputable def idealSection (U : X.Opens) (a : Γ(X, U)) :
    Γ(closedImmersionIdealSheaf j, nbhd q₁ q₂ U) :=
  (exists_idealSection h₁ h₂ U a).choose

/-- `idealSection` is a lift of the difference section to the ideal sheaf. -/
theorem ι_idealSection (U : X.Opens) (a : Γ(X, U)) :
    (closedImmersionIdealSheafι j).app _ (idealSection h₁ h₂ U a) = diffSection q₁ q₂ U a :=
  (exists_idealSection h₁ h₂ U a).choose_spec

/-- `idealSection` is the unique lift of the difference section. -/
theorem idealSection_eq {U : X.Opens} (a : Γ(X, U))
    (t : Γ(closedImmersionIdealSheaf j, nbhd q₁ q₂ U))
    (ht : (closedImmersionIdealSheafι j).app _ t = diffSection q₁ q₂ U a) :
    idealSection h₁ h₂ U a = t :=
  modules_app_injective (closedImmersionIdealSheafι j) _
    ((ι_idealSection h₁ h₂ U a).trans ht.symm)

/-- `idealSection` is additive. -/
theorem idealSection_add (U : X.Opens) (a b : Γ(X, U)) :
    idealSection h₁ h₂ U (a + b) = idealSection h₁ h₂ U a + idealSection h₁ h₂ U b := by
  refine idealSection_eq h₁ h₂ _ _ ?_
  rw [map_add, ι_idealSection, ι_idealSection]
  exact (map_add _ a b).symm

/-- Leibniz rule for `idealSection`:
`q₁(ab) - q₂(ab) = q₁(a) (q₁(b) - q₂(b)) + q₂(b) (q₁(a) - q₂(a))`. -/
theorem idealSection_mul (U : X.Opens) (a b : Γ(X, U)) :
    idealSection h₁ h₂ U (a * b) =
      W.presheaf.map (homOfLE (inf_le_left : nbhd q₁ q₂ U ≤ q₁ ⁻¹ᵁ U)).op (q₁.app U a) •
          idealSection h₁ h₂ U b +
        W.presheaf.map (homOfLE (inf_le_right : nbhd q₁ q₂ U ≤ q₂ ⁻¹ᵁ U)).op (q₂.app U b) •
          idealSection h₁ h₂ U a := by
  refine idealSection_eq h₁ h₂ _ _ ?_
  erw [map_add, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, ι_idealSection,
    ι_idealSection]
  simp only [diffSection_apply, map_mul]
  change (_ : Γ(W, nbhd q₁ q₂ U)) * _ + _ * _ = _
  ring

/-- Restricting a difference section is the difference section of the restriction. -/
theorem diffSection_map {U V : X.Opens} (i : V ⟶ U) (a : Γ(X, U))
    (hVU : nbhd q₁ q₂ V ≤ nbhd q₁ q₂ U) :
    diffSection q₁ q₂ V (X.presheaf.map i.op a) =
      W.presheaf.map (homOfLE hVU).op (diffSection q₁ q₂ U a) := by
  rw [diffSection_apply, diffSection_apply, map_sub]
  congr 1
  · change (X.presheaf.map i.op ≫ q₁.appLE V _ inf_le_left) a =
      (q₁.appLE U _ inf_le_left ≫ W.presheaf.map (homOfLE hVU).op) a
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · change (X.presheaf.map i.op ≫ q₂.appLE V _ inf_le_right) a =
      (q₂.appLE U _ inf_le_right ≫ W.presheaf.map (homOfLE hVU).op) a
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

/-- `idealSection` commutes with restriction. -/
theorem idealSection_map {U V : X.Opens} (i : V ⟶ U) (a : Γ(X, U))
    (hVU : nbhd q₁ q₂ V ≤ nbhd q₁ q₂ U) :
    idealSection h₁ h₂ V (X.presheaf.map i.op a) =
      (closedImmersionIdealSheaf j).presheaf.map (homOfLE hVU).op (idealSection h₁ h₂ U a) := by
  refine idealSection_eq h₁ h₂ _ _ ?_
  refine (Scheme.Modules.app_presheaf_map _ _ _).trans ?_
  rw [ι_idealSection, diffSection_map _ _ hVU]
  rfl

/-- `appLE` along equal morphisms. -/
theorem appLE_congr_hom {X' Y' : Scheme.{u}} {k k' : X' ⟶ Y'} (hk : k = k') {U : Y'.Opens}
    {V : X'.Opens} (e : V ≤ k ⁻¹ᵁ U) (e' : V ≤ k' ⁻¹ᵁ U) : k.appLE U V e = k'.appLE U V e' := by
  subst hk
  rfl

/-- The difference section of a function pulled back from `Y` vanishes. -/
theorem diffSection_app_eq_zero {f : X ⟶ Y} (hq : q₁ ≫ f = q₂ ≫ f) (V : Y.Opens)
    (b : Γ(Y, V)) : diffSection q₁ q₂ (f ⁻¹ᵁ V) (f.app V b) = 0 := by
  rw [diffSection_apply, sub_eq_zero]
  change (f.app V ≫ q₁.appLE (f ⁻¹ᵁ V) _ inf_le_left) b =
    (f.app V ≫ q₂.appLE (f ⁻¹ᵁ V) _ inf_le_right) b
  rw [← Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom hq]

/-- The ideal section of a function pulled back from `Y` vanishes. -/
theorem idealSection_app_eq_zero {f : X ⟶ Y} (hq : q₁ ≫ f = q₂ ≫ f) (V : Y.Opens)
    (b : Γ(Y, V)) : idealSection h₁ h₂ (f ⁻¹ᵁ V) (f.app V b) = 0 := by
  refine idealSection_eq h₁ h₂ _ _ ?_
  exact (map_zero _).trans (diffSection_app_eq_zero hq V b).symm

/-- The image of the unit `I ⟶ j_* j^* I` on a section of `I` over `V`, a section of `j^* I`
over `j⁻¹ V`. -/
noncomputable abbrev unitApp (V : W.Opens) (x : Γ(closedImmersionIdealSheaf j, V)) :
    Γ((Scheme.Modules.pullback j).obj (closedImmersionIdealSheaf j), j ⁻¹ᵁ V) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
    (closedImmersionIdealSheaf j)).app V x

omit h₁ h₂ in
variable (j) in
/-- The unit `I ⟶ j_* j^* I` is linear, with `𝒪_W` acting on `j_* j^* I` through
`j^♯`. -/
theorem unitApp_smul (V : W.Opens) (r : Γ(W, V)) (x : Γ(closedImmersionIdealSheaf j, V)) :
    unitApp (j := j) V (r • x) = j.app V r • unitApp (j := j) V x :=
  ((((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
    (closedImmersionIdealSheaf j)).val.app (op V)).hom.map_smul r x)

omit h₁ h₂ in
variable (j) in
/-- `unitApp` is additive. -/
theorem unitApp_add (V : W.Opens) (x y : Γ(closedImmersionIdealSheaf j, V)) :
    unitApp (j := j) V (x + y) = unitApp (j := j) V x + unitApp (j := j) V y :=
  map_add _ x y

omit h₁ h₂ in
variable (j) in
/-- `unitApp` sends zero to zero. -/
theorem unitApp_zero (V : W.Opens) :
    unitApp (j := j) V 0 = 0 :=
  map_zero _

omit h₁ h₂ in
variable (j) in
/-- `unitApp` commutes with restriction. -/
theorem unitApp_map {V V' : W.Opens} (h : V' ≤ V) (x : Γ(closedImmersionIdealSheaf j, V)) :
    unitApp (j := j) V' ((closedImmersionIdealSheaf j).presheaf.map (homOfLE h).op x) =
      ((Scheme.Modules.pullback j).obj (closedImmersionIdealSheaf j)).presheaf.map
        (homOfLE (fun _ hx => h hx : j ⁻¹ᵁ V' ≤ j ⁻¹ᵁ V)).op (unitApp (j := j) V x) :=
  Scheme.Modules.app_presheaf_map _ (homOfLE h) x

/-- The section of the conormal sheaf `j^* I` over `U` attached to `a ∈ Γ(X, U)`: the class of
`q₁^* a - q₂^* a`. -/
noncomputable def conormalD (U : X.Opens) (a : Γ(X, U)) :
    Γ((Scheme.Modules.pullback j).obj (closedImmersionIdealSheaf j), U) :=
  ((Scheme.Modules.pullback j).obj (closedImmersionIdealSheaf j)).presheaf.map
    (homOfLE (preimage_nbhd h₁ h₂ U).ge).op (unitApp (j := j) _ (idealSection h₁ h₂ U a))

/-- `conormalD` is additive. -/
theorem conormalD_add (U : X.Opens) (a b : Γ(X, U)) :
    conormalD h₁ h₂ U (a + b) = conormalD h₁ h₂ U a + conormalD h₁ h₂ U b := by
  rw [conormalD, idealSection_add, unitApp_add, map_add]
  rfl

/-- Leibniz rule for `conormalD`. -/
theorem conormalD_mul (U : X.Opens) (a b : Γ(X, U)) :
    conormalD h₁ h₂ U (a * b) = a • conormalD h₁ h₂ U b + b • conormalD h₁ h₂ U a := by
  rw [conormalD, idealSection_mul, unitApp_add, unitApp_smul, unitApp_smul, map_add,
    Scheme.Modules.map_smul, Scheme.Modules.map_smul,
    app_res_app q₁ h₁ _ (preimage_nbhd h₁ h₂ U).le, app_res_app q₂ h₂ _ (preimage_nbhd h₁ h₂ U).le]
  have e : ∀ c : Γ(X, U), X.presheaf.map (homOfLE (preimage_nbhd h₁ h₂ U).ge).op
      (X.presheaf.map (homOfLE (preimage_nbhd h₁ h₂ U).le).op c) = c := fun c => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact (ConcreteCategory.congr_hom (X.presheaf.map_id (op U)) c)
  rw [e, e]
  rfl

/-- `conormalD` commutes with restriction. -/
theorem conormalD_map {U V : X.Opens} (i : V ⟶ U) (a : Γ(X, U)) :
    conormalD h₁ h₂ V (X.presheaf.map i.op a) =
      ((Scheme.Modules.pullback j).obj (closedImmersionIdealSheaf j)).presheaf.map i.op
        (conormalD h₁ h₂ U a) := by
  have hVU : nbhd q₁ q₂ V ≤ nbhd q₁ q₂ U :=
    inf_le_inf (fun x hx => i.le hx) (fun x hx => i.le hx)
  rw [conormalD, conormalD, idealSection_map h₁ h₂ i a hVU]
  have r : op (j ⁻¹ᵁ nbhd q₁ q₂ U) ⟶ op V :=
    (homOfLE (le_trans i.le (preimage_nbhd h₁ h₂ U).ge)).op
  rw [unitApp_map, Scheme.Modules.presheaf_map_map _ _ _ r,
    Scheme.Modules.presheaf_map_map _ _ _ r]

end Retractions

section Derivation

variable {j : X ⟶ W} {q₁ q₂ : W ⟶ X} (h₁ : j ≫ q₁ = 𝟙 X) (h₂ : j ≫ q₂ = 𝟙 X)
  (f : X ⟶ Y) (hq : q₁ ≫ f = q₂ ≫ f)

/-- The derivation `a ↦ [q₁^* a - q₂^* a]` of `𝒪_X` into the conormal sheaf `j^* I`, relative to
`f`. -/
noncomputable def retractionsDerivation :
    ((Scheme.Modules.pullback j).obj (closedImmersionIdealSheaf j)).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom :=
  RelDiffLocal.derivationOfKills f
    (fun {U} => AddMonoidHom.mk' (conormalD h₁ h₂ U.unop) (conormalD_add h₁ h₂ U.unop))
    (fun {U} a b => conormalD_mul h₁ h₂ U.unop a b)
    (fun {_ _} i x => conormalD_map h₁ h₂ i.unop x)
    (RelDiffLocal.modules_sep _)
    (fun V b => by
      change conormalD h₁ h₂ (f ⁻¹ᵁ V) (f.app V b) = 0
      rw [conormalD, idealSection_app_eq_zero h₁ h₂ hq, unitApp_zero, map_zero])

/-- The derivation `retractionsDerivation` is `conormalD` on sections. -/
theorem retractionsDerivation_d (U : X.Opens) (a : Γ(X, U)) :
    (retractionsDerivation h₁ h₂ f hq).d (X := op U) a = conormalD h₁ h₂ U a :=
  rfl

end Derivation

section Diagonal

variable (f : X ⟶ Y)

/-- The first projection restricted to the open `W ⊆ X ×_Y X` where the diagonal is closed. -/
noncomputable abbrev diagFst : (pullback.diagonal f).coborderRange.toScheme ⟶ X :=
  (pullback.diagonal f).coborderRange.ι ≫ pullback.fst f f

/-- The second projection restricted to the open `W ⊆ X ×_Y X` where the diagonal is closed. -/
noncomputable abbrev diagSnd : (pullback.diagonal f).coborderRange.toScheme ⟶ X :=
  (pullback.diagonal f).coborderRange.ι ≫ pullback.snd f f

/-- The closed immersion of `X` into `W` is a section of the first projection. -/
theorem liftCoborder_diagFst : (pullback.diagonal f).liftCoborder ≫ diagFst f = 𝟙 X := by
  rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, pullback.diagonal_fst]

/-- The closed immersion of `X` into `W` is a section of the second projection. -/
theorem liftCoborder_diagSnd : (pullback.diagonal f).liftCoborder ≫ diagSnd f = 𝟙 X := by
  rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, pullback.diagonal_snd]

/-- The two projections from `W` agree after composing with `f`. -/
theorem diagFst_comp : diagFst f ≫ f = diagSnd f ≫ f := by
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- **The derivation of `𝒪_X` into the conormal sheaf of the diagonal**: `a ↦ [p₁^* a - p₂^* a]`,
relative to `f`. -/
noncomputable def diagonalConormalDerivation :
    (immersionConormalSheaf (pullback.diagonal f)).val.Derivation'
      (Scheme.inverseImageStructureSheafMap f).hom :=
  retractionsDerivation (liftCoborder_diagFst f) (liftCoborder_diagSnd f) f (diagFst_comp f)

/-- **The comparison morphism `Ω_{X/Y} ⟶ N^*_Δ`** induced by the universal property of
`Ω_{X/Y}`, sending `d a` to the class of `p₁^* a - p₂^* a`. -/
noncomputable def relativeDifferentialsToDiagonalConormal :
    Scheme.relativeDifferentials f ⟶ immersionConormalSheaf (pullback.diagonal f) :=
  (Scheme.relativeDifferentialsHomEquiv f _).symm (diagonalConormalDerivation f)

/-- The comparison morphism carries the universal derivation to the diagonal derivation. -/
theorem relativeDifferentialsToDiagonalConormal_d :
    (Scheme.relativeDifferentialsDerivation f).postcomp
        (relativeDifferentialsToDiagonalConormal f).val =
      diagonalConormalDerivation f :=
  (Scheme.relativeDifferentialsHomEquiv_apply f _ _).symm.trans
    ((Scheme.relativeDifferentialsHomEquiv f _).apply_symm_apply _)

/-- On sections, the comparison morphism sends `d a` to the class of `p₁^* a - p₂^* a`. -/
theorem relativeDifferentialsToDiagonalConormal_app_d (U : X.Opens) (a : Γ(X, U)) :
    (relativeDifferentialsToDiagonalConormal f).app U
        ((Scheme.relativeDifferentialsDerivation f).d (X := op U) a) =
      conormalD (liftCoborder_diagFst f) (liftCoborder_diagSnd f) U a :=
  congrArg (fun D => PresheafOfModules.Derivation.d D (X := op U) a)
    (relativeDifferentialsToDiagonalConormal_d f)

end Diagonal


end Hartshorne.DiagonalConormal
