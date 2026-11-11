/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.ImmersionConormalSheaf
import Hartshorne.Scheme.Differentials.ClosedImmersionConormalSequence

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
/-- `unitApp` commutes with negation. -/
theorem unitApp_neg (V : W.Opens) (x : Γ(closedImmersionIdealSheaf j, V)) :
    unitApp (j := j) V (-x) = -unitApp (j := j) V x :=
  map_neg _ x

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

/-- Restricting from `U` to `j⁻¹(nbhd U) = U` and back is the identity. -/
theorem res_res_nbhd (U : X.Opens) (c : Γ(X, U)) :
    X.presheaf.map (homOfLE (preimage_nbhd h₁ h₂ U).ge).op
      (X.presheaf.map (homOfLE (preimage_nbhd h₁ h₂ U).le).op c) = c := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact (ConcreteCategory.congr_hom (X.presheaf.map_id (op U)) c)

/-- Leibniz rule for `conormalD`. -/
theorem conormalD_mul (U : X.Opens) (a b : Γ(X, U)) :
    conormalD h₁ h₂ U (a * b) = a • conormalD h₁ h₂ U b + b • conormalD h₁ h₂ U a := by
  rw [conormalD, idealSection_mul, unitApp_add, unitApp_smul, unitApp_smul, map_add,
    Scheme.Modules.map_smul, Scheme.Modules.map_smul,
    app_res_app q₁ h₁ _ (preimage_nbhd h₁ h₂ U).le, app_res_app q₂ h₂ _ (preimage_nbhd h₁ h₂ U).le]
  rw [res_res_nbhd h₁ h₂, res_res_nbhd h₁ h₂]
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

/-- `j^♯` kills the sections of the ideal sheaf. -/
theorem app_ι_eq_zero (V : W.Opens) (t : Γ(closedImmersionIdealSheaf j, V)) :
    j.app V ((closedImmersionIdealSheafι j).app V t) = 0 :=
  congrArg (fun φ => Scheme.Modules.Hom.app φ V t)
    (kernel.condition (structureSheafToPushforward j))

include h₁ h₂ in
/-- **Local generation of the conormal sheaf.** If every function on `nbhd U` is a sum of
products `q₁^* a · q₂^* b`, and the unit `I ⟶ j_* j^* I` is surjective on sections over
`nbhd U`, then the sections of `j^* I` over `U` are spanned by the `conormalD a`. -/
theorem mem_span_conormalD (U : X.Opens)
    (hgen : ∀ z : Γ(W, nbhd q₁ q₂ U), z ∈ AddSubmonoid.closure
      (Set.range fun p : Γ(X, U) × Γ(X, U) =>
        q₁.appLE U _ inf_le_left p.1 * q₂.appLE U _ inf_le_right p.2))
    (hsurj : Function.Surjective (unitApp (j := j) (nbhd q₁ q₂ U)))
    (y : Γ((Scheme.Modules.pullback j).obj (closedImmersionIdealSheaf j), U)) :
    y ∈ Submodule.span Γ(X, U) (Set.range (conormalD h₁ h₂ U)) := by
  let N := (Scheme.Modules.pullback j).obj (closedImmersionIdealSheaf j)
  set T := nbhd q₁ q₂ U
  have hR : IsIso (homOfLE (preimage_nbhd h₁ h₂ U).ge) :=
    ⟨⟨homOfLE (preimage_nbhd h₁ h₂ U).le, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  obtain ⟨y', hy'⟩ := (ConcreteCategory.bijective_of_isIso
    (N.presheaf.map (homOfLE (preimage_nbhd h₁ h₂ U).ge).op)).2 y
  obtain ⟨s, hs⟩ := hsurj y'
  rw [← hy', ← hs]
  let ρ : Γ(W, T) →+* Γ(X, U) :=
    (j.app T ≫ X.presheaf.map (homOfLE (preimage_nbhd h₁ h₂ U).ge).op).hom
  have hρ : ∀ z, ρ z = X.presheaf.map (homOfLE (preimage_nbhd h₁ h₂ U).ge).op (j.app T z) :=
    fun _ => rfl
  have hρ₁ : ∀ c, ρ (q₁.appLE U T inf_le_left c) = c := fun c => by
    rw [hρ]
    exact (congrArg _ (app_res_app q₁ h₁ _ (preimage_nbhd h₁ h₂ U).le c)).trans
      (res_res_nbhd h₁ h₂ U c)
  have hρ₂ : ∀ c, ρ (q₂.appLE U T inf_le_right c) = c := fun c => by
    rw [hρ]
    exact (congrArg _ (app_res_app q₂ h₂ _ (preimage_nbhd h₁ h₂ U).le c)).trans
      (res_res_nbhd h₁ h₂ U c)
  have hker : ∀ z, j.app T (z - q₁.appLE U T inf_le_left (ρ z)) = 0 := fun z => by
    rw [map_sub, sub_eq_zero]
    refine Eq.symm ((app_res_app q₁ h₁ inf_le_left (preimage_nbhd h₁ h₂ U).le (ρ z)).trans ?_)
    rw [hρ, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    exact ConcreteCategory.congr_hom (X.presheaf.map_id _) _
  have hlift : ∀ z, ∃ t : Γ(closedImmersionIdealSheaf j, T),
      (closedImmersionIdealSheafι j).app T t = z - q₁.appLE U T inf_le_left (ρ z) := by
    intro z
    let S : ShortComplex W.Modules := ShortComplex.mk
      (closedImmersionIdealSheafι j) (structureSheafToPushforward j)
      (kernel.condition (structureSheafToPushforward j))
    have : Mono S.f := inferInstanceAs (Mono (closedImmersionIdealSheafι j))
    exact modules_sections_exact (S := S)
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)) (U := T) _ (hker z)
  set M := Submodule.span Γ(X, U) (Set.range (conormalD h₁ h₂ U))
  suffices key : ∀ z, ∀ t : Γ(closedImmersionIdealSheaf j, T),
      (closedImmersionIdealSheafι j).app T t = z - q₁.appLE U T inf_le_left (ρ z) →
      N.presheaf.map (homOfLE (preimage_nbhd h₁ h₂ U).ge).op (unitApp (j := j) T t) ∈ M by
    refine key ((closedImmersionIdealSheafι j).app T s) s ?_
    have h0 : ρ ((closedImmersionIdealSheafι j).app T s) = 0 :=
      (hρ _).trans (by rw [app_ι_eq_zero, map_zero])
    refine (sub_zero _).symm.trans ?_
    congr 1
    exact ((congrArg _ h0).trans (map_zero _)).symm
  intro z
  induction hgen z using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    intro t ht
    dsimp only at ht
    have e1 : ρ (q₁.appLE U T inf_le_left a * q₂.appLE U T inf_le_right b) = a * b := by
      rw [map_mul, hρ₁, hρ₂]
    have ht' : t = -(q₁.appLE U T inf_le_left a • idealSection h₁ h₂ U b) := by
      refine modules_app_injective (closedImmersionIdealSheafι j) _ (ht.trans ?_)
      change q₁.appLE U T inf_le_left a * q₂.appLE U T inf_le_right b -
        q₁.appLE U T inf_le_left (ρ (q₁.appLE U T inf_le_left a *
          q₂.appLE U T inf_le_right b)) = _
      rw [e1]
      erw [map_neg, Scheme.Modules.Hom.app_smul, ι_idealSection]
      rw [diffSection_apply]
      change _ = -(q₁.appLE U T inf_le_left a *
        (q₁.appLE U T inf_le_left b - q₂.appLE U T inf_le_right b))
      rw [map_mul]
      ring
    rw [ht', unitApp_neg, unitApp_smul, map_neg, Scheme.Modules.map_smul]
    change -(X.presheaf.map _ (j.app T (W.presheaf.map (homOfLE inf_le_left).op
      (q₁.app U a))) • conormalD h₁ h₂ U b) ∈ M
    rw [app_res_app q₁ h₁ _ (preimage_nbhd h₁ h₂ U).le, res_res_nbhd h₁ h₂]
    exact M.neg_mem (M.smul_mem a (Submodule.subset_span ⟨b, rfl⟩))
  | zero =>
    intro t ht
    have ht' : t = 0 := modules_app_injective (closedImmersionIdealSheafι j) _
      (ht.trans (by rw [map_zero, map_zero, sub_zero, map_zero]; rfl))
    rw [ht', unitApp_zero, map_zero]
    exact M.zero_mem
  | add x y _ _ hx hy =>
    intro t ht
    obtain ⟨t₁, ht₁⟩ := hlift x
    obtain ⟨t₂, ht₂⟩ := hlift y
    have e2 : (closedImmersionIdealSheafι j).app T (t₁ + t₂) =
        (x + y) - q₁.appLE U T inf_le_left (ρ (x + y)) := by
      erw [map_add, ht₁, ht₂]
      rw [map_add ρ, map_add]
      abel
    have ht' : t = t₁ + t₂ := modules_app_injective (closedImmersionIdealSheafι j) _
      (ht.trans e2.symm)
    rw [ht', unitApp_add, map_add]
    exact M.add_mem (hx t₁ ht₁) (hy t₂ ht₂)

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


open scoped TensorProduct in
/-- In a pushout square of commutative rings, every element of the pushout is a sum of products
`inl a * inr b`. -/
theorem mem_closure_of_isPushout {R A B P : CommRingCat.{u}} {f : R ⟶ A} {g : R ⟶ B}
    {inl : A ⟶ P} {inr : B ⟶ P} (h : IsPushout f g inl inr) (x : P) :
    x ∈ AddSubmonoid.closure (Set.range fun p : A × B => inl p.1 * inr p.2) := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  have H : IsPushout f g
      (CommRingCat.ofHom (S := A ⊗[R] B) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := A ⊗[R] B) Algebra.TensorProduct.includeRight.toRingHom) :=
    CommRingCat.isPushout_tensorProduct R A B
  let e := H.isoIsPushout _ _ h
  obtain ⟨y, rfl⟩ : ∃ y, e.hom y = x := ⟨e.inv x, by simp⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a b =>
    have h1 := ConcreteCategory.congr_hom (H.inl_isoIsPushout_hom _ _ h) a
    have h2 := ConcreteCategory.congr_hom (H.inr_isoIsPushout_hom _ _ h) b
    refine AddSubmonoid.subset_closure ⟨(a, b), ?_⟩
    have e3 : (a ⊗ₜ[R] b : A ⊗[R] B) = (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    change inl a * inr b = e.hom (a ⊗ₜ[R] b)
    rw [e3, map_mul]
    exact congrArg₂ (· * ·) h1.symm h2.symm
  | add y z hy hz => rw [map_add]; exact add_mem hy hz

section SquareMap

open Scheme Scheme.Modules

/-- For a commutative square `q₁ ≫ f = q₂ ≫ f`, the map `q₁^* Ω_{X/Y} ⟶ Ω_{W/X}` (relative to
`q₂`), sending `q₁^*(d b)` to `d (q₁^♯ b)`; for the projections of `X ×_Y X` it is the base-change
map. -/
noncomputable def squareMap (f : X ⟶ Y) {q₁ q₂ : W ⟶ X} (hq : q₁ ≫ f = q₂ ≫ f) :
    (Modules.pullback q₁).obj (relativeDifferentials f) ⟶ relativeDifferentials q₂ :=
  pullbackRelativeDifferentialsToComp q₁ f ≫ (relativeDifferentialsCongr hq).hom ≫
    relativeDifferentialsCompToLeft q₂ f

/-- `squareMap` sends `q₁^*(d b)` to `d (q₁^♯ b)`. -/
theorem squareMap_unit_d (f : X ⟶ Y) {q₁ q₂ : W ⟶ X} (hq : q₁ ≫ f = q₂ ≫ f) (V : X.Opens)
    (b : Γ(X, V)) :
    (squareMap f hq).val.app (op (q₁ ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction q₁).unit.app
        (relativeDifferentials f)).val.app (op V) ((relativeDifferentialsDerivation f).d b)) =
      (relativeDifferentialsDerivation q₂).d (q₁.app V b) := by
  change (relativeDifferentialsCompToLeft q₂ f).val.app _
    ((relativeDifferentialsCongr hq).hom.val.app _
      ((pullbackRelativeDifferentialsToComp q₁ f).val.app _ _)) = _
  rw [pullbackRelativeDifferentialsToComp_unit_d, relativeDifferentialsCongr_hom_d,
    relativeDifferentialsCompToLeft_d]

variable (f : X ⟶ Y)

/-- `Ω_{W/X} ≅ Ω_{(X ×_Y X)/X}|_W`, for `W ⊆ X ×_Y X` mapping to `X` by the second projection. -/
noncomputable abbrev diagRestrictIso :
    relativeDifferentials (diagSnd f) ≅
      (relativeDifferentials (pullback.snd f f)).restrict (pullback.diagonal f).coborderRange.ι :=
  RelDiffLocal.restrictIso (pullback.snd f f) (pullback.diagonal f).coborderRange.ι (diagSnd f)
    (𝟙 X) (Category.comp_id _).symm

/-- `p₁^* Ω_{X/Y}` on `W` is the restriction of `p₁^* Ω_{X/Y}` on `X ×_Y X`. -/
noncomputable abbrev diagPullbackIso :
    (Modules.pullback (diagFst f)).obj (relativeDifferentials f) ≅
      ((Modules.pullback (pullback.fst f f)).obj (relativeDifferentials f)).restrict
        (pullback.diagonal f).coborderRange.ι :=
  ((pullbackComp (pullback.diagonal f).coborderRange.ι (pullback.fst f f)).app
      (relativeDifferentials f)).symm ≪≫
    ((restrictFunctorIsoPullback (pullback.diagonal f).coborderRange.ι).app _).symm

theorem squareMap_comp_diagRestrictIso :
    squareMap f (diagFst_comp f) ≫ (diagRestrictIso f).hom =
      (diagPullbackIso f).hom ≫ (restrictFunctor (pullback.diagonal f).coborderRange.ι).map
        (baseChangeRelativeDifferentialsMap f f) := by
  set ι := (pullback.diagonal f).coborderRange.ι
  apply ((Modules.pullbackPushforwardAdjunction (diagFst f)).homEquiv _ _).injective
  apply (relativeDifferentialsHomEquiv f _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V b
  change (diagRestrictIso f).hom.val.app _ ((squareMap f (diagFst_comp f)).val.app _
      (((Modules.pullbackPushforwardAdjunction (diagFst f)).unit.app
        (relativeDifferentials f)).val.app V ((relativeDifferentialsDerivation f).d b))) =
    (baseChangeRelativeDifferentialsMap f f).val.app _ ((diagPullbackIso f).hom.val.app _
      (((Modules.pullbackPushforwardAdjunction (diagFst f)).unit.app
        (relativeDifferentials f)).val.app V ((relativeDifferentialsDerivation f).d b)))
  obtain ⟨V⟩ := V
  change Γ(X, V) at b
  set Wo : (pullback.diagonal f).coborderRange.toScheme.Opens := diagFst f ⁻¹ᵁ V
  have hle : ι ''ᵁ Wo ≤ pullback.fst f f ⁻¹ᵁ V := ι.image_preimage_le (pullback.fst f f ⁻¹ᵁ V)
  set c : Γ(pullback f f, ι ''ᵁ Wo) :=
    (pullback f f).presheaf.map (homOfLE hle).op (pullback.fst f f |>.app V b)
  have e2 : (diagFst f).app V b = (ι.appIso Wo).hom c := by
    rw [Scheme.Hom.appIso_hom', ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE,
      ← ConcreteCategory.comp_apply, Scheme.Hom.app_eq_appLE (pullback.fst f f),
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE]
  have lhs : (diagRestrictIso f).hom.val.app (op Wo) ((squareMap f (diagFst_comp f)).val.app
      (op Wo) (((Modules.pullbackPushforwardAdjunction (diagFst f)).unit.app
        (relativeDifferentials f)).val.app (op V) ((relativeDifferentialsDerivation f).d b))) =
      (relativeDifferentials (pullback.snd f f)).presheaf.map (homOfLE hle).op
        ((relativeDifferentialsDerivation (pullback.snd f f)).d
          (X := op (pullback.fst f f ⁻¹ᵁ V)) ((pullback.fst f f).app V b)) := by
    rw [squareMap_unit_d, e2, RelDiffLocal.restrictIso_hom_d]
    exact (relativeDifferentialsDerivation (pullback.snd f f)).d_map _ _
  have rhs1 : (diagPullbackIso f).hom.val.app (op Wo)
      (((Modules.pullbackPushforwardAdjunction (diagFst f)).unit.app
        (relativeDifferentials f)).val.app (op V) ((relativeDifferentialsDerivation f).d b)) =
      ((Modules.pullback (pullback.fst f f)).obj (relativeDifferentials f)).presheaf.map
        (homOfLE hle).op (((Modules.pullbackPushforwardAdjunction (pullback.fst f f)).unit.app
          (relativeDifferentials f)).app V ((relativeDifferentialsDerivation f).d b)) := by
    change ((restrictFunctorIsoPullback ι).inv.app _).app _
      (((pullbackComp ι (pullback.fst f f)).inv.app (relativeDifferentials f)).app _
        (((Modules.pullbackPushforwardAdjunction (ι ≫ pullback.fst f f)).unit.app
          (relativeDifferentials f)).app V ((relativeDifferentialsDerivation f).d b))) = _
    refine (congrArg (((restrictFunctorIsoPullback ι).inv.app _).app (ι ⁻¹ᵁ (pullback.fst f f ⁻¹ᵁ V)))
      (pullbackComp_inv_unit ι (pullback.fst f f) (relativeDifferentials f) V _)).trans ?_
    exact restrictFunctorIsoPullback_inv_unit ι _ (pullback.fst f f ⁻¹ᵁ V) _
  refine lhs.trans ?_
  refine Eq.trans ?_ (congrArg ((baseChangeRelativeDifferentialsMap f f).val.app _) rhs1).symm
  have h3 := Scheme.Modules.app_presheaf_map (baseChangeRelativeDifferentialsMap f f)
    (homOfLE hle) (((Modules.pullbackPushforwardAdjunction (pullback.fst f f)).unit.app
      (relativeDifferentials f)).app V ((relativeDifferentialsDerivation f).d b))
  exact (h3.trans (congrArg _ (baseChangeRelativeDifferentialsMap_unit_d f f V b))).symm

/-- The map `p₁^* Ω_{X/Y} ⟶ Ω_{W/X}` on `W` is an isomorphism (base change). -/
theorem isIso_squareMap : IsIso (squareMap f (diagFst_comp f)) := by
  have := isIso_baseChangeRelativeDifferentialsMap f f
  have h : squareMap f (diagFst_comp f) = (diagPullbackIso f).hom ≫
      (restrictFunctor (pullback.diagonal f).coborderRange.ι).map
        (baseChangeRelativeDifferentialsMap f f) ≫ (diagRestrictIso f).inv := by
    rw [← Category.assoc, ← squareMap_comp_diagRestrictIso, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [h]
  infer_instance

end SquareMap

section LeftInverse

open Scheme Scheme.Modules

/-- The unit of the pullback along the identity, followed by `𝟙^* ≅ 𝟭`, is the identity. -/
theorem pullbackId_hom_unit (F : X.Modules) (T : X.Opens) (s : Γ(F, T)) :
    ((pullbackId X).hom.app F).app T
      (((pullbackPushforwardAdjunction (𝟙 X)).unit.app F).app T s) = s := by
  have h := unit_conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 X))
    (pullbackId X).hom F
  rw [conjugateEquiv_pullbackId_hom] at h
  exact (ConcreteCategory.congr_hom (congrArg (fun φ => Modules.Hom.app φ T) h) s).symm

/-- For `k = 𝟙`, `k^* F ≅ F` sends `k^* s` to the restriction of `s`. -/
theorem pullbackCongr_id_unit {k : X ⟶ X} (hk : k = 𝟙 X) (F : X.Modules) (T : X.Opens)
    (hT : k ⁻¹ᵁ T ≤ T) (s : Γ(F, T)) :
    ((pullbackId X).hom.app F).app (k ⁻¹ᵁ T) (((pullbackCongr hk).hom.app F).app (k ⁻¹ᵁ T)
      (((pullbackPushforwardAdjunction k).unit.app F).app T s)) =
      F.presheaf.map (homOfLE hT).op s := by
  subst hk
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  refine (pullbackId_hom_unit F T s).trans ?_
  exact (ConcreteCategory.congr_hom (F.presheaf.map_id _) s).symm

/-- For `j ≫ q = 𝟙`, `j^* q^* F ≅ F` sends `j^* q^* s` to the restriction of `s`. -/
theorem pullbackPullback_unit {j : X ⟶ W} {q : W ⟶ X} (h : j ≫ q = 𝟙 X) (F : X.Modules)
    (T : X.Opens) (hT : j ⁻¹ᵁ (q ⁻¹ᵁ T) ≤ T) (s : Γ(F, T)) :
    ((pullbackComp j q).hom.app F ≫ (pullbackCongr h).hom.app F ≫ (pullbackId X).hom.app F).app
        (j ⁻¹ᵁ (q ⁻¹ᵁ T))
      (((pullbackPushforwardAdjunction j).unit.app ((Modules.pullback q).obj F)).app (q ⁻¹ᵁ T)
        (((pullbackPushforwardAdjunction q).unit.app F).app T s)) =
      F.presheaf.map (homOfLE hT).op s := by
  have e1 := pullbackComp_hom_unit j q F T s
  have e2 := pullbackCongr_id_unit h F T hT s
  change ((pullbackId X).hom.app F).app ((j ≫ q) ⁻¹ᵁ T)
    (((pullbackCongr h).hom.app F).app ((j ≫ q) ⁻¹ᵁ T)
      (((pullbackComp j q).hom.app F).app ((j ≫ q) ⁻¹ᵁ T)
        (((pullbackPushforwardAdjunction j).unit.app ((Modules.pullback q).obj F)).app (q ⁻¹ᵁ T)
          (((pullbackPushforwardAdjunction q).unit.app F).app T s)))) = _
  rw [e1]
  exact e2

end LeftInverse

section Inverse

open Scheme Scheme.Modules

variable (f : X ⟶ Y)

/-- The identification `j^* p₁^* Ω_{X/Y} ≅ Ω_{X/Y}`, from `j ≫ p₁ = 𝟙`. -/
noncomputable abbrev diagPullbackPullbackIso :
    (Modules.pullback (pullback.diagonal f).liftCoborder).obj
        ((Modules.pullback (diagFst f)).obj (relativeDifferentials f)) ⟶
      relativeDifferentials f :=
  (pullbackComp _ (diagFst f)).hom.app _ ≫ (pullbackCongr (liftCoborder_diagFst f)).hom.app _ ≫
    (pullbackId X).hom.app _

/-- **A left inverse of the comparison morphism**: the conormal map `N^*_Δ ⟶ j^* Ω_{W/X}` of the
closed immersion `j : X ⟶ W` over `p₂`, followed by `j^* Ω_{W/X} ≅ j^* p₁^* Ω_{X/Y} ≅ Ω_{X/Y}`
(base change and `j ≫ p₁ = 𝟙`). -/
noncomputable def diagonalConormalToRelativeDifferentials :
    immersionConormalSheaf (pullback.diagonal f) ⟶ relativeDifferentials f :=
  haveI := isIso_squareMap f
  ClosedConormal.conormalToPullback (pullback.diagonal f).liftCoborder (diagSnd f) ≫
    (Modules.pullback (pullback.diagonal f).liftCoborder).map
      (inv (squareMap f (diagFst_comp f))) ≫ diagPullbackPullbackIso f

theorem diagonalConormalToRelativeDifferentials_conormalD (U : X.Opens) (a : Γ(X, U)) :
    (diagonalConormalToRelativeDifferentials f).app U
        (conormalD (liftCoborder_diagFst f) (liftCoborder_diagSnd f) U a) =
      (relativeDifferentialsDerivation f).d (X := op U) a := by
  have := isIso_squareMap f
  set j := (pullback.diagonal f).liftCoborder
  set q₁ := diagFst f
  set q₂ := diagSnd f
  set T := nbhd q₁ q₂ U
  set β := diagonalConormalToRelativeDifferentials f
  set Ψ := inv (squareMap f (diagFst_comp f))
  set t := idealSection (liftCoborder_diagFst f) (liftCoborder_diagSnd f) U a
  have hl : T ≤ q₁ ⁻¹ᵁ U := inf_le_left
  -- Step C: the conormal map on `j^* t`.
  have sC : (ClosedConormal.conormalToPullback j q₂).app (j ⁻¹ᵁ T) (unitApp (j := j) T t) =
      (ClosedConormal.unitΩ j q₂).app T
        ((relativeDifferentialsDerivation q₂).d ((closedImmersionIdealSheafι j).app T t)) := by
    have h := ClosedConormal.homEquiv_conormalToPullback j q₂
    rw [Adjunction.homEquiv_unit] at h
    exact ConcreteCategory.congr_hom (congrArg (fun φ => Modules.Hom.app φ T) h) t
  -- Step E: `d (ι t)` is the image of `p₁^*(d a)`.
  have sE : (relativeDifferentialsDerivation q₂).d ((closedImmersionIdealSheafι j).app T t) =
      (relativeDifferentials q₂).presheaf.map (homOfLE hl).op
        ((squareMap f (diagFst_comp f)).app (q₁ ⁻¹ᵁ U)
          (((Modules.pullbackPushforwardAdjunction q₁).unit.app (relativeDifferentials f)).app U
            ((relativeDifferentialsDerivation f).d a))) := by
    have e0 : (relativeDifferentialsDerivation q₂).d (X := op (q₂ ⁻¹ᵁ U)) (q₂.app U a) = 0 :=
      RelDiffLocal.kills_of_derivation q₂ (relativeDifferentialsDerivation q₂) U a
    have e1 := (relativeDifferentialsDerivation q₂).d_map (homOfLE hl).op (q₁.app U a)
    have e2 := (relativeDifferentialsDerivation q₂).d_map
      (homOfLE (inf_le_right : T ≤ q₂ ⁻¹ᵁ U)).op (q₂.app U a)
    erw [ι_idealSection, diffSection_apply, map_sub, e1, e2, e0, map_zero, sub_zero]
    exact congrArg _ (squareMap_unit_d f (diagFst_comp f) U a).symm
  have ge := (preimage_nbhd (liftCoborder_diagFst f) (liftCoborder_diagSnd f) U).ge
  have hm : j ⁻¹ᵁ T ≤ j ⁻¹ᵁ (q₁ ⁻¹ᵁ U) := fun x hx => hl hx
  have hT : (j ≫ q₁) ⁻¹ᵁ U ≤ U := by
    rw [liftCoborder_diagFst f]; exact le_rfl
  set z := ((Modules.pullbackPushforwardAdjunction q₁).unit.app (relativeDifferentials f)).app U
    ((relativeDifferentialsDerivation f).d a)
  -- Step H: `j^* p₁^* (d a) ↦ d a`.
  have sH : (diagPullbackPullbackIso f).app (j ⁻¹ᵁ (q₁ ⁻¹ᵁ U))
      (((Modules.pullbackPushforwardAdjunction j).unit.app
        ((Modules.pullback q₁).obj (relativeDifferentials f))).app (q₁ ⁻¹ᵁ U) z) =
      (relativeDifferentials f).presheaf.map (homOfLE hT).op
        ((relativeDifferentialsDerivation f).d (X := op U) a) := by
    exact pullbackPullback_unit (liftCoborder_diagFst f) _ U hT _
  -- Step Ψ: `Ψ (φ z) = z`.
  have sΨ : Ψ.app (q₁ ⁻¹ᵁ U) ((squareMap f (diagFst_comp f)).app (q₁ ⁻¹ᵁ U) z) = z :=
    ConcreteCategory.congr_hom (congrArg (fun φ => Modules.Hom.app φ (q₁ ⁻¹ᵁ U))
      (IsIso.hom_inv_id (squareMap f (diagFst_comp f)))) z
  refine (Scheme.Modules.app_presheaf_map β (homOfLE ge) (unitApp (j := j) T t)).trans ?_
  have sB : β.app (j ⁻¹ᵁ T) (unitApp (j := j) T t) = (diagPullbackPullbackIso f).app (j ⁻¹ᵁ T)
      (((Modules.pullback j).map Ψ).app (j ⁻¹ᵁ T)
        ((ClosedConormal.conormalToPullback j q₂).app (j ⁻¹ᵁ T) (unitApp (j := j) T t))) := rfl
  have sD := pullback_map_unit j Ψ T ((relativeDifferentials q₂).presheaf.map (homOfLE hl).op
    ((squareMap f (diagFst_comp f)).app (q₁ ⁻¹ᵁ U) z))
  have sΨ' := Scheme.Modules.app_presheaf_map Ψ (homOfLE hl)
    ((squareMap f (diagFst_comp f)).app (q₁ ⁻¹ᵁ U) z)
  have sF := Scheme.Modules.app_presheaf_map (((Modules.pullbackPushforwardAdjunction j).unit.app
      ((Modules.pullback q₁).obj (relativeDifferentials f)))) (homOfLE hl) z
  have sG := Scheme.Modules.app_presheaf_map (diagPullbackPullbackIso f) (homOfLE hm)
    (((Modules.pullbackPushforwardAdjunction j).unit.app
      ((Modules.pullback q₁).obj (relativeDifferentials f))).app (q₁ ⁻¹ᵁ U) z)
  rw [sB, sC, sE]
  erw [sD]
  rw [sΨ', sΨ]
  erw [sF]
  erw [sG]
  erw [sH]
  exact ((congrArg _ (Scheme.Modules.presheaf_map_map (relativeDifferentials f)
    (homOfLE hT).op (homOfLE hm).op (homOfLE (hm.trans hT)).op _)).trans
    (Scheme.Modules.presheaf_map_map _ _ _ (𝟙 (op U)) _)).trans
    (ConcreteCategory.congr_hom ((relativeDifferentials f).presheaf.map_id _) _)

end Inverse

section AffineChart

variable (f : X ⟶ Y) (U : X.affineOpens) (V : Y.affineOpens)
  (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens))

/-- The open immersion `U ×_V U ⟶ X ×_Y X`. -/
noncomputable abbrev chartMap :
    pullback (f.resLE V U hUV) (f.resLE V U hUV) ⟶ pullback f f :=
  pullback.map _ _ _ _ (U : X.Opens).ι (U : X.Opens).ι (V : Y.Opens).ι (by simp) (by simp)

theorem range_chartMap :
    Set.range (chartMap f U V hUV) =
      pullback.fst f f ⁻¹' ((U : X.Opens) : Set X) ∩
        pullback.snd f f ⁻¹' ((U : X.Opens) : Set X) := by
  rw [Scheme.Pullback.range_map]
  simp only [Scheme.Opens.range_ι]

theorem diagonal_chartMap :
    pullback.diagonal (f.resLE V U hUV) ≫ chartMap f U V hUV =
      (U : X.Opens).ι ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, ← Category.assoc,
      pullback.diagonal_fst, Category.id_comp, pullback.diagonal_fst, Category.comp_id]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, ← Category.assoc,
      pullback.diagonal_snd, Category.id_comp, pullback.diagonal_snd, Category.comp_id]

theorem preimage_range_diagonal :
    chartMap f U V hUV ⁻¹' Set.range (pullback.diagonal f) =
      Set.range (pullback.diagonal (f.resLE V U hUV)) := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    have hxU : x ∈ (U : X.Opens) := by
      have e : pullback.fst f f (pullback.diagonal f x) = x := by
        rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
        rfl
      rw [← e, hx, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
      exact (pullback.fst (f.resLE V U hUV) (f.resLE V U hUV) z).2
    obtain ⟨u, rfl⟩ : x ∈ Set.range (U : X.Opens).ι := by simpa using hxU
    refine ⟨u, (chartMap f U V hUV).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, diagonal_chartMap, Scheme.Hom.comp_apply, hx]
  · rintro ⟨u, rfl⟩
    refine ⟨(U : X.Opens).ι u, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← diagonal_chartMap, Scheme.Hom.comp_apply]

include hUV in
/-- The open `U ×_V U = p₁⁻¹ U ∩ p₂⁻¹ U` lies in the open where the diagonal is closed. -/
theorem chart_le_coborderRange :
    pullback.fst f f ⁻¹ᵁ (U : X.Opens) ⊓ pullback.snd f f ⁻¹ᵁ (U : X.Opens) ≤
      (pullback.diagonal f).coborderRange := by
  intro x hx
  have hx' : x ∈ Set.range (chartMap f U V hUV) := by
    rw [range_chartMap]; exact hx
  obtain ⟨z, rfl⟩ := hx'
  have hcl : IsClosed (Set.range (pullback.diagonal (f.resLE V U hUV))) :=
    (pullback.diagonal (f.resLE V U hUV)).isClosedEmbedding.isClosed_range
  have h := (chartMap f U V hUV).isOpenEmbedding.coborder_preimage
    (Set.range (pullback.diagonal f))
  rw [preimage_range_diagonal, coborder_eq_univ_iff.mpr hcl] at h
  have hz : z ∈ chartMap f U V hUV ⁻¹' coborder (Set.range (pullback.diagonal f)) := by
    rw [← h]; trivial
  exact hz

include hUV in
/-- The open `p₁⁻¹ U ∩ p₂⁻¹ U` of `W` is affine. -/
theorem isAffineOpen_nbhd : IsAffineOpen (nbhd (diagFst f) (diagSnd f) (U : X.Opens)) :=
  (IsAffineOpen.pullback_inf U.2 U.2 V.2 hUV hUV).preimage_of_isOpenImmersion
    (pullback.diagonal f).coborderRange.ι
    (by rw [Scheme.Opens.opensRange_ι]; exact chart_le_coborderRange f U V hUV)

include hUV in
/-- Every function on `p₁⁻¹ U ∩ p₂⁻¹ U ⊆ W` is a sum of products `p₁^* a · p₂^* b`. -/
theorem mem_closure_nbhd (s : Γ((pullback.diagonal f).coborderRange.toScheme,
      nbhd (diagFst f) (diagSnd f) (U : X.Opens))) :
    s ∈ AddSubmonoid.closure (Set.range fun p : Γ(X, (U : X.Opens)) × Γ(X, (U : X.Opens)) =>
      (diagFst f).appLE U _ inf_le_left p.1 * (diagSnd f).appLE U _ inf_le_right p.2) := by
  have hP := AlgebraicGeometry.Scheme.baseChange_isPushout f f U V U hUV hUV
  have hle : pullback.fst f f ⁻¹ᵁ (U : X.Opens) ⊓ pullback.snd f f ⁻¹ᵁ (U : X.Opens) ≤
      (pullback.diagonal f).coborderRange.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]; exact chart_le_coborderRange f U V hUV
  have hiso := (pullback.diagonal f).coborderRange.ι.isIso_app _ hle
  obtain ⟨s₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((pullback.diagonal f).coborderRange.ι.app
      (pullback.fst f f ⁻¹ᵁ (U : X.Opens) ⊓ pullback.snd f f ⁻¹ᵁ (U : X.Opens)))).2 s
  have hs₀ := mem_closure_of_isPushout hP s₀
  induction hs₀ using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    refine AddSubmonoid.subset_closure ⟨(a, b), ?_⟩
    dsimp only
    rw [map_mul]
    congr 1
    · rw [← ConcreteCategory.comp_apply,
        Scheme.Hom.app_eq_appLE (pullback.diagonal f).coborderRange.ι,
        Scheme.Hom.appLE_comp_appLE]
      rfl
    · rw [← ConcreteCategory.comp_apply,
        Scheme.Hom.app_eq_appLE (pullback.diagonal f).coborderRange.ι,
        Scheme.Hom.appLE_comp_appLE]
      rfl
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy

end AffineChart

section Surjective

open QuasicoherentAbelianAux in
/-- For a closed immersion `i` with ideal sheaf `I` and an affine open `O`, the unit
`I ⟶ i_* i^* I` is surjective on sections over `O`. -/
theorem unit_app_surjective_of_isAffineOpen {Z : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    (O : W.Opens) (hO : IsAffineOpen O) :
    Function.Surjective (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (closedImmersionIdealSheaf i)).app O) := by
  have := isQuasicoherent_closedImmersionIdealSheaf i
  have : (idealTensor (I := closedImmersionIdealSheaf i)
      (closedImmersionIdealSheaf i)).IsQuasicoherent :=
    isQuasicoherent_moduleSheafTensor _ _
  have : IsOpenImmersion hO.fromSpec := hO.isOpenImmersion_fromSpec
  have hO' : hO.fromSpec ''ᵁ ⊤ = O := by
    rw [Scheme.Hom.image_top_eq_opensRange, hO.opensRange_fromSpec]
  have hb := bijective_idealSheafSqQuotientToPushforward_app i ⟨O, hO⟩
  have hπ := surjective_cokernel_π_app
    (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i)) ⟨O, hO⟩
  have hπΨ : ∀ x, (idealSheafSqQuotientToPushforward i).app (hO.fromSpec ''ᵁ ⊤)
      ((cokernel.π (idealMul (closedImmersionIdealSheafι i) (closedImmersionIdealSheaf i))).app
        (hO.fromSpec ''ᵁ ⊤) x) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (closedImmersionIdealSheaf i)).app (hO.fromSpec ''ᵁ ⊤) x := fun x =>
    ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ (hO.fromSpec ''ᵁ ⊤))
      (cokernel.π_desc _ _ (idealMul_comp_unit i))) x
  have key : Function.Surjective (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (closedImmersionIdealSheaf i)).app (hO.fromSpec ''ᵁ ⊤)) := by
    intro y
    obtain ⟨z, rfl⟩ := hb.2 y
    obtain ⟨x, rfl⟩ := hπ z
    exact ⟨x, (hπΨ x).symm⟩
  rw [hO'] at key
  exact key

variable (f : X ⟶ Y) (U : X.affineOpens) (V : Y.affineOpens)
  (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Y.Opens))

include hUV in
/-- On an affine open `U` over an affine open of `Y`, the comparison morphism is surjective on
sections. -/
theorem relativeDifferentialsToDiagonalConormal_app_surjective :
    Function.Surjective ((relativeDifferentialsToDiagonalConormal f).app U) := by
  intro y
  have hy := mem_span_conormalD (liftCoborder_diagFst f) (liftCoborder_diagSnd f) (U : X.Opens)
    (mem_closure_nbhd f U V hUV)
    (unit_app_surjective_of_isAffineOpen _ _ (isAffineOpen_nbhd f U V hUV)) y
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact ⟨_, relativeDifferentialsToDiagonalConormal_app_d f U b⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨ω₁, h₁⟩ := hx
    obtain ⟨ω₂, h₂⟩ := hy
    exact ⟨ω₁ + ω₂, (map_add _ _ _).trans (congrArg₂ (· + ·) h₁ h₂)⟩
  | smul r x _ hx =>
    obtain ⟨ω, hω⟩ := hx
    exact ⟨r • ω, (Scheme.Modules.Hom.app_smul _ r ω).trans (congrArg (r • ·) hω)⟩

end Surjective

section Isomorphism

open Scheme Scheme.Modules

variable (f : X ⟶ Y)

/-- The comparison morphism followed by its left inverse is the identity. -/
theorem relativeDifferentialsToDiagonalConormal_comp_inverse :
    relativeDifferentialsToDiagonalConormal f ≫ diagonalConormalToRelativeDifferentials f =
      𝟙 _ := by
  apply (relativeDifferentialsHomEquiv f _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext ⟨U⟩ a
  change Γ(X, U) at a
  change (diagonalConormalToRelativeDifferentials f).app U
    ((relativeDifferentialsToDiagonalConormal f).app U
      ((relativeDifferentialsDerivation f).d (X := op U) a)) =
    (relativeDifferentialsDerivation f).d (X := op U) a
  exact (congrArg _ (relativeDifferentialsToDiagonalConormal_app_d f U a)).trans
    (diagonalConormalToRelativeDifferentials_conormalD f U a)

/-- The comparison morphism is an epimorphism: it is locally surjective on sections. -/
theorem epi_relativeDifferentialsToDiagonalConormal :
    Epi (relativeDifferentialsToDiagonalConormal f) := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (relativeDifferentialsToDiagonalConormal f)).hom := by
    rw [TopCat.Presheaf.isLocallySurjective_iff]
    intro U y x hx
    obtain ⟨V, hV, hfxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f x) trivial
    obtain ⟨U', hU', hxU', hU'le⟩ := exists_isAffineOpen_mem_and_subset
      (U := U ⊓ f ⁻¹ᵁ V) (x := x) ⟨hx, hfxV⟩
    obtain ⟨ω, hω⟩ := relativeDifferentialsToDiagonalConormal_app_surjective f ⟨U', hU'⟩ ⟨V, hV⟩
      (hU'le.trans inf_le_right)
      ((immersionConormalSheaf (pullback.diagonal f)).presheaf.map
        (homOfLE (hU'le.trans inf_le_left)).op y)
    exact ⟨U', hU'le.trans inf_le_left, ⟨ω, hω⟩, hxU'⟩
  have : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (relativeDifferentialsToDiagonalConormal f)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hls
  exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map this

/-- The comparison morphism `Ω_{X/Y} ⟶ N^*_Δ` is an isomorphism. -/
theorem isIso_relativeDifferentialsToDiagonalConormal :
    IsIso (relativeDifferentialsToDiagonalConormal f) := by
  have := epi_relativeDifferentialsToDiagonalConormal f
  refine ⟨diagonalConormalToRelativeDifferentials f,
    relativeDifferentialsToDiagonalConormal_comp_inverse f, ?_⟩
  rw [← cancel_epi (relativeDifferentialsToDiagonalConormal f), ← Category.assoc,
    relativeDifferentialsToDiagonalConormal_comp_inverse, Category.id_comp, Category.comp_id]

/-- **Hartshorne II, p. 175: the relative differentials are the conormal sheaf of the
diagonal.** For a morphism of schemes `f : X ⟶ Y` with diagonal `Δ : X ⟶ X ×_Y X`, the canonical
morphism `Ω_{X/Y} ⟶ N^*_Δ`, sending `d a` to the class of `p₁^* a - p₂^* a`, is an isomorphism
of `𝒪_X`-modules. -/
noncomputable def relativeDifferentialsDiagonalConormalIso :
    relativeDifferentials f ≅ immersionConormalSheaf (pullback.diagonal f) :=
  haveI := isIso_relativeDifferentialsToDiagonalConormal f
  asIso (relativeDifferentialsToDiagonalConormal f)

end Isomorphism

end Hartshorne.DiagonalConormal
