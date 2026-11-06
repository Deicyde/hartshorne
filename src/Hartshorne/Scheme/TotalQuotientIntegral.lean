/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CartierDivisor
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# The total quotient sheaf of an integral scheme

Hartshorne, *Algebraic Geometry*, II.6 (p. 141): on an integral scheme `X` the sheaf of total
quotient rings `K_X` is the constant sheaf with value the function field `K(X)`.

We construct a morphism from `K_X` to the skyscraper sheaf at the generic point with value `K(X)`
(whose sections over every nonempty open set are `K(X)`), by sending a local fraction `a / s` to
the quotient of the germs of `a` and `s` at the generic point, and show that it is an isomorphism:
it is injective on sections because germs at the generic point are injective, and locally
surjective because `K(X)` is the fraction field of the ring of sections of every nonempty affine
open set. Consequently, for every open `U` containing the generic point, we obtain ring and unit
group isomorphisms `K_X(U) ≃ K(X)` and `K_X^*(U) ≃ K(X)^*`, compatible with restriction and with
the inclusion of regular functions.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {X : Scheme.{u}}

noncomputable section

/-- The denominators inverted in the total quotient presheaf: sections whose germs are
non-zero-divisors at every point. -/
abbrev totalQuotientPresheafDenominators (X : Scheme.{u}) (U : X.Opensᵒᵖ) :
    Submonoid Γ(X, U.unop) :=
  (X.sheaf.presheaf.submonoidPresheafOfStalk
    (fun x ↦ nonZeroDivisors (X.sheaf.presheaf.stalk x))).obj U

theorem totalQuotientPresheaf_isLocalization (U : X.Opensᵒᵖ) :
    IsLocalization (totalQuotientPresheafDenominators X U) (X.totalQuotientPresheaf.obj U) :=
  inferInstanceAs (IsLocalization ((X.sheaf.presheaf.submonoidPresheafOfStalk
    (fun x ↦ nonZeroDivisors (X.sheaf.presheaf.stalk x))).obj U)
    ((X.sheaf.presheaf.submonoidPresheafOfStalk
    (fun x ↦ nonZeroDivisors (X.sheaf.presheaf.stalk x))).localizationPresheaf.obj U))

/-- The generic point lies in every nonempty open set. -/
theorem genericPoint_mem_opens_of_mem [IrreducibleSpace X] {U : X.Opens} {x : X} (hx : x ∈ U) :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

/-- An open set not containing the generic point is empty. -/
theorem opens_eq_bot_of_genericPoint_notMem [IrreducibleSpace X] {U : X.Opens}
    (h : genericPoint X ∉ U) : U = ⊥ := by
  have h' : ¬ (U : Set X).Nonempty := fun hne ↦
    h (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne))
  exact SetLike.ext' (Set.not_nonempty_iff_eq_empty.mp h')

variable [IsIntegral X]

theorem isUnit_germ_genericPoint_of_mem_totalQuotientPresheafDenominators (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(X, U)) (hs : s ∈ totalQuotientPresheafDenominators X (op U)) :
    IsUnit (X.presheaf.germ U (genericPoint X) h s) := by
  have := Submonoid.mem_iInf.mp hs ⟨_, h⟩
  exact isUnit_iff_ne_zero.mpr (nonZeroDivisors.ne_zero this)

/-- The map from a section of the total quotient presheaf over an open set containing the generic
point to the function field, sending `a / s` to the quotient of the germs of `a` and `s`. -/
def totalQuotientPresheafToFunctionField (U : X.Opens) (h : genericPoint X ∈ U) :
    X.totalQuotientPresheaf.obj (op U) ⟶ X.functionField :=
  haveI := totalQuotientPresheaf_isLocalization (X := X) (op U)
  CommRingCat.ofHom <| IsLocalization.lift (M := totalQuotientPresheafDenominators X (op U))
    (S := X.totalQuotientPresheaf.obj (op U))
    (g := (X.presheaf.germ U (genericPoint X) h).hom)
    (fun s ↦ isUnit_germ_genericPoint_of_mem_totalQuotientPresheafDenominators U h s s.2)

theorem totalQuotientPresheafToFunctionField_algebraMap (U : X.Opens) (h : genericPoint X ∈ U)
    (a : Γ(X, U)) :
    totalQuotientPresheafToFunctionField U h
        (algebraMap Γ(X, U) (X.totalQuotientPresheaf.obj (op U)) a) =
      X.presheaf.germ U (genericPoint X) h a := by
  have := totalQuotientPresheaf_isLocalization (X := X) (op U)
  exact IsLocalization.lift_eq (M := totalQuotientPresheafDenominators X (op U))
    (S := X.totalQuotientPresheaf.obj (op U)) _ a

theorem totalQuotientPresheafToFunctionField_map {U V : X.Opens} (i : V ≤ U)
    (h : genericPoint X ∈ V) (s) :
    totalQuotientPresheafToFunctionField V h (X.totalQuotientPresheaf.map (homOfLE i).op s) =
      totalQuotientPresheafToFunctionField U (i h) s := by
  suffices H : (totalQuotientPresheafToFunctionField V h).hom.comp
      (X.totalQuotientPresheaf.map (homOfLE i).op).hom =
      (totalQuotientPresheafToFunctionField U (i h)).hom from DFunLike.congr_fun H s
  have := totalQuotientPresheaf_isLocalization (X := X) (op U)
  refine IsLocalization.ringHom_ext (totalQuotientPresheafDenominators X (op U)) ?_
  ext a
  simp only [RingHom.comp_apply]
  rw [totalQuotientPresheafToFunctionField_algebraMap]
  have : X.totalQuotientPresheaf.map (homOfLE i).op
      (algebraMap Γ(X, U) (X.totalQuotientPresheaf.obj (op U)) a) =
      algebraMap Γ(X, V) (X.totalQuotientPresheaf.obj (op V))
        (X.presheaf.map (homOfLE i).op a) :=
    (ConcreteCategory.congr_hom
      (X.sheaf.presheaf.toTotalQuotientPresheaf.naturality (homOfLE i).op) a).symm
  rw [this, totalQuotientPresheafToFunctionField_algebraMap, X.presheaf.germ_res_apply]

theorem totalQuotientPresheafToFunctionField_injective (U : X.Opens) (h : genericPoint X ∈ U) :
    Function.Injective (totalQuotientPresheafToFunctionField U h) := by
  have := totalQuotientPresheaf_isLocalization (X := X) (op U)
  have hg := germ_injective_of_isIntegral (X := X) (U := U) (genericPoint X) h
  change Function.Injective (IsLocalization.lift (M := totalQuotientPresheafDenominators X (op U))
    (S := X.totalQuotientPresheaf.obj (op U))
    (g := (X.presheaf.germ U (genericPoint X) h).hom) _)
  rw [IsLocalization.lift_injective_iff]
  intro a b
  constructor
  · intro hab
    have := congrArg (totalQuotientPresheafToFunctionField U h) hab
    rwa [totalQuotientPresheafToFunctionField_algebraMap,
      totalQuotientPresheafToFunctionField_algebraMap] at this
  · intro hab
    rw [hg hab]

/-- On a nonempty affine open set, every rational function is a fraction of regular functions
whose denominator has nonzero germs everywhere. -/
theorem exists_totalQuotientPresheafToFunctionField_eq (U : X.Opens) (hU : IsAffineOpen U)
    (h : genericPoint X ∈ U) (k : X.functionField) :
    ∃ s, totalQuotientPresheafToFunctionField U h s = k := by
  have := totalQuotientPresheaf_isLocalization (X := X) (op U)
  have : Nonempty U := ⟨⟨_, h⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) k
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbden : b ∈ totalQuotientPresheafDenominators X (op U) := by
    refine Submonoid.mem_iInf.mpr fun y ↦ ?_
    change X.presheaf.germ U y.1 y.2 b ∈ nonZeroDivisors (X.presheaf.stalk y.1)
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro hy
    apply hb0
    apply germ_injective_of_isIntegral (X := X) (U := U) y.1 y.2
    rw [hy, map_zero]
  refine ⟨IsLocalization.mk' (X.totalQuotientPresheaf.obj (op U)) a ⟨b, hbden⟩, ?_⟩
  rw [eq_div_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)]
  have := congrArg (totalQuotientPresheafToFunctionField U h)
    (IsLocalization.mk'_spec (S := X.totalQuotientPresheaf.obj (op U)) a ⟨b, hbden⟩)
  rw [map_mul, totalQuotientPresheafToFunctionField_algebraMap,
    totalQuotientPresheafToFunctionField_algebraMap] at this
  exact this

/-- The induced map from the stalk of the total quotient presheaf at the generic point to the
function field. -/
def totalQuotientStalkToFunctionField (X : Scheme.{u}) [IsIntegral X] :
    X.totalQuotientPresheaf.stalk (genericPoint X) ⟶ X.functionField :=
  colimit.desc _
    { pt := X.functionField
      ι :=
        { app := fun V ↦ totalQuotientPresheafToFunctionField V.unop.1 V.unop.2
          naturality := fun V W i ↦ by
            ext s
            exact totalQuotientPresheafToFunctionField_map (leOfHom i.unop) W.unop.2 s } }

theorem germ_totalQuotientStalkToFunctionField (U : X.Opens) (h : genericPoint X ∈ U) :
    X.totalQuotientPresheaf.germ U (genericPoint X) h ≫ totalQuotientStalkToFunctionField X =
      totalQuotientPresheafToFunctionField U h :=
  colimit.ι_desc _ _

open Classical in
/-- The morphism from the total quotient presheaf to the skyscraper presheaf at the generic point
with value the function field. -/
def totalQuotientPresheafToSkyscraper (X : Scheme.{u}) [IsIntegral X] :
    X.totalQuotientPresheaf ⟶ skyscraperPresheaf (genericPoint X) X.functionField :=
  StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf _
    (totalQuotientStalkToFunctionField X)

open Classical in
theorem functionFieldSkyscraper_obj_eq (U : X.Opens) (h : genericPoint X ∈ U) :
    (skyscraperPresheaf (genericPoint X) X.functionField).obj (op U) = X.functionField := by
  rw [skyscraperPresheaf_obj, if_pos h]

set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem totalQuotientPresheafToSkyscraper_app (U : X.Opens) (h : genericPoint X ∈ U) :
    (totalQuotientPresheafToSkyscraper X).app (op U) =
      totalQuotientPresheafToFunctionField U h ≫
        eqToHom (functionFieldSkyscraper_obj_eq U h).symm := by
  rw [totalQuotientPresheafToSkyscraper,
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app]
  rw [dif_pos h, ← Category.assoc, germ_totalQuotientStalkToFunctionField]

set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem totalQuotientPresheafToSkyscraper_injective (U : X.Opensᵒᵖ) :
    Function.Injective ((totalQuotientPresheafToSkyscraper X).app U) := by
  by_cases h : genericPoint X ∈ U.unop
  · rw [show U = op U.unop from rfl, totalQuotientPresheafToSkyscraper_app U.unop h]
    intro s t hst
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hst
    exact totalQuotientPresheafToFunctionField_injective U.unop h
      ((ConcreteCategory.bijective_of_isIso _).1 hst)
  · have hU := opens_eq_bot_of_genericPoint_notMem h
    have : Subsingleton Γ(X, U.unop) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hU)
    have := totalQuotientPresheaf_isLocalization (X := X) U
    have : Subsingleton (X.totalQuotientPresheaf.obj U) := by
      refine subsingleton_of_zero_eq_one ?_
      rw [← map_zero (algebraMap Γ(X, U.unop) (X.totalQuotientPresheaf.obj U)),
        ← map_one (algebraMap Γ(X, U.unop) (X.totalQuotientPresheaf.obj U)),
        Subsingleton.elim (0 : Γ(X, U.unop)) 1]
    intro s t _
    exact Subsingleton.elim s t

set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem totalQuotientPresheafToSkyscraper_isLocallySurjective :
    TopCat.Presheaf.IsLocallySurjective (totalQuotientPresheafToSkyscraper X) := by
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro U t x hx
  have hU : genericPoint X ∈ U := genericPoint_mem_opens_of_mem hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hV' : genericPoint X ∈ V := genericPoint_mem_opens_of_mem hxV
  obtain ⟨s, hs⟩ := exists_totalQuotientPresheafToFunctionField_eq V hV hV'
    ((eqToHom (functionFieldSkyscraper_obj_eq U hU)) t)
  refine ⟨V, hVU, ⟨s, ?_⟩, hxV⟩
  rw [totalQuotientPresheafToSkyscraper_app V hV', ConcreteCategory.comp_apply, hs,
    ← ConcreteCategory.comp_apply, eqToHom_trans]
  change _ = (skyscraperPresheaf (genericPoint X) X.functionField).map (homOfLE hVU).op t
  rw [skyscraperPresheaf_map, dif_pos hV']

open Classical in
/-- The morphism from the total quotient sheaf of an integral scheme to the skyscraper sheaf at
the generic point with value the function field. -/
def totalQuotientSheafToSkyscraper (X : Scheme.{u}) [IsIntegral X] :
    X.totalQuotientSheaf ⟶ skyscraperSheaf (genericPoint X) X.functionField :=
  ObjectProperty.homMk
    (sheafifyLift _ (totalQuotientPresheafToSkyscraper X) (skyscraperSheaf _ _).property)

open Classical in
theorem toSheafify_totalQuotientSheafToSkyscraper :
    toSheafify (Opens.grothendieckTopology X) X.totalQuotientPresheaf ≫
      (totalQuotientSheafToSkyscraper X).hom = totalQuotientPresheafToSkyscraper X :=
  toSheafify_sheafifyLift _ _ _

/-- On an integral scheme, the total quotient sheaf is the constant sheaf `K(X)`: its morphism to
the skyscraper sheaf at the generic point is an isomorphism. -/
theorem isIso_totalQuotientSheafToSkyscraper : IsIso (totalQuotientSheafToSkyscraper X) := by
  refine (Sheaf.isLocallyBijective_iff_isIso (J := Opens.grothendieckTopology X)
    (A := CommRingCat.{u}) (totalQuotientSheafToSkyscraper X)).1 ?_
  have hinj : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (totalQuotientPresheafToSkyscraper X) :=
    Presheaf.isLocallyInjective_of_injective _ _ totalQuotientPresheafToSkyscraper_injective
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (totalQuotientPresheafToSkyscraper X) :=
    totalQuotientPresheafToSkyscraper_isLocallySurjective
  constructor
  · exact @Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ toSheafify_totalQuotientSheafToSkyscraper hinj
      (Presheaf.isLocallySurjective_toSheafify' (J := Opens.grothendieckTopology X) _)
  · exact @Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      toSheafify_totalQuotientSheafToSkyscraper hsurj

set_option backward.isDefEq.respectTransparency false in
open Classical in
theorem toTotalQuotientSheaf_comp_totalQuotientSheafToSkyscraper :
    X.toTotalQuotientSheaf.hom ≫ (totalQuotientSheafToSkyscraper X).hom =
      X.sheaf.presheaf.toTotalQuotientPresheaf ≫ totalQuotientPresheafToSkyscraper X := by
  change (toSheafify (Opens.grothendieckTopology X) X.sheaf.presheaf ≫
      sheafifyMap (Opens.grothendieckTopology X) X.sheaf.presheaf.toTotalQuotientPresheaf) ≫
      sheafifyLift _ (totalQuotientPresheafToSkyscraper X) (skyscraperSheaf _ _).property = _
  rw [Category.assoc, sheafifyMap_sheafifyLift, toSheafify_sheafifyLift]

/-- On an integral scheme, the sections of the total quotient sheaf over an open set containing
the generic point are identified with the function field. -/
def totalQuotientSheafEquivFunctionField (U : X.Opens) (h : genericPoint X ∈ U) :
    X.totalQuotientSheaf.obj.obj (op U) ≃+* X.functionField :=
  (((sheafToPresheaf _ _).mapIso
    (@asIso _ _ _ _ (totalQuotientSheafToSkyscraper X)
      isIso_totalQuotientSheafToSkyscraper)).app (op U) ≪≫
    eqToIso (functionFieldSkyscraper_obj_eq U h)).commRingCatIsoToRingEquiv

theorem totalQuotientSheafEquivFunctionField_apply (U : X.Opens) (h : genericPoint X ∈ U) (s) :
    totalQuotientSheafEquivFunctionField U h s =
      eqToHom (functionFieldSkyscraper_obj_eq U h)
        ((totalQuotientSheafToSkyscraper X).hom.app (op U) s) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- The identification of sections with the function field is compatible with restriction. -/
theorem totalQuotientSheafEquivFunctionField_map {U V : X.Opens} (i : V ≤ U)
    (h : genericPoint X ∈ V) (s) :
    totalQuotientSheafEquivFunctionField V h (X.totalQuotientSheaf.obj.map (homOfLE i).op s) =
      totalQuotientSheafEquivFunctionField U (i h) s := by
  rw [totalQuotientSheafEquivFunctionField_apply, totalQuotientSheafEquivFunctionField_apply]
  have := ConcreteCategory.congr_hom
    ((totalQuotientSheafToSkyscraper X).hom.naturality (homOfLE i).op) s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  rw [this]
  change (eqToHom (functionFieldSkyscraper_obj_eq V h))
    ((skyscraperPresheaf (genericPoint X) X.functionField).map (homOfLE i).op _) = _
  rw [skyscraperPresheaf_map, dif_pos h, ← ConcreteCategory.comp_apply, eqToHom_trans]

private theorem eqToHom_eqToHom_apply {A B : CommRingCat.{u}} (p : A = B) (q : B = A) (x : A) :
    eqToHom q (eqToHom p x) = x := by
  subst p
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identification of sections with the function field sends a regular function to its germ
at the generic point. -/
theorem totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf (U : X.Opens)
    (h : genericPoint X ∈ U) (a : Γ(X, U)) :
    totalQuotientSheafEquivFunctionField U h (X.toTotalQuotientSheaf.hom.app (op U) a) =
      X.presheaf.germ U (genericPoint X) h a := by
  rw [totalQuotientSheafEquivFunctionField_apply]
  have := ConcreteCategory.congr_hom
    (NatTrans.congr_app toTotalQuotientSheaf_comp_totalQuotientSheafToSkyscraper (op U)) a
  rw [NatTrans.comp_app, NatTrans.comp_app, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, totalQuotientPresheafToSkyscraper_app U h,
    ConcreteCategory.comp_apply] at this
  rw [this]
  exact (eqToHom_eqToHom_apply _ _ _).trans
    (totalQuotientPresheafToFunctionField_algebraMap U h a)

/-- On an integral scheme, the sections of `K_X^*` over an open set containing the generic point
are identified with the nonzero rational functions. -/
def totalQuotientUnitsEquivFunctionField (U : X.Opens) (h : genericPoint X ∈ U) :
    X.totalQuotientUnitsSheaf.obj.obj (op U) ≃* X.functionFieldˣ :=
  Units.mapEquiv (totalQuotientSheafEquivFunctionField U h).toMulEquiv

theorem coe_totalQuotientUnitsEquivFunctionField (U : X.Opens) (h : genericPoint X ∈ U)
    (f : (X.totalQuotientSheaf.obj.obj (op U))ˣ) :
    (totalQuotientUnitsEquivFunctionField U h f : X.functionField) =
      totalQuotientSheafEquivFunctionField U h f :=
  rfl

theorem totalQuotientUnitsEquivFunctionField_map {U V : X.Opens} (i : V ≤ U)
    (h : genericPoint X ∈ V) (f) :
    totalQuotientUnitsEquivFunctionField V h (X.totalQuotientUnitsSheaf.obj.map (homOfLE i).op f) =
      totalQuotientUnitsEquivFunctionField U (i h) f := by
  ext
  exact totalQuotientSheafEquivFunctionField_map i h _

theorem totalQuotientUnitsEquivFunctionField_structureUnits (U : X.Opens)
    (h : genericPoint X ∈ U) (a : Γ(X, U)ˣ) :
    (totalQuotientUnitsEquivFunctionField U h
        (X.structureUnitsToTotalQuotientUnits.hom.app (op U) a) : X.functionField) =
      X.presheaf.germ U (genericPoint X) h a :=
  totalQuotientSheafEquivFunctionField_toTotalQuotientSheaf U h _

end

end AlgebraicGeometry.Scheme
