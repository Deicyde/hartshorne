/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.Differentials.AffineRelativeDifferentials

/-!
# The transitivity sequence for differential sheaves

Hartshorne, *Algebraic Geometry*, II.8, Proposition 8.11 (p. 176).

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` we construct the natural maps
`f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y}` and prove that the sequence
`f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0` of `𝒪_X`-modules is exact.

Both maps come from the universal property of the relative differential sheaf. The key input is
that a derivation `𝒪_X ⟶ M` kills the inverse image `f⁻¹𝒪_Y` as soon as it kills the comorphism
`f^♯`: the sections of `f⁻¹𝒪_Y` on which the derivation vanishes form a subsheaf of rings through
which the adjunction unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y` factors, so by adjunction the subsheaf is everything.
Then `d_{X/Y}` kills `(f ≫ g)^♯`, giving `Ω_{X/Z} ⟶ Ω_{X/Y}`, and `b ↦ d_{X/Z}(f^♯ b)` is a
derivation `𝒪_Y ⟶ f_*Ω_{X/Z}` killing `g^♯`, giving `Ω_{Y/Z} ⟶ f_*Ω_{X/Z}` and by adjunction
`f^*Ω_{Y/Z} ⟶ Ω_{X/Z}`. Right exactness is the statement that `Ω_{X/Z} ⟶ Ω_{X/Y}` is a cokernel:
a map `τ : Ω_{X/Z} ⟶ M` killing the image of `f^*Ω_{Y/Z}` corresponds to a derivation killing
`f^♯`, hence one killing `f⁻¹𝒪_Y`, hence to a map out of `Ω_{X/Y}`.

On affine charts `Spec C ⟶ Spec B ⟶ Spec A`, under the identifications of the differential
sheaves with the sheaves associated to Kähler modules, the second map is the sheaf associated to
`Ω_{C/A} ⟶ Ω_{C/B}`, and the first map sends `c · f^*(db)` to `c · db`, as does the first map
`C ⊗_B Ω_{B/A} ⟶ Ω_{C/A}` of the first exact sequence for Kähler differentials.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- The unit `𝒪_Y ⟶ f_* f⁻¹𝒪_Y` of the inverse-image adjunction for structure sheaves. -/
noncomputable abbrev inverseImageStructureSheafUnit (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj (inverseImageStructureSheaf f) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app Y.sheaf

/-- The unit followed by the structural map `f⁻¹𝒪_Y ⟶ 𝒪_X` is the comorphism of `f`. -/
theorem inverseImageStructureSheafMap_unit_apply (f : X ⟶ Y) (V : Y.Opens) (b : Γ(Y, V)) :
    (inverseImageStructureSheafMap f).hom.app (op (f ⁻¹ᵁ V))
      ((inverseImageStructureSheafUnit f).hom.app (op V) b) = f.app V b := by
  have h := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv_unit
    (X := Y.sheaf) (Y := X.sheaf) (f := inverseImageStructureSheafMap f)
  simp only [inverseImageStructureSheafMap] at h
  erw [Equiv.apply_symm_apply] at h
  exact (ConcreteCategory.congr_hom (congrArg (fun g => g.hom.app (op V)) h) b).symm

section Kernel

variable (f : X ⟶ Y) {M : X.Modules}
  (D : M.val.Derivation (F := Opens.map f.base) f.c)

/-- Sections of `f⁻¹𝒪_Y` on which a derivation killing `f^♯` vanishes. -/
def derivationKerSubring (U : X.Opensᵒᵖ) :
    Subring ((inverseImageStructureSheaf f).obj.obj U) where
  carrier := {s | D.d ((inverseImageStructureSheafMap f).hom.app U s) = 0}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
    rw [D.d_mul, ha, hb, smul_zero, smul_zero, add_zero]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one]
    exact D.d_one _
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    rw [ha, hb, add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_neg] at ha ⊢
    rw [ha, neg_zero]


/-- The presheaf of sections of `f⁻¹𝒪_Y` on which the derivation vanishes. -/
noncomputable def derivationKerPresheaf : TopCat.Presheaf CommRingCat X where
  obj U := CommRingCat.of (derivationKerSubring f D U)
  map {U V} i := CommRingCat.ofHom (((inverseImageStructureSheaf f).obj.map i).hom.restrict _ _
    (fun s (hs : D.d _ = 0) => by
      change D.d ((inverseImageStructureSheafMap f).hom.app V
        ((inverseImageStructureSheaf f).obj.map i s)) = 0
      rw [NatTrans.naturality_apply (inverseImageStructureSheafMap f).hom i s]
      erw [D.d_map i, hs, map_zero]
      rfl))
  map_id _ := by
    ext s
    exact (ConcreteCategory.congr_hom ((inverseImageStructureSheaf f).obj.map_id _) s.1)
  map_comp _ _ := by
    ext s
    exact (ConcreteCategory.congr_hom ((inverseImageStructureSheaf f).obj.map_comp _ _) s.1)

/-- The vanishing presheaf is a sheaf, because `f⁻¹𝒪_Y` and the module sheaf are sheaves. -/
theorem derivationKerPresheaf_isSheaf : (derivationKerPresheaf f D).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  have hsf' : TopCat.Presheaf.IsCompatible (inverseImageStructureSheaf f).obj U
      (fun i => (sf i).1) := fun i j => congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hsu⟩ := (inverseImageStructureSheaf f).existsUnique_gluing U _ hsf'
  let F : TopCat.Sheaf Ab.{u} X := ⟨M.val.presheaf, M.isSheaf⟩
  have hmem : s ∈ derivationKerSubring f D (op (iSup U)) := by
    change D.d _ = 0
    refine F.eq_of_locally_eq U _ 0 fun i => ?_
    change M.val.map (Opens.leSupr U i).op (D.d _) = M.val.map (Opens.leSupr U i).op 0
    rw [map_zero]
    erw [← D.d_map, ← NatTrans.naturality_apply (inverseImageStructureSheafMap f).hom]
    erw [hs i]
    exact (sf i).2
  exact ⟨⟨s, hmem⟩, fun i => Subtype.ext (hs i),
    fun t ht => Subtype.ext (hsu t.1 fun i => congrArg Subtype.val (ht i))⟩

/-- The subsheaf of sections of `f⁻¹𝒪_Y` on which the derivation vanishes. -/
noncomputable def derivationKerSheaf : TopCat.Sheaf CommRingCat X :=
  ⟨derivationKerPresheaf f D, derivationKerPresheaf_isSheaf f D⟩

/-- Its inclusion into `f⁻¹𝒪_Y`. -/
noncomputable def derivationKerSheafι : derivationKerSheaf f D ⟶ inverseImageStructureSheaf f :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (derivationKerSubring f D U).subtype
      naturality _ _ _ := rfl }

/-- The unit `𝒪_Y ⟶ f_* f⁻¹𝒪_Y` factors through the vanishing subsheaf. -/
noncomputable def derivationKerUnit :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj (derivationKerSheaf f D) :=
  ObjectProperty.homMk
    { app V := CommRingCat.ofHom (R := Y.presheaf.obj V)
        (S := derivationKerSubring f D (op (f ⁻¹ᵁ V.unop)))
        (((inverseImageStructureSheafUnit f).hom.app V).hom.codRestrict _ (fun b => by
          change D.d _ = 0
          erw [inverseImageStructureSheafMap_unit_apply f V.unop b]
          exact D.d_app b))
      naturality _ _ i := by
        ext b
        exact Subtype.ext (ConcreteCategory.congr_hom
          ((inverseImageStructureSheafUnit f).hom.naturality i) b) }

/-- A derivation killing the comorphism `f^♯` kills the whole inverse image `f⁻¹𝒪_Y`. -/
theorem derivation_d_inverseImage_eq_zero (U : X.Opensᵒᵖ)
    (a : (inverseImageStructureSheaf f).obj.obj U) :
    D.d ((inverseImageStructureSheafMap f).hom.app U a) = 0 := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base
  let r := (adj.homEquiv _ _).symm (derivationKerUnit f D)
  have key : derivationKerUnit f D ≫
      (TopCat.Sheaf.pushforward CommRingCat f.base).map (derivationKerSheafι f D) =
        adj.unit.app Y.sheaf := rfl
  have hr : r ≫ derivationKerSheafι f D = (adj.homEquiv _ _).symm (adj.unit.app Y.sheaf) := by
    rw [← key]
    exact (adj.homEquiv_naturality_right_symm _ _).symm
  have h1 : (adj.homEquiv _ _).symm (adj.unit.app Y.sheaf) =
      𝟙 ((TopCat.Sheaf.pullback CommRingCat f.base).obj Y.sheaf) := by
    rw [adj.homEquiv_counit]
    exact adj.left_triangle_components Y.sheaf
  have ha := ConcreteCategory.congr_hom (congrArg (fun g => g.hom.app U) (hr.trans h1)) a
  let x : derivationKerSubring f D U := r.hom.app U a
  have h2 : (x : (inverseImageStructureSheaf f).obj.obj U) = a := ha
  rw [← h2]
  exact x.2

end Kernel

/-- A derivation killing the comorphism `f^♯` is a relative derivation for `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
noncomputable def derivationToInverseImage (f : X ⟶ Y) {M : X.Modules}
    (D : M.val.Derivation (F := Opens.map f.base) f.c) :
    M.val.Derivation' (inverseImageStructureSheafMap f).hom where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app a := derivation_d_inverseImage_eq_zero f D _ a

/-- A relative derivation for `f⁻¹𝒪_Y ⟶ 𝒪_X` kills the comorphism `f^♯`. -/
noncomputable def derivationOfInverseImage (f : X ⟶ Y) {M : X.Modules}
    (D : M.val.Derivation' (inverseImageStructureSheafMap f).hom) :
    M.val.Derivation (F := Opens.map f.base) f.c where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {V} b := by
    have h := D.d_app ((inverseImageStructureSheafUnit f).hom.app V b)
    erw [inverseImageStructureSheafMap_unit_apply f V.unop b] at h
    exact h

/-- Relative derivations for `f⁻¹𝒪_Y ⟶ 𝒪_X` are exactly the derivations killing `f^♯`. -/
noncomputable def derivationInverseImageEquiv (f : X ⟶ Y) (M : X.Modules) :
    M.val.Derivation' (inverseImageStructureSheafMap f).hom ≃
      M.val.Derivation (F := Opens.map f.base) f.c where
  toFun := derivationOfInverseImage f
  invFun := derivationToInverseImage f
  left_inv _ := rfl
  right_inv _ := rfl

section Transitivity

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical derivation of `Ω_{X/Y}`, which also kills `(f ≫ g)^♯`. -/
noncomputable def transitivityDerivationLeft :
    (relativeDifferentials f).val.Derivation' (inverseImageStructureSheafMap (f ≫ g)).hom :=
  derivationToInverseImage (f ≫ g)
    { d := (relativeDifferentialsDerivation f).d
      d_mul := (relativeDifferentialsDerivation f).d_mul
      d_map := (relativeDifferentialsDerivation f).d_map
      d_app {W} t :=
        (derivationOfInverseImage f (relativeDifferentialsDerivation f)).d_app (g.c.app W t) }

/-- The derivation `𝒪_Y ⟶ f_*Ω_{X/Z}`, `b ↦ d(f^♯ b)`, relative to `g⁻¹𝒪_Z ⟶ 𝒪_Y`. -/
noncomputable def transitivityDerivationPushforward :
    ((Modules.pushforward f).obj (relativeDifferentials (f ≫ g))).val.Derivation'
      (inverseImageStructureSheafMap g).hom :=
  derivationToInverseImage g
    { d {V} := ((relativeDifferentialsDerivation (f ≫ g)).d (X := op (f ⁻¹ᵁ V.unop))).comp
        (f.c.app V).hom.toAddMonoidHom
      d_mul {V} a b := by
        change (relativeDifferentialsDerivation (f ≫ g)).d (f.c.app V (a * b)) = _
        refine (congrArg (relativeDifferentialsDerivation (f ≫ g)).d
          (map_mul (f.c.app V).hom a b)).trans ?_
        exact (relativeDifferentialsDerivation (f ≫ g)).d_mul _ _
      d_map {V W} i b := by
        change (relativeDifferentialsDerivation (f ≫ g)).d (f.c.app W (Y.presheaf.map i b)) = _
        rw [NatTrans.naturality_apply f.c i b]
        exact (relativeDifferentialsDerivation (f ≫ g)).d_map _ _
      d_app {W} t :=
        (derivationOfInverseImage (f ≫ g) (relativeDifferentialsDerivation (f ≫ g))).d_app t }

/-- The map `Ω_{X/Z} ⟶ Ω_{X/Y}` of the transitivity sequence. -/
noncomputable def relativeDifferentialsCompToLeft :
    relativeDifferentials (f ≫ g) ⟶ relativeDifferentials f :=
  (relativeDifferentialsHomEquiv (f ≫ g) _).symm (transitivityDerivationLeft f g)

/-- The adjoint `Ω_{Y/Z} ⟶ f_*Ω_{X/Z}` of the first map of the transitivity sequence. -/
noncomputable def relativeDifferentialsToPushforwardComp :
    relativeDifferentials g ⟶ (Modules.pushforward f).obj (relativeDifferentials (f ≫ g)) :=
  (relativeDifferentialsHomEquiv g _).symm (transitivityDerivationPushforward f g)

/-- The map `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` of the transitivity sequence. -/
noncomputable def pullbackRelativeDifferentialsToComp :
    (Modules.pullback f).obj (relativeDifferentials g) ⟶ relativeDifferentials (f ≫ g) :=
  ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (relativeDifferentialsToPushforwardComp f g)


/-- The map `Ω_{X/Z} ⟶ Ω_{X/Y}` sends `d_{X/Z} x` to `d_{X/Y} x`. -/
theorem relativeDifferentialsCompToLeft_d (U : X.Opensᵒᵖ) (x : X.presheaf.obj U) :
    (relativeDifferentialsCompToLeft f g).val.app U
      ((relativeDifferentialsDerivation (f ≫ g)).d x) =
        (relativeDifferentialsDerivation f).d x := by
  have h : (relativeDifferentialsDerivation (f ≫ g)).postcomp
      (relativeDifferentialsCompToLeft f g).val = transitivityDerivationLeft f g := by
    rw [← relativeDifferentialsHomEquiv_apply]
    exact Equiv.apply_symm_apply _ _
  exact PresheafOfModules.Derivation.congr_d h x

/-- The adjoint map `Ω_{Y/Z} ⟶ f_*Ω_{X/Z}` sends `d_{Y/Z} b` to `d_{X/Z}(f^♯ b)`. -/
theorem relativeDifferentialsToPushforwardComp_d (V : Y.Opensᵒᵖ) (b : Y.presheaf.obj V) :
    (relativeDifferentialsToPushforwardComp f g).val.app V
      ((relativeDifferentialsDerivation g).d b) =
        (relativeDifferentialsDerivation (f ≫ g)).d (f.c.app V b) := by
  have h : (relativeDifferentialsDerivation g).postcomp
      (relativeDifferentialsToPushforwardComp f g).val = transitivityDerivationPushforward f g := by
    rw [← relativeDifferentialsHomEquiv_apply]
    exact Equiv.apply_symm_apply _ _
  exact PresheafOfModules.Derivation.congr_d h b

/-- The adjoint transpose of `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` is `Ω_{Y/Z} ⟶ f_*Ω_{X/Z}`. -/
theorem pullbackRelativeDifferentialsToComp_homEquiv :
    (Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackRelativeDifferentialsToComp f g) = relativeDifferentialsToPushforwardComp f g :=
  Equiv.apply_symm_apply _ _

/-- On pulled-back sections `f^*ω`, the map `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` is its adjoint transpose. -/
theorem pullbackRelativeDifferentialsToComp_unit (V : Y.Opens)
    (y : (relativeDifferentials g).val.obj (op V)) :
    (pullbackRelativeDifferentialsToComp f g).val.app (op (f ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction f).unit.app (relativeDifferentials g)).val.app
        (op V) y) = (relativeDifferentialsToPushforwardComp f g).val.app (op V) y := by
  have h := pullbackRelativeDifferentialsToComp_homEquiv f g
  rw [Adjunction.homEquiv_unit] at h
  rw [← h]
  rfl

/-- The map `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` sends the pullback `f^*(d_{Y/Z} b)` to `d_{X/Z}(f^♯ b)`. -/
theorem pullbackRelativeDifferentialsToComp_unit_d (V : Y.Opens) (b : Y.presheaf.obj (op V)) :
    (pullbackRelativeDifferentialsToComp f g).val.app (op (f ⁻¹ᵁ V))
      (((Modules.pullbackPushforwardAdjunction f).unit.app (relativeDifferentials g)).val.app
        (op V) ((relativeDifferentialsDerivation g).d b)) =
          (relativeDifferentialsDerivation (f ≫ g)).d (f.c.app (op V) b) :=
  (pullbackRelativeDifferentialsToComp_unit f g V _).trans
    (relativeDifferentialsToPushforwardComp_d f g (op V) b)

/-- The composite `f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y}` vanishes. -/
theorem pullbackRelativeDifferentialsToComp_comp_relativeDifferentialsCompToLeft :
    pullbackRelativeDifferentialsToComp f g ≫ relativeDifferentialsCompToLeft f g = 0 := by
  apply ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, pullbackRelativeDifferentialsToComp_homEquiv,
    Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  apply (relativeDifferentialsHomEquiv g _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  ext V b
  change (relativeDifferentialsCompToLeft f g).val.app _
    ((relativeDifferentialsToPushforwardComp f g).val.app V
      ((relativeDifferentialsDerivation g).d b)) = 0
  refine (congrArg (fun z => (relativeDifferentialsCompToLeft f g).val.app
    (op (f ⁻¹ᵁ V.unop)) z) (relativeDifferentialsToPushforwardComp_d f g V b)).trans
      ((relativeDifferentialsCompToLeft_d f g (op (f ⁻¹ᵁ V.unop)) (f.c.app V b)).trans ?_)
  exact (derivationOfInverseImage f (relativeDifferentialsDerivation f)).d_app b

variable {f g} in
/-- If `τ : Ω_{X/Z} ⟶ M` kills the image of `f^*Ω_{Y/Z}`, then `τ ∘ d_{X/Z}` kills `f^♯`. -/
theorem transitivity_d_app_eq_zero {M : X.Modules} (τ : relativeDifferentials (f ≫ g) ⟶ M)
    (hτ : pullbackRelativeDifferentialsToComp f g ≫ τ = 0) (V : Y.Opensᵒᵖ)
    (b : Y.presheaf.obj V) :
    τ.val.app (op (f ⁻¹ᵁ V.unop)) ((relativeDifferentialsDerivation (f ≫ g)).d (f.c.app V b)) =
      0 := by
  have h := congrArg ((Modules.pullbackPushforwardAdjunction f).homEquiv _ _) hτ
  rw [Adjunction.homEquiv_naturality_right, pullbackRelativeDifferentialsToComp_homEquiv,
    Adjunction.homEquiv_unit, Functor.map_zero, comp_zero] at h
  have h' := congrArg (fun φ => φ.val.app V ((relativeDifferentialsDerivation g).d b)) h
  simp only at h'
  rw [← relativeDifferentialsToPushforwardComp_d]
  exact h'

variable {f g} in
/-- The derivation `τ ∘ d_{X/Z}`, which kills `f^♯` when `τ` kills the image of `f^*Ω_{Y/Z}`. -/
noncomputable def transitivityDescDerivation {M : X.Modules}
    (τ : relativeDifferentials (f ≫ g) ⟶ M)
    (hτ : pullbackRelativeDifferentialsToComp f g ≫ τ = 0) :
    M.val.Derivation' (inverseImageStructureSheafMap f).hom :=
  derivationToInverseImage f
    { d := ((relativeDifferentialsDerivation (f ≫ g)).postcomp τ.val).d
      d_mul := ((relativeDifferentialsDerivation (f ≫ g)).postcomp τ.val).d_mul
      d_map := ((relativeDifferentialsDerivation (f ≫ g)).postcomp τ.val).d_map
      d_app {V} b := transitivity_d_app_eq_zero τ hτ V b }

/-- `Ω_{X/Z} ⟶ Ω_{X/Y}` is a cokernel of `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}`. -/
noncomputable def relativeDifferentialsTransitivityIsColimit :
    IsColimit (CokernelCofork.ofπ (relativeDifferentialsCompToLeft f g)
      (pullbackRelativeDifferentialsToComp_comp_relativeDifferentialsCompToLeft f g)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {M} τ hτ => (relativeDifferentialsHomEquiv f M).symm (transitivityDescDerivation τ hτ))
    (fun {M} τ hτ => by
      apply (relativeDifferentialsHomEquiv (f ≫ g) M).injective
      rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
      ext U x
      have h : (relativeDifferentialsDerivation f).postcomp
          ((relativeDifferentialsHomEquiv f M).symm (transitivityDescDerivation τ hτ)).val =
            transitivityDescDerivation τ hτ := by
        rw [← relativeDifferentialsHomEquiv_apply]
        exact Equiv.apply_symm_apply _ _
      change ((relativeDifferentialsHomEquiv f M).symm (transitivityDescDerivation τ hτ)).val.app U
        ((relativeDifferentialsCompToLeft f g).val.app U
          ((relativeDifferentialsDerivation (f ≫ g)).d x)) = _
      refine (congrArg (fun z => ((relativeDifferentialsHomEquiv f M).symm
        (transitivityDescDerivation τ hτ)).val.app U z)
          (relativeDifferentialsCompToLeft_d f g U x)).trans ?_
      exact PresheafOfModules.Derivation.congr_d h x)
    (fun {M} τ hτ m hm => by
      apply (relativeDifferentialsHomEquiv f M).injective
      rw [Equiv.apply_symm_apply, relativeDifferentialsHomEquiv_apply]
      ext U x
      change m.val.app U ((relativeDifferentialsDerivation f).d x) =
        τ.val.app U ((relativeDifferentialsDerivation (f ≫ g)).d x)
      refine (congrArg (fun z => m.val.app U z)
        (relativeDifferentialsCompToLeft_d f g U x)).symm.trans ?_
      rw [← hm]
      rfl)

/-- **Hartshorne II, Proposition 8.11.** For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, the
transitivity sequence `f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0` of `𝒪_X`-modules is exact. -/
theorem relativeDifferentials_transitivity_exact :
    (ShortComplex.mk (pullbackRelativeDifferentialsToComp f g)
      (relativeDifferentialsCompToLeft f g)
      (pullbackRelativeDifferentialsToComp_comp_relativeDifferentialsCompToLeft f g)).Exact ∧
      Epi (relativeDifferentialsCompToLeft f g) :=
  (ShortComplex.exact_and_epi_g_iff_g_is_cokernel _).2
    ⟨relativeDifferentialsTransitivityIsColimit f g⟩

end Transitivity

/-- The identification of relative differential sheaves of equal morphisms. It is irreducible so
that the kernel never unfolds it into a transport along the equation. -/
noncomputable irreducible_def relativeDifferentialsCongr {k k' : X ⟶ Z} (h : k = k') :
    relativeDifferentials k ≅ relativeDifferentials k' :=
  eqToIso (congrArg relativeDifferentials h)

/-- The identification of differential sheaves of equal morphisms respects the derivations. -/
theorem relativeDifferentialsCongr_hom_d {k k' : X ⟶ Z} (h : k = k') (U : X.Opensᵒᵖ)
    (x : X.presheaf.obj U) :
    (relativeDifferentialsCongr h).hom.val.app U ((relativeDifferentialsDerivation k).d x) =
      (relativeDifferentialsDerivation k').d x := by
  subst h
  rw [relativeDifferentialsCongr_def]
  rfl

/-- Sections of a composite of module maps. -/
theorem Modules.comp_val_app_apply {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P)
    (U : X.Opensᵒᵖ) (x : M.val.obj U) :
    (φ ≫ ψ).val.app U x = ψ.val.app U (φ.val.app U x) :=
  rfl

/-- The canonical derivation postcomposed with a composite of module maps. -/
theorem relativeDifferentialsDerivation_postcomp_comp_d {k : X ⟶ Z} {N P : X.Modules}
    (α : relativeDifferentials k ⟶ N) (β : N ⟶ P) (U : X.Opensᵒᵖ) (x : X.presheaf.obj U) :
    ((relativeDifferentialsDerivation k).postcomp (α ≫ β).val).d x =
      β.val.app U (α.val.app U ((relativeDifferentialsDerivation k).d x)) :=
  rfl

/-- Module maps are linear over the sections of the structure sheaf. -/
theorem Modules.val_app_smul {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (r : Γ(X, U))
    (y : Γ(M, U)) :
    φ.val.app (op U) (r • @id Γ(M, U) y) = r • @id Γ(N, U) (φ.val.app (op U) y) :=
  Modules.Hom.app_smul φ r y

/-- The map `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` sends `r · f^*(d_{Y/Z} b)` to `r · d_{X/Z}(f^♯ b)`. -/
theorem pullbackRelativeDifferentialsToComp_smul_unit_d (f : X ⟶ Y) (g : Y ⟶ Z) (V : Y.Opens)
    (r : Γ(X, f ⁻¹ᵁ V)) (b : Γ(Y, V)) :
    (pullbackRelativeDifferentialsToComp f g).val.app (op (f ⁻¹ᵁ V))
      (r • @id Γ((Modules.pullback f).obj (relativeDifferentials g), f ⁻¹ᵁ V)
        (((Modules.pullbackPushforwardAdjunction f).unit.app (relativeDifferentials g)).val.app
          (op V) ((relativeDifferentialsDerivation g).d b))) =
      r • @id Γ(relativeDifferentials (f ≫ g), f ⁻¹ᵁ V)
        ((relativeDifferentialsDerivation (f ≫ g)).d (f.c.app (op V) b)) :=
  (Modules.val_app_smul _ _ r _).trans
    (congrArg (fun z => r • @id Γ(relativeDifferentials (f ≫ g), f ⁻¹ᵁ V) z)
      (pullbackRelativeDifferentialsToComp_unit_d f g V b))

/-- The inverse of an isomorphism of module sheaves undoes it on sections. -/
theorem Modules.iso_inv_app_hom_app {M N : X.Modules} (e : M ≅ N) (U : X.Opensᵒᵖ)
    (x : M.val.obj U) : e.inv.val.app U (e.hom.val.app U x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app U) e.hom_inv_id) x

section Affine

open SpecKaehler

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C]

/-- `Spec C ⟶ Spec B ⟶ Spec A` is the morphism induced by `A ⟶ C`. -/
theorem spec_map_algebraMap_comp :
    Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (IsScalarTower.algebraMap_apply A B C x).symm

/-- The identification `Ω_{Spec C/Spec A} ≅ (Ω_{C/A})^~` for the composite
`Spec C ⟶ Spec B ⟶ Spec A`. -/
noncomputable def relativeDifferentialsSpecCompIso :
    relativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
        tilde (ModuleCat.of (CommRingCat.of C) Ω[C⁄A]) :=
  relativeDifferentialsCongr (spec_map_algebraMap_comp A B C) ≪≫ relativeDifferentialsSpecIso A C

/-- The identification for the composite is the one for `Spec C ⟶ Spec A` on derivations. -/
theorem relativeDifferentialsSpecCompIso_hom_d (U : (Spec (CommRingCat.of C)).Opens)
    (x : (Spec (CommRingCat.of C)).presheaf.obj (op U)) :
    (relativeDifferentialsSpecCompIso A B C).hom.val.app (op U)
      ((relativeDifferentialsDerivation (Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)))).d x) =
    (relativeDifferentialsSpecIso A C).hom.val.app (op U)
      ((relativeDifferentialsDerivation (Spec.map (CommRingCat.ofHom (algebraMap A C)))).d x) :=
  (Modules.comp_val_app_apply (relativeDifferentialsCongr (spec_map_algebraMap_comp A B C)).hom
    (relativeDifferentialsSpecIso A C).hom _ _).trans
      (congrArg (fun z => (relativeDifferentialsSpecIso A C).hom.val.app (op U) z)
        (relativeDifferentialsCongr_hom_d (spec_map_algebraMap_comp A B C) (op U) x))

/-- The second map `Ω_{C/A} ⟶ Ω_{C/B}` of the first exact sequence, as a morphism of modules. -/
noncomputable def kaehlerMapHom :
    ModuleCat.of (CommRingCat.of C) Ω[C⁄A] ⟶ ModuleCat.of (CommRingCat.of C) Ω[C⁄B] :=
  ModuleCat.ofHom (KaehlerDifferential.map A B C C)

/-- Under the identification `Ω_{Spec C/Spec A} ≅ (Ω_{C/A})^~`, the derivation of `c` is `dc`. -/
theorem relativeDifferentialsSpecCompIso_hom_d_globalRes (U : (Spec (CommRingCat.of C)).Opens)
    (c : C) :
    (relativeDifferentialsSpecCompIso A B C).hom.val.app (op U)
      ((relativeDifferentialsDerivation (Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)))).d (globalRes U c)) =
      (tilde.toOpen (ModuleCat.of (CommRingCat.of C) Ω[C⁄A]) U).hom
        (KaehlerDifferential.D A C c) :=
  (relativeDifferentialsSpecCompIso_hom_d A B C U (globalRes U c)).trans
    (relativeDifferentialsSpecIso_hom_d A C U c)

omit [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] in
/-- The sheaf map `M^~ ⟶ N^~` induced by a linear map `φ` sends `m` to `φ m`. -/
theorem tilde_map_app_toOpen {R : CommRingCat.{u}} {M N : ModuleCat.{u} R} (φ : M ⟶ N)
    (U : (Spec R).Opens) (m : M) :
    (tilde.map φ).val.app (op U) ((tilde.toOpen M U).hom m) = (tilde.toOpen N U).hom (φ m) :=
  ConcreteCategory.congr_hom (tilde.toOpen_map_app φ U) m

omit [CommRing A] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] in
/-- On an affine scheme, two relative derivations agreeing on restrictions of global functions
coincide. -/
theorem derivation_ext_of_global {Z : Scheme.{u}} {k : Spec (CommRingCat.of B) ⟶ Z}
    {M : (Spec (CommRingCat.of B)).Modules}
    (D₁ D₂ : M.val.Derivation' (inverseImageStructureSheafMap k).hom)
    (hρ : ∀ (V : (Spec (CommRingCat.of B)).Opens) (b : B),
      D₁.d (globalRes V b) = D₂.d (globalRes V b)) :
    D₁ = D₂ := by
  have key : ∀ (f g : B) (t : (Spec (CommRingCat.of B)).presheaf.obj
      (op (PrimeSpectrum.basicOpen g))), t = constSec f g → D₁.d t = D₂.d t := by
    rintro f g t rfl
    have e₁ := (congrArg D₁.d (const_mul_globalRes f g)).symm.trans (D₁.d_mul _ _)
    have e₂ := (congrArg D₂.d (const_mul_globalRes f g)).symm.trans (D₂.d_mul _ _)
    have e := e₁.symm.trans ((hρ _ f).trans e₂)
    let c : (Spec (CommRingCat.of B)).ringCatSheaf.obj.obj (op (PrimeSpectrum.basicOpen g)) :=
      constSec f g
    let r : (Spec (CommRingCat.of B)).ringCatSheaf.obj.obj (op (PrimeSpectrum.basicOpen g)) :=
      globalRes (PrimeSpectrum.basicOpen g) g
    have e' := (congrArg (fun z => c • z + r • D₁.d (constSec f g)) (hρ _ g)).symm.trans e
    have e'' : r • D₁.d (constSec f g) = r • D₂.d (constSec f g) := add_left_cancel e'
    exact M.isSMulRegular_of_le_basicOpen (f := g) le_rfl e''
  ext U s
  apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj M).2
  intro x hxU
  obtain ⟨g, hxg, hgU, f, hf⟩ := StructureSheaf.exists_const _ s x hxU
  refine ⟨PrimeSpectrum.basicOpen g, hgU, hxg, ?_⟩
  exact ((D₁.d_map (homOfLE hgU).op s).symm.trans (key f g _ hf.symm)).trans
    (D₂.d_map (homOfLE hgU).op s)

/-- The two maps of the affine comparison agree on derivatives of restricted global functions. -/
theorem relativeDifferentialsCompToLeft_spec_d (V : (Spec (CommRingCat.of C)).Opens) (c : C) :
    ((relativeDifferentialsDerivation (Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)))).postcomp
          (relativeDifferentialsCompToLeft (Spec.map (CommRingCat.ofHom (algebraMap B C)))
            (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫
              (relativeDifferentialsSpecIso B C).hom).val).d (globalRes V c) =
    ((relativeDifferentialsDerivation (Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)))).postcomp
          ((relativeDifferentialsSpecCompIso A B C).hom ≫
            tilde.map (kaehlerMapHom A B C)).val).d (globalRes V c) := by
  rw [relativeDifferentialsDerivation_postcomp_comp_d,
    relativeDifferentialsDerivation_postcomp_comp_d, relativeDifferentialsSpecCompIso_hom_d,
    relativeDifferentialsSpecIso_hom_d,
    relativeDifferentialsCompToLeft_d, relativeDifferentialsSpecIso_hom_d, tilde_map_app_toOpen]
  change _ = (tilde.toOpen (ModuleCat.of (CommRingCat.of C) Ω[C⁄B]) V).hom
    (KaehlerDifferential.map A B C C (KaehlerDifferential.D A C c))
  rw [KaehlerDifferential.map_D]
  rfl

/-- On affine charts, the map `Ω_{X/Z} ⟶ Ω_{X/Y}` is the sheaf associated to the second map
`Ω_{C/A} ⟶ Ω_{C/B}` of the first exact sequence for Kähler differentials. -/
theorem relativeDifferentialsCompToLeft_spec :
    relativeDifferentialsCompToLeft (Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≫
      (relativeDifferentialsSpecIso B C).hom =
    (relativeDifferentialsSpecCompIso A B C).hom ≫ tilde.map (kaehlerMapHom A B C) := by
  apply (relativeDifferentialsHomEquiv _ _).injective
  rw [relativeDifferentialsHomEquiv_apply, relativeDifferentialsHomEquiv_apply]
  exact derivation_ext_of_global C _ _ (relativeDifferentialsCompToLeft_spec_d A B C)

omit [Algebra A B] [Algebra A C] [IsScalarTower A B C] in
/-- The comorphism of `Spec C ⟶ Spec B` sends the restriction of `b` to that of its image. -/
theorem spec_map_app_globalRes (V : (Spec (CommRingCat.of B)).Opens) (b : B) :
    (Spec.map (CommRingCat.ofHom (algebraMap B C))).c.app (op V) (globalRes V b) =
      globalRes ((Spec.map (CommRingCat.ofHom (algebraMap B C))) ⁻¹ᵁ V) (algebraMap B C b) := by
  have h : (ΓSpecIso (CommRingCat.of C)).inv ((CommRingCat.ofHom (algebraMap B C)) b) =
      (Spec.map (CommRingCat.ofHom (algebraMap B C))).c.app (op ⊤)
        ((ΓSpecIso (CommRingCat.of B)).inv b) :=
    ConcreteCategory.congr_hom (ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap B C))) b
  rw [globalRes, NatTrans.naturality_apply]
  change _ = (Spec (CommRingCat.of C)).presheaf.map _ ((ΓSpecIso (CommRingCat.of C)).inv
    ((CommRingCat.ofHom (algebraMap B C)) b))
  rw [h]
  rfl

/-- On affine charts, the map `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` sends `c · f^*(db)` to `c · db`: under the
identifications with sheaves associated to Kähler modules it agrees with the first map
`C ⊗_B Ω_{B/A} ⟶ Ω_{C/A}`, `c ⊗ db ↦ c · db`, of the first exact sequence. -/
theorem pullbackRelativeDifferentialsToComp_spec (V : (Spec (CommRingCat.of B)).Opens) (c : C)
    (b : B) :
    (relativeDifferentialsSpecCompIso A B C).hom.val.app
      (op (Spec.map (CommRingCat.ofHom (algebraMap B C)) ⁻¹ᵁ V))
      ((pullbackRelativeDifferentialsToComp (Spec.map (CommRingCat.ofHom (algebraMap B C)))
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).val.app
        (op (Spec.map (CommRingCat.ofHom (algebraMap B C)) ⁻¹ᵁ V))
        (globalRes (Spec.map (CommRingCat.ofHom (algebraMap B C)) ⁻¹ᵁ V) c •
          @id Γ((Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap B C)))).obj
              (relativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap A B)))),
                Spec.map (CommRingCat.ofHom (algebraMap B C)) ⁻¹ᵁ V)
          (((Modules.pullbackPushforwardAdjunction
            (Spec.map (CommRingCat.ofHom (algebraMap B C)))).unit.app
              (relativeDifferentials (Spec.map (CommRingCat.ofHom (algebraMap A B))))).val.app
                (op V)
            ((relativeDifferentialsSpecIso A B).inv.val.app (op V)
              ((tilde.toOpen (ModuleCat.of (CommRingCat.of B) Ω[B⁄A]) V).hom
                (KaehlerDifferential.D A B b)))))) =
      (tilde.toOpen (ModuleCat.of (CommRingCat.of C) Ω[C⁄A])
        (Spec.map (CommRingCat.ofHom (algebraMap B C)) ⁻¹ᵁ V)).hom
          (KaehlerDifferential.mapBaseChange A B C (c ⊗ₜ KaehlerDifferential.D A B b)) := by
  rw [← relativeDifferentialsSpecIso_hom_d A B V b, Modules.iso_inv_app_hom_app,
    pullbackRelativeDifferentialsToComp_smul_unit_d, spec_map_app_globalRes]
  erw [Modules.val_app_smul]
  rw [relativeDifferentialsSpecCompIso_hom_d_globalRes,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, map_smul]
  rfl

end Affine

end AlgebraicGeometry.Scheme
