/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Cohomology.KoszulRegularImmersionTopExtGlue

/-!
# Gluing the local top-Ext isomorphisms of a Koszul-regular immersion

Let `i : X ⟶ Y` be a closed immersion and `M` a quasi-coherent `𝒪_Y`-module. A *Koszul chart*
(`Hartshorne.KoszulImmersion.KoszulChart`) on an open `V` of `Y` is an affine `V` with a
Koszul-regular sequence `f₁, …, f_r` generating the ideal of `i` over `V`; it gives the local
isomorphism `ℰxt^r_Y(i_* 𝒪_X, M)|_V ≅ (i_* i^* M)|_V` (`KoszulChart.topExtIso`, for `r = s + 1`).
Charts restrict to basic opens (`KoszulChart.restrict`).

Given an `𝒪_X`-module `G` and isomorphisms `ν_c : (i_* G)|_V ≅ (i_* i^* M)|_V` for all charts,
compatible with restriction to basic opens and transforming under a change of generators
`f ↦ f Q` by multiplication with `det Q` (the transition law of the local top-Ext isomorphisms,
`KoszulChart.topExtIso_hom_of_eq_vecMul`), the composites `ν_c ≫ (topExtIso c)⁻¹` agree on
overlaps (`compatible_localMap`) and glue to an isomorphism
`ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_* G` when the charts cover `Y` (`nonempty_sheafExt_iso_of_localIso`).

Agreement near a point `y` of `V ∩ V'`: restrict both charts to a common basic open `W ∋ y`
(`exists_basicOpen_le_affine_inter`). The two generating sequences on `W` differ by a matrix `Q`
with `det Q` invertible modulo the ideal (`exists_vecMul_eq_det_isUnit_mod`). If some generator
is invertible at `y`, then `y ∉ X` and the sections of `i_* G` vanish near `y`
(`pushforward_sections_eq_zero`); otherwise `det Q` is invertible at `y`
(`KoszulChart.mem_basicOpen_det`) and the two local maps agree on `D(det Q)`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace KoszulImmersion

open AlgebraicGeometry Koszul Ringed.KoszulSheaf Ringed.Transport Ringed.RestrictCompose
  Ringed.SheafExtRestrict Ringed.RestrictGlue

variable {Y : Scheme.{u}} {X : Scheme.{u}} (i : X ⟶ Y) (r : ℕ)

/-- A Koszul chart of `i` on an open `V` of `Y`: `V` is affine and `r` sections over `V` form a
Koszul-regular sequence generating the ideal of `i` over `V`. -/
structure KoszulChart (V : Y.Opens) where
  /-- The open is affine. -/
  hV : IsAffineOpen V
  /-- The generators. -/
  f : Fin r → Γ(Y, V)
  /-- The generators generate the ideal of `i` over `V`. -/
  hI : i.ker.ideal ⟨V, hV⟩ = Ideal.span (Set.range f)
  /-- The generators form a Koszul-regular sequence. -/
  hf : IsKoszulRegular f (ModuleCat.of Γ(Y, V) Γ(Y, V))

variable {i r}

/-- The restriction of a Koszul chart to a basic open `W = D(b)` of its open. -/
noncomputable def KoszulChart.restrict {V : Y.Opens} (c : KoszulChart i r V) (W : Y.Opens)
    (b : Γ(Y, V)) (hb : Y.basicOpen b = W) : KoszulChart i r W where
  hV := hb ▸ c.hV.basicOpen b
  f j := Y.presheaf.map (homOfLE (hb ▸ Y.basicOpen_le b)).op (c.f j)
  hI := by
    subst hb
    have h := i.ker.map_ideal_basicOpen ⟨V, c.hV⟩ b
    rw [c.hI, Ideal.map_span, ← Set.range_comp] at h
    exact h.symm
  hf := by
    subst hb
    exact isKoszulRegular_basicOpen c.hV c.hf b

/-- A basic open of `V` is contained in `V`. -/
lemma le_of_basicOpen_eq {V W : Y.Opens} (b : Γ(Y, V)) (hb : Y.basicOpen b = W) : W ≤ V :=
  hb ▸ Y.basicOpen_le b

/-- If no generator of a chart is invertible at `y` and `det Q · e ≡ 1` modulo the ideal they
generate, then `det Q` is invertible at `y`. -/
lemma KoszulChart.mem_basicOpen_det {W : Y.Opens} (c : KoszulChart i r W) (y : Y) (hyW : y ∈ W)
    (hA : ∀ j, y ∉ Y.basicOpen (c.f j)) (Q : Matrix (Fin r) (Fin r) Γ(Y, W)) (e : Γ(Y, W))
    (he : Q.det * e - 1 ∈ Ideal.span (Set.range c.f)) : y ∈ Y.basicOpen Q.det := by
  let γ := (Y.presheaf.germ W y hyW).hom
  have hspanle : Ideal.span (Set.range c.f) ≤ (IsLocalRing.maximalIdeal _).comap γ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu => hA j ((Y.mem_basicOpen _ y hyW).mpr hu)
  refine (Y.mem_basicOpen _ y hyW).mpr ?_
  have hm : γ (Q.det * e - 1) ∈ IsLocalRing.maximalIdeal _ := hspanle he
  have hu : IsUnit (γ (Q.det * e)) := by
    refine IsLocalRing.isUnit_of_mem_nonunits_one_sub_self _ ?_
    have : 1 - γ (Q.det * e) = -γ (Q.det * e - 1) := by rw [map_sub, map_one]; ring
    rw [this]
    exact (IsLocalRing.mem_maximalIdeal _).mp (neg_mem hm)
  rw [map_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

variable (M : Y.Modules) {s : ℕ}

/-- The local top-Ext isomorphism `ℰxt^r_Y(i_* 𝒪_X, M)|_V ≅ (i_* i^* M)|_V` of a chart. -/
noncomputable def KoszulChart.topExtIso [IsClosedImmersion i] [M.IsQuasicoherent]
    {V : Y.Opens} (c : KoszulChart i (s + 1) V) :
    (Ringed.moduleRestrict V).obj ((Ringed.sheafExt (R := Y.sheaf)
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf)) (s + 1)).obj M) ≅
      pullbackRestrict i M V :=
  localTopExtIso c.hV i c.f M c.hI c.hf

/-- The inverse local top-Ext isomorphisms of a chart and of its restriction to a basic open
agree on sections. -/
lemma KoszulChart.localApp_topExtIso_inv_restrict [IsClosedImmersion i] [M.IsQuasicoherent]
    {V : Y.Opens} (c : KoszulChart i (s + 1) V) (W : Y.Opens) (b : Γ(Y, V))
    (hb : Y.basicOpen b = W)
    {U : Y.Opens} (hU : U ≤ W)
    (x : ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj M)).val.obj
      (op U)) :
    localApp (c.topExtIso M).inv (hU.trans (le_of_basicOpen_eq b hb)) x =
      localApp ((c.restrict W b hb).topExtIso M).inv hU x :=
  localApp_localTopExtIso_inv_restrict i M c.hV (c.restrict W b hb).hV (le_of_basicOpen_eq b hb)
    c.f c.hI c.hf (c.restrict W b hb).hI (c.restrict W b hb).hf hU x

/-- The determinant transition law, for generators `g` equal to `f Q`. -/
lemma localTopExtIso_hom_of_eq_vecMul [IsClosedImmersion i] [M.IsQuasicoherent] {V : Y.Opens}
    (hV : IsAffineOpen V) (f g : Fin (s + 1) → Γ(Y, V)) (Q : Matrix (Fin (s + 1)) (Fin (s + 1))
      Γ(Y, V)) (hg : g = Matrix.vecMul f Q)
    (hIf : i.ker.ideal ⟨V, hV⟩ = Ideal.span (Set.range f))
    (hff : IsKoszulRegular f (ModuleCat.of Γ(Y, V) Γ(Y, V)))
    (hIg : i.ker.ideal ⟨V, hV⟩ = Ideal.span (Set.range g))
    (hfg : IsKoszulRegular g (ModuleCat.of Γ(Y, V) Γ(Y, V))) :
    (localTopExtIso hV i g M hIg hfg).hom =
      (localTopExtIso hV i f M hIf hff).hom ≫
        scalarHom (restrictPhi V Q.det) (pullbackRestrict i M V) := by
  subst hg
  exact localTopExtIso_changeOfBasis (hV₀ := hV) (i := i) (f := f) (M := M) (hI := hIf) Q hff
    hIg hfg

/-- The determinant transition law for charts. -/
lemma KoszulChart.topExtIso_hom_of_eq_vecMul [IsClosedImmersion i] [M.IsQuasicoherent]
    {V : Y.Opens} (c : KoszulChart i (s + 1) V) (g : Fin (s + 1) → Γ(Y, V))
    (hIg : i.ker.ideal ⟨V, c.hV⟩ = Ideal.span (Set.range g))
    (hfg : IsKoszulRegular g (ModuleCat.of Γ(Y, V) Γ(Y, V)))
    (Q : Matrix (Fin (s + 1)) (Fin (s + 1)) Γ(Y, V)) (hg : g = Matrix.vecMul c.f Q) :
    (KoszulChart.topExtIso M (⟨c.hV, g, hIg, hfg⟩ : KoszulChart i (s + 1) V)).hom =
      (c.topExtIso M).hom ≫ scalarHom (restrictPhi V Q.det) (pullbackRestrict i M V) :=
  localTopExtIso_hom_of_eq_vecMul M c.hV c.f g Q hg c.hI c.hf hIg hfg

/-- If `ν₂ = ν₁ ≫ s` and `e₂ = e₁ ≫ s`, then `ν₂ ≫ e₂⁻¹ = ν₁ ≫ e₁⁻¹`. -/
lemma comp_inv_eq_of_hom_eq {C : Type*} [Category C] {E B D : C} {ν₁ ν₂ : E ⟶ B}
    {e₁ e₂ : D ≅ B} {σ : B ⟶ B} [IsIso σ] (hν : ν₂ = ν₁ ≫ σ) (he : e₂.hom = e₁.hom ≫ σ) :
    ν₂ ≫ e₂.inv = ν₁ ≫ e₁.inv := by
  have hinv : e₂.inv = inv σ ≫ e₁.inv := by
    rw [← cancel_epi e₂.hom, Iso.hom_inv_id, he, Category.assoc, IsIso.hom_inv_id_assoc,
      Iso.hom_inv_id]
  rw [hν, hinv, Category.assoc, IsIso.hom_inv_id_assoc]

end KoszulImmersion

namespace Ringed.KoszulSheaf

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- Multiplications by global sections compose. -/
lemma scalarHom_comp (a b : R.obj.obj (op ⊤)) (G : SheafOfModules.{u} (ringCatSheafOf R)) :
    scalarHom a G ≫ scalarHom b G = scalarHom (b * a) G := by
  apply SheafOfModules.hom_ext
  ext W x
  change (R.obj.map (homOfLE (le_top : W.unop ≤ ⊤)).op b) •
      ((R.obj.map (homOfLE (le_top : W.unop ≤ ⊤)).op a) • x) =
    (R.obj.map (homOfLE (le_top : W.unop ≤ ⊤)).op (b * a)) • x
  rw [map_mul, mul_smul]

/-- Multiplication by `1` is the identity. -/
lemma scalarHom_one (G : SheafOfModules.{u} (ringCatSheafOf R)) : scalarHom 1 G = 𝟙 G := by
  apply SheafOfModules.hom_ext
  ext W x
  change (R.obj.map (homOfLE (le_top : W.unop ≤ ⊤)).op 1) • x = x
  rw [map_one, one_smul]

/-- Multiplication by a unit is an isomorphism. -/
lemma isIso_scalarHom {a : R.obj.obj (op ⊤)} (ha : IsUnit a)
    (G : SheafOfModules.{u} (ringCatSheafOf R)) : IsIso (scalarHom a G) := by
  obtain ⟨v, rfl⟩ := ha
  exact ⟨⟨scalarHom ↑v⁻¹ G, by rw [scalarHom_comp, Units.inv_mul, scalarHom_one],
    by rw [scalarHom_comp, Units.mul_inv, scalarHom_one]⟩⟩

end Ringed.KoszulSheaf

namespace KoszulImmersion

open AlgebraicGeometry Koszul Ringed.KoszulSheaf Ringed.Transport Ringed.RestrictCompose
  Ringed.SheafExtRestrict Ringed.RestrictGlue

variable {Y : Scheme.{u}} {X : Scheme.{u}} {i : X ⟶ Y} (M : Y.Modules) {s : ℕ}
  [IsClosedImmersion i] [M.IsQuasicoherent] (G : X.Modules)

/-- Sections of `i_* G` over an open `U` contained in a basic open `D(fⱼ)` of a chart vanish:
`i⁻¹ U` is empty. -/
lemma pushforward_sections_eq_zero {V : Y.Opens} (c : KoszulChart i (s + 1) V) (j : Fin (s + 1))
    {U : Y.Opens}
    (hU : U ≤ Y.basicOpen (c.f j)) (x : ((Scheme.Modules.pushforward i).obj G).val.obj (op U)) :
    x = 0 := by
  have h0 : i.app V (c.f j) = 0 := by
    have hmem : c.f j ∈ i.ker.ideal ⟨V, c.hV⟩ := c.hI ▸ Ideal.subset_span ⟨j, rfl⟩
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hmem
    exact hmem
  have hbot : i ⁻¹ᵁ U ≤ ⊥ := by
    refine (i.preimage_mono hU).trans ?_
    rw [Scheme.preimage_basicOpen, h0, Scheme.basicOpen_zero]
  exact ModuleGluing.sheaf_ext _ G (κ := PEmpty) PEmpty.elim (fun k => k.elim)
    (hbot.trans bot_le) x 0 (fun k => k.elim)

variable (ν : ∀ (V : Y.Opens) (_ : KoszulChart i (s + 1) V),
    (Ringed.moduleRestrict V).obj ((Scheme.Modules.pushforward i).obj G) ≅ pullbackRestrict i M V)

/-- The local maps `(i_* G)|_V ⟶ ℰxt^r_Y(i_* 𝒪_X, M)|_V` of the charts. -/
noncomputable def localMap {V : Y.Opens} (c : KoszulChart i (s + 1) V) :
    (Ringed.moduleRestrict V).obj ((Scheme.Modules.pushforward i).obj G) ⟶
      (Ringed.moduleRestrict V).obj ((Ringed.sheafExt (R := Y.sheaf)
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit X.ringCatSheaf)) (s + 1)).obj M) :=
  (ν V c).hom ≫ (c.topExtIso M).inv

/-- Unfolding `localMap`. -/
lemma localMap_def {V : Y.Opens} (c : KoszulChart i (s + 1) V) :
    localMap M G ν c = (ν V c).hom ≫ (c.topExtIso M).inv :=
  rfl

variable (hres : ∀ (V : Y.Opens) (c : KoszulChart i (s + 1) V) (W : Y.Opens) (b : Γ(Y, V))
    (hb : Y.basicOpen b = W) {U : Y.Opens} (hU : U ≤ W)
    (x : ((Scheme.Modules.pushforward i).obj G).val.obj (op U)),
    localApp (ν V c).hom (hU.trans (le_of_basicOpen_eq b hb)) x =
      localApp (ν W (c.restrict W b hb)).hom hU x)
  (htrans : ∀ (V : Y.Opens) (c : KoszulChart i (s + 1) V) (g : Fin (s + 1) → Γ(Y, V))
    (hIg : i.ker.ideal ⟨V, c.hV⟩ = Ideal.span (Set.range g))
    (hfg : IsKoszulRegular g (ModuleCat.of Γ(Y, V) Γ(Y, V)))
    (Q : Matrix (Fin (s + 1)) (Fin (s + 1)) Γ(Y, V)) (_ : g = Matrix.vecMul c.f Q),
    (ν V ⟨c.hV, g, hIg, hfg⟩).hom =
      (ν V c).hom ≫ scalarHom (restrictPhi V Q.det) (pullbackRestrict i M V))

include hres in
/-- The local maps of a chart and of its restriction to a basic open agree on sections. -/
lemma localApp_localMap_restrict {V : Y.Opens} (c : KoszulChart i (s + 1) V) (W : Y.Opens)
    (b : Γ(Y, V)) (hb : Y.basicOpen b = W) {U : Y.Opens} (hU : U ≤ W)
    (x : ((Scheme.Modules.pushforward i).obj G).val.obj (op U)) :
    localApp (localMap M G ν c) (hU.trans (le_of_basicOpen_eq b hb)) x =
      localApp (localMap M G ν (c.restrict W b hb)) hU x := by
  rw [localMap_def, localMap_def, localApp_comp, localApp_comp, hres V c W b hb hU x,
    c.localApp_topExtIso_inv_restrict M W b hb hU]

include htrans in
/-- The local map does not change under a change of generators `f ↦ f Q` with `det Q` a unit. -/
lemma localMap_eq_of_eq_vecMul {V : Y.Opens} (c : KoszulChart i (s + 1) V)
    (g : Fin (s + 1) → Γ(Y, V)) (hIg : i.ker.ideal ⟨V, c.hV⟩ = Ideal.span (Set.range g))
    (hfg : IsKoszulRegular g (ModuleCat.of Γ(Y, V) Γ(Y, V)))
    (Q : Matrix (Fin (s + 1)) (Fin (s + 1)) Γ(Y, V)) (hg : g = Matrix.vecMul c.f Q)
    (hQ : IsUnit Q.det) :
    localMap M G ν (⟨c.hV, g, hIg, hfg⟩ : KoszulChart i (s + 1) V) = localMap M G ν c := by
  have := isIso_scalarHom (hQ.map (restrictPhi V)) (pullbackRestrict i M V)
  rw [localMap_def, localMap_def]
  exact comp_inv_eq_of_hom_eq (htrans V c g hIg hfg Q hg)
    (c.topExtIso_hom_of_eq_vecMul M g hIg hfg Q hg)

include htrans in
/-- Two charts on the same open whose generators differ by a matrix `Q` with `det Q` a unit have
the same local map. -/
lemma localMap_eq_of_eq_vecMul' {V : Y.Opens} (c d : KoszulChart i (s + 1) V)
    (Q : Matrix (Fin (s + 1)) (Fin (s + 1)) Γ(Y, V)) (hg : d.f = Matrix.vecMul c.f Q)
    (hQ : IsUnit Q.det) :
    localMap M G ν d = localMap M G ν c := by
  obtain ⟨hV, g, hIg, hfg⟩ := d
  exact localMap_eq_of_eq_vecMul M G ν htrans c g hIg hfg Q hg hQ

omit [IsClosedImmersion i] [M.IsQuasicoherent] in
/-- The restriction of a matrix to the basic open of its determinant has invertible
determinant. -/
lemma isUnit_det_map_res {W : Y.Opens} (Q : Matrix (Fin (s + 1)) (Fin (s + 1)) Γ(Y, W)) :
    IsUnit (Q.map (Y.presheaf.map (homOfLE (Y.basicOpen_le Q.det)).op).hom).det := by
  rw [show (Q.map (Y.presheaf.map (homOfLE (Y.basicOpen_le Q.det)).op).hom).det =
    (Y.presheaf.map (homOfLE (Y.basicOpen_le Q.det)).op).hom Q.det from
      (RingHom.map_det _ Q).symm]
  exact RingedSpace.isUnit_res_basicOpen _ Q.det

include hres htrans in
/-- Two charts on `W` whose generators differ by a matrix `Q` have local maps agreeing on the
sections over the opens contained in `D(det Q)`. -/
lemma localApp_localMap_eq_of_vecMul {W : Y.Opens} (c d : KoszulChart i (s + 1) W)
    (Q : Matrix (Fin (s + 1)) (Fin (s + 1)) Γ(Y, W)) (hQ : Matrix.vecMul c.f Q = d.f)
    {U : Y.Opens} (hU : U ≤ Y.basicOpen Q.det)
    (x : ((Scheme.Modules.pushforward i).obj G).val.obj (op U)) :
    localApp (localMap M G ν c) (hU.trans (le_of_basicOpen_eq Q.det rfl)) x =
      localApp (localMap M G ν d) (hU.trans (le_of_basicOpen_eq Q.det rfl)) x := by
  have hQ' : (d.restrict _ Q.det rfl).f = Matrix.vecMul (c.restrict _ Q.det rfl).f
      (Q.map (Y.presheaf.map (homOfLE (Y.basicOpen_le Q.det)).op).hom) := by
    funext j
    change (Y.presheaf.map (homOfLE (Y.basicOpen_le Q.det)).op).hom (d.f j) = _
    rw [← hQ, RingHom.map_vecMul]
    rfl
  rw [localApp_localMap_restrict M G ν hres c _ Q.det rfl hU x,
    localApp_localMap_restrict M G ν hres d _ Q.det rfl hU x,
    localMap_eq_of_eq_vecMul' M G ν htrans _ _ _ hQ' (isUnit_det_map_res Q)]

include hres htrans in
/-- **Two charts agree near every common point.** For charts `c` on `V` and `d` on `V'` and a
point `y` of `V ∩ V'`, the local maps of `c` and `d` induce the same maps on sections over the
opens contained in some neighbourhood of `y`. -/
lemma exists_localApp_localMap_eq {V V' : Y.Opens} (c : KoszulChart i (s + 1) V)
    (d : KoszulChart i (s + 1) V') (y : Y) (hy : y ∈ V ⊓ V') :
    ∃ N : Y.Opens, y ∈ N ∧ N ≤ V ⊓ V' ∧ ∀ (U : Y.Opens) (h₁ : U ≤ V) (h₂ : U ≤ V'),
      U ≤ N → ∀ x : ((Scheme.Modules.pushforward i).obj G).val.obj (op U),
        localApp (localMap M G ν c) h₁ x = localApp (localMap M G ν d) h₂ x := by
  obtain ⟨a, b, hab, hya⟩ := exists_basicOpen_le_affine_inter c.hV d.hV y hy
  have hWc : Y.basicOpen a ≤ V := le_of_basicOpen_eq a rfl
  have hWd : Y.basicOpen a ≤ V' := le_of_basicOpen_eq b hab.symm
  have hspan : Ideal.span (Set.range (d.restrict _ b hab.symm).f) =
      Ideal.span (Set.range (c.restrict _ a rfl).f) :=
    (d.restrict _ b hab.symm).hI.symm.trans (c.restrict _ a rfl).hI
  obtain ⟨Q, hQ, e, he⟩ := exists_vecMul_eq_det_isUnit_mod (c.restrict _ a rfl).hf hspan
  by_cases hA : ∃ j, y ∈ Y.basicOpen ((c.restrict _ a rfl).f j)
  · obtain ⟨j, hj⟩ := hA
    refine ⟨Y.basicOpen ((c.restrict _ a rfl).f j), hj, (Y.basicOpen_le _).trans (le_inf hWc hWd),
      fun U h₁ h₂ hU x => ?_⟩
    obtain rfl := pushforward_sections_eq_zero G (c.restrict _ a rfl) j hU x
    rw [localApp_zero, localApp_zero]
  · push Not at hA
    have hdet := (c.restrict _ a rfl).mem_basicOpen_det y hya hA Q e he
    have hNW : Y.basicOpen Q.det ≤ Y.basicOpen a := le_of_basicOpen_eq Q.det rfl
    refine ⟨Y.basicOpen Q.det, hdet, hNW.trans (le_inf hWc hWd), fun U h₁ h₂ hU x => ?_⟩
    have e1 := localApp_localMap_restrict M G ν hres c _ a rfl (hU.trans hNW) x
    have e2 := localApp_localMap_restrict M G ν hres d _ b hab.symm (hU.trans hNW) x
    have e3 := localApp_localMap_eq_of_vecMul M G ν hres htrans _ _ Q hQ hU x
    exact e1.trans (e3.trans e2.symm)

/-- The index type of the cover by Koszul charts. -/
abbrev ChartIndex (i : X ⟶ Y) (r : ℕ) := Σ V : Y.Opens, KoszulChart i r V

include hres htrans in
/-- The local maps of the charts agree on overlaps. -/
lemma compatible_localMap :
    Compatible (fun k : ChartIndex i (s + 1) => k.1) (fun k => localMap M G ν k.2) := by
  intro k l U h₁ h₂ x
  choose N hyN hNle hN using fun y : U =>
    exists_localApp_localMap_eq M G ν hres htrans k.2 l.2 y.1 ⟨h₁ y.2, h₂ y.2⟩
  refine ModuleGluing.sheaf_ext _ _ (fun y : U => U ⊓ N y) (fun _ => inf_le_left)
    (fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hy, hyN ⟨y, hy⟩⟩) _ _ fun y => ?_
  rw [localApp_naturality, localApp_naturality]
  exact hN y _ _ _ inf_le_right _

include hres htrans in
/-- **Gluing the local top-Ext isomorphisms.** Local isomorphisms `ν_c : (i_* G)|_V ≅
(i_* i^* M)|_V` on the Koszul charts `c` of `i`, compatible on sections with restriction to basic
opens and transforming like the local top-Ext isomorphisms under a change of generators, give an
isomorphism `ℰxt^r_Y(i_* 𝒪_X, M) ≅ i_* G` when the charts cover `Y`. -/
theorem nonempty_sheafExt_iso_of_localIso
    (hcover : ∀ y : Y, ∃ (V : Y.Opens) (_ : KoszulChart i (s + 1) V), y ∈ V) :
    Nonempty ((Ringed.sheafExt (R := Y.sheaf) ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit X.ringCatSheaf)) (s + 1)).obj M ≅
        (Scheme.Modules.pushforward i).obj G) := by
  have hcov : ⊤ ≤ iSup (fun k : ChartIndex i (s + 1) => k.1) := fun y _ => by
    obtain ⟨V, c, hc⟩ := hcover y
    exact Opens.mem_iSup.mpr ⟨⟨V, c⟩, hc⟩
  have hψ := compatible_localMap M G ν hres htrans
  have := isIso_glueHom hcov hψ (fun k => by rw [localMap_def]; infer_instance)
  exact ⟨(asIso (glueHom hcov hψ)).symm⟩

end KoszulImmersion

end Hartshorne
