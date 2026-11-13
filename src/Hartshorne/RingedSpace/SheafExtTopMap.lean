/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.RingedSpace.SheafExtResolutionExactFunctor

/-!
# Maps out of a top sheaf `ℰxt` given by a locally free resolution

Let `L_• ⟶ F` be a resolution of an `𝒪_X`-module by locally free `𝒪_X`-modules of finite rank and
`t : ℋom(L_{s+1}, G) ⟶ T` a morphism killing the image of `ℋom(L_s, G)`. Then `t` induces a map
`h^{s+1}(ℋom(L_•, G)) ⟶ T` (`Hartshorne.CochainTop.desc`) and hence, through the isomorphism
`ℰxt^{s+1}(F, G) ≅ h^{s+1}(ℋom(L_•, G))` of Hartshorne III.6, Proposition 6.5, a map
`ℰxt^{s+1}(F, G) ⟶ T` (`Hartshorne.Ringed.extTopMap`). These maps are compatible with

* chain maps between two resolutions of `F` (`Hartshorne.Ringed.extTopMap_naturality`);
* restriction to an open subset (`Hartshorne.Ringed.extTopMap_restrict`);
* transport along a homeomorphism (`Hartshorne.Ringed.extTopMap_transport`).

Only the map `t` on top cochains has to be matched in each case.
-/

universe u v' u' v'' u''

open CategoryTheory Limits Opposite TopologicalSpace

/- The objects of `Φ(K)` for a complex `K` are only definitionally (not reducibly) the images of
the objects of `K`; rewriting along such identifications needs the default transparency. -/
set_option backward.isDefEq.respectTransparency false

namespace Hartshorne

namespace CochainTop

variable {C : Type*} [Category C] [Abelian C] (K : CochainComplex C ℕ) {s : ℕ} {T : C}
  (t : K.X (s + 1) ⟶ T) (w : K.d s (s + 1) ≫ t = 0)

/-- The map `h^{s+1}(K) ⟶ T` induced by `t : K^{s+1} ⟶ T` killing the image of `K^s`. -/
noncomputable def desc : K.homology (s + 1) ⟶ T :=
  K.homologyι (s + 1) ≫ K.descOpcycles t s (by simp) w

@[reassoc (attr := simp)]
lemma homologyπ_desc : K.homologyπ (s + 1) ≫ desc K t w = K.iCycles (s + 1) ≫ t := by
  rw [desc, HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles]

lemma desc_comp {T' : C} (e : T ⟶ T') :
    desc K t w ≫ e = desc K (t ≫ e) (by rw [reassoc_of% w, zero_comp]) := by
  rw [← cancel_epi (K.homologyπ (s + 1)), homologyπ_desc_assoc, homologyπ_desc]

lemma desc_congr {t₁ t₂ : K.X (s + 1) ⟶ T} (w₁ : K.d s (s + 1) ≫ t₁ = 0)
    (w₂ : K.d s (s + 1) ≫ t₂ = 0) (h : t₁ = t₂) : desc K t₁ w₁ = desc K t₂ w₂ := by
  subst h; rfl

lemma homologyMap_desc {K' : CochainComplex C ℕ} (χ : K ⟶ K') (t' : K'.X (s + 1) ⟶ T)
    (w' : K'.d s (s + 1) ≫ t' = 0) :
    HomologicalComplex.homologyMap χ (s + 1) ≫ desc K' t' w' =
      desc K (χ.f (s + 1) ≫ t') (by rw [← χ.comm_assoc, w', comp_zero]) := by
  rw [← cancel_epi (K.homologyπ (s + 1)), HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_desc, homologyπ_desc, HomologicalComplex.cyclesMap_i_assoc]

end CochainTop

namespace Ringed

namespace LocallyFreeResolutionExt

section ExactFunctor

variable {C : Type u'} [Category.{v'} C] [Abelian C]
  {D : Type u''} [Category.{v''} D] [Abelian D]
  (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.PreservesZeroMorphisms] (H' : Dᵒᵖ ⥤ D ⥤ D)
  [H'.PreservesZeroMorphisms] (α : ∀ F : C, H.obj (op F) ⋙ Φ ≅ Φ ⋙ H'.obj (op (Φ.obj F)))
  (hα : ∀ {F' F : C} (f : F' ⟶ F) (G : C),
    Φ.map ((H.map f.op).app G) ≫ (α F').hom.app G =
      (α F).hom.app G ≫ (H'.map (Φ.map f).op).app (Φ.obj G))

/-- The map induced on `h^{s+1}` by a top map, read through `Φ(hⁱ(H(L_•, G))) ≅ hⁱ(H'(Φ L_•, Φ G))`,
is induced by the top map transported along `α`. -/
lemma homologyCompIso'_inv_map_desc (L : ChainComplex C ℕ) (G : C) {s : ℕ} {T : C}
    (t : ((homComplex H L).obj G).X (s + 1) ⟶ T)
    (w : ((homComplex H L).obj G).d s (s + 1) ≫ t = 0) :
    (homologyCompIso' H H' α hα L G (s + 1)).inv ≫ Φ.map (CochainTop.desc _ t w) =
      CochainTop.desc _ ((α (L.X (s + 1))).inv.app G ≫ Φ.map t) (by
        have h : ((homComplex H' ((Φ.mapHomologicalComplex _).obj L)).obj (Φ.obj G)).d s (s + 1) ≫
            (α (L.X (s + 1))).inv.app G =
              (α (L.X s)).inv.app G ≫ Φ.map (((homComplex H L).obj G).d s (s + 1)) :=
          ((homComplexCompIso H H' α hα L G).inv.comm s (s + 1)).symm
        rw [reassoc_of% h, ← Φ.map_comp, w, Φ.map_zero, comp_zero]) := by
  rw [← cancel_epi (Φ.map (((homComplex H L).obj G).homologyπ (s + 1)) ≫
    (homologyCompIso' H H' α hα L G (s + 1)).hom)]
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Φ.map_comp, CochainTop.homologyπ_desc,
    map_homologyπ_comp_homologyCompIso'_hom, Category.assoc, Category.assoc,
    CochainTop.homologyπ_desc, Φ.map_comp]
  have h := mapCyclesIso_inv_cyclesMap_iCycles (Φ := Φ) H H' α hα L G (s + 1)
  rw [reassoc_of% h, Iso.hom_inv_id_app_assoc]

omit [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] in
include hα in
/-- A top map transported along `α` and pulled back along a chain map still kills the image of the
previous term. -/
lemma comp_inv_map_eq_zero (L : ChainComplex C ℕ) (G : C) {s : ℕ} {T : C}
    (t : ((homComplex H L).obj G).X (s + 1) ⟶ T)
    (w : ((homComplex H L).obj G).d s (s + 1) ≫ t = 0) {K' : CochainComplex D ℕ}
    (χ : K' ⟶ (homComplex H' ((Φ.mapHomologicalComplex _).obj L)).obj (Φ.obj G)) {E' : D}
    (e : Φ.obj T ⟶ E') :
    K'.d s (s + 1) ≫ χ.f (s + 1) ≫ (α (L.X (s + 1))).inv.app G ≫ Φ.map t ≫ e = 0 := by
  have h : ((homComplex H' ((Φ.mapHomologicalComplex _).obj L)).obj (Φ.obj G)).d s (s + 1) ≫
      (α (L.X (s + 1))).inv.app G =
        (α (L.X s)).inv.app G ≫ Φ.map (((homComplex H L).obj G).d s (s + 1)) :=
    ((homComplexCompIso H H' α hα L G).inv.comm s (s + 1)).symm
  rw [← χ.comm_assoc, reassoc_of% h, ← Φ.map_comp_assoc, w, Φ.map_zero, zero_comp, comp_zero,
    comp_zero]

end ExactFunctor

end LocallyFreeResolutionExt

/-! ### Sheaf `ℰxt` -/

section Sheaf

open LocallyFreeResolutionExt

attribute [local instance 2000] Abelian.toPreadditive

/-- Injective resolutions of module sheaves, as a single constant (see
`Hartshorne.RingedSpace.SheafExtLongExact`). -/
private theorem sheafOfModules_hasInjectiveResolutions₄ {Y : TopCat.{u}}
    {S : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} :
    HasInjectiveResolutions (SheafOfModules.{u} (ringCatSheafOf S)) :=
  inferInstance

attribute [local instance 3000] sheafOfModules_hasInjectiveResolutions₄

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- **The map out of a top `ℰxt` induced by a top map.** For a resolution `L_• ⟶ F` by locally
free modules of finite rank and `t : ℋom(L_{s+1}, G) ⟶ E` killing the image of `ℋom(L_s, G)`, the
composite `ℰxt^{s+1}(F, G) ≅ h^{s+1}(ℋom(L_•, G)) ⟶ E` (Hartshorne III.6, Proposition 6.5). -/
noncomputable def extTopMap {F : SheafOfModules.{u} (ringCatSheafOf R)}
    (L : ChainComplex (SheafOfModules.{u} (ringCatSheafOf R)) ℕ)
    (π : L ⟶ (ChainComplex.single₀ _).obj F) [QuasiIso π] (hL : ∀ p, IsFiniteLocallyFree (L.X p))
    {s : ℕ} (G : SheafOfModules.{u} (ringCatSheafOf R)) {E : SheafOfModules.{u} (ringCatSheafOf R)}
    (t : ((moduleSheafHomComplex L).obj G).X (s + 1) ⟶ E)
    (w : ((moduleSheafHomComplex L).obj G).d s (s + 1) ≫ t = 0) :
    (sheafExt F (s + 1)).obj G ⟶ E :=
  (sheafExtIsoHomologyOfLocallyFreeResolution L π hL (s + 1)).hom.app G ≫ CochainTop.desc _ t w

/-- **Naturality of `extTopMap` in the resolution.** For a chain map `φ : L_• ⟶ L'_•` over the
identity of `F` and top maps `t`, `t'` with `t ∘ φ^* = e ∘ t'`, the induced maps out of
`ℰxt^{s+1}(F, G)` satisfy `e ∘ (map for t') = (map for t)`. -/
theorem extTopMap_naturality {F : SheafOfModules.{u} (ringCatSheafOf R)}
    {L L' : ChainComplex (SheafOfModules.{u} (ringCatSheafOf R)) ℕ}
    (π : L ⟶ (ChainComplex.single₀ _).obj F) (π' : L' ⟶ (ChainComplex.single₀ _).obj F)
    [QuasiIso π] [QuasiIso π'] (hL : ∀ p, IsFiniteLocallyFree (L.X p))
    (hL' : ∀ p, IsFiniteLocallyFree (L'.X p)) (φ : L ⟶ L') (hφ : φ ≫ π' = π) {s : ℕ}
    (G : SheafOfModules.{u} (ringCatSheafOf R)) {E E' : SheafOfModules.{u} (ringCatSheafOf R)}
    (t : ((moduleSheafHomComplex L).obj G).X (s + 1) ⟶ E)
    (w : ((moduleSheafHomComplex L).obj G).d s (s + 1) ≫ t = 0)
    (t' : ((moduleSheafHomComplex L').obj G).X (s + 1) ⟶ E')
    (w' : ((moduleSheafHomComplex L').obj G).d s (s + 1) ≫ t' = 0) (e : E' ⟶ E)
    (he : ((moduleSheafHomComplexMap φ).app G).f (s + 1) ≫ t = t' ≫ e) :
    extTopMap L' π' hL' G t' w' ≫ e = extTopMap L π hL G t w := by
  rw [extTopMap, extTopMap, Category.assoc, CochainTop.desc_comp,
    ← sheafExtIsoHomologyOfLocallyFreeResolution_comp_homologyMap π π' hL hL' φ hφ (s + 1) G,
    Category.assoc]
  congr 1
  exact (CochainTop.desc_congr _ _ _ he.symm).trans
    (CochainTop.homologyMap_desc _ ((moduleSheafHomComplexMap φ).app G) t w).symm

/-- **`extTopMap` and a change of the first argument.** For resolutions `L_• ⟶ F`, `L'_• ⟶ F'`
and a chain map `φ : L_• ⟶ L'_•` over `u : F ⟶ F'`, the map `ℰxt^{s+1}(F', G) ⟶ ℰxt^{s+1}(F, G)`
followed by the map induced by `t` is the map induced by `t ∘ φ^*`. -/
theorem extTopMap_precomp {F F' : SheafOfModules.{u} (ringCatSheafOf R)} {u : F ⟶ F'}
    {L L' : ChainComplex (SheafOfModules.{u} (ringCatSheafOf R)) ℕ}
    (π : L ⟶ (ChainComplex.single₀ _).obj F) [QuasiIso π]
    (π' : L' ⟶ (ChainComplex.single₀ _).obj F') [QuasiIso π']
    (hL : ∀ p, IsFiniteLocallyFree (L.X p)) (hL' : ∀ p, IsFiniteLocallyFree (L'.X p))
    (φ : L ⟶ L') (hφ : φ ≫ π' = π ≫ (ChainComplex.single₀ _).map u) {s : ℕ}
    (G : SheafOfModules.{u} (ringCatSheafOf R)) {E : SheafOfModules.{u} (ringCatSheafOf R)}
    (t : ((moduleSheafHomComplex L).obj G).X (s + 1) ⟶ E)
    (w : ((moduleSheafHomComplex L).obj G).d s (s + 1) ≫ t = 0) :
    sheafExtPrecomp u G (s + 1) ≫ extTopMap L π hL G t w =
      extTopMap L' π' hL' G (((moduleSheafHomComplexMap φ).app G).f (s + 1) ≫ t)
        (by rw [← ((moduleSheafHomComplexMap φ).app G).comm_assoc, w, comp_zero]) := by
  rw [extTopMap, extTopMap, ← Category.assoc,
    sheafExtIsoHomologyOfLocallyFreeResolution_naturality π π' hL hL' φ hφ (s + 1) G,
    Category.assoc]
  congr 1
  exact CochainTop.homologyMap_desc _ ((moduleSheafHomComplexMap φ).app G) t w

/-- **`extTopMap` and a change of the second argument.** For `g : G ⟶ G'`, the map
`ℰxt^{s+1}(F, G) ⟶ ℰxt^{s+1}(F, G')` followed by the map induced by `t'` is the map induced by
`t' ∘ g_*`. -/
theorem extTopMap_map {F : SheafOfModules.{u} (ringCatSheafOf R)}
    (L : ChainComplex (SheafOfModules.{u} (ringCatSheafOf R)) ℕ)
    (π : L ⟶ (ChainComplex.single₀ _).obj F) [QuasiIso π] (hL : ∀ p, IsFiniteLocallyFree (L.X p))
    {s : ℕ} {G G' : SheafOfModules.{u} (ringCatSheafOf R)} (g : G ⟶ G')
    {E : SheafOfModules.{u} (ringCatSheafOf R)}
    (t' : ((moduleSheafHomComplex L).obj G').X (s + 1) ⟶ E)
    (w' : ((moduleSheafHomComplex L).obj G').d s (s + 1) ≫ t' = 0) :
    (sheafExt F (s + 1)).map g ≫ extTopMap L π hL G' t' w' =
      extTopMap L π hL G (((moduleSheafHomComplex L).map g).f (s + 1) ≫ t')
        (by rw [← ((moduleSheafHomComplex L).map g).comm_assoc, w', comp_zero]) := by
  rw [extTopMap, extTopMap, ← Category.assoc,
    (sheafExtIsoHomologyOfLocallyFreeResolution L π hL (s + 1)).hom.naturality g,
    Category.assoc]
  congr 1
  exact CochainTop.homologyMap_desc _ ((moduleSheafHomComplex L).map g) t' w'

/-- The top map on `U` induced by a top map on `X` through a chain map `L_•|_U ⟶ L'_•` kills the
image of the previous term. -/
lemma restrict_top_eq_zero (U : Opens X) (L : ChainComplex (SheafOfModules.{u} (ringCatSheafOf R)) ℕ)
    {L' : ChainComplex (SheafOfModules.{u} (ringCatSheafOf (restrictRingSheaf R U))) ℕ}
    (ψ : ((moduleRestrict U).mapHomologicalComplex _).obj L ⟶ L') {s : ℕ}
    (G : SheafOfModules.{u} (ringCatSheafOf R)) {E : SheafOfModules.{u} (ringCatSheafOf R)}
    (t : ((moduleSheafHomComplex L).obj G).X (s + 1) ⟶ E)
    (w : ((moduleSheafHomComplex L).obj G).d s (s + 1) ≫ t = 0)
    {E' : SheafOfModules.{u} (ringCatSheafOf (restrictRingSheaf R U))}
    (e : (moduleRestrict U).obj E ⟶ E') :
    ((moduleSheafHomComplex L').obj ((moduleRestrict U).obj G)).d s (s + 1) ≫
      ((moduleSheafHomComplexMap ψ).app _).f (s + 1) ≫
        (homRestrictIso U (L.X (s + 1))).inv.app G ≫ (moduleRestrict U).map t ≫ e = 0 :=
  comp_inv_map_eq_zero (Φ := moduleRestrict U) (moduleSheafHomBifunctor R)
    (moduleSheafHomBifunctor (restrictRingSheaf R U)) (fun F => homRestrictIso U F)
    (fun f G => homRestrict_precomp_naturality U f G) L G t w ((moduleSheafHomComplexMap ψ).app _) e

open Transport in
/-- The transported top map pulled back along a chain map `τ L_• ⟶ L'_•` kills the image of the
previous term. -/
lemma transport_top_eq_zero {A B : TopCat.{u}} {Hh : B ≅ A}
    {S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u}}
    {T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}} (ρ : RingTransport Hh S T)
    (L : ChainComplex (SheafOfModules.{u} (ringCatSheafOf T)) ℕ)
    {L' : ChainComplex (SheafOfModules.{u} (ringCatSheafOf S)) ℕ}
    (ψ : ((transport ρ).mapHomologicalComplex _).obj L ⟶ L') {s : ℕ}
    (G : SheafOfModules.{u} (ringCatSheafOf T)) {E : SheafOfModules.{u} (ringCatSheafOf T)}
    (t : ((moduleSheafHomComplex L).obj G).X (s + 1) ⟶ E)
    (w : ((moduleSheafHomComplex L).obj G).d s (s + 1) ≫ t = 0)
    {E' : SheafOfModules.{u} (ringCatSheafOf S)} (e : (transport ρ).obj E ⟶ E') :
    ((moduleSheafHomComplex L').obj ((transport ρ).obj G)).d s (s + 1) ≫
      ((moduleSheafHomComplexMap ψ).app _).f (s + 1) ≫
        (homTransportIso ρ (L.X (s + 1))).inv.app G ≫ (transport ρ).map t ≫ e = 0 :=
  comp_inv_map_eq_zero (Φ := transport ρ) (moduleSheafHomBifunctor T)
    (moduleSheafHomBifunctor S) (fun F => homTransportIso ρ F)
    (fun f G => homTransport_precomp_naturality ρ f G) L G t w
    ((moduleSheafHomComplexMap ψ).app _) e

/-- **`extTopMap` restricted to an open subset.** Let `L_• ⟶ F` be a resolution on `X`, `L'_• ⟶ F|_U`
one on `U` and `ψ : L_•|_U ⟶ L'_•` a chain map over the identity, all by locally free modules of
finite rank. If the top map `t'` on `U` is the restriction of `t` followed by `e`, read through
`ψ` and `ℋom_X(L_{s+1}, G)|_U ≅ ℋom_U(L_{s+1}|_U, G|_U)`, then the restriction of the map out of
`ℰxt^{s+1}_X(F, G)` induced by `t`, followed by `e`, is the map out of
`ℰxt^{s+1}_U(F|_U, G|_U) ≅ ℰxt^{s+1}_X(F, G)|_U` induced by `t'`. -/
theorem extTopMap_restrict (U : Opens X) {F : SheafOfModules.{u} (ringCatSheafOf R)}
    (L : ChainComplex (SheafOfModules.{u} (ringCatSheafOf R)) ℕ)
    (π : L ⟶ (ChainComplex.single₀ _).obj F) [QuasiIso π] (hL : ∀ p, IsFiniteLocallyFree (L.X p))
    (L' : ChainComplex (SheafOfModules.{u} (ringCatSheafOf (restrictRingSheaf R U))) ℕ)
    (π' : L' ⟶ (ChainComplex.single₀ _).obj ((moduleRestrict U).obj F)) [QuasiIso π']
    (hL' : ∀ p, IsFiniteLocallyFree (L'.X p))
    (ψ : ((moduleRestrict U).mapHomologicalComplex _).obj L ⟶ L')
    (hψ : ψ.f 0 ≫ π'.f 0 = (moduleRestrict U).map (π.f 0)) {s : ℕ}
    (G : SheafOfModules.{u} (ringCatSheafOf R)) {E : SheafOfModules.{u} (ringCatSheafOf R)}
    (t : ((moduleSheafHomComplex L).obj G).X (s + 1) ⟶ E)
    (w : ((moduleSheafHomComplex L).obj G).d s (s + 1) ≫ t = 0)
    {E' : SheafOfModules.{u} (ringCatSheafOf (restrictRingSheaf R U))}
    (t' : ((moduleSheafHomComplex L').obj ((moduleRestrict U).obj G)).X (s + 1) ⟶ E')
    (w' : ((moduleSheafHomComplex L').obj ((moduleRestrict U).obj G)).d s (s + 1) ≫ t' = 0)
    (e : (moduleRestrict U).obj E ⟶ E')
    (he : ((moduleSheafHomComplexMap ψ).app _).f (s + 1) ≫
      (homRestrictIso U (L.X (s + 1))).inv.app G ≫ (moduleRestrict U).map t ≫ e = t') :
    (sheafExtRestrictIso U F G (s + 1)).inv ≫ (moduleRestrict U).map (extTopMap L π hL G t w) ≫ e =
      extTopMap L' π' hL' _ t' w' := by
  have h := sheafExtIsoHomologyOfLocallyFreeResolution_restrict U L π hL L' π' hL' ψ hψ (s + 1) G
  have h2 := homologyCompIso'_inv_map_desc (Φ := moduleRestrict U) (moduleSheafHomBifunctor R)
    (moduleSheafHomBifunctor (restrictRingSheaf R U)) (fun F => homRestrictIso U F)
    (fun f G => homRestrict_precomp_naturality U f G) L G t w
  change (homologyHomComplexRestrictIso U L G (s + 1)).inv ≫ _ = _ at h2
  rw [extTopMap, extTopMap, Functor.map_comp]
  calc _ = ((sheafExtRestrictIso U F G (s + 1)).inv ≫
        (moduleRestrict U).map ((sheafExtIsoHomologyOfLocallyFreeResolution L π hL (s + 1)).hom.app G) ≫
          (homologyHomComplexRestrictIso U L G (s + 1)).hom) ≫
        ((homologyHomComplexRestrictIso U L G (s + 1)).inv ≫ (moduleRestrict U).map (CochainTop.desc _ t w)) ≫ e := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [h]
      erw [h2]
      rw [Category.assoc, CochainTop.desc_comp]
      congr 1
      exact (CochainTop.homologyMap_desc _ _ _ _).trans
        (CochainTop.desc_congr _ _ _ (by rw [← he]; simp only [Category.assoc]; try rfl))

open Transport in
/-- **`extTopMap` transported along a homeomorphism.** For a resolution `L_• ⟶ F` on `B`, one
`L'_• ⟶ τF` on `A` and a chain map `ψ : τ L_• ⟶ L'_•` over the identity, all by locally free
modules of finite rank, and a top map `t'` on `A` that is the transport of `t` followed by `e`,
read through `ψ` and `τ ℋom_B(L_{s+1}, G) ≅ ℋom_A(τ L_{s+1}, τ G)`, the transport of the map out of
`ℰxt^{s+1}_B(F, G)` induced by `t`, followed by `e`, is the map out of
`ℰxt^{s+1}_A(τF, τG) ≅ τ ℰxt^{s+1}_B(F, G)` induced by `t'`. -/
theorem extTopMap_transport {A B : TopCat.{u}} {Hh : B ≅ A}
    {S : Sheaf (Opens.grothendieckTopology A) CommRingCat.{u}}
    {T : Sheaf (Opens.grothendieckTopology B) CommRingCat.{u}} (ρ : RingTransport Hh S T)
    {F : SheafOfModules.{u} (ringCatSheafOf T)}
    (L : ChainComplex (SheafOfModules.{u} (ringCatSheafOf T)) ℕ)
    (π : L ⟶ (ChainComplex.single₀ _).obj F) [QuasiIso π] (hL : ∀ p, IsFiniteLocallyFree (L.X p))
    (L' : ChainComplex (SheafOfModules.{u} (ringCatSheafOf S)) ℕ)
    (π' : L' ⟶ (ChainComplex.single₀ _).obj ((transport ρ).obj F)) [QuasiIso π']
    (hL' : ∀ p, IsFiniteLocallyFree (L'.X p))
    (ψ : ((transport ρ).mapHomologicalComplex _).obj L ⟶ L')
    (hψ : ψ.f 0 ≫ π'.f 0 = (transport ρ).map (π.f 0)) {s : ℕ}
    (G : SheafOfModules.{u} (ringCatSheafOf T)) {E : SheafOfModules.{u} (ringCatSheafOf T)}
    (t : ((moduleSheafHomComplex L).obj G).X (s + 1) ⟶ E)
    (w : ((moduleSheafHomComplex L).obj G).d s (s + 1) ≫ t = 0)
    {E' : SheafOfModules.{u} (ringCatSheafOf S)}
    (t' : ((moduleSheafHomComplex L').obj ((transport ρ).obj G)).X (s + 1) ⟶ E')
    (w' : ((moduleSheafHomComplex L').obj ((transport ρ).obj G)).d s (s + 1) ≫ t' = 0)
    (e : (transport ρ).obj E ⟶ E')
    (he : ((moduleSheafHomComplexMap ψ).app _).f (s + 1) ≫
      (homTransportIso ρ (L.X (s + 1))).inv.app G ≫ (transport ρ).map t ≫ e = t') :
    (sheafExtTransportIso ρ F G (s + 1)).inv ≫ (transport ρ).map (extTopMap L π hL G t w) ≫ e =
      extTopMap L' π' hL' _ t' w' := by
  have h := sheafExtIsoHomologyOfLocallyFreeResolution_transport ρ L π hL L' π' hL' ψ hψ (s + 1) G
  have h2 := homologyCompIso'_inv_map_desc (Φ := transport ρ) (moduleSheafHomBifunctor T)
    (moduleSheafHomBifunctor S) (fun F => homTransportIso ρ F)
    (fun f G => homTransport_precomp_naturality ρ f G) L G t w
  change (homologyHomComplexTransportIso ρ L G (s + 1)).inv ≫ _ = _ at h2
  rw [extTopMap, extTopMap, Functor.map_comp]
  calc _ = ((sheafExtTransportIso ρ F G (s + 1)).inv ≫
        (transport ρ).map ((sheafExtIsoHomologyOfLocallyFreeResolution L π hL (s + 1)).hom.app G) ≫
          (homologyHomComplexTransportIso ρ L G (s + 1)).hom) ≫
        ((homologyHomComplexTransportIso ρ L G (s + 1)).inv ≫ (transport ρ).map (CochainTop.desc _ t w)) ≫ e := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by
      rw [h]
      erw [h2]
      rw [Category.assoc, CochainTop.desc_comp]
      congr 1
      exact (CochainTop.homologyMap_desc _ _ _ _).trans
        (CochainTop.desc_congr _ _ _ (by rw [← he]; simp only [Category.assoc]; try rfl))

end Sheaf

end Ringed

end Hartshorne
