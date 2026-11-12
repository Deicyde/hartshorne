/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.FormalCompletion

/-!
# The formal completion depends only on the closed support

Hartshorne, *Algebraic Geometry*, II.9, Remark 9.3.1 (p. 194).

Let `I` and `J` be quasi-coherent ideal sheaves on a Noetherian scheme `X` whose closed subschemes
have the same support `Z`.

* `Hartshorne.idealSheafData_exists_pow_le_of_le_radical`: on a Noetherian scheme, an ideal sheaf
  contained in the radical of `K` has a positive power contained in `K` (exponents found on a
  finite affine cover, made uniform).
* `Hartshorne.QuasicoherentIdealSubsheaf.exists_pow_carrier_le_of_support_le`: hence a positive
  power of `I` lies in `J` and vice versa.
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletionIsoOfSupportEq`: the isomorphism
  `X̂_I ≅ X̂_J` of locally ringed spaces. Both are compared with the inverse limit of the structure
  sheaves of *all* closed subschemes with support `Z`, transported to the reduced subscheme on `Z`
  (`Hartshorne.FormalCompletionSupport.supportSpace`): the powers of `I` (and of `J`) are cofinal
  among these ideal sheaves (`Hartshorne.FormalCompletionSupport.initial_powChain`), so the limits
  agree.
* `QuasicoherentIdealSubsheaf.infinitesimalNeighborhoodι_formalCompletionIsoOfSupportEq_hom_base`
  and `QuasicoherentIdealSubsheaf.formalCompletionIsoOfSupportEq_hom_c_app_π`: the
  isomorphism is canonical, the identity on points of `Z` and compatible with the projections to
  the infinitesimal neighbourhoods.
* `Hartshorne.QuasicoherentIdealSubsheaf.formalCompletion_support_invariant`: the statement of the
  remark.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Topology Opposite TopologicalSpace

namespace Hartshorne

universe u

variable {X : Scheme.{u}}

/-! ### Powers of one ideal sheaf in another -/

/-- On a Noetherian scheme, if `J` is contained in the radical of `K`, then a positive power of
`J` is contained in `K`. The exponents found on a finite affine cover are made uniform. -/
theorem idealSheafData_exists_pow_le_of_le_radical [IsNoetherian X] {J K : X.IdealSheafData}
    (h : J ≤ K.radical) : ∃ n, 0 < n ∧ J ^ n ≤ K := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U : Set X))
    (fun U => U.1.2) (fun x _ => by
      obtain ⟨U, -, hx⟩ :=
        ArtinReesKernelSheaf.exists_affine_le (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨U, hx⟩)
  have key : ∀ U : X.affineOpens, ∃ n, J.ideal U ^ n ≤ K.ideal U := fun U => by
    have := IsLocallyNoetherian.component_noetherian U
    exact Ideal.exists_pow_le_of_le_radical_of_fg (h U) (IsNoetherian.noetherian _)
  choose n hn using key
  refine ⟨t.sup n + 1, Nat.succ_pos _, ?_⟩
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : t => U.1) ?_ fun U => ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨U, hU, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
  · change J.ideal U.1 ^ (t.sup n + 1) ≤ K.ideal U.1
    exact (Ideal.pow_le_pow_right ((Finset.le_sup U.2).trans (Nat.le_succ _))).trans (hn U.1)

/-- If the support of `K` is contained in that of `J`, then `J` is contained in the radical of
`K`. -/
theorem idealSheafData_le_radical_of_support_le {J K : X.IdealSheafData}
    (h : K.support ≤ J.support) : J ≤ K.radical := by
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h

namespace QuasicoherentIdealSubsheaf

/-- Containment of quasi-coherent ideal subsheaves can be checked on affine opens. -/
theorem carrier_le_of_le {I J : QuasicoherentIdealSubsheaf X}
    (h : quasicoherentIdealSubsheafEquiv I ≤ quasicoherentIdealSubsheafEquiv J) :
    I.carrier ≤ J.carrier := by
  intro U s hs
  refine J.isLocal _ _ fun x hx => ?_
  obtain ⟨V, hVU, hxV⟩ := ArtinReesKernelSheaf.exists_affine_le hx
  exact ⟨V, hVU, hxV, h V (ArtinReesKernelSheaf.res_mem I.carrier hVU hs)⟩

/-- Containment of quasi-coherent ideal subsheaves gives containment of their ideals on affine
opens. -/
theorem quasicoherentIdealSubsheafEquiv_le_of_carrier_le {I J : QuasicoherentIdealSubsheaf X}
    (h : I.carrier ≤ J.carrier) :
    quasicoherentIdealSubsheafEquiv I ≤ quasicoherentIdealSubsheafEquiv J :=
  fun _ _ hx => h _ hx

/-- On a Noetherian scheme, if the closed set cut out by `J` contains the one cut out by `I`, then
a positive power of `I` is contained in `J`. -/
theorem exists_pow_carrier_le_of_support_le [IsNoetherian X] {I J : QuasicoherentIdealSubsheaf X}
    (h : (quasicoherentIdealSubsheafEquiv J).support ≤
      (quasicoherentIdealSubsheafEquiv I).support) :
    ∃ a, 0 < a ∧ (I ^ a).carrier ≤ J.carrier := by
  obtain ⟨a, ha, hle⟩ := idealSheafData_exists_pow_le_of_le_radical
    (idealSheafData_le_radical_of_support_le h)
  exact ⟨a, ha, carrier_le_of_le (by rwa [quasicoherentIdealSubsheafEquiv_pow])⟩

end QuasicoherentIdealSubsheaf

/-- `appLE` along equal morphisms. -/
private lemma Scheme.Hom.appLE_congr_hom {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g)
    (U : B.Opens) (V : A.Opens) (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-! ### Ideal sheaves with a given support -/

namespace FormalCompletionSupport

open Scheme.IdealSheafData in
/-- The ideal sheaves (ideal sheaf data) of `X` with support `Z`, ordered by inclusion. -/
abbrev SupportIdeal (Z : Closeds X) : Type u := {K : X.IdealSheafData // K.support = Z}

variable (Z : Closeds X)

/-- An ideal sheaf with support `Z` lies in the vanishing ideal of `Z`. -/
lemma le_vanishingIdeal (K : SupportIdeal Z) :
    K.1 ≤ Scheme.IdealSheafData.vanishingIdeal Z :=
  Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp K.2.ge

/-- The reduced closed subscheme on `Z`, a closed subscheme of every closed subscheme with
support `Z`. -/
abbrev reduced : Scheme.{u} := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme

/-- The closed immersion of the reduced subscheme on `Z` into the subscheme cut out by `K`. -/
def toSubscheme (K : SupportIdeal Z) : reduced Z ⟶ K.1.subscheme :=
  Scheme.IdealSheafData.inclusion (le_vanishingIdeal Z K)

@[reassoc (attr := simp)]
lemma toSubscheme_comp_inclusion {K L : SupportIdeal Z} (h : K.1 ≤ L.1) :
    toSubscheme Z L ≫ Scheme.IdealSheafData.inclusion h = toSubscheme Z K :=
  Scheme.IdealSheafData.inclusion_comp _ _

@[reassoc (attr := simp)]
lemma toSubscheme_comp_subschemeι (K : SupportIdeal Z) :
    toSubscheme Z K ≫ K.1.subschemeι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- The reduced subscheme on `Z` has the same points as every subscheme with support `Z`. -/
lemma toSubscheme_surjective (K : SupportIdeal Z) : Function.Surjective (toSubscheme Z K) := by
  intro z
  have hz : K.1.subschemeι z ∈
      Set.range (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      show (Z : Set X) = K.1.support from congrArg _ K.2.symm,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  obtain ⟨y, hy⟩ := hz
  refine ⟨y, K.1.subschemeι.isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, toSubscheme_comp_subschemeι, hy]

/-- The inclusion of the reduced subscheme on `Z` is a homeomorphism, in particular an open
embedding. -/
lemma isOpenEmbedding_toSubscheme (K : SupportIdeal Z) : IsOpenEmbedding (toSubscheme Z K) := by
  have h1 : IsEmbedding (K.1.subschemeι ∘ toSubscheme Z K) := by
    have h := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι.isClosedEmbedding.isEmbedding
    convert h using 1
    funext y
    rw [Function.comp_apply, ← Scheme.Hom.comp_apply, toSubscheme_comp_subschemeι]
  refine ⟨(IsEmbedding.of_comp_iff K.1.subschemeι.isClosedEmbedding.isEmbedding).mp h1, ?_⟩
  rw [(toSubscheme_surjective Z K).range_eq]
  exact isOpen_univ

/-- The image of `V` in the subscheme of `L` lies in the preimage of its image in the subscheme
of `K`, for `K ≤ L`. -/
lemma functor_obj_le_preimage_inclusion {K L : SupportIdeal Z} (h : K.1 ≤ L.1)
    (V : Opens (reduced Z)) :
    (isOpenEmbedding_toSubscheme Z L).functor.obj V ≤
      Scheme.IdealSheafData.inclusion h ⁻¹ᵁ (isOpenEmbedding_toSubscheme Z K).functor.obj V := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, by rw [← Scheme.Hom.comp_apply, toSubscheme_comp_inclusion]⟩

/-- The structure sheaf of the subscheme cut out by `K`, as a presheaf on the reduced subscheme
on `Z`, functorially in `K` (restriction along the inclusions of subschemes). -/
def supportPresheaf : SupportIdeal Z ⥤ TopCat.Presheaf CommRingCat.{u} (reduced Z) where
  obj K := (isOpenEmbedding_toSubscheme Z K).functor.op ⋙ K.1.subscheme.presheaf
  map {K L} f :=
    { app V := (Scheme.IdealSheafData.inclusion (leOfHom f)).appLE _ _
        (functor_obj_le_preimage_inclusion Z (leOfHom f) V.unop)
      naturality V V' i := by
        simp only [Functor.comp_map, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }
  map_id K := by
    refine NatTrans.ext (funext fun V => ?_)
    change (Scheme.IdealSheafData.inclusion le_rfl).appLE _ _ _ = 𝟙 _
    rw [Scheme.Hom.appLE_congr_hom (Scheme.IdealSheafData.inclusion_id _)]
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact K.1.subscheme.presheaf.map_id _
  map_comp {K L M} f g := by
    refine NatTrans.ext (funext fun V => ?_)
    change _ = (Scheme.IdealSheafData.inclusion _).appLE _ _ _ ≫
      (Scheme.IdealSheafData.inclusion _).appLE _ _ _
    rw [Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_congr_hom (Scheme.IdealSheafData.inclusion_comp _ _)]

lemma isSheaf_supportPresheaf (K : SupportIdeal Z) : ((supportPresheaf Z).obj K).IsSheaf :=
  TopCat.Presheaf.isSheaf_of_isOpenEmbedding (isOpenEmbedding_toSubscheme Z K)
    K.1.subscheme.IsSheaf

/-- The sheafed space on the reduced subscheme on `Z` whose structure sheaf is the inverse limit
of the structure sheaves of all closed subschemes with support `Z`. -/
def supportSpace : SheafedSpace CommRingCat.{u} where
  carrier := (reduced Z).toTopCat
  presheaf := limit (supportPresheaf Z)
  IsSheaf := TopCat.limit_isSheaf _ fun K => isSheaf_supportPresheaf Z K

/-! ### Comparison with the formal completion along an ideal sheaf with support `Z` -/

variable {Z} (I : QuasicoherentIdealSubsheaf X)
  (hI : (quasicoherentIdealSubsheafEquiv I).support = Z)
include hI

lemma support_pow_succ (n : ℕ) :
    (quasicoherentIdealSubsheafEquiv (I ^ (n + 1))).support = Z := by
  rw [quasicoherentIdealSubsheafEquiv_pow, Scheme.IdealSheafData.support_pow_succ, hI]

/-- The inverse system `n ↦ I ^ (n + 1)` of ideal sheaves with support `Z`. -/
def powChain : ℕᵒᵖ ⥤ SupportIdeal Z where
  obj n := ⟨quasicoherentIdealSubsheafEquiv (I ^ (n.unop + 1)), support_pow_succ I hI n.unop⟩
  map {m n} f := homOfLE (by
    change quasicoherentIdealSubsheafEquiv (I ^ (m.unop + 1)) ≤
      quasicoherentIdealSubsheafEquiv (I ^ (n.unop + 1))
    rw [quasicoherentIdealSubsheafEquiv_pow, quasicoherentIdealSubsheafEquiv_pow]
    intro U
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    exact Ideal.pow_le_pow_right (Nat.succ_le_succ (leOfHom f.unop)))

/-- On a Noetherian scheme the powers of `I` are cofinal among the ideal sheaves with support
`Z`. -/
lemma initial_powChain [IsNoetherian X] : (powChain I hI).Initial := by
  refine Functor.initial_of_exists_of_isCofiltered _ (fun K => ?_)
    (fun _ _ => ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  obtain ⟨n, hn, hle⟩ := idealSheafData_exists_pow_le_of_le_radical
    (J := quasicoherentIdealSubsheafEquiv I) (K := K.1)
    (idealSheafData_le_radical_of_support_le (by rw [K.2, hI]))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  refine ⟨op k, ⟨homOfLE ?_⟩⟩
  change quasicoherentIdealSubsheafEquiv (I ^ (k + 1)) ≤ K.1
  rwa [quasicoherentIdealSubsheafEquiv_pow]

/-- The closed immersion of the reduced subscheme on `Z` into `Y_1`, a homeomorphism. -/
def toOne : reduced Z ⟶ I.infinitesimalNeighborhood 1 :=
  toSubscheme Z ((powChain I hI).obj (op 0))

lemma toOne_comp_infinitesimalNeighborhoodFromOne (n : ℕ) :
    toOne I hI ≫ I.infinitesimalNeighborhoodFromOne n =
      toSubscheme Z ((powChain I hI).obj (op n)) :=
  Scheme.IdealSheafData.inclusion_comp _ _

@[reassoc]
lemma toOne_comp_infinitesimalNeighborhoodι :
    toOne I hI ≫ I.infinitesimalNeighborhoodι 1 =
      (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
  toSubscheme_comp_subschemeι Z ((powChain I hI).obj (op 0))

lemma functor_obj_preimage_toOne (n : ℕ) (W : Opens (I.infinitesimalNeighborhood 1)) :
    (isOpenEmbedding_toSubscheme Z ((powChain I hI).obj (op n))).functor.obj
        ((Opens.map (toOne I hI).base).obj W) =
      (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨toOne I hI y, hy, by
      rw [← Scheme.Hom.comp_apply, toOne_comp_infinitesimalNeighborhoodFromOne]
      rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, rfl⟩ := toSubscheme_surjective Z ((powChain I hI).obj (op 0)) w
    refine ⟨y, hw, ?_⟩
    change _ = I.infinitesimalNeighborhoodFromOne n (toOne I hI y)
    rw [← Scheme.Hom.comp_apply, toOne_comp_infinitesimalNeighborhoodFromOne]
    rfl

/-- The `n`-th term of the comparison: the two descriptions of `𝒪_{Y_(n+1)}` on `|Y_1|`. -/
def compareApp (n : ℕ) :
    (TopCat.Presheaf.pushforward _ (toOne I hI).base).obj
        ((supportPresheaf Z).obj ((powChain I hI).obj (op n))) ⟶
      (I.formalCompletionSheafObj n).obj where
  app W := show Γ(((powChain I hI).obj (op n)).1.subscheme,
      (isOpenEmbedding_toSubscheme Z ((powChain I hI).obj (op n))).functor.obj
        ((Opens.map (toOne I hI).base).obj W.unop)) ⟶
      Γ(((powChain I hI).obj (op n)).1.subscheme,
        (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj W.unop) from
    ((powChain I hI).obj (op n)).1.subscheme.presheaf.map
      (eqToHom (congrArg op (functor_obj_preimage_toOne I hI n W.unop)))
  naturality W W' i := by
    change ((powChain I hI).obj (op n)).1.subscheme.presheaf.map _ ≫
        ((powChain I hI).obj (op n)).1.subscheme.presheaf.map _ =
      ((powChain I hI).obj (op n)).1.subscheme.presheaf.map _ ≫
        ((powChain I hI).obj (op n)).1.subscheme.presheaf.map _
    rw [← Functor.map_comp]
    exact (congrArg _ (Subsingleton.elim _ _)).trans (Functor.map_comp _ _ _)

instance (n : ℕ) : IsIso (compareApp I hI n) := by
  have (W : (Opens (I.infinitesimalNeighborhood 1))ᵒᵖ) : IsIso ((compareApp I hI n).app W) := by
    change IsIso (((powChain I hI).obj (op n)).1.subscheme.presheaf.map _)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The comparison between the inverse system `n ↦ 𝒪_{Y_(n+1)}` transported to the reduced
subscheme on `Z`, and the inverse system of the formal completion. -/
def compare :
    (powChain I hI ⋙ supportPresheaf Z) ⋙ TopCat.Presheaf.pushforward _ (toOne I hI).base ⟶
      I.formalCompletionDiagram ⋙ sheafToPresheaf _ _ :=
  NatTrans.ofOpSequence (fun n => compareApp I hI n) (fun n => by
    have hmap : I.formalCompletionDiagram.map (homOfLE (Nat.le_add_right n 1)).op =
        I.formalCompletionSheafMap n :=
      CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ _ n
    refine NatTrans.ext (funext fun W => ?_)
    change (((powChain I hI ⋙ supportPresheaf Z) ⋙
        TopCat.Presheaf.pushforward _ (toOne I hI).base).map
          (homOfLE (Nat.le_add_right n 1)).op).app W ≫ (compareApp I hI n).app W =
      (compareApp I hI (n + 1)).app W ≫
        (I.formalCompletionDiagram.map (homOfLE (Nat.le_add_right n 1)).op).hom.app W
    rw [hmap]
    change (Scheme.IdealSheafData.inclusion _).appLE _ _ _ ≫
        ((powChain I hI).obj (op n)).1.subscheme.presheaf.map _ =
      ((powChain I hI).obj (op (n + 1))).1.subscheme.presheaf.map _ ≫
        (I.infinitesimalNeighborhoodSucc n).appLE _ _ _
    refine (Scheme.Hom.appLE_map _ _ _).trans ?_
    refine Eq.trans ?_ (Scheme.Hom.map_appLE _ _ _).symm
    rfl)

instance : IsIso (compare I hI) := by
  have (n : ℕᵒᵖ) : IsIso ((compare I hI).app n) := by
    change IsIso (compareApp I hI n.unop)
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The underlying homeomorphism from the reduced subscheme on `Z` to `|Y_1|`. -/
def homeomorphToOne : (reduced Z).toTopCat ≅ (I.infinitesimalNeighborhood 1).toTopCat :=
  let h := (Equiv.ofBijective _
    ⟨(isOpenEmbedding_toSubscheme Z ((powChain I hI).obj (op 0))).injective,
      toSubscheme_surjective Z ((powChain I hI).obj (op 0))⟩).toHomeomorphOfContinuousOpen
    (toOne I hI).continuous (isOpenEmbedding_toSubscheme Z ((powChain I hI).obj (op 0))).isOpenMap
  { hom := (toOne I hI).base
    inv := TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
    hom_inv_id := by
      ext y
      exact h.symm_apply_apply y
    inv_hom_id := by
      ext y
      exact h.apply_symm_apply y }

omit hI in
/-- The limit defining the formal completion is preserved by forgetting the sheaf condition. -/
lemma limitPreserved : Nonempty (IsLimit ((sheafToPresheaf
    (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1 : TopCat)) CommRingCat.{u}).mapCone
      (limit.cone I.formalCompletionDiagram))) := by
  have hpres : PreservesLimitsOfShape ℕᵒᵖ (sheafToPresheaf
      (Opens.grothendieckTopology (I.infinitesimalNeighborhood 1 : TopCat)) CommRingCat.{u}) :=
    inferInstance
  exact (hpres.preservesLimit (K := I.formalCompletionDiagram)).preserves
    (limit.isLimit I.formalCompletionDiagram)

/-- The structure sheaf of `supportSpace Z`, pushed forward to `|Y_1|`, is the structure sheaf of
the formal completion along `I`. -/
def pushforwardIso [IsNoetherian X] :
    (toOne I hI).base _* limit (supportPresheaf Z) ≅ (limit I.formalCompletionDiagram).obj :=
  haveI := initial_powChain I hI
  haveI : PreservesLimitsOfShape ℕᵒᵖ
      (TopCat.Presheaf.pushforward CommRingCat.{u} (toOne I hI).base) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ ((Functor.whiskeringLeft _ _ _).obj _))
  (TopCat.Presheaf.pushforward _ (toOne I hI).base).mapIso
      (Functor.Initial.limitIso (powChain I hI) (supportPresheaf Z)).symm ≪≫
    preservesLimitIso (TopCat.Presheaf.pushforward _ _) _ ≪≫
    HasLimit.isoOfNatIso (asIso (compare I hI)) ≪≫
    (IsLimit.conePointUniqueUpToIso (limitPreserved I).some
      (limit.isLimit (I.formalCompletionDiagram ⋙ sheafToPresheaf _ _))).symm

/-- The formal completion along `I` is isomorphic, as a sheafed space, to `supportSpace Z`. -/
def sheafedSpaceIso [IsNoetherian X] : supportSpace Z ≅ I.formalCompletion.toSheafedSpace :=
  SheafedSpace.isoMk (PresheafedSpace.isoOfComponents (homeomorphToOne I hI) (pushforwardIso I hI))

/-- `pushforwardIso` followed by the `n`-th projection of the formal completion is the projection
of the limit onto `𝒪_{Y_(n+1)}`, followed by `compareApp`. -/
lemma pushforwardIso_hom_π [IsNoetherian X] (n : ℕ) :
    (pushforwardIso I hI).hom ≫ (limit.π I.formalCompletionDiagram (op n)).hom =
      (TopCat.Presheaf.pushforward _ (toOne I hI).base).map
        (limit.π (supportPresheaf Z) ((powChain I hI).obj (op n))) ≫ compareApp I hI n := by
  have := initial_powChain I hI
  have : PreservesLimitsOfShape ℕᵒᵖ
      (TopCat.Presheaf.pushforward CommRingCat.{u} (toOne I hI).base) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ ((Functor.whiskeringLeft _ _ _).obj _))
  have h1 := IsLimit.conePointUniqueUpToIso_inv_comp (limitPreserved I).some
    (limit.isLimit (I.formalCompletionDiagram ⋙ sheafToPresheaf _ _)) (op n)
  unfold pushforwardIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  erw [h1, limit.cone_π, HasLimit.isoOfNatIso_hom_π, asIso_hom, preservesLimitIso_hom_π_assoc,
    ← Functor.map_comp_assoc, Functor.Initial.limitIso_inv, limit.pre_π]
  rfl

/-- The sections version of `pushforwardIso_hom_π`. -/
lemma pushforwardIso_hom_app_π [IsNoetherian X] (n : ℕ)
    (W : (Opens (I.infinitesimalNeighborhood 1))ᵒᵖ) :
    (pushforwardIso I hI).hom.app W ≫ (limit.π I.formalCompletionDiagram (op n)).hom.app W =
      (limit.π (supportPresheaf Z) ((powChain I hI).obj (op n))).app
          (op ((Opens.map (toOne I hI).base).obj W.unop)) ≫ (compareApp I hI n).app W :=
  congrArg (fun f => f.app W) (pushforwardIso_hom_π I hI n)

/-- The `n`-th projection of the formal completion, through `pushforwardIso`. -/
lemma pushforwardIso_inv_app_π [IsNoetherian X] (n : ℕ)
    (W : (Opens (I.infinitesimalNeighborhood 1))ᵒᵖ) :
    (pushforwardIso I hI).inv.app W ≫
        (limit.π (supportPresheaf Z) ((powChain I hI).obj (op n))).app
          (op ((Opens.map (toOne I hI).base).obj W.unop)) ≫ (compareApp I hI n).app W =
      (limit.π I.formalCompletionDiagram (op n)).hom.app W := by
  rw [← pushforwardIso_hom_app_π]
  erw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

omit hI in
/-- The comparison underlying `formalCompletionIsoOfSupportEq_hom_c_app_π`: for ideal sheaves `I`
and `J` with support `Z` and `J ^ (m + 1) ≤ I ^ (n + 1)`, the map from the limit over all ideal
sheaves with support `Z` to `𝒪_{Y_(n+1)}` factors through `𝒪_{Y'_(m+1)}`, where `Y'` is cut out by
`J`, followed by restriction. -/
lemma toPushforwardOfIso_app_π [IsNoetherian X] (J : QuasicoherentIdealSubsheaf X)
    (hI : (quasicoherentIdealSubsheafEquiv I).support = Z)
    (hJ : (quasicoherentIdealSubsheafEquiv J).support = Z) {n m : ℕ}
    (hnm : quasicoherentIdealSubsheafEquiv (J ^ (m + 1)) ≤
      quasicoherentIdealSubsheafEquiv (I ^ (n + 1)))
    (V : Opens (J.infinitesimalNeighborhood 1))
    (hle : (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
        ((Opens.map (homeomorphToOne I hI).inv).obj ((Opens.map (toOne J hJ).base).obj V)) ≤
      Scheme.IdealSheafData.inclusion hnm ⁻¹ᵁ
        (J.isOpenEmbedding_infinitesimalNeighborhoodFromOne m).functor.obj V) :
    (TopCat.Presheaf.toPushforwardOfIso (homeomorphToOne I hI) (pushforwardIso I hI).hom).app
        (op ((Opens.map (toOne J hJ).base).obj V)) ≫
      (limit.π I.formalCompletionDiagram (op n)).hom.app
        (op ((Opens.map (homeomorphToOne I hI).inv).obj ((Opens.map (toOne J hJ).base).obj V))) =
    (limit.π (supportPresheaf Z) ((powChain J hJ).obj (op m))).app
        (op ((Opens.map (toOne J hJ).base).obj V)) ≫
      (compareApp J hJ m).app (op V) ≫
        (Scheme.IdealSheafData.inclusion hnm).appLE _ _ hle := by
  have hw := congrArg (fun g => g.app (op ((Opens.map (toOne J hJ).base).obj V)))
    (limit.w (supportPresheaf Z)
      (homOfLE hnm : (powChain J hJ).obj (op m) ⟶ (powChain I hI).obj (op n)))
  erw [TopCat.Presheaf.toPushforwardOfIso_app]
  erw [Category.assoc]
  erw [pushforwardIso_hom_app_π I hI n]
  erw [← Category.assoc, NatTrans.naturality, Category.assoc]
  erw [← hw]
  erw [NatTrans.comp_app, Category.assoc]
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (Scheme.Hom.appLE_map _ _ _)).trans ?_
  refine (Scheme.Hom.appLE_map _ _ _).trans ?_
  refine Eq.trans ?_ (Scheme.Hom.map_appLE _ _ _).symm
  rfl

end FormalCompletionSupport

namespace QuasicoherentIdealSubsheaf

open FormalCompletionSupport

/-- **The formal completion depends only on the closed support** (Hartshorne II.9,
Remark 9.3.1, p. 194). -/
def formalCompletionIsoOfSupportEq [IsNoetherian X] {I J : QuasicoherentIdealSubsheaf X}
    (h : (quasicoherentIdealSubsheafEquiv I).support =
      (quasicoherentIdealSubsheafEquiv J).support) :
    I.formalCompletion ≅ J.formalCompletion :=
  LocallyRingedSpace.isoOfSheafedSpaceIso
    ((sheafedSpaceIso I rfl).symm ≪≫ sheafedSpaceIso J h.symm)

/-- The isomorphism `formalCompletionIsoOfSupportEq` is the identity on points of the common
support: it commutes with the inclusions of `|Y_1|` into `X`. -/
theorem infinitesimalNeighborhoodι_formalCompletionIsoOfSupportEq_hom_base [IsNoetherian X]
    {I J : QuasicoherentIdealSubsheaf X}
    (h : (quasicoherentIdealSubsheafEquiv I).support =
      (quasicoherentIdealSubsheafEquiv J).support)
    (y : I.formalCompletion) :
    J.infinitesimalNeighborhoodι 1 ((formalCompletionIsoOfSupportEq h).hom.base y) =
      I.infinitesimalNeighborhoodι 1 y := by
  obtain ⟨z, rfl⟩ := toSubscheme_surjective _ ((powChain I rfl).obj (op 0)) y
  change J.infinitesimalNeighborhoodι 1 ((homeomorphToOne J h.symm).hom
      ((homeomorphToOne I rfl).inv ((homeomorphToOne I rfl).hom z))) =
    I.infinitesimalNeighborhoodι 1 (toOne I rfl z)
  rw [Iso.hom_inv_id_apply]
  change J.infinitesimalNeighborhoodι 1 (toOne J h.symm z) = _
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, toOne_comp_infinitesimalNeighborhoodι,
    toOne_comp_infinitesimalNeighborhoodι]

/-- For a morphism `f : X̂_I ⟶ X̂_J` which is the identity on points of `X` and for
`J ^ (m + 1) ≤ I ^ (n + 1)`, the image in `Y_(n+1)` of the preimage of `V` lies over the image of
`V` in `Y'_(m+1)`, where `Y'` is cut out by `J`. -/
lemma functor_obj_le_preimage_inclusion_of_comp {I J : QuasicoherentIdealSubsheaf X}
    (f : I.formalCompletion ⟶ J.formalCompletion)
    (hf : ∀ y : I.formalCompletion,
      J.infinitesimalNeighborhoodι 1 (f.base y) = I.infinitesimalNeighborhoodι 1 y)
    {n m : ℕ} (hnm : (J ^ (m + 1)).carrier ≤ (I ^ (n + 1)).carrier)
    (V : Opens (J.infinitesimalNeighborhood 1)) :
    (I.isOpenEmbedding_infinitesimalNeighborhoodFromOne n).functor.obj
        ((Opens.map f.base).obj V) ≤
      Scheme.IdealSheafData.inclusion (quasicoherentIdealSubsheafEquiv_le_of_carrier_le hnm) ⁻¹ᵁ
        (J.isOpenEmbedding_infinitesimalNeighborhoodFromOne m).functor.obj V := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨f.base y, hy, (J.infinitesimalNeighborhoodι (m + 1)).isClosedEmbedding.injective ?_⟩
  have e1 : (J.infinitesimalNeighborhoodFromOne m ≫ J.infinitesimalNeighborhoodι (m + 1))
      (f.base y) = I.infinitesimalNeighborhoodι 1 y := by
    rw [infinitesimalNeighborhoodFromOne_comp_ι]
    exact hf y
  have e3 : I.infinitesimalNeighborhoodFromOne n ≫
      Scheme.IdealSheafData.inclusion (quasicoherentIdealSubsheafEquiv_le_of_carrier_le hnm) ≫
      J.infinitesimalNeighborhoodι (m + 1) = I.infinitesimalNeighborhoodι 1 :=
    (congrArg (I.infinitesimalNeighborhoodFromOne n ≫ ·)
      (Scheme.IdealSheafData.inclusion_subschemeι _)).trans
      (infinitesimalNeighborhoodFromOne_comp_ι I n)
  have e2 := congrArg (fun g => g y) e3
  exact e1.trans e2.symm

/-- **The isomorphism `formalCompletionIsoOfSupportEq` is canonical on sections.** Whenever
`J ^ (m + 1) ⊆ I ^ (n + 1)`, so that `Y_(n+1)` (cut out by `I ^ (n + 1)`) is a closed subscheme of
`Y'_(m+1)` (cut out by `J ^ (m + 1)`), the isomorphism followed by the projection of `𝒪_{X̂_I}` to
`𝒪_{Y_(n+1)}` equals the projection of `𝒪_{X̂_J}` to `𝒪_{Y'_(m+1)}` followed by restriction along
`Y_(n+1) ⟶ Y'_(m+1)`. By the universal property of the limit `𝒪_{X̂_I}`, these conditions determine
the isomorphism on sections. -/
theorem formalCompletionIsoOfSupportEq_hom_c_app_π [IsNoetherian X]
    {I J : QuasicoherentIdealSubsheaf X}
    (h : (quasicoherentIdealSubsheafEquiv I).support =
      (quasicoherentIdealSubsheafEquiv J).support)
    {n m : ℕ} (hnm : (J ^ (m + 1)).carrier ≤ (I ^ (n + 1)).carrier)
    (V : Opens (J.infinitesimalNeighborhood 1)) :
    (formalCompletionIsoOfSupportEq h).hom.c.app (op V) ≫
        (limit.π I.formalCompletionDiagram (op n)).hom.app
          (op ((Opens.map (formalCompletionIsoOfSupportEq h).hom.base).obj V)) =
      (limit.π J.formalCompletionDiagram (op m)).hom.app (op V) ≫
        (Scheme.IdealSheafData.inclusion
          (quasicoherentIdealSubsheafEquiv_le_of_carrier_le hnm)).appLE _ _
          (functor_obj_le_preimage_inclusion_of_comp _
            (infinitesimalNeighborhoodι_formalCompletionIsoOfSupportEq_hom_base h) hnm V) := by
  have hB := pushforwardIso_inv_app_π J h.symm m (op V)
  have he : (formalCompletionIsoOfSupportEq h).hom.c.app (op V) =
      (pushforwardIso J h.symm).inv.app (op V) ≫
        (TopCat.Presheaf.toPushforwardOfIso (homeomorphToOne I rfl)
          (pushforwardIso I rfl).hom).app (op ((Opens.map (toOne J h.symm).base).obj V)) := rfl
  rw [he]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (toPushforwardOfIso_app_π I J rfl h.symm
    (quasicoherentIdealSubsheafEquiv_le_of_carrier_le hnm) V
    (functor_obj_le_preimage_inclusion_of_comp _
      (infinitesimalNeighborhoodι_formalCompletionIsoOfSupportEq_hom_base h) hnm V))).trans ?_
  refine Eq.trans ?_ (congrArg (· ≫ _) hB)
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

/-- **The formal completion depends only on the closed support** (Hartshorne II.9,
Remark 9.3.1, p. 194). Let `I` and `J` be quasi-coherent (on a Noetherian scheme equivalently,
coherent) ideal sheaves on a Noetherian scheme `X` whose closed subschemes have the same support.
Then a positive power of each is contained in the other, and the formal completions `X̂_I` and
`X̂_J` are canonically isomorphic as locally ringed spaces: there is an isomorphism which is the
identity on the points of the common support and which, on sections, is compatible with the
projections to the infinitesimal neighbourhoods (`formalCompletionIsoOfSupportEq_hom_c_app_π`). -/
theorem formalCompletion_support_invariant [IsNoetherian X] {I J : QuasicoherentIdealSubsheaf X}
    (h : (quasicoherentIdealSubsheafEquiv I).support =
      (quasicoherentIdealSubsheafEquiv J).support) :
    (∃ a, 0 < a ∧ (I ^ a).carrier ≤ J.carrier) ∧ (∃ b, 0 < b ∧ (J ^ b).carrier ≤ I.carrier) ∧
      ∃ (e : I.formalCompletion ≅ J.formalCompletion)
        (he : ∀ y : I.formalCompletion,
          J.infinitesimalNeighborhoodι 1 (e.hom.base y) = I.infinitesimalNeighborhoodι 1 y),
        ∀ (n m : ℕ) (hnm : (J ^ (m + 1)).carrier ≤ (I ^ (n + 1)).carrier)
          (V : Opens (J.infinitesimalNeighborhood 1)),
          e.hom.c.app (op V) ≫ (limit.π I.formalCompletionDiagram (op n)).hom.app
              (op ((Opens.map e.hom.base).obj V)) =
            (limit.π J.formalCompletionDiagram (op m)).hom.app (op V) ≫
              (Scheme.IdealSheafData.inclusion
                (quasicoherentIdealSubsheafEquiv_le_of_carrier_le hnm)).appLE _ _
                (functor_obj_le_preimage_inclusion_of_comp e.hom he hnm V) :=
  ⟨exists_pow_carrier_le_of_support_le h.ge, exists_pow_carrier_le_of_support_le h.le,
    formalCompletionIsoOfSupportEq h,
    infinitesimalNeighborhoodι_formalCompletionIsoOfSupportEq_hom_base h,
    fun _ _ hnm V => formalCompletionIsoOfSupportEq_hom_c_app_π h hnm V⟩

end QuasicoherentIdealSubsheaf

end Hartshorne
