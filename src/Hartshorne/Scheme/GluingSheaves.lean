/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# Gluing sheaves on an open cover

Hartshorne, *Algebraic Geometry*, II, Exercise 1.22 (p. 69).

Let `{U i}` be an open cover of a topological space `X`, let `F i` be a sheaf on `U i`, and let
`φ i j : F i |(U i ∩ U j) ≅ F j |(U i ∩ U j)` be isomorphisms with `φ i i = id` and
`φ i k = φ j k ∘ φ i j` on `U i ∩ U j ∩ U k`. Then there is a sheaf `F` on `X` with isomorphisms
`ψ i : F|U i ≅ F i` such that `ψ j = φ i j ∘ ψ i` on `U i ∩ U j`, and `F` is unique up to a
unique isomorphism compatible with the `ψ i`.

## Conventions

* A sheaf on an open subset `V` of `X` is a sheaf on the subspace `V`.
* For opens `V ≤ W`, the restriction `G|V` of a sheaf `G` on `W` (or on `X`) is the inverse image
  along the open embedding `V ↪ W`, whose sections over an open `V' ⊆ V` are the sections of `G`
  over `V'`; this is Mathlib's `Topology.IsOpenEmbedding.sheafPullback`, which
  `Topology.IsOpenEmbedding.sheafPullbackIso` identifies with the inverse image
  `TopCat.Sheaf.pullback` (for the usual concrete categories, such as abelian groups).
* The value category `C` is arbitrary, subject to having limits indexed by the pairwise
  intersection category of the index type of the cover; this includes abelian groups.

## Construction

The glued sheaf is the limit of the diagram consisting of the pushforwards `(ι_i)_* F i` and
`(ι_ij)_* (F j |(U i ∩ U j))`, with the maps given by restriction and by restriction followed by
`φ i j`. Sections over `O` are thus compatible families of sections of the `F i` over `O ∩ U i`.
The cocycle condition and `φ i i = id` give the isomorphisms `ψ i`; the sheaf condition of a
second solution `G`, in the form of pairwise intersections, gives the uniqueness.

## Main results

* `Hartshorne.SheafGluing.GluingData`: the gluing data.
* `Hartshorne.SheafGluing.GluingData.exists_unique_gluing`: existence and uniqueness of the glued
  sheaf.
* `Hartshorne.SheafGluing.exists_unique_gluing_addCommGrp`: the case of sheaves of abelian groups.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology

namespace Hartshorne.SheafGluing

universe w u

variable {C : Type*} [Category.{u} C] {X : TopCat.{u}}

/-- The inclusion `V ↪ W` of open subspaces of `X`, for `V ≤ W`. -/
def inclLE {V W : Opens X} (h : V ≤ W) : (Opens.toTopCat X).obj V ⟶ (Opens.toTopCat X).obj W :=
  (Opens.toTopCat X).map (homOfLE h)

lemma isOpenEmbedding_inclLE {V W : Opens X} (h : V ≤ W) : IsOpenEmbedding (inclLE h) := by
  have h1 : IsOpenEmbedding ((inclLE h) ≫ W.inclusion') := V.isOpenEmbedding
  exact IsOpenEmbedding.of_comp _ W.isOpenEmbedding h1

variable (C) in
/-- Restriction of a sheaf on `X` to an open subset `V`. -/
abbrev restrictOpen (V : Opens X) :
    Sheaf (Opens.grothendieckTopology X) C ⥤
      Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V)) C :=
  V.isOpenEmbedding.sheafPullback C

variable (C) in
/-- Restriction of a sheaf on an open subset `W` to an open subset `V ≤ W`. -/
abbrev restrictLE {V W : Opens X} (h : V ≤ W) :
    Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C ⥤
      Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V)) C :=
  (isOpenEmbedding_inclLE h).sheafPullback C

/-- Precomposing a presheaf with two functors of opens that agree on objects. -/
@[simps!]
def precompIso {A B : TopCat.{u}} (e e' : Opens A ⥤ Opens B) (h : ∀ O, e.obj O = e'.obj O)
    (G : B.Presheaf C) : e.op ⋙ G ≅ e'.op ⋙ G :=
  NatIso.ofComponents (fun O => G.mapIso (eqToIso (h O.unop)).symm.op) (by
    intros
    simp only [Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map,
      Functor.mapIso_hom, Iso.op_hom, ← G.map_comp]
    rfl)

lemma inclLE_functor_comp_obj {T V W : Opens X} (hTV : T ≤ V) (hVW : V ≤ W)
    (O : Opens ((Opens.toTopCat X).obj T)) :
    (isOpenEmbedding_inclLE hVW).functor.obj ((isOpenEmbedding_inclLE hTV).functor.obj O) =
      (isOpenEmbedding_inclLE (hTV.trans hVW)).functor.obj O := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

lemma inclusion'_functor_inclLE_functor_obj {V W : Opens X} (h : V ≤ W)
    (O : Opens ((Opens.toTopCat X).obj V)) :
    W.isOpenEmbedding.functor.obj ((isOpenEmbedding_inclLE h).functor.obj O) =
      V.isOpenEmbedding.functor.obj O := by
  ext x
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

lemma le_of_functor_le (V : Opens X) {O₁ O₂ : Opens ((Opens.toTopCat X).obj V)}
    (h : V.isOpenEmbedding.functor.obj O₁ ≤ V.isOpenEmbedding.functor.obj O₂) : O₁ ≤ O₂ := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := h ⟨x, hx, rfl⟩
  obtain rfl : y = x := Subtype.ext hyx
  exact hy

lemma functor_le (V : Opens X) (O : Opens ((Opens.toTopCat X).obj V)) :
    V.isOpenEmbedding.functor.obj O ≤ V := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

lemma mem_of_mem_functor {V : Opens X} {O : Opens ((Opens.toTopCat X).obj V)} {x : X}
    (h : x ∈ V.isOpenEmbedding.functor.obj O) : x ∈ V :=
  functor_le V O h

lemma functor_mono (V : Opens X) {O₁ O₂ : Opens ((Opens.toTopCat X).obj V)} (h : O₁ ≤ O₂) :
    V.isOpenEmbedding.functor.obj O₁ ≤ V.isOpenEmbedding.functor.obj O₂ :=
  (V.isOpenEmbedding.functor.map (homOfLE h)).le

/-- A tactic proving inequalities between the opens appearing in the gluing construction, by
comparing their images in `X`. -/
local macro "opens_le" : tactic => `(tactic| (
  (try apply le_of_functor_le)
  (try simp only [inclusion'_functor_inclLE_functor_obj, Opens.functor_map_eq_inf])
  intro x hx
  (try simp only [Opens.mem_inf] at hx ⊢)
  first
  | aesop (add safe forward mem_of_mem_functor) (add norm simp [SetLike.le_def, Opens.mem_inf])
      (config := { terminal := true })
  | aesop (add safe forward functor_le) (add norm simp SetLike.le_def)
      (config := { terminal := true })))

/-- The restriction map between two opens, with the inequality proved by `opens_le`. -/
local macro "le%" : term => `((homOfLE (by opens_le)).op)

/-- `(G|V)|T ≅ G|T` for a sheaf `G` on `W` and opens `T ≤ V ≤ W`. -/
def restrictLERestrictLEIso {T V W : Opens X} (hTV : T ≤ V) (hVW : V ≤ W)
    (G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C) :
    (restrictLE C hTV).obj ((restrictLE C hVW).obj G) ≅ (restrictLE C (hTV.trans hVW)).obj G :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (precompIso ((isOpenEmbedding_inclLE hTV).functor ⋙ (isOpenEmbedding_inclLE hVW).functor)
      (isOpenEmbedding_inclLE (hTV.trans hVW)).functor (inclLE_functor_comp_obj hTV hVW) G.obj)

@[simp]
lemma restrictLERestrictLEIso_hom_app {T V W : Opens X} (hTV : T ≤ V) (hVW : V ≤ W)
    (G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C)
    (O : (Opens ((Opens.toTopCat X).obj T))ᵒᵖ) :
    (restrictLERestrictLEIso hTV hVW G).hom.hom.app O =
      G.obj.map (eqToHom (inclLE_functor_comp_obj hTV hVW O.unop).symm).op := rfl

@[simp]
lemma restrictLERestrictLEIso_inv_app {T V W : Opens X} (hTV : T ≤ V) (hVW : V ≤ W)
    (G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C)
    (O : (Opens ((Opens.toTopCat X).obj T))ᵒᵖ) :
    (restrictLERestrictLEIso hTV hVW G).inv.hom.app O =
      G.obj.map (eqToHom (inclLE_functor_comp_obj hTV hVW O.unop)).op := rfl

/-- `(F|W)|V ≅ F|V` for a sheaf `F` on `X` and opens `V ≤ W`. -/
def restrictOpenRestrictLEIso {V W : Opens X} (h : V ≤ W)
    (F : Sheaf (Opens.grothendieckTopology X) C) :
    (restrictLE C h).obj ((restrictOpen C W).obj F) ≅ (restrictOpen C V).obj F :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (precompIso ((isOpenEmbedding_inclLE h).functor ⋙ W.isOpenEmbedding.functor)
      V.isOpenEmbedding.functor (inclusion'_functor_inclLE_functor_obj h) F.obj)

@[simp]
lemma restrictOpenRestrictLEIso_hom_app {V W : Opens X} (h : V ≤ W)
    (F : Sheaf (Opens.grothendieckTopology X) C) (O : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ) :
    (restrictOpenRestrictLEIso h F).hom.hom.app O =
      F.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj h O.unop).symm).op := rfl

@[simp]
lemma restrictOpenRestrictLEIso_inv_app {V W : Opens X} (h : V ≤ W)
    (F : Sheaf (Opens.grothendieckTopology X) C) (O : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ) :
    (restrictOpenRestrictLEIso h F).inv.hom.app O =
      F.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj h O.unop)).op := rfl

/-- Restriction to `T ≤ V` of an isomorphism `G|V ≅ G'|V`, where `G`, `G'` are sheaves on
opens `W`, `W'` containing `V`; the result is an isomorphism `G|T ≅ G'|T`. -/
def restrictIso {T V W W' : Opens X} (hT : T ≤ V) {hW : V ≤ W} {hW' : V ≤ W'}
    {G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C}
    {G' : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W')) C}
    (α : (restrictLE C hW).obj G ≅ (restrictLE C hW').obj G') :
    (restrictLE C (hT.trans hW)).obj G ≅ (restrictLE C (hT.trans hW')).obj G' :=
  (restrictLERestrictLEIso hT hW G).symm ≪≫ (restrictLE C hT).mapIso α ≪≫
    restrictLERestrictLEIso hT hW' G'

variable (C X) in
/-- Gluing data for sheaves (Hartshorne II, Exercise 1.22): an open cover `U` of `X`, a sheaf
`F i` on each `U i`, and isomorphisms `φ i j` on the double intersections satisfying the identity
and cocycle conditions. -/
structure GluingData where
  /-- The index type of the cover. -/
  ι : Type w
  /-- The open cover. -/
  U : ι → Opens X
  /-- The `U i` cover `X`. -/
  iSup_eq_top : iSup U = ⊤
  /-- A sheaf on each open of the cover. -/
  F : ∀ i, Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i))) C
  /-- The gluing isomorphisms `F i |(U i ⊓ U j) ≅ F j |(U i ⊓ U j)`. -/
  φ : ∀ i j, (restrictLE C (inf_le_left : U i ⊓ U j ≤ U i)).obj (F i) ≅
    (restrictLE C (inf_le_right : U i ⊓ U j ≤ U j)).obj (F j)
  /-- The identity condition `φ i i = id`. -/
  φ_self : ∀ i, (φ i i).hom = 𝟙 _
  /-- The cocycle condition `φ i k = φ j k ∘ φ i j` on `U i ⊓ U j ⊓ U k`. -/
  cocycle : ∀ i j k,
    restrictIso (T := U i ⊓ U j ⊓ U k) inf_le_left (φ i j) ≪≫
      restrictIso (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (φ j k) =
    restrictIso (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (φ i k)

@[simp]
lemma restrictLE_obj_obj_obj {V W : Opens X} (h : V ≤ W)
    (G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C)
    (O : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ) :
    ((restrictLE C h).obj G).obj.obj O =
      G.obj.obj (op ((isOpenEmbedding_inclLE h).isOpenMap.functor.obj O.unop)) := rfl

@[simp]
lemma restrictLE_obj_obj_map {V W : Opens X} (h : V ≤ W)
    (G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C)
    {O O' : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ} (f : O ⟶ O') :
    ((restrictLE C h).obj G).obj.map f =
      G.obj.map ((isOpenEmbedding_inclLE h).isOpenMap.functor.map f.unop).op := rfl

@[simp]
lemma restrictLE_map_hom_app {V W : Opens X} (h : V ≤ W)
    {G G' : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C} (α : G ⟶ G')
    (O : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ) :
    ((restrictLE C h).map α).hom.app O =
      α.hom.app (op ((isOpenEmbedding_inclLE h).isOpenMap.functor.obj O.unop)) := rfl

@[simp]
lemma restrictOpen_obj_obj_obj (V : Opens X) (G : Sheaf (Opens.grothendieckTopology X) C)
    (O : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ) :
    ((restrictOpen C V).obj G).obj.obj O =
      G.obj.obj (op (V.isOpenEmbedding.isOpenMap.functor.obj O.unop)) := rfl

@[simp]
lemma restrictOpen_obj_obj_map (V : Opens X) (G : Sheaf (Opens.grothendieckTopology X) C)
    {O O' : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ} (f : O ⟶ O') :
    ((restrictOpen C V).obj G).obj.map f =
      G.obj.map (V.isOpenEmbedding.isOpenMap.functor.map f.unop).op := rfl

@[simp]
lemma restrictOpen_map_hom_app (V : Opens X) {G G' : Sheaf (Opens.grothendieckTopology X) C}
    (α : G ⟶ G')
    (O : (Opens ((Opens.toTopCat X).obj V))ᵒᵖ) :
    ((restrictOpen C V).map α).hom.app O =
      α.hom.app (op (V.isOpenEmbedding.isOpenMap.functor.obj O.unop)) := rfl

lemma map_eq_map {A : TopCat.{u}} (G : A.Presheaf C) {a b : (Opens A)ᵒᵖ} (f g : a ⟶ b) :
    G.map f = G.map g := by
  congr 1
  exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)

lemma inclLE_functor_map_le {V W : Opens X} (h : V ≤ W) (O : Opens X) :
    (isOpenEmbedding_inclLE h).isOpenMap.functor.obj ((Opens.map V.inclusion').obj O) ≤
      (Opens.map W.inclusion').obj O := by
  rintro _ ⟨z, hz, rfl⟩
  exact hz

/-- The comparison `(ι_W)_* G ⟶ (ι_V)_* (G|V)` for a sheaf `G` on `W` and `V ≤ W`. -/
@[simps]
def pushRestrict {V W : Opens X} (h : V ≤ W)
    (G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C) :
    (TopCat.Presheaf.pushforward C W.inclusion').obj G.obj ⟶
      (TopCat.Presheaf.pushforward C V.inclusion').obj ((restrictLE C h).obj G).obj where
  app O := G.obj.map (homOfLE (inclLE_functor_map_le h O.unop)).op
  naturality := by
    intros
    dsimp only [TopCat.Presheaf.pushforward_obj_obj, TopCat.Presheaf.pushforward_obj_map,
      restrictLE_obj_obj_map, restrictLE_obj_obj_obj]
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply map_eq_map

lemma map_comp_map {A : TopCat.{u}} (G : A.Presheaf C) {a b c : (Opens A)ᵒᵖ} (f : a ⟶ b)
    (g : b ⟶ c) (h : a ⟶ c) : G.map f ≫ G.map g = G.map h := by
  rw [← Functor.map_comp]
  exact map_eq_map _ _ _

lemma map_comp_map_assoc {A : TopCat.{u}} (G : A.Presheaf C) {a b c : (Opens A)ᵒᵖ} (f : a ⟶ b)
    (g : b ⟶ c) (h : a ⟶ c) {Z : C} (k : G.obj c ⟶ Z) : G.map f ≫ G.map g ≫ k = G.map h ≫ k := by
  rw [← Category.assoc, map_comp_map]

lemma map_eq_id {A : TopCat.{u}} (G : A.Presheaf C) {a : (Opens A)ᵒᵖ} (f : a ⟶ a) :
    G.map f = 𝟙 _ := by
  rw [map_eq_map G f (𝟙 a), G.map_id]

section components

variable {V W W' : Opens X} {hW : V ≤ W} {hW' : V ≤ W'}
  {G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W)) C}
  {G' : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj W')) C}

/-- The component of a morphism between restrictions `G|V ⟶ G'|V`, with its type written in terms
of the sections of `G` and `G'`. -/
def appLE (α : (restrictLE C hW).obj G ⟶ (restrictLE C hW').obj G')
    (O : Opens ((Opens.toTopCat X).obj V)) :
    G.obj.obj (op ((isOpenEmbedding_inclLE hW).functor.obj O)) ⟶
      G'.obj.obj (op ((isOpenEmbedding_inclLE hW').functor.obj O)) :=
  α.hom.app (op O)

lemma appLE_naturality (α : (restrictLE C hW).obj G ⟶ (restrictLE C hW').obj G')
    {O₁ O₂ : Opens ((Opens.toTopCat X).obj V)} (h : O₂ ≤ O₁) :
    G.obj.map ((isOpenEmbedding_inclLE hW).functor.map (homOfLE h)).op ≫ appLE α O₂ =
      appLE α O₁ ≫ G'.obj.map ((isOpenEmbedding_inclLE hW').functor.map (homOfLE h)).op :=
  α.hom.naturality (homOfLE h).op

/-- Moving a component of a morphism of restrictions to a smaller open. -/
@[reassoc]
lemma map_appLE_map (α : (restrictLE C hW).obj G ⟶ (restrictLE C hW').obj G')
    {O₁ O₂ : Opens ((Opens.toTopCat X).obj V)} (h : O₂ ≤ O₁) {A B}
    (a : A ⟶ op ((isOpenEmbedding_inclLE hW).functor.obj O₁))
    (a' : A ⟶ op ((isOpenEmbedding_inclLE hW).functor.obj O₂))
    (b : op ((isOpenEmbedding_inclLE hW').functor.obj O₁) ⟶ B)
    (b' : op ((isOpenEmbedding_inclLE hW').functor.obj O₂) ⟶ B) :
    G.obj.map a ≫ appLE α O₁ ≫ G'.obj.map b = G.obj.map a' ≫ appLE α O₂ ≫ G'.obj.map b' := by
  rw [show a' = a ≫ ((isOpenEmbedding_inclLE hW).functor.map (homOfLE h)).op from
      Subsingleton.elim _ _,
    show b = ((isOpenEmbedding_inclLE hW').functor.map (homOfLE h)).op ≫ b' from
      Subsingleton.elim _ _, Functor.map_comp, Functor.map_comp, Category.assoc,
    reassoc_of% appLE_naturality α h]

@[reassoc]
lemma appLE_comp (α : (restrictLE C hW).obj G ⟶ (restrictLE C hW').obj G')
    (β : (restrictLE C hW').obj G' ⟶ (restrictLE C hW).obj G)
    (O : Opens ((Opens.toTopCat X).obj V)) :
    appLE α O ≫ appLE β O = appLE (α ≫ β) O := rfl

lemma appLE_id (O : Opens ((Opens.toTopCat X).obj V)) :
    appLE (𝟙 ((restrictLE C hW).obj G)) O = 𝟙 _ := rfl

end components

section componentsOpen

variable {V : Opens X} {F : Sheaf (Opens.grothendieckTopology X) C}
  {G : Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V)) C}

/-- The component of a morphism `F|V ⟶ G`, with its type written in terms of the sections of
`F`. -/
def appOpen (α : (restrictOpen C V).obj F ⟶ G) (O : Opens ((Opens.toTopCat X).obj V)) :
    F.obj.obj (op (V.isOpenEmbedding.functor.obj O)) ⟶ G.obj.obj (op O) :=
  α.hom.app (op O)

/-- The component of a morphism `G ⟶ F|V`, with its type written in terms of the sections of
`F`. -/
def appOpen' (α : G ⟶ (restrictOpen C V).obj F) (O : Opens ((Opens.toTopCat X).obj V)) :
    G.obj.obj (op O) ⟶ F.obj.obj (op (V.isOpenEmbedding.functor.obj O)) :=
  α.hom.app (op O)

@[reassoc]
lemma map_appOpen_map (α : (restrictOpen C V).obj F ⟶ G)
    {O₁ O₂ : Opens ((Opens.toTopCat X).obj V)} (h : O₂ ≤ O₁) {A B}
    (a : A ⟶ op (V.isOpenEmbedding.functor.obj O₁)) (a' : A ⟶ op (V.isOpenEmbedding.functor.obj O₂))
    (b : op O₁ ⟶ B) (b' : op O₂ ⟶ B) :
    F.obj.map a ≫ appOpen α O₁ ≫ G.obj.map b = F.obj.map a' ≫ appOpen α O₂ ≫ G.obj.map b' := by
  rw [show a' = a ≫ (V.isOpenEmbedding.functor.map (homOfLE h)).op from Subsingleton.elim _ _,
    show b = (homOfLE h).op ≫ b' from Subsingleton.elim _ _, Functor.map_comp, Functor.map_comp,
    Category.assoc]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact (α.hom.naturality (homOfLE h).op).symm

@[reassoc]
lemma map_appOpen'_map (α : G ⟶ (restrictOpen C V).obj F)
    {O₁ O₂ : Opens ((Opens.toTopCat X).obj V)} (h : O₂ ≤ O₁) {A B}
    (a : A ⟶ op O₁) (a' : A ⟶ op O₂)
    (b : op (V.isOpenEmbedding.functor.obj O₁) ⟶ B)
    (b' : op (V.isOpenEmbedding.functor.obj O₂) ⟶ B) :
    G.obj.map a ≫ appOpen' α O₁ ≫ F.obj.map b = G.obj.map a' ≫ appOpen' α O₂ ≫ F.obj.map b' := by
  rw [show a' = a ≫ (homOfLE h).op from Subsingleton.elim _ _,
    show b = (V.isOpenEmbedding.functor.map (homOfLE h)).op ≫ b' from Subsingleton.elim _ _,
    Functor.map_comp, Functor.map_comp, Category.assoc]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact (α.hom.naturality (homOfLE h).op).symm

lemma map_appOpen_res (α : (restrictOpen C V).obj F ⟶ G)
    {O₁ O₂ : Opens ((Opens.toTopCat X).obj V)} {A}
    (a : A ⟶ op (V.isOpenEmbedding.functor.obj O₁)) (a' : A ⟶ op (V.isOpenEmbedding.functor.obj O₂))
    (b : op O₁ ⟶ op O₂) :
    F.obj.map a ≫ appOpen α O₁ ≫ G.obj.map b = F.obj.map a' ≫ appOpen α O₂ := by
  have h := map_appOpen_map α (leOfHom b.unop) a a' b (𝟙 _)
  rwa [CategoryTheory.Functor.map_id, Category.comp_id] at h

lemma appOpen_hom_inv (α : (restrictOpen C V).obj F ≅ G) (O : Opens ((Opens.toTopCat X).obj V)) :
    appOpen α.hom O ≫ appOpen' α.inv O = 𝟙 _ := by
  change (α.hom ≫ α.inv).hom.app (op O) = _
  rw [α.hom_inv_id]
  rfl

lemma appOpen_inv_hom (α : (restrictOpen C V).obj F ≅ G) (O : Opens ((Opens.toTopCat X).obj V)) :
    appOpen' α.inv O ≫ appOpen α.hom O = 𝟙 _ := by
  change (α.inv ≫ α.hom).hom.app (op O) = _
  rw [α.inv_hom_id]
  rfl

end componentsOpen

lemma pairwise_hom_ext {ι : Type w} {K : (Pairwise ι)ᵒᵖ ⥤ C} {c : Cone K} (hc : IsLimit c) {Z : C}
    {f g : Z ⟶ c.pt} (h : ∀ i, f ≫ c.π.app (op (.single i)) = g ≫ c.π.app (op (.single i))) :
    f = g := by
  apply hc.hom_ext
  rintro ⟨(i | ⟨i, j⟩)⟩
  · exact h i
  · rw [← c.w (Quiver.Hom.op (Pairwise.Hom.left i j)), reassoc_of% h i]

namespace GluingData

variable (D : GluingData.{w} C X)

/-- Objects of the gluing diagram. -/
def diagramObj : Pairwise D.ι → X.Presheaf C
  | .single i => (TopCat.Presheaf.pushforward C (D.U i).inclusion').obj (D.F i).obj
  | .pair i j => (TopCat.Presheaf.pushforward C (D.U i ⊓ D.U j).inclusion').obj
      ((restrictLE C inf_le_right).obj (D.F j)).obj

/-- Morphisms of the gluing diagram. -/
def diagramMap : ∀ {a b : Pairwise D.ι}, (a ⟶ b) → (D.diagramObj b ⟶ D.diagramObj a)
  | _, _, .id_single _ => 𝟙 _
  | _, _, .id_pair _ _ => 𝟙 _
  | _, _, .left i j => pushRestrict inf_le_left (D.F i) ≫
      (TopCat.Presheaf.pushforward C _).map (D.φ i j).hom.hom
  | _, _, .right i j => pushRestrict inf_le_right (D.F j)

/-- The gluing diagram, as a functor to the opposite category. -/
def diagramOp : Pairwise D.ι ⥤ (X.Presheaf C)ᵒᵖ where
  obj o := op (D.diagramObj o)
  map f := (D.diagramMap f).op
  map_id o := by cases o <;> rfl
  map_comp f g := by
    cases f <;> cases g <;> simp [diagramMap] <;> rfl

/-- The gluing diagram: `single i ↦ (ι_i)_* F_i`, `pair i j ↦ (ι_ij)_* (F_j|U_ij)`. -/
def diagram : (Pairwise D.ι)ᵒᵖ ⥤ X.Presheaf C := D.diagramOp.leftOp

/-- The gluing diagram as a diagram of sheaves. -/
def sheafDiagram : (Pairwise D.ι)ᵒᵖ ⥤ Sheaf (Opens.grothendieckTopology X) C :=
  ObjectProperty.lift _ D.diagram (by
    rintro ⟨(i | ⟨i, j⟩)⟩
    · exact TopCat.Sheaf.pushforward_sheaf_of_sheaf _ (D.F i).property
    · exact TopCat.Sheaf.pushforward_sheaf_of_sheaf _
        ((restrictLE C inf_le_right).obj (D.F j)).property)

/-- A family of isomorphisms `ψ i : F|U_i ≅ F_i` is compatible with the gluing isomorphisms
when `ψ j = φ i j ∘ ψ i` on `U_i ∩ U_j`. -/
def Compatible (F : Sheaf (Opens.grothendieckTopology X) C)
    (ψ : ∀ i, (restrictOpen C (D.U i)).obj F ≅ D.F i) : Prop :=
  ∀ i j, (restrictOpenRestrictLEIso inf_le_left F).symm ≪≫
      (restrictLE C inf_le_left).mapIso (ψ i) ≪≫ D.φ i j =
    (restrictOpenRestrictLEIso inf_le_right F).symm ≪≫ (restrictLE C inf_le_right).mapIso (ψ j)

section compat

variable {D} {F : Sheaf (Opens.grothendieckTopology X) C}
  {ψ : ∀ i, (restrictOpen C (D.U i)).obj F ≅ D.F i} (hψ : D.Compatible F ψ) (i j : D.ι)
include hψ

@[reassoc]
lemma Compatible.app (P : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j))) :
    F.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_left P)).op ≫
      appOpen (ψ i).hom _ ≫ appLE (D.φ i j).hom P =
    F.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_right P)).op ≫
      appOpen (ψ j).hom _ := by
  have h0 := congr_arg (fun e => e.hom.hom.app (op P)) (hψ i j)
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    restrictOpenRestrictLEIso_inv_app, restrictLE_map_hom_app] at h0
  exact h0

/-- The compatibility `ψ j = φ i j ∘ ψ i` on sections over arbitrary opens, with arbitrary
restriction maps. -/
lemma Compatible.gen (P : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j)))
    (Q₁ : Opens ((Opens.toTopCat X).obj (D.U i))) (Q₂ : Opens ((Opens.toTopCat X).obj (D.U j)))
    {A : (Opens X)ᵒᵖ} {B : (Opens ((Opens.toTopCat X).obj (D.U j)))ᵒᵖ}
    (a : A ⟶ op ((D.U i).isOpenEmbedding.functor.obj Q₁))
    (m : op Q₁ ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj P))
    (b : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj P) ⟶ B)
    (a' : A ⟶ op ((D.U j).isOpenEmbedding.functor.obj Q₂)) (b' : op Q₂ ⟶ B) :
    F.obj.map a ≫ appOpen (ψ i).hom Q₁ ≫ (D.F i).obj.map m ≫ appLE (D.φ i j).hom P ≫
      (D.F j).obj.map b =
    F.obj.map a' ≫ appOpen (ψ j).hom Q₂ ≫ (D.F j).obj.map b' := by
  have ha := leOfHom a.unop
  have ha' := leOfHom a'.unop
  have hm := functor_mono _ (leOfHom m.unop)
  have hb := functor_mono _ (leOfHom b.unop)
  have hb' := functor_mono _ (leOfHom b'.unop)
  simp only [inclusion'_functor_inclLE_functor_obj] at hm hb hb'
  have hR := functor_le (D.U j) B.unop
  have hR' : (D.U j).isOpenEmbedding.functor.obj B.unop ≤ D.U i ⊓ D.U j :=
    hb.trans (functor_le _ _)
  obtain ⟨R, hRB⟩ : ∃ R, (D.U j).isOpenEmbedding.functor.obj B.unop = R := ⟨_, rfl⟩
  rw [hRB] at hb hb' hR hR'
  rw [map_appLE_map (D.φ i j).hom (O₂ := (Opens.map (D.U i ⊓ D.U j).inclusion').obj R)
    (by opens_le) m le% b le%]
  calc _ = F.obj.map le% ≫ appOpen (ψ i).hom ((isOpenEmbedding_inclLE
          (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj
            ((Opens.map (D.U i ⊓ D.U j).inclusion').obj R)) ≫ (D.F i).obj.map (𝟙 _) ≫
          appLE (D.φ i j).hom ((Opens.map (D.U i ⊓ D.U j).inclusion').obj R) ≫
          (D.F j).obj.map le% :=
        map_appOpen_map_assoc _ (by opens_le) _ _ _ _ _
    _ = F.obj.map le% ≫ F.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_left
          ((Opens.map (D.U i ⊓ D.U j).inclusion').obj R))).op ≫ appOpen (ψ i).hom _ ≫
          appLE (D.φ i j).hom ((Opens.map (D.U i ⊓ D.U j).inclusion').obj R) ≫
          (D.F j).obj.map le% := by
        rw [CategoryTheory.Functor.map_id, Category.id_comp, map_comp_map_assoc]
    _ = F.obj.map le% ≫ F.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_right
          ((Opens.map (D.U i ⊓ D.U j).inclusion').obj R))).op ≫ appOpen (ψ j).hom _ ≫
          (D.F j).obj.map le% := by
        rw [hψ.app_assoc]
    _ = _ := (map_comp_map_assoc _ _ _ le% _).trans
          (map_appOpen_map _ (by opens_le) _ _ _ _).symm

lemma Compatible.gen' (P : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j)))
    (Q₁ : Opens ((Opens.toTopCat X).obj (D.U i))) (Q₂ : Opens ((Opens.toTopCat X).obj (D.U j)))
    {A : (Opens X)ᵒᵖ}
    (a : A ⟶ op ((D.U i).isOpenEmbedding.functor.obj Q₁))
    (m : op Q₁ ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj P))
    (a' : A ⟶ op ((D.U j).isOpenEmbedding.functor.obj Q₂))
    (b' : op Q₂ ⟶
      op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj P)) :
    F.obj.map a ≫ appOpen (ψ i).hom Q₁ ≫ (D.F i).obj.map m ≫ appLE (D.φ i j).hom P =
    F.obj.map a' ≫ appOpen (ψ j).hom Q₂ ≫ (D.F j).obj.map b' := by
  have h := hψ.gen i j P Q₁ Q₂ a m (𝟙 _) a' b'
  rwa [CategoryTheory.Functor.map_id, Category.comp_id] at h

@[reassoc]
lemma Compatible.app_inv (P : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j))) :
    appLE (D.φ i j).inv P ≫ appOpen' (ψ i).inv _ ≫
      F.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_left P).symm).op =
    appOpen' (ψ j).inv _ ≫
      F.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_right P).symm).op := by
  have h0 := congr_arg (fun e => e.inv.hom.app (op P)) (hψ i j)
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    restrictOpenRestrictLEIso_hom_app, restrictLE_map_hom_app] at h0
  exact (Category.assoc _ _ _).symm.trans h0

/-- The inverse form of the compatibility, on sections over arbitrary opens. -/
lemma Compatible.gen_inv (P : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j)))
    (Q₁ : Opens ((Opens.toTopCat X).obj (D.U i))) (Q₂ : Opens ((Opens.toTopCat X).obj (D.U j)))
    {A : (Opens ((Opens.toTopCat X).obj (D.U j)))ᵒᵖ} {B : (Opens X)ᵒᵖ}
    (a : A ⟶ op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj P))
    (m : op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj P) ⟶ op Q₁)
    (b : op ((D.U i).isOpenEmbedding.functor.obj Q₁) ⟶ B)
    (a' : A ⟶ op Q₂) (b' : op ((D.U j).isOpenEmbedding.functor.obj Q₂) ⟶ B) :
    (D.F j).obj.map a ≫ appLE (D.φ i j).inv P ≫ (D.F i).obj.map m ≫ appOpen' (ψ i).inv Q₁ ≫
      F.obj.map b =
    (D.F j).obj.map a' ≫ appOpen' (ψ j).inv Q₂ ≫ F.obj.map b' := by
  have hm := functor_mono _ (leOfHom m.unop)
  have hb := leOfHom b.unop
  have hb' := leOfHom b'.unop
  have ha := functor_mono _ (leOfHom a.unop)
  have ha' := functor_mono _ (leOfHom a'.unop)
  simp only [inclusion'_functor_inclLE_functor_obj] at hm ha
  have hR' : B.unop ≤ D.U i ⊓ D.U j := hb.trans (hm.trans (functor_le _ _))
  have hRP := hb.trans hm
  have hRA := hRP.trans ha
  obtain ⟨R, hRB⟩ : ∃ R, B.unop = R := ⟨_, rfl⟩
  rw [hRB] at hb hb' hR' hRP hRA
  rw [map_appOpen'_map (ψ i).inv (O₂ := (isOpenEmbedding_inclLE
      (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj
        ((Opens.map (D.U i ⊓ D.U j).inclusion').obj R)) (by opens_le) m le% b le%,
    map_appLE_map_assoc (D.φ i j).inv (O₂ := (Opens.map (D.U i ⊓ D.U j).inclusion').obj R)
      (B := op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj
        ((Opens.map (D.U i ⊓ D.U j).inclusion').obj R))) (by opens_le) a le% le% (𝟙 _),
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← map_comp_map F.obj (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_left
      ((Opens.map (D.U i ⊓ D.U j).inclusion').obj R)).symm).op le%, hψ.app_inv_assoc,
    map_comp_map F.obj _ _ le%]
  exact (map_appOpen'_map _ (by opens_le) _ _ _ _).symm

end compat

lemma appLE_φ_self (i : D.ι) (O : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U i))) :
    appLE (D.φ i i).hom O = 𝟙 _ := by
  simp only [appLE, D.φ_self]
  rfl

section cocycle

variable (i j k : D.ι)

lemma le_ij : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i ⊓ D.U j := inf_le_left
lemma le_jk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j ⊓ D.U k :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right
lemma le_ik : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i ⊓ D.U k :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- The cocycle condition on sections over an open `T` of `U i ⊓ U j ⊓ U k`, with arbitrary
restriction maps on the outside and in the middle. -/
lemma cocycle_app (T : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j ⊓ D.U k)))
    {A : (Opens ((Opens.toTopCat X).obj (D.U i)))ᵒᵖ}
    {B : (Opens ((Opens.toTopCat X).obj (D.U k)))ᵒᵖ}
    (x : A ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj
      ((isOpenEmbedding_inclLE (D.le_ij i j k)).functor.obj T)))
    (y : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj
      ((isOpenEmbedding_inclLE (D.le_ij i j k)).functor.obj T)) ⟶
      op ((isOpenEmbedding_inclLE (inf_le_left : D.U j ⊓ D.U k ≤ D.U j)).functor.obj
      ((isOpenEmbedding_inclLE (D.le_jk i j k)).functor.obj T)))
    (z : op ((isOpenEmbedding_inclLE (inf_le_right : D.U j ⊓ D.U k ≤ D.U k)).functor.obj
      ((isOpenEmbedding_inclLE (D.le_jk i j k)).functor.obj T)) ⟶ B)
    (x' : A ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U k ≤ D.U i)).functor.obj
      ((isOpenEmbedding_inclLE (D.le_ik i j k)).functor.obj T)))
    (z' : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U k ≤ D.U k)).functor.obj
      ((isOpenEmbedding_inclLE (D.le_ik i j k)).functor.obj T)) ⟶ B) :
    (D.F i).obj.map x ≫ appLE (D.φ i j).hom _ ≫ (D.F j).obj.map y ≫
      appLE (D.φ j k).hom _ ≫ (D.F k).obj.map z =
    (D.F i).obj.map x' ≫ appLE (D.φ i k).hom _ ≫ (D.F k).obj.map z' := by
  have p1 := inclLE_functor_comp_obj (D.le_ij i j k) inf_le_left T
  have p2 := inclLE_functor_comp_obj (D.le_ij i j k) inf_le_right T
  have p3 := inclLE_functor_comp_obj (D.le_jk i j k) inf_le_left T
  have p4 := inclLE_functor_comp_obj (D.le_jk i j k) inf_le_right T
  have p5 := inclLE_functor_comp_obj (D.le_ik i j k) inf_le_left T
  have p6 := inclLE_functor_comp_obj (D.le_ik i j k) inf_le_right T
  have h0 := congr_arg (fun e => e.hom.hom.app (op T)) (D.cocycle i j k)
  simp only [restrictIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, restrictLERestrictLEIso_hom_app,
    restrictLERestrictLEIso_inv_app, restrictLE_map_hom_app, Category.assoc] at h0
  have h1 : (D.F i).obj.map (eqToHom p1).op ≫ appLE (D.φ i j).hom _ ≫
      (D.F j).obj.map (eqToHom p2.symm).op ≫ (D.F j).obj.map (eqToHom p3).op ≫
      appLE (D.φ j k).hom _ ≫ (D.F k).obj.map (eqToHom p4.symm).op =
      (D.F i).obj.map (eqToHom p5).op ≫ appLE (D.φ i k).hom _ ≫
      (D.F k).obj.map (eqToHom p6.symm).op := h0
  rw [← map_comp_map (D.F i).obj (x ≫ (eqToHom p1.symm).op) (eqToHom p1).op x,
    ← map_comp_map (D.F j).obj (eqToHom p2.symm).op (eqToHom p3).op y,
    ← map_comp_map (D.F k).obj (eqToHom p4.symm).op ((eqToHom p4).op ≫ z) z,
    ← map_comp_map (D.F i).obj (x' ≫ (eqToHom p5.symm).op) (eqToHom p5).op x',
    ← map_comp_map (D.F k).obj (eqToHom p6.symm).op ((eqToHom p6).op ≫ z') z']
  simp only [Category.assoc]
  rw [reassoc_of% h1, map_eq_map (D.F i).obj (x ≫ (eqToHom p1.symm).op) (x' ≫ (eqToHom p5.symm).op),
    map_eq_map (D.F k).obj ((eqToHom p4).op ≫ z) ((eqToHom p6).op ≫ z')]

/-- The cocycle condition on sections over arbitrary opens of the double intersections, with
arbitrary restriction maps. -/
lemma cocycle_gen (P₁ : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j)))
    (P₂ : Opens ((Opens.toTopCat X).obj (D.U j ⊓ D.U k)))
    (P₃ : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U k)))
    {A : (Opens ((Opens.toTopCat X).obj (D.U i)))ᵒᵖ}
    {B : (Opens ((Opens.toTopCat X).obj (D.U k)))ᵒᵖ}
    (x : A ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj P₁))
    (y : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj P₁) ⟶
      op ((isOpenEmbedding_inclLE (inf_le_left : D.U j ⊓ D.U k ≤ D.U j)).functor.obj P₂))
    (z : op ((isOpenEmbedding_inclLE (inf_le_right : D.U j ⊓ D.U k ≤ D.U k)).functor.obj P₂) ⟶ B)
    (x' : A ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U k ≤ D.U i)).functor.obj P₃))
    (z' : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U k ≤ D.U k)).functor.obj P₃) ⟶ B) :
    (D.F i).obj.map x ≫ appLE (D.φ i j).hom P₁ ≫ (D.F j).obj.map y ≫
      appLE (D.φ j k).hom P₂ ≫ (D.F k).obj.map z =
    (D.F i).obj.map x' ≫ appLE (D.φ i k).hom P₃ ≫ (D.F k).obj.map z' := by
  have hx := functor_mono _ (leOfHom x.unop)
  have hy := functor_mono _ (leOfHom y.unop)
  have hz := functor_mono _ (leOfHom z.unop)
  have hz' := functor_mono _ (leOfHom z'.unop)
  simp only [inclusion'_functor_inclLE_functor_obj] at hx hy hz hz'
  have hQk := functor_le (D.U k) B.unop
  have hQ : (D.U k).isOpenEmbedding.functor.obj B.unop ≤ D.U i ⊓ D.U j ⊓ D.U k :=
    le_inf (le_inf ((hz'.trans (functor_le _ _)).trans inf_le_left)
      (hz.trans ((hy.trans (functor_le _ _)).trans inf_le_right))) hQk
  obtain ⟨Q, hQB⟩ : ∃ Q, (D.U k).isOpenEmbedding.functor.obj B.unop = Q := ⟨_, rfl⟩
  rw [hQB] at hz hz' hQ hQk
  calc _ = (D.F i).obj.map le% ≫ appLE (D.φ i j).hom
          ((isOpenEmbedding_inclLE (D.le_ij i j k)).functor.obj
            ((Opens.map (D.U i ⊓ D.U j ⊓ D.U k).inclusion').obj Q)) ≫ (D.F j).obj.map le% ≫
        appLE (D.φ j k).hom ((isOpenEmbedding_inclLE (D.le_jk i j k)).functor.obj
            ((Opens.map (D.U i ⊓ D.U j ⊓ D.U k).inclusion').obj Q)) ≫
          (D.F k).obj.map le% := by
        rw [map_appLE_map (D.φ j k).hom (O₂ := (isOpenEmbedding_inclLE (D.le_jk i j k)).functor.obj
            ((Opens.map (D.U i ⊓ D.U j ⊓ D.U k).inclusion').obj Q)) (by opens_le) y le% z le%]
        exact map_appLE_map_assoc _ (by opens_le) _ _ _ _ _
    _ = (D.F i).obj.map le% ≫ appLE (D.φ i k).hom
          ((isOpenEmbedding_inclLE (D.le_ik i j k)).functor.obj
            ((Opens.map (D.U i ⊓ D.U j ⊓ D.U k).inclusion').obj Q)) ≫ (D.F k).obj.map le% :=
        D.cocycle_app i j k _ _ _ _ _ _
    _ = _ := (map_appLE_map _ (by opens_le) _ _ _ _).symm

lemma cocycle_gen' (P₁ : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j)))
    (P₂ : Opens ((Opens.toTopCat X).obj (D.U j ⊓ D.U k)))
    (P₃ : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U k)))
    {A : (Opens ((Opens.toTopCat X).obj (D.U i)))ᵒᵖ}
    (x : A ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj P₁))
    (y : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj P₁) ⟶
      op ((isOpenEmbedding_inclLE (inf_le_left : D.U j ⊓ D.U k ≤ D.U j)).functor.obj P₂))
    (x' : A ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U k ≤ D.U i)).functor.obj P₃))
    (z' : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U k ≤ D.U k)).functor.obj P₃) ⟶
      op ((isOpenEmbedding_inclLE (inf_le_right : D.U j ⊓ D.U k ≤ D.U k)).functor.obj P₂)) :
    (D.F i).obj.map x ≫ appLE (D.φ i j).hom P₁ ≫ (D.F j).obj.map y ≫ appLE (D.φ j k).hom P₂ =
    (D.F i).obj.map x' ≫ appLE (D.φ i k).hom P₃ ≫ (D.F k).obj.map z' := by
  have h := D.cocycle_gen i j k P₁ P₂ P₃ x y (𝟙 _) x' z'
  rwa [CategoryTheory.Functor.map_id, Category.comp_id] at h

end cocycle

lemma φ_self_gen (i : D.ι) {P : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U i))}
    {A B : (Opens ((Opens.toTopCat X).obj (D.U i)))ᵒᵖ}
    (x : A ⟶ op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U i ≤ D.U i)).functor.obj P))
    (z : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U i ≤ D.U i)).functor.obj P) ⟶ B)
    (w : A ⟶ B) :
    (D.F i).obj.map x ≫ appLE (D.φ i i).hom P ≫ (D.F i).obj.map z = (D.F i).obj.map w := by
  rw [appLE_φ_self, Category.id_comp, map_comp_map]

variable [HasLimitsOfShape (Pairwise D.ι)ᵒᵖ C]

/-- The glued sheaf. -/
def glue : Sheaf (Opens.grothendieckTopology X) C :=
  ⟨limit D.diagram,
    Sheaf.isSheaf_of_isLimit D.sheafDiagram (limit.cone D.diagram) (limit.isLimit _)⟩

section limit

/-- The projection from the sections of the glued sheaf to those of `F i`. -/
def πs (i : D.ι) (O : Opens X) :
    D.glue.obj.obj (op O) ⟶ (D.F i).obj.obj (op ((Opens.map (D.U i).inclusion').obj O)) :=
  (limit.π D.diagram (op (.single i))).app (op O)

/-- The projection from the sections of the glued sheaf to those of `F j | U i ⊓ U j`. -/
def πp (i j : D.ι) (O : Opens X) :
    D.glue.obj.obj (op O) ⟶ (D.F j).obj.obj (op ((isOpenEmbedding_inclLE
      (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj
        ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O))) :=
  (limit.π D.diagram (op (.pair i j))).app (op O)

lemma πs_naturality (i : D.ι) {O₁ O₂ : Opens X} (f : op O₁ ⟶ op O₂) :
    D.glue.obj.map f ≫ D.πs i O₂ =
      D.πs i O₁ ≫ (D.F i).obj.map ((Opens.map (D.U i).inclusion').map f.unop).op :=
  (limit.π D.diagram (op (.single i))).naturality f

@[reassoc]
lemma map_πs_map (i : D.ι) {O₁ O₂ : Opens X} (f : op O₁ ⟶ op O₂) {B}
    (b : op ((Opens.map (D.U i).inclusion').obj O₁) ⟶ B)
    (b' : op ((Opens.map (D.U i).inclusion').obj O₂) ⟶ B) :
    D.glue.obj.map f ≫ D.πs i O₂ ≫ (D.F i).obj.map b' = D.πs i O₁ ≫ (D.F i).obj.map b := by
  rw [reassoc_of% D.πs_naturality i f, map_comp_map]

@[reassoc]
lemma πs_right (i j : D.ι) (O : Opens X) :
    D.πs j O ≫ (D.F j).obj.map (homOfLE (inclLE_functor_map_le inf_le_right O)).op = D.πp i j O :=
  congr_app (limit.w D.diagram (Quiver.Hom.op (Pairwise.Hom.right i j))) (op O)

@[reassoc]
lemma πs_left (i j : D.ι) (O : Opens X) :
    D.πs i O ≫ (D.F i).obj.map (homOfLE (inclLE_functor_map_le inf_le_left O)).op ≫
      appLE (D.φ i j).hom ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O) = D.πp i j O :=
  congr_app (limit.w D.diagram (Quiver.Hom.op (Pairwise.Hom.left i j))) (op O)

lemma glue_hom_ext {O : Opens X} {Z : C} {f g : Z ⟶ D.glue.obj.obj (op O)}
    (h : ∀ i, f ≫ D.πs i O = g ≫ D.πs i O) : f = g := by
  apply limit_obj_ext
  rintro ⟨(i | ⟨i, j⟩)⟩
  · exact h i
  · change f ≫ D.πp i j O = g ≫ D.πp i j O
    rw [← D.πs_right i j O, reassoc_of% h j]

/-- The cone used to construct maps into the sections of the glued sheaf. -/
def liftCone {O : Opens X} {Z : C}
    (t : ∀ i, Z ⟶ (D.F i).obj.obj (op ((Opens.map (D.U i).inclusion').obj O)))
    (ht : ∀ i j, t i ≫ (D.F i).obj.map (homOfLE (inclLE_functor_map_le inf_le_left O)).op ≫
      appLE (D.φ i j).hom ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O) =
      t j ≫ (D.F j).obj.map (homOfLE (inclLE_functor_map_le inf_le_right O)).op) :
    Cone (D.diagram ⋙ (evaluation _ C).obj (op O)) where
  pt := Z
  π :=
    { app := fun o => match o with
        | ⟨.single i⟩ => t i
        | ⟨.pair _ j⟩ => t j ≫ (D.F j).obj.map (homOfLE (inclLE_functor_map_le inf_le_right O)).op
      naturality := by
        rintro ⟨a⟩ ⟨b⟩ ⟨f⟩
        cases f with
        | id_single i =>
          change 𝟙 Z ≫ t i = t i ≫ 𝟙 _
          simp
        | id_pair i j =>
          change 𝟙 Z ≫ _ = _ ≫ 𝟙 _
          simp
        | left i j =>
          change 𝟙 Z ≫ (t j ≫ _) = t i ≫ ((D.F i).obj.map _ ≫ appLE (D.φ i j).hom _)
          rw [Category.id_comp]
          exact (ht i j).symm
        | right i j =>
          change 𝟙 Z ≫ (t j ≫ _) = t j ≫ _
          rw [Category.id_comp]
          rfl }

/-- Maps into the sections of the glued sheaf from compatible families. -/
def glueLift {O : Opens X} {Z : C}
    (t : ∀ i, Z ⟶ (D.F i).obj.obj (op ((Opens.map (D.U i).inclusion').obj O)))
    (ht : ∀ i j, t i ≫ (D.F i).obj.map (homOfLE (inclLE_functor_map_le inf_le_left O)).op ≫
      appLE (D.φ i j).hom ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O) =
      t j ≫ (D.F j).obj.map (homOfLE (inclLE_functor_map_le inf_le_right O)).op) :
    Z ⟶ D.glue.obj.obj (op O) :=
  limit.lift _ (D.liftCone t ht) ≫ (limitObjIsoLimitCompEvaluation D.diagram (op O)).inv

@[reassoc (attr := simp)]
lemma glueLift_πs {O : Opens X} {Z : C}
    (t : ∀ i, Z ⟶ (D.F i).obj.obj (op ((Opens.map (D.U i).inclusion').obj O)))
    (ht : ∀ i j, t i ≫ (D.F i).obj.map (homOfLE (inclLE_functor_map_le inf_le_left O)).op ≫
      appLE (D.φ i j).hom ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O) =
      t j ≫ (D.F j).obj.map (homOfLE (inclLE_functor_map_le inf_le_right O)).op) (i : D.ι) :
    D.glueLift t ht ≫ D.πs i O = t i := by
  rw [glueLift, πs]
  erw [Category.assoc, limitObjIsoLimitCompEvaluation_inv_π_app, limit.lift_π]
  rfl

/-- The defining relation of the glued sheaf, on sections over arbitrary opens. -/
lemma πs_gen (i j : D.ι) (O : Opens X) (P : Opens ((Opens.toTopCat X).obj (D.U i ⊓ D.U j)))
    {B : (Opens ((Opens.toTopCat X).obj (D.U j)))ᵒᵖ}
    (m : op ((Opens.map (D.U i).inclusion').obj O) ⟶
      op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj P))
    (b : op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj P) ⟶ B)
    (b' : op ((Opens.map (D.U j).inclusion').obj O) ⟶ B) :
    D.πs i O ≫ (D.F i).obj.map m ≫ appLE (D.φ i j).hom P ≫ (D.F j).obj.map b =
      D.πs j O ≫ (D.F j).obj.map b' := by
  have hm := functor_mono _ (leOfHom m.unop)
  have hb := functor_mono _ (leOfHom b.unop)
  simp only [inclusion'_functor_inclLE_functor_obj, Opens.functor_map_eq_inf] at hm hb
  have hBO := hb.trans hm
  rw [← map_appLE_map (D.φ i j).hom (O₁ := (Opens.map (D.U i ⊓ D.U j).inclusion').obj O)
    (by opens_le) (homOfLE (inclLE_functor_map_le inf_le_left O)).op m le% b,
    D.πs_left_assoc, ← D.πs_right_assoc, map_comp_map _ _ _ b']

end limit

section psi

variable (i : D.ι)

/-- The comparison map `F|U_i ⟶ F_i` from the restriction of the glued sheaf. -/
def ψHom : (restrictOpen C (D.U i)).obj D.glue ⟶ D.F i :=
  ObjectProperty.homMk
    { app := fun W => D.πs i ((D.U i).isOpenEmbedding.functor.obj W.unop) ≫ (D.F i).obj.map le%
      naturality := by
        intro W₁ W₂ f
        change D.glue.obj.map ((D.U i).isOpenEmbedding.functor.map f.unop).op ≫ D.πs i _ ≫
          (D.F i).obj.map le% = (D.πs i _ ≫ (D.F i).obj.map le%) ≫ (D.F i).obj.map f
        simp only [Category.assoc, ← Functor.map_comp]
        exact D.map_πs_map i _ _ _ }

lemma ψHom_app (W : Opens ((Opens.toTopCat X).obj (D.U i))) :
    (D.ψHom i).hom.app (op W) =
      D.πs i ((D.U i).isOpenEmbedding.functor.obj W) ≫ (D.F i).obj.map le% := rfl

/-- The inverse of `ψHom` on sections over `W`. -/
def ψInvApp (W : Opens ((Opens.toTopCat X).obj (D.U i))) :
    (D.F i).obj.obj (op W) ⟶ D.glue.obj.obj (op ((D.U i).isOpenEmbedding.functor.obj W)) :=
  D.glueLift (fun k => (D.F i).obj.map le% ≫
    appLE (D.φ i k).hom ((Opens.map (D.U i ⊓ D.U k).inclusion').obj
      ((D.U i).isOpenEmbedding.functor.obj W)) ≫ (D.F k).obj.map le%) (fun k l => by
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp]
    exact D.cocycle_gen' i k l _ _ _ _ _ _ _)

lemma ψHom_ψInvApp (W : Opens ((Opens.toTopCat X).obj (D.U i))) :
    (D.πs i ((D.U i).isOpenEmbedding.functor.obj W) ≫ (D.F i).obj.map le%) ≫ D.ψInvApp i W =
      𝟙 _ := by
  apply D.glue_hom_ext
  intro k
  rw [ψInvApp, Category.assoc, Category.assoc, glueLift_πs, Category.id_comp,
    ← Functor.map_comp_assoc,
    map_eq_map (D.F i).obj _ (homOfLE (inclLE_functor_map_le inf_le_left _)).op,
    D.πs_left_assoc, ← D.πs_right i k, Category.assoc, map_comp_map _ _ _ (𝟙 _),
    CategoryTheory.Functor.map_id, Category.comp_id]

lemma ψInvApp_ψHom (W : Opens ((Opens.toTopCat X).obj (D.U i))) :
    D.ψInvApp i W ≫ D.πs i ((D.U i).isOpenEmbedding.functor.obj W) ≫ (D.F i).obj.map le% =
      𝟙 _ := by
  rw [ψInvApp, D.glueLift_πs_assoc, Category.assoc, Category.assoc,
    map_comp_map (D.F i).obj _ _ le%, D.φ_self_gen i _ _ (𝟙 _), CategoryTheory.Functor.map_id]

instance isIso_ψHom : IsIso (D.ψHom i) := by
  have : ∀ W, IsIso ((D.ψHom i).hom.app W) := fun W =>
    ⟨D.ψInvApp i W.unop, D.ψHom_ψInvApp i W.unop, D.ψInvApp_ψHom i W.unop⟩
  have : IsIso ((sheafToPresheaf _ _).map (D.ψHom i)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (D.ψHom i).hom this
  exact isIso_of_reflects_iso (D.ψHom i) (sheafToPresheaf _ _)

/-- The isomorphism `F|U_i ≅ F_i`. -/
def ψ : (restrictOpen C (D.U i)).obj D.glue ≅ D.F i := asIso (D.ψHom i)

lemma glue_compatible : D.Compatible D.glue D.ψ := by
  intro i j
  apply Iso.ext
  apply Sheaf.hom_ext
  ext ⟨W⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    restrictOpenRestrictLEIso_inv_app, restrictLE_map_hom_app, ψ, asIso_hom]
  change D.glue.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_left W)).op ≫
      (D.ψHom i).hom.app (op _) ≫ appLE (D.φ i j).hom W =
    D.glue.obj.map (eqToHom (inclusion'_functor_inclLE_functor_obj inf_le_right W)).op ≫
      (D.ψHom j).hom.app (op _)
  rw [ψHom_app, ψHom_app, Category.assoc,
    D.map_πs_map_assoc i _ (le% : op ((Opens.map (D.U i).inclusion').obj
      ((D.U i ⊓ D.U j).isOpenEmbedding.functor.obj W)) ⟶
        op ((isOpenEmbedding_inclLE (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj W)),
    D.map_πs_map j _ (le% : op ((Opens.map (D.U j).inclusion').obj
      ((D.U i ⊓ D.U j).isOpenEmbedding.functor.obj W)) ⟶
        op ((isOpenEmbedding_inclLE (inf_le_right : D.U i ⊓ D.U j ≤ D.U j)).functor.obj W))]
  have h := D.πs_gen i j ((D.U i ⊓ D.U j).isOpenEmbedding.functor.obj W) W le% (𝟙 _) le%
  rwa [CategoryTheory.Functor.map_id, Category.comp_id] at h

end psi

section uniqueness

variable {G : Sheaf (Opens.grothendieckTopology X) C}
  {ψ' : ∀ i, (restrictOpen C (D.U i)).obj G ≅ D.F i} (hψ' : D.Compatible G ψ')

variable (ψ') in
/-- The components of the comparison map from `G` to the glued sheaf. -/
def legs (O : Opens X) (i : D.ι) :
    G.obj.obj (op O) ⟶ (D.F i).obj.obj (op ((Opens.map (D.U i).inclusion').obj O)) :=
  G.obj.map le% ≫ appOpen (ψ' i).hom ((Opens.map (D.U i).inclusion').obj O)

include hψ'

omit [HasLimitsOfShape (Pairwise D.ι)ᵒᵖ C] in
lemma legs_compat (O : Opens X) (i j : D.ι) :
    D.legs ψ' O i ≫ (D.F i).obj.map (homOfLE (inclLE_functor_map_le inf_le_left O)).op ≫
      appLE (D.φ i j).hom ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O) =
    D.legs ψ' O j ≫ (D.F j).obj.map (homOfLE (inclLE_functor_map_le inf_le_right O)).op := by
  simp only [legs, Category.assoc]
  exact hψ'.gen' i j _ _ _ _ _ _ _

/-- The comparison map from `G` to the glued sheaf on sections over `O`. -/
def θApp (O : Opens X) : G.obj.obj (op O) ⟶ D.glue.obj.obj (op O) :=
  D.glueLift (D.legs ψ' O) (D.legs_compat hψ' O)

@[reassoc (attr := simp)]
lemma θApp_πs (O : Opens X) (i : D.ι) : D.θApp hψ' O ≫ D.πs i O = D.legs ψ' O i :=
  D.glueLift_πs _ _ i

/-- The comparison map from `G` to the glued sheaf. -/
def θHom : G ⟶ D.glue :=
  ObjectProperty.homMk
    { app := fun O => D.θApp hψ' O.unop
      naturality := by
        intro O₁ O₂ f
        have hf := leOfHom f.unop
        apply D.glue_hom_ext
        intro i
        rw [Category.assoc, θApp_πs, Category.assoc, D.πs_naturality i f, θApp_πs_assoc, legs,
          legs, Category.assoc]
        exact (map_comp_map_assoc _ _ _ le% _).trans (map_appOpen_res _ _ _ _).symm }

omit hψ' [HasLimitsOfShape (Pairwise D.ι)ᵒᵖ C] in
lemma iSup_functor_map (O : Opens X) :
    iSup (fun i => (D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O)) =
      O := by
  simp only [Opens.functor_map_eq_inf, ← inf_iSup_eq, D.iSup_eq_top, inf_top_eq]

/-- The cone used to construct the inverse of the comparison map. -/
def invCone (O : Opens X) : Cone ((Pairwise.diagram (fun i =>
    (D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O))).op ⋙ G.obj) where
  pt := D.glue.obj.obj (op O)
  π :=
    { app := fun o => match o with
        | ⟨.single i⟩ => D.πs i O ≫ appOpen' (ψ' i).inv ((Opens.map (D.U i).inclusion').obj O)
        | ⟨.pair i _⟩ => (D.πs i O ≫ appOpen' (ψ' i).inv ((Opens.map (D.U i).inclusion').obj O)) ≫
            G.obj.map (homOfLE inf_le_left).op
      naturality := by
        rintro ⟨a⟩ ⟨b⟩ ⟨f⟩
        cases f with
        | id_single i =>
          change 𝟙 _ ≫ _ = _ ≫ G.obj.map (𝟙 _)
          simp
        | id_pair i j =>
          change 𝟙 _ ≫ _ = _ ≫ G.obj.map (𝟙 _)
          simp
        | left i j =>
          exact Category.id_comp _
        | right i j =>
          change 𝟙 _ ≫ ((D.πs i O ≫ appOpen' (ψ' i).inv _) ≫ G.obj.map _) =
            (D.πs j O ≫ appOpen' (ψ' j).inv _) ≫ G.obj.map (homOfLE inf_le_right).op
          rw [Category.id_comp, Category.assoc, Category.assoc]
          calc _ = D.πs i O ≫ (D.F i).obj.map
                (homOfLE (inclLE_functor_map_le (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) O)).op ≫
                appOpen' (ψ' i).inv ((isOpenEmbedding_inclLE
                  (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj
                    ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O)) ≫ G.obj.map le% := by
                have h := map_appOpen'_map (ψ' i).inv (by opens_le) (𝟙 _)
                  (homOfLE (inclLE_functor_map_le (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) O)).op
                  (homOfLE (inf_le_left :
                    (D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O) ⊓
                    (D.U j).isOpenEmbedding.functor.obj ((Opens.map (D.U j).inclusion').obj O) ≤
                      _)).op le%
                rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
                rw [h]
            _ = D.πs i O ≫ (D.F i).obj.map
                (homOfLE (inclLE_functor_map_le (inf_le_left : D.U i ⊓ D.U j ≤ D.U i) O)).op ≫
                appLE (D.φ i j).hom ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O) ≫
                appLE (D.φ i j).inv ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O) ≫
                appOpen' (ψ' i).inv ((isOpenEmbedding_inclLE
                  (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj
                    ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O)) ≫ G.obj.map le% := by
                rw [appLE_comp_assoc, Iso.hom_inv_id, appLE_id, Category.id_comp]
            _ = D.πs j O ≫ (D.F j).obj.map
                (homOfLE (inclLE_functor_map_le (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) O)).op ≫
                appLE (D.φ i j).inv ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O) ≫
                appOpen' (ψ' i).inv ((isOpenEmbedding_inclLE
                  (inf_le_left : D.U i ⊓ D.U j ≤ D.U i)).functor.obj
                    ((Opens.map (D.U i ⊓ D.U j).inclusion').obj O)) ≫ G.obj.map le% := by
                rw [D.πs_left_assoc, ← D.πs_right_assoc]
            _ = _ := by
                have h := hψ'.gen_inv i j _ _ ((Opens.map (D.U j).inclusion').obj O)
                  (homOfLE (inclLE_functor_map_le (inf_le_right : D.U i ⊓ D.U j ≤ D.U j) O)).op
                  (𝟙 _) le% (𝟙 _)
                  (homOfLE (inf_le_right :
                    (D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O) ⊓
                    (D.U j).isOpenEmbedding.functor.obj ((Opens.map (D.U j).inclusion').obj O) ≤
                      _)).op
                rw [CategoryTheory.Functor.map_id, Category.id_comp,
                  CategoryTheory.Functor.map_id, Category.id_comp] at h
                rw [h] }

omit hψ' [HasLimitsOfShape (Pairwise D.ι)ᵒᵖ C] in
/-- The sheaf condition of `G` for the cover of `O` by the `O ∩ U i`, with cone point `G(O)`. -/
def isLimitG (O : Opens X) :
    IsLimit ((G.obj.mapCone (Pairwise.cocone (fun i =>
      (D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O))).op).extend
        (G.obj.mapIso (eqToIso (congrArg op (D.iSup_functor_map O)))).inv) :=
  (TopCat.Presheaf.IsSheaf.isSheafPairwiseIntersections (U := fun i =>
      (D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O))
    G.property).some.ofIsoLimit (Cone.extendIso _ _)

/-- The inverse of the comparison map on sections over `O`. -/
def θInv (O : Opens X) : D.glue.obj.obj (op O) ⟶ G.obj.obj (op O) :=
  (D.isLimitG O).lift (D.invCone hψ' O)

omit hψ' [HasLimitsOfShape (Pairwise D.ι)ᵒᵖ C] in
lemma isLimitG_π (O : Opens X) (i : D.ι) :
    ((G.obj.mapCone (Pairwise.cocone (fun i =>
      (D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O))).op).extend
        (G.obj.mapIso (eqToIso (congrArg op (D.iSup_functor_map O)))).inv).π.app (op (.single i)) =
      G.obj.map (le% : op O ⟶
        op ((D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O))) :=
  map_comp_map _ _ _ _

@[reassoc]
lemma θInv_π (O : Opens X) (i : D.ι) :
    D.θInv hψ' O ≫ G.obj.map (le% : op O ⟶
      op ((D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O))) =
      D.πs i O ≫ appOpen' (ψ' i).inv ((Opens.map (D.U i).inclusion').obj O) := by
  rw [← isLimitG_π]
  exact (D.isLimitG O).fac (D.invCone hψ' O) (op (.single i))

lemma θApp_θInv (O : Opens X) : D.θApp hψ' O ≫ D.θInv hψ' O = 𝟙 _ := by
  apply pairwise_hom_ext (D.isLimitG O)
  intro i
  rw [isLimitG_π]
  change (D.θApp hψ' O ≫ D.θInv hψ' O) ≫ G.obj.map _ = 𝟙 (G.obj.obj (op O)) ≫ G.obj.map _
  rw [Category.assoc, θInv_π, θApp_πs_assoc, legs, Category.assoc, appOpen_hom_inv,
    Category.comp_id, Category.id_comp]

lemma θInv_θApp (O : Opens X) : D.θInv hψ' O ≫ D.θApp hψ' O = 𝟙 _ := by
  apply D.glue_hom_ext
  intro i
  rw [Category.assoc, θApp_πs, legs, Category.id_comp, θInv_π_assoc, appOpen_inv_hom,
    Category.comp_id]

instance isIso_θHom : IsIso (D.θHom hψ') := by
  have : ∀ O, IsIso ((D.θHom hψ').hom.app O) := fun O =>
    ⟨D.θInv hψ' O.unop, D.θApp_θInv hψ' O.unop, D.θInv_θApp hψ' O.unop⟩
  have : IsIso ((sheafToPresheaf _ _).map (D.θHom hψ')) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (D.θHom hψ').hom this
  exact isIso_of_reflects_iso (D.θHom hψ') (sheafToPresheaf _ _)

/-- The comparison isomorphism from `G` to the glued sheaf. -/
def θ : G ≅ D.glue := asIso (D.θHom hψ')

lemma θ_comp (i : D.ι) : (restrictOpen C (D.U i)).mapIso (D.θ hψ') ≪≫ D.ψ i = ψ' i := by
  apply Iso.ext
  apply Sheaf.hom_ext
  ext ⟨W⟩
  change D.θApp hψ' _ ≫ (D.ψHom i).hom.app (op W) = appOpen (ψ' i).hom W
  rw [ψHom_app, θApp_πs_assoc, legs, Category.assoc, map_appOpen_res _ _ (𝟙 _),
    CategoryTheory.Functor.map_id, Category.id_comp]

lemma θ_unique (θ' : G ≅ D.glue)
    (h : ∀ i, (restrictOpen C (D.U i)).mapIso θ' ≪≫ D.ψ i = ψ' i) : θ' = D.θ hψ' := by
  apply Iso.ext
  apply Sheaf.hom_ext
  ext ⟨O⟩
  apply D.glue_hom_ext
  intro i
  change θ'.hom.hom.app (op O) ≫ D.πs i O = D.θApp hψ' O ≫ D.πs i O
  rw [θApp_πs, legs]
  have hi : θ'.hom.hom.app (op _) ≫ (D.ψHom i).hom.app (op ((Opens.map (D.U i).inclusion').obj O)) =
      appOpen (ψ' i).hom _ :=
    congr_arg (fun e => e.hom.hom.app (op ((Opens.map (D.U i).inclusion').obj O))) (h i)
  rw [ψHom_app] at hi
  calc _ = θ'.hom.hom.app (op O) ≫ D.glue.obj.map le% ≫
        D.πs i ((D.U i).isOpenEmbedding.functor.obj ((Opens.map (D.U i).inclusion').obj O)) ≫
        (D.F i).obj.map le% := by
        rw [D.map_πs_map i _ (𝟙 _), CategoryTheory.Functor.map_id, Category.comp_id]
    _ = _ := by
        rw [← θ'.hom.hom.naturality_assoc]
        dsimp only at hi
        rw [hi]

end uniqueness

/-- **Gluing sheaves** (Hartshorne II, Exercise 1.22). Given gluing data, there is a sheaf `F` on
`X` with isomorphisms `ψ i : F|U_i ≅ F_i` such that `ψ j = φ i j ∘ ψ i` on `U_i ∩ U_j`, and it is
unique up to a unique isomorphism compatible with these identifications. -/
theorem exists_unique_gluing :
    ∃ (F : Sheaf (Opens.grothendieckTopology X) C)
      (ψ : ∀ i, (restrictOpen C (D.U i)).obj F ≅ D.F i), D.Compatible F ψ ∧
      ∀ (G : Sheaf (Opens.grothendieckTopology X) C)
        (ψ' : ∀ i, (restrictOpen C (D.U i)).obj G ≅ D.F i), D.Compatible G ψ' →
        ∃! θ : G ≅ F, ∀ i, (restrictOpen C (D.U i)).mapIso θ ≪≫ ψ i = ψ' i :=
  ⟨D.glue, D.ψ, D.glue_compatible, fun _ _ hψ' =>
    ⟨D.θ hψ', D.θ_comp hψ', fun θ' h => D.θ_unique hψ' θ' h⟩⟩

end GluingData

/-- **Gluing sheaves of abelian groups** (Hartshorne II, Exercise 1.22). -/
theorem exists_unique_gluing_addCommGrp {X : TopCat.{u}} (D : GluingData.{u} AddCommGrpCat.{u} X) :
    ∃ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ψ : ∀ i, (restrictOpen AddCommGrpCat.{u} (D.U i)).obj F ≅ D.F i), D.Compatible F ψ ∧
      ∀ (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
        (ψ' : ∀ i, (restrictOpen AddCommGrpCat.{u} (D.U i)).obj G ≅ D.F i), D.Compatible G ψ' →
        ∃! θ : G ≅ F, ∀ i, (restrictOpen AddCommGrpCat.{u} (D.U i)).mapIso θ ≪≫ ψ i = ψ' i :=
  D.exists_unique_gluing

end Hartshorne.SheafGluing
