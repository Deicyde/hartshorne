/-
Copyright (c) 2026 Hartshorne formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Hartshorne.Scheme.CoherentExtensionAffine

/-!
# Extension of coherent subsheaves on a Noetherian scheme

Hartshorne, *Algebraic Geometry*, II, Exercise 5.15(d)–(e) (p. 127).

Let `X` be a Noetherian scheme, `E` a quasi-coherent `𝒪_X`-module, `U ⊆ X` open and `N ⊆ E` a
submodule sheaf whose restriction to `U` is coherent. Then there is a coherent submodule sheaf
`N' ⊆ E` with `N'|_U = N|_U` (`exists_isCoherent_extension_of_isNoetherian`). Consequently every
coherent sheaf on `U` is the restriction of a coherent sheaf on `X`
(`exists_isCoherent_restrict_iso_of_isNoetherian`), applied to the pushforward of the sheaf to
`X`, which is quasi-coherent.

## Proof

Cover `X` by finitely many affine opens `V₁, …, Vₘ` and extend over one of them at a time. Write
`U'` for the open over which `N` is already known to be coherent, in the form `CoherentNear N U'`:
every point of `U'` has an affine neighbourhood `W ⊆ U'` on which `N` has the extension property
of II.5.3 and finitely generated sections. For an affine open `V`:

* `exists_finite_spanOn_eq`: there are finitely many sections `S` of `E` over `V` whose span
  `spanOn V S` agrees with `N` on every open contained in `U' ∩ V` (the affine argument of
  Exercise 5.15(c), run inside `V`);
* `extOn U' N ⊓ extOn V (spanOn V S)` (sections lying in `N` over their intersection with `U'`
  and in the span over their intersection with `V`) agrees with `N` on `U'` and with the span on
  `V`, so it is coherent near every point of `U' ∪ V`.

After the last step `N` is coherent near every point of `X`, which is coherence.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Hartshorne

universe u

open ArtinReesKernelSheaf

variable {X : Scheme.{u}} {E : X.Modules}

/-! ### Constraining sections on an open -/

/-- The submodule sheaf of sections of `E` whose restriction to their intersection with the open
`V` lies in `Q`. -/
def extOn (V : X.Opens) (Q : E.val.Submodule) : E.val.Submodule where
  obj W := Submodule.comap (res E (inf_le_left : W.unop ⊓ V ≤ W.unop)) (sub Q (W.unop ⊓ V))
  map {W W'} f s hs := by
    have h1 := res_mem Q (inf_le_inf_right V (leOfHom f.unop)) hs
    exact (congrArg (fun y => y ∈ sub Q (W'.unop ⊓ V))
      ((res_res E inf_le_left (inf_le_inf_right V (leOfHom f.unop)) s).trans
        (res_res E (leOfHom f.unop) inf_le_left s).symm)).mp h1

lemma mem_extOn {V W : X.Opens} {Q : E.val.Submodule} (s : Γ(E, W)) :
    s ∈ sub (extOn V Q) W ↔ res E (inf_le_left : W ⊓ V ≤ W) s ∈ sub Q (W ⊓ V) :=
  Iff.rfl

lemma isLocal_extOn (V : X.Opens) {Q : E.val.Submodule} (hQ : IsLocal Q) :
    IsLocal (extOn V Q) := by
  intro W s hs
  refine hQ _ _ fun x hx => ?_
  obtain ⟨O, hOW, hxO, hO⟩ := hs x hx.1
  refine ⟨O ⊓ V, inf_le_inf_right V hOW, ⟨hxO, hx.2⟩, ?_⟩
  exact (congrArg (fun y => y ∈ sub Q (O ⊓ V))
    ((res_res E hOW inf_le_left s).trans
      (res_res E inf_le_left (inf_le_inf_right V hOW) s).symm)).mp hO

lemma le_extOn (V : X.Opens) (Q : E.val.Submodule) : Q ≤ extOn V Q := fun _ _ hs =>
  res_mem Q inf_le_left hs

/-- On opens contained in `V`, the sections of `extOn V Q` are those of `Q`. -/
lemma mem_extOn_iff_of_le {V W : X.Opens} {Q : E.val.Submodule} (hQ : IsLocal Q) (hW : W ≤ V)
    (s : Γ(E, W)) : s ∈ sub (extOn V Q) W ↔ s ∈ sub Q W := by
  refine ⟨fun hs => hQ W s fun x hx => ⟨W ⊓ V, inf_le_left, ⟨hx, hW hx⟩, hs⟩,
    fun hs => le_extOn V Q _ hs⟩

/-! ### The span of sections over an open -/

/-- The restrictions to `W` of the elements of `S`, if `W ⊆ V`. -/
def genOn (V : X.Opens) (S : Set Γ(E, V)) (W : X.Opens) : Set Γ(E, W) :=
  {y | ∃ (h : W ≤ V) (t : Γ(E, V)), t ∈ S ∧ res E h t = y}

lemma genOn_of_le {V W : X.Opens} (S : Set Γ(E, V)) (h : W ≤ V) :
    genOn V S W = res E h '' S := by
  ext y
  exact ⟨fun ⟨_, t, ht, e⟩ => ⟨t, ht, e⟩, fun ⟨t, ht, e⟩ => ⟨h, t, ht, e⟩⟩

lemma res_mem_span_genOn {V W W' : X.Opens} (S : Set Γ(E, V)) (h : W' ≤ W) {s : Γ(E, W)}
    (hs : s ∈ Submodule.span Γ(X, W) (genOn V S W)) :
    res E h s ∈ Submodule.span Γ(X, W') (genOn V S W') := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨hWV, t, ht, rfl⟩ := hx
    rw [res_res]
    exact Submodule.subset_span ⟨h.trans hWV, t, ht, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

/-- The family `W ↦ span (S|_W)` on affine opens `W ⊆ V` (and `0` on the others). -/
def spanOnFamily (V : X.Opens) (S : Set Γ(E, V)) : AffineFamily E where
  obj W := Submodule.span Γ(X, W) (genOn V S W)
  res_mem h _ hs := res_mem_span_genOn S h hs

/-- The submodule sheaf of `E` spanned by a set `S` of sections over the open `V`: the sections
lying, near every point, in the span of `S|_W` on an affine open `W ⊆ V`. -/
def spanOn (V : X.Opens) (S : Set Γ(E, V)) : E.val.Submodule :=
  (spanOnFamily V S).closure

lemma isLocal_spanOn (V : X.Opens) (S : Set Γ(E, V)) : IsLocal (spanOn V S) :=
  AffineFamily.isLocal_closure _

lemma span_le_sub_spanOn {V : X.Opens} (S : Set Γ(E, V)) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ V) :
    Submodule.span Γ(X, W) (res E hW '' S) ≤ sub (spanOn V S) W := by
  intro s hs x hx
  refine ⟨W, le_rfl, hx, ?_⟩
  rw [res_refl]
  change s ∈ Submodule.span _ (genOn V S W)
  rwa [genOn_of_le S hW]

lemma span_le_powSmulRes_genOn {V : X.Opens} (S : Set Γ(E, V)) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ V) (g : Γ(X, W)) :
    Submodule.span Γ(X, X.basicOpen g) (genOn V S (X.basicOpen g)) ≤
      powSmulRes W g (Submodule.span Γ(X, W) (res E hW '' S)) := by
  rw [Submodule.span_le]
  rintro _ ⟨h, t, ht, rfl⟩
  refine ⟨0, res E hW t, Submodule.subset_span ⟨t, ht, rfl⟩, ?_⟩
  rw [pow_zero, one_smul, res_res]

/-- The local step: if the restriction of `s` to a basic open `D(g)` of the affine open `W ⊆ V`
lies in the span of `S|_{D(g)}`, then `g ^ n s` lies in the span of `S|_W` for some `n`. -/
theorem exists_pow_smul_mem_span_genOn [E.IsQuasicoherent] {V : X.Opens} (S : Set Γ(E, V))
    (W : X.affineOpens) (hW : (W : X.Opens) ≤ V) (g : Γ(X, W)) {s : Γ(E, W)}
    (hs : res E (X.basicOpen_le g) s ∈
      Submodule.span Γ(X, X.basicOpen g) (genOn V S (X.basicOpen g))) :
    ∃ n : ℕ, g ^ n • s ∈ Submodule.span Γ(X, W) (res E hW '' S) := by
  obtain ⟨n, p, hp, h⟩ := span_le_powSmulRes_genOn S W hW g hs
  have hres : res E (X.basicOpen_le g) (g ^ n • s - p) = 0 := by
    rw [map_sub, LinearMap.map_smulₛₗ, map_pow, h, sub_self]
  obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_isAffineOpen E W.2 g _ hres
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hm
  exact ⟨m + n, hm ▸ Submodule.smul_mem _ _ hp⟩

/-- **Sections of the span on an affine open.** If `E` is quasi-coherent, then over every affine
open `W ⊆ V` the sections of `spanOn V S` are exactly the span of `S|_W`. -/
theorem sub_spanOn_eq [E.IsQuasicoherent] {V : X.Opens} (S : Set Γ(E, V)) (W : X.affineOpens)
    (hW : (W : X.Opens) ≤ V) :
    sub (spanOn V S) W = Submodule.span Γ(X, W) (res E hW '' S) := by
  refine le_antisymm (fun s hs => ?_) (span_le_sub_spanOn S W hW)
  set P := Submodule.span Γ(X, W) (res E hW '' S)
  let T : Set Γ(X, W) := {g | ∃ n : ℕ, g ^ n • s ∈ P}
  have hT : Ideal.span T = ⊤ := by
    rw [← W.2.self_le_iSup_basicOpen_iff]
    intro x hxW
    obtain ⟨W', hW'W, hxW', hW'⟩ := hs x hxW
    obtain ⟨g, hgW', hxg⟩ := W.2.exists_basicOpen_le ⟨x, hxW'⟩ hxW
    have hD := res_mem_span_genOn (W := W') (W' := X.basicOpen g) S hgW' hW'
    rw [res_res] at hD
    exact Opens.mem_iSup.2 ⟨⟨g, exists_pow_smul_mem_span_genOn S W hW g hD⟩, hxg⟩
  exact Submodule.mem_of_span_eq_top_of_smul_pow_mem P T hT s fun g => g.2

/-- The span of `S` has the extension property of II.5.3 over the affine opens in `V`. -/
theorem extendsOver_spanOn [E.IsQuasicoherent] {V : X.Opens} (S : Set Γ(E, V)) :
    ExtendsOver V (spanOn V S) := by
  intro W hWV g t ht
  have hgV : X.basicOpen g ≤ V := (X.basicOpen_le g).trans hWV
  have ht' : t ∈ Submodule.span Γ(X, X.basicOpen g) (genOn V S (X.basicOpen g)) := by
    have h1 : t ∈ Submodule.span Γ(X, X.basicOpen g) (res E hgV '' S) :=
      (sub_spanOn_eq S (X.affineBasicOpen g) hgV).le ht
    rwa [genOn_of_le S hgV]
  obtain ⟨n, p, hp, h⟩ := span_le_powSmulRes_genOn S W hWV g ht'
  exact ⟨n, p, span_le_sub_spanOn S W hWV hp, h.symm⟩

/-! ### Extension inside an affine open -/

lemma ExtendsOver.mono {U U' : X.Opens} {N : E.val.Submodule} (h : ExtendsOver U N)
    (hU : U' ≤ U) : ExtendsOver U' N := fun V hV => h V (hV.trans hU)

/-- If a section `s₀` over the affine open `V` lies in `N` over `D(g)`, then some `g ^ k s₀` lies
in `N` over `D(g')`, provided `N` has the extension property over `D(g')`. -/
theorem exists_pow_smul_res_mem_of_extendsOver [E.IsQuasicoherent] {N : E.val.Submodule}
    (V : X.affineOpens) {g' : Γ(X, V)} (hext : ExtendsOver (X.basicOpen g') N) (g : Γ(X, V))
    {s₀ : Γ(E, V)} (hs₀ : res E (X.basicOpen_le g) s₀ ∈ sub N (X.basicOpen g)) :
    ∃ k : ℕ, res E (X.basicOpen_le g') (g ^ k • s₀) ∈ sub N (X.basicOpen g') := by
  let D : X.affineOpens := X.affineBasicOpen g'
  let h : Γ(X, D) := (X.presheaf.map (homOfLE (X.basicOpen_le g')).op).hom g
  have hDh : X.basicOpen h ≤ X.basicOpen g := by
    change X.basicOpen ((X.presheaf.map (homOfLE (X.basicOpen_le g')).op) g) ≤ _
    rw [Scheme.basicOpen_res]
    exact inf_le_right
  let s₁ : Γ(E, D) := res E (X.basicOpen_le g') s₀
  have hr : res E (X.basicOpen_le h) s₁ ∈ sub N (X.basicOpen h) := by
    have := res_mem N hDh hs₀
    rw [res_res] at this
    rw [show res E (X.basicOpen_le h) s₁ = res E (hDh.trans (X.basicOpen_le g)) s₀ from
      res_res E (X.basicOpen_le g') (X.basicOpen_le h) s₀]
    exact this
  obtain ⟨k, u, hu, e⟩ := hext D le_rfl h _ hr
  have hres : res E (X.basicOpen_le h) (h ^ k • s₁ - u) = 0 := by
    rw [map_sub, LinearMap.map_smulₛₗ, map_pow, e, sub_self]
  obtain ⟨l, hl⟩ := exists_pow_smul_eq_zero_of_isAffineOpen E D.2 h _ hres
  rw [smul_sub, sub_eq_zero, smul_smul, ← pow_add] at hl
  refine ⟨l + k, ?_⟩
  rw [LinearMap.map_smulₛₗ, map_pow]
  change h ^ (l + k) • s₁ ∈ _
  rw [hl]
  exact Submodule.smul_mem _ _ hu

/-- **Extending a local section of `N` to a section of `E` over an affine open `V`.** A section
`t` of `N` over a basic open `D(g)` of `V` is, after multiplication by a power of `g`, the
restriction of a section of `E` over `V` which lies in `N` over each of finitely many basic opens
`D(g')` of `V` over which `N` has the extension property. -/
theorem exists_extension_of_extendsOver [E.IsQuasicoherent] {N : E.val.Submodule}
    (V : X.affineOpens) (G : Finset Γ(X, V)) (hG : ∀ g' ∈ G, ExtendsOver (X.basicOpen g') N)
    (g : Γ(X, V)) {t : Γ(E, X.basicOpen g)} (ht : t ∈ sub N (X.basicOpen g)) :
    ∃ (n : ℕ) (s : Γ(E, V)),
      res E (X.basicOpen_le g) s = (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ n • t ∧
      ∀ g' ∈ G, res E (X.basicOpen_le g') s ∈ sub N (X.basicOpen g') := by
  obtain ⟨m, s₀, hs₀⟩ := exists_pow_smul_extension_of_isAffineOpen E V.2 g t
  replace hs₀ : res E (X.basicOpen_le g) s₀ =
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ m • t := hs₀
  have hs₀N : res E (X.basicOpen_le g) s₀ ∈ sub N (X.basicOpen g) := by
    rw [hs₀]
    exact Submodule.smul_mem _ _ ht
  choose k hk using fun (g' : Γ(X, V)) (hg' : g' ∈ G) =>
    exists_pow_smul_res_mem_of_extendsOver V (hG g' hg') g hs₀N
  let K : ℕ := ∑ g' ∈ G.attach, k g'.1 g'.2
  refine ⟨K + m, g ^ K • s₀, ?_, fun g' hg' => ?_⟩
  · rw [LinearMap.map_smulₛₗ, map_pow, hs₀, smul_smul, ← pow_add]
  · have hle : k g' hg' ≤ K :=
      Finset.single_le_sum (f := fun g'' : G => k g''.1 g''.2) (fun _ _ => Nat.zero_le _)
        (Finset.mem_attach _ ⟨g', hg'⟩)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le' hle
    rw [hj, pow_add, ← smul_smul, LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (hk g' hg')

/-- **Extension inside an affine open** (the argument of Hartshorne II, Exercise 5.15(c), run
inside an affine open `V` of a Noetherian scheme). Suppose `U ∩ V` is covered by basic opens
`D(g) ⊆ U` of `V` over which `N` has the extension property and finitely generated sections. Then
there are finitely many sections `S` of `E` over `V` whose span agrees with `N` on every open
contained in `U ∩ V`. -/
theorem exists_finite_spanOn_eq [IsNoetherian X] [E.IsQuasicoherent] {N : E.val.Submodule}
    (hN : IsLocal N) (U : X.Opens) (V : X.affineOpens)
    (hcov : ∀ x ∈ U ⊓ (V : X.Opens), ∃ g : Γ(X, V), X.basicOpen g ≤ U ∧ x ∈ X.basicOpen g ∧
      ExtendsOver (X.basicOpen g) N ∧
        Module.Finite Γ(X, X.basicOpen g) (sub N (X.basicOpen g))) :
    ∃ S : Set Γ(E, V), S.Finite ∧
      ∀ W : X.Opens, W ≤ U ⊓ (V : X.Opens) → sub (spanOn V S) W = sub N W := by
  classical
  choose gx hgxU hgx hgxE hgxF using fun x : (U ⊓ (V : X.Opens) : X.Opens) => hcov x.1 x.2
  obtain ⟨F, hF⟩ := (NoetherianSpace.isCompact
    ((U ⊓ (V : X.Opens) : X.Opens) : Set X)).elim_finite_subcover
    (fun x : (U ⊓ (V : X.Opens) : X.Opens) => (X.basicOpen (gx x) : Set X))
    (fun _ => (X.basicOpen _).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hgx _⟩)
  let G : Finset Γ(X, V) := F.image gx
  have hGE : ∀ g ∈ G, ExtendsOver (X.basicOpen g) N := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hg
    exact hgxE x
  have hGF : ∀ g ∈ G, Module.Finite Γ(X, X.basicOpen g) (sub N (X.basicOpen g)) := by
    intro g hg
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hg
    exact hgxF x
  have hGcov : ∀ x ∈ U ⊓ (V : X.Opens), ∃ g ∈ G, x ∈ X.basicOpen g := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hF hx)
    exact ⟨gx y, Finset.mem_image_of_mem _ hy, hxy⟩
  -- Finite generating sets of `N` over the `D(g)`.
  choose Tg hTgfin hTgspan using fun (g : Γ(X, V)) (hg : g ∈ G) =>
    Submodule.fg_def.1 (Module.Finite.iff_fg.1 (hGF g hg))
  have hTgN : ∀ g (hg : g ∈ G), ∀ t ∈ Tg g hg, t ∈ sub N (X.basicOpen g) := fun g hg t ht =>
    hTgspan g hg ▸ Submodule.subset_span ht
  choose n s hsA hsB using fun (g : Γ(X, V)) (hg : g ∈ G) (t : Γ(E, X.basicOpen g))
    (ht : t ∈ Tg g hg) => exists_extension_of_extendsOver V G hGE g (hTgN g hg t ht)
  let S : Set Γ(E, V) := Set.range fun p : Σ g : G, Tg g.1 g.2 => s p.1.1 p.1.2 p.2.1 p.2.2
  have hS : S.Finite := by
    have : ∀ g : G, Finite (Tg g.1 g.2) := fun g => (hTgfin g.1 g.2).to_subtype
    exact Set.finite_range _
  -- The elements of `S` lie in `N` over every open `W ⊆ U ∩ V`.
  have hSN : ∀ s' ∈ S, ∀ (W : X.Opens) (hW : W ≤ (V : X.Opens)), W ≤ U →
      res E hW s' ∈ sub N W := by
    rintro _ ⟨⟨⟨g, hg⟩, ⟨t, ht⟩⟩, rfl⟩ W hWV hWU
    refine hN W _ fun x hx => ?_
    obtain ⟨g', hg', hxg'⟩ := hGcov x ⟨hWU hx, hWV hx⟩
    refine ⟨W ⊓ X.basicOpen g', inf_le_left, ⟨hx, hxg'⟩, ?_⟩
    have := res_mem N (inf_le_right : W ⊓ X.basicOpen g' ≤ X.basicOpen g') (hsB g hg t ht g' hg')
    rw [res_res] at this
    rwa [res_res]
  -- The generators of `N(D(g))` lie in the span of `S` over `D(g)`.
  have hTgS : ∀ g (hg : g ∈ G), sub N (X.basicOpen g) ≤
      Submodule.span Γ(X, X.basicOpen g) (genOn V S (X.basicOpen g)) := by
    intro g hg
    rw [← hTgspan g hg, Submodule.span_le]
    intro t ht
    have hu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom g ^ n g hg t ht) :=
      (isUnit_res_of_le_basicOpen g (X.basicOpen_le g) le_rfl).pow _
    refine mem_of_isUnit_smul_mem _ hu ?_
    rw [← hsA g hg t ht]
    exact Submodule.subset_span ⟨X.basicOpen_le g, _, ⟨⟨⟨g, hg⟩, ⟨t, ht⟩⟩, rfl⟩, rfl⟩
  refine ⟨S, hS, fun W hW => le_antisymm (fun a ha => ?_) (fun a ha => ?_)⟩
  · refine hN W a fun x hx => ?_
    obtain ⟨W', hW'W, hxW', hW'⟩ := ha x hx
    refine ⟨W', hW'W, hxW', ?_⟩
    have hle : Submodule.span Γ(X, (W' : X.Opens)) (genOn (V : X.Opens) S (W' : X.Opens)) ≤
        sub N (W' : X.Opens) := by
      rw [Submodule.span_le]
      rintro _ ⟨h, s', hs', rfl⟩
      exact hSN s' hs' W' h ((hW'W.trans hW).trans inf_le_left)
    exact hle hW'
  · intro x hx
    obtain ⟨g, hg, hxg⟩ := hGcov x (hW hx)
    let D : X.affineOpens := X.affineBasicOpen g
    obtain ⟨h, hhW, hxh⟩ := D.2.exists_basicOpen_le (V := W ⊓ X.basicOpen g) ⟨x, hx, hxg⟩ hxg
    let W' : X.affineOpens := X.affineBasicOpen h
    have hW'W : X.basicOpen h ≤ W := hhW.trans inf_le_left
    refine ⟨W', hW'W, hxh, ?_⟩
    have hr : res E hW'W a ∈ sub N (X.basicOpen h) := res_mem N hW'W ha
    obtain ⟨k, u, hu, e⟩ := hGE g hg D le_rfl h _ hr
    have huS := res_mem_span_genOn S (X.basicOpen_le h) (hTgS g hg hu)
    rw [e] at huS
    have hunit : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le h)).op).hom h ^ k) :=
      (isUnit_res_of_le_basicOpen h (X.basicOpen_le h) le_rfl).pow _
    change res E hW'W a ∈ Submodule.span Γ(X, X.basicOpen h) (genOn V S (X.basicOpen h))
    exact mem_of_isUnit_smul_mem _ hunit huS

/-! ### Coherence near the points of an open -/

/-- `N` is *coherent near every point of `U`*: every point of `U` has an affine neighbourhood
`W ⊆ U` over which `N` has the extension property of II.5.3 and `N(W)` is finitely generated. -/
def CoherentNear (N : E.val.Submodule) (U : X.Opens) : Prop :=
  ∀ x ∈ U, ∃ W : X.affineOpens, (W : X.Opens) ≤ U ∧ x ∈ (W : X.Opens) ∧ ExtendsOver W N ∧
    Module.Finite Γ(X, W) (sub N W)

lemma CoherentNear.sup {N : E.val.Submodule} {U₁ U₂ : X.Opens} (h₁ : CoherentNear N U₁)
    (h₂ : CoherentNear N U₂) : CoherentNear N (U₁ ⊔ U₂) := by
  rintro x (hx | hx)
  · obtain ⟨W, hW, hxW, h⟩ := h₁ x hx
    exact ⟨W, hW.trans le_sup_left, hxW, h⟩
  · obtain ⟨W, hW, hxW, h⟩ := h₂ x hx
    exact ⟨W, hW.trans le_sup_right, hxW, h⟩

lemma extendsOver_congr {N₁ N₂ : E.val.Submodule} {U : X.Opens}
    (h : ∀ W : X.Opens, W ≤ U → sub N₁ W = sub N₂ W) : ExtendsOver U N₁ ↔ ExtendsOver U N₂ := by
  unfold ExtendsOver
  refine forall_congr' fun V => forall_congr' fun hVU => forall_congr' fun g =>
    forall_congr' fun t => ?_
  rw [h _ ((X.basicOpen_le g).trans hVU), h _ hVU]

/-- Coherence near the points of `U` only depends on the sections over opens contained in `U`. -/
lemma CoherentNear.congr {N₁ N₂ : E.val.Submodule} {U : X.Opens}
    (h : ∀ W : X.Opens, W ≤ U → sub N₁ W = sub N₂ W) (h₁ : CoherentNear N₁ U) :
    CoherentNear N₂ U := by
  intro x hx
  obtain ⟨W, hWU, hxW, hext, hfin⟩ := h₁ x hx
  refine ⟨W, hWU, hxW, (extendsOver_congr fun W' hW' => h W' (hW'.trans hWU)).1 hext, ?_⟩
  rw [← h W hWU]
  exact hfin

/-- If `N` has the extension property over the affine open `W` and `N(W)` is finitely generated,
then `N(D(f))` is finitely generated for every basic open `D(f)` of `W`. -/
lemma finite_sub_basicOpen {N : E.val.Submodule} {W : X.affineOpens} (hext : ExtendsOver W N)
    (hfin : Module.Finite Γ(X, W) (sub N W)) (f : Γ(X, W)) :
    Module.Finite Γ(X, X.basicOpen f) (sub N (X.basicOpen f)) := by
  obtain ⟨T, hTfin, hT⟩ := Submodule.fg_def.1 (Module.Finite.iff_fg.1 hfin)
  refine Module.Finite.iff_fg.2 (Submodule.fg_def.2
    ⟨res E (X.basicOpen_le f) '' T, hTfin.image _, le_antisymm ?_ ?_⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    exact res_mem N _ (hT ▸ Submodule.subset_span ht)
  · intro t ht
    obtain ⟨n, u, hu, e⟩ := hext W le_rfl f t ht
    have hle : Submodule.span Γ(X, W) T ≤ Submodule.comap (res E (X.basicOpen_le f))
        (Submodule.span Γ(X, X.basicOpen f) (res E (X.basicOpen_le f) '' T)) := by
      rw [Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ⟨t, ht, rfl⟩
    have hu' : res E (X.basicOpen_le f) u ∈
        Submodule.span Γ(X, X.basicOpen f) (res E (X.basicOpen_le f) '' T) :=
      hle (hT.symm ▸ hu)
    rw [e] at hu'
    exact mem_of_isUnit_smul_mem _
      ((isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).pow _) hu'

/-- The span of finitely many sections over an affine open `V` is coherent near every point of
`V`. -/
lemma coherentNear_spanOn [E.IsQuasicoherent] (V : X.affineOpens) {S : Set Γ(E, V)}
    (hS : S.Finite) : CoherentNear (spanOn (V : X.Opens) S) V := fun x hx => by
  refine ⟨V, le_rfl, hx, extendsOver_spanOn S, ?_⟩
  rw [sub_spanOn_eq S V le_rfl]
  exact Module.Finite.span_of_finite _ (hS.image _)

/-- **The extension step.** If `N` is coherent near every point of `U` and `V` is an affine open,
there is a submodule sheaf, coherent near every point of `U ∪ V`, agreeing with `N` on `U`. -/
theorem exists_coherentNear_sup [IsNoetherian X] [E.IsQuasicoherent] {N : E.val.Submodule}
    (hN : IsLocal N) {U : X.Opens} (hU : CoherentNear N U) (V : X.affineOpens) :
    ∃ N₁ : E.val.Submodule, IsLocal N₁ ∧ CoherentNear N₁ (U ⊔ V) ∧
      ∀ W : X.Opens, W ≤ U → sub N₁ W = sub N W := by
  obtain ⟨S, hS, hSN⟩ := exists_finite_spanOn_eq hN U V fun x hx => by
    obtain ⟨W, hWU, hxW, hext, hfin⟩ := hU x hx.1
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter W.2 V.2 x ⟨hxW, hx.2⟩
    have hgW : X.basicOpen g ≤ W := hfg ▸ X.basicOpen_le f
    refine ⟨g, hgW.trans hWU, hfg ▸ hxf, hext.mono hgW, ?_⟩
    rw [← hfg]
    exact finite_sub_basicOpen hext hfin f
  have hP := isLocal_spanOn (V : X.Opens) S
  refine ⟨extOn U N ⊓ extOn V (spanOn V S),
    isLocal_inf (isLocal_extOn U hN) (isLocal_extOn _ hP), ?_, fun W hWU => ?_⟩
  · refine CoherentNear.sup (hU.congr fun W hWU => ?_)
      ((coherentNear_spanOn V hS).congr fun W hWV => ?_)
    · ext s
      refine ⟨fun hs => ⟨(mem_extOn_iff_of_le hN hWU s).2 hs, ?_⟩, fun hs => ?_⟩
      · show res E (inf_le_left : W ⊓ (V : X.Opens) ≤ W) s ∈
          sub (spanOn (V : X.Opens) S) (W ⊓ V)
        rw [hSN _ (inf_le_inf_right _ hWU)]
        exact res_mem N inf_le_left hs
      · exact (mem_extOn_iff_of_le hN hWU s).1 hs.1
    · ext s
      refine ⟨fun hs => ⟨?_, (mem_extOn_iff_of_le hP hWV s).2 hs⟩, fun hs => ?_⟩
      · show res E (inf_le_left : W ⊓ U ≤ W) s ∈ sub N (W ⊓ U)
        rw [← hSN _ (le_inf inf_le_right (inf_le_left.trans hWV))]
        exact res_mem _ inf_le_left hs
      · exact (mem_extOn_iff_of_le hP hWV s).1 hs.2
  · ext s
    refine ⟨fun hs => (mem_extOn_iff_of_le hN hWU s).1 hs.1,
      fun hs => ⟨(mem_extOn_iff_of_le hN hWU s).2 hs, ?_⟩⟩
    show res E (inf_le_left : W ⊓ (V : X.Opens) ≤ W) s ∈ sub (spanOn (V : X.Opens) S) (W ⊓ V)
    rw [hSN _ (inf_le_inf_right _ hWU)]
    exact res_mem N inf_le_left hs

/-- On a Noetherian scheme, a submodule sheaf coherent near every point of `U` agrees on `U` with a
submodule sheaf coherent near every point of `X`. -/
theorem exists_coherentNear_top [IsNoetherian X] [E.IsQuasicoherent] {N : E.val.Submodule}
    (hN : IsLocal N) {U : X.Opens} (hU : CoherentNear N U) :
    ∃ N' : E.val.Submodule, IsLocal N' ∧ CoherentNear N' ⊤ ∧
      ∀ W : X.Opens, W ≤ U → sub N' W = sub N W := by
  classical
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact (Set.univ : Set X)).elim_finite_subcover
    (fun V : X.affineOpens => ((V : X.Opens) : Set X)) (fun V => V.1.isOpen)
    fun x _ => by
      obtain ⟨V, -, hxV⟩ := exists_affine_le (U := ⊤) (x := x) trivial
      exact Set.mem_iUnion.2 ⟨V, hxV⟩
  have key : ∀ t : Finset X.affineOpens, ∃ N' : E.val.Submodule, IsLocal N' ∧
      CoherentNear N' (U ⊔ ⨆ V ∈ t, (V : X.Opens)) ∧
        ∀ W : X.Opens, W ≤ U → sub N' W = sub N W := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨N, hN, by simpa using hU, fun _ _ => rfl⟩
    | insert V t _ ih =>
      obtain ⟨N', hN', hU', heq⟩ := ih
      obtain ⟨N₁, hN₁, hU₁, heq₁⟩ := exists_coherentNear_sup hN' hU' V
      refine ⟨N₁, hN₁, ?_, fun W hW => (heq₁ W (hW.trans le_sup_left)).trans (heq W hW)⟩
      rw [Finset.iSup_insert, sup_left_comm, sup_comm]
      exact hU₁
  obtain ⟨N', hN', hU', heq⟩ := key t
  have htop : U ⊔ ⨆ V ∈ t, (V : X.Opens) = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Or.inr (Opens.mem_iSup.2 ⟨V, Opens.mem_iSup.2 ⟨hV, hxV⟩⟩)
  rw [htop] at hU'
  exact ⟨N', hN', hU', heq⟩

/-- A submodule sheaf of a quasi-coherent `E` which is coherent near every point is coherent. -/
theorem isCoherent_of_coherentNear_top [E.IsQuasicoherent] {N : E.val.Submodule} (hN : IsLocal N)
    (h : CoherentNear N ⊤) : IsCoherent (toModules N hN) := by
  refine ⟨{W : X.affineOpens // ExtendsOver W N ∧ Module.Finite Γ(X, W) (sub N W)},
    fun W => W.1, ?_, fun W => ?_⟩
  · refine top_le_iff.1 fun x _ => ?_
    obtain ⟨W, -, hxW, hW⟩ := h x trivial
    exact Opens.mem_iSup.2 ⟨⟨W, hW⟩, hxW⟩
  · have hiso : IsIso (specRestriction (toModules N hN) W.1).fromTildeΓ := by
      refine isIso_fromTildeΓ_of_pow_smul _ W.1 (fun g s hs => ?_) (fun g t => ?_)
      · let s' : N.obj (op (W.1 : X.Opens)) := s
        have hs' := congrArg (fun x : N.obj (op (X.basicOpen g)) => x.1) hs
        obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isAffineOpen E W.1.2 g s'.1 hs'
        exact ⟨n, Subtype.ext hn⟩
      · let t' : N.obj (op (X.basicOpen g)) := t
        obtain ⟨n, u, hu, e⟩ := W.2.1 W.1 le_rfl g t'.1 t'.2
        exact ⟨n, (⟨u, hu⟩ : N.obj (op (W.1 : X.Opens))), Subtype.ext e⟩
    exact ⟨moduleSpecΓFunctor.obj (specRestriction (toModules N hN) W.1),
      (finite_specRestriction_iff _ W.1).mpr W.2.2,
      ⟨@asIso _ _ _ _ (specRestriction (toModules N hN) W.1).fromTildeΓ hiso⟩⟩

end Hartshorne
